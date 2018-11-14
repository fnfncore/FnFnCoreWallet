// Copyright (c) 2017-2018 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "dbpservice.h"

#include "dbputils.h"
#include <boost/assign/list_of.hpp>
#include <boost/lexical_cast.hpp>
#include <algorithm>

using namespace multiverse;

CDbpService::CDbpService()
    : walleve::IIOModule("dbpservice")
{
    pService = NULL;
    pCoreProtocol = NULL;
    pWallet = NULL;
    pDbpServer = NULL;
    pNetChannel = NULL;

    std::unordered_map<std::string, IdsType> temp_map = 
        boost::assign::map_list_of("all-block", std::set<std::string>())
                                  ("all-tx",    std::set<std::string>())
                                  ("sys-cmd",   std::set<std::string>())
                                  ("tx-cmd",    std::set<std::string>())
                                  ("block-cmd", std::set<std::string>())
                                  ("changed",   std::set<std::string>())
                                  ("removed",   std::set<std::string>());

    mapTopicIds = temp_map;
}

CDbpService::~CDbpService()
{
}

bool CDbpService::WalleveHandleInitialize()
{
    if (!WalleveGetObject("coreprotocol", pCoreProtocol))
    {
        WalleveLog("Failed to request coreprotocol\n");
        return false;
    }

    if (!WalleveGetObject("service", pService))
    {
        WalleveLog("Failed to request service\n");
        return false;
    }

    if (!WalleveGetObject("wallet", pWallet))
    {
        WalleveLog("Failed to request wallet\n");
        return false;
    }

    if (!WalleveGetObject("dbpserver", pDbpServer))
    {
        WalleveLog("Failed to request dbpserver\n");
        return false;
    }

    if(!WalleveGetObject("dbpclient",pDbpClient))
    {
        WalleveLog("Failed to request dbpclient\n");
        return false;
    }

    if (!WalleveGetObject("netchannel",pNetChannel))
    {
        WalleveLog("Failed to request peer net datachannel\n");
        return false;
    }

    return true;
}

void CDbpService::WalleveHandleDeinitialize()
{
    pDbpServer = NULL;
    pService = NULL;
    pCoreProtocol = NULL;
    pWallet = NULL;
    pNetChannel = NULL;
}

bool CDbpService::HandleEvent(CMvEventDbpPong& event)
{
    (void)event;
    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpBroken& event)
{
    mapSessionChildNodeForks.erase(event.strSessionId);
    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpRemoveSession& event)
{
    RemoveSession(event.data.session);
    return true;
}

static std::string GetHex(std::string data)
{
    int n = 2 * data.length() + 1;
    std::string ret;
    const char c_map[16] = {'0', '1', '2', '3', '4', '5', '6', '7',
                            '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};

    ret.reserve(n);
    for (const unsigned char &c : data)
    {
        ret.push_back(c_map[c >> 4]);
        ret.push_back(c_map[c & 15]);
    }

    return ret;
}

static void print_block(const CMvDbpBlock &block)
{
    uint256 hash(std::vector<unsigned char>(block.hash.begin(),block.hash.end()));
    uint256 prevHash(std::vector<unsigned char>(block.hashPrev.begin(),block.hashPrev.end()));
    uint256 forkHash(std::vector<unsigned char>(block.fork.begin(),block.fork.end()));
    
    std::cout << "[<]recived block" << std::endl;
    std::cout << "   hash: " << hash.ToString() << std::endl;
    std::cout << "   height: " << block.nHeight << std::endl;
    std::cout << "   prev hash: " << prevHash.ToString() << std::endl;
    std::cout << "   fork hash: " << forkHash.ToString() << std::endl;

}

static void print_tx(const CMvDbpTransaction &tx)
{
    uint256 hash(std::vector<unsigned char>(tx.hash.begin(),tx.hash.end()));
    uint256 sig(std::vector<unsigned char>(tx.vchSig.begin(),tx.vchSig.end()));
    uint256 forkHash(std::vector<unsigned char>(tx.fork.begin(),tx.fork.end()));

    std::cout << "[<]recived transaction" << std::endl;
    std::cout << "   hash:" << hash.ToString() << std::endl;
    std::cout << "   sig:" << sig.ToString() << std::endl;
    std::cout << "   fork hash:" << forkHash.ToString() << std::endl;
}

static void print_syscmd(const CMvDbpSysCmd &cmd)
{
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    std::cout << "[<]recived sys cmd" << std::endl;
    std::cout << "   fork hash:" << forkHash.ToString() << std::endl;
}

static void print_blockcmd(const CMvDbpBlockCmd &cmd)
{
    uint256 hash(std::vector<unsigned char>(cmd.hash.begin(),cmd.hash.end()));
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    std::cout << "[<]recived block cmd" << std::endl;
    std::cout << "   hash:" << hash.ToString() << std::endl;
    std::cout << "   fork hash:" << forkHash.ToString() << std::endl;
}

static void print_txcmd(const CMvDbpTxCmd &cmd)
{
    uint256 hash(std::vector<unsigned char>(cmd.hash.begin(),cmd.hash.end()));
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    std::cout << "[<]recived tx cmd" << std::endl;
    std::cout << "   hash:" << hash.ToString() << std::endl;
    std::cout << "   fork hash:" << forkHash.ToString() << std::endl;
}

void CDbpService::HandleAddedBlock(const CMvDbpBlock& block)
{
    uint256 forkHash(std::vector<unsigned char>(block.fork.begin(),block.fork.end()));

    if(setThisNodeForks.find(forkHash.ToString()) != setThisNodeForks.end())
    {
        // THIS FORK NODE Handle this TODO
        print_block(block);
    }
    else
    {
        // Push Block to child fork node
        PushBlock(forkHash.ToString(),block);
    }

}

void CDbpService::HandleAddedTx(const CMvDbpTransaction& tx)
{
    uint256 forkHash(std::vector<unsigned char>(tx.fork.begin(),tx.fork.end()));

    if(setThisNodeForks.find(forkHash.ToString()) != setThisNodeForks.end())
    {
        // THIS FORK NODE Handle this TODO
        print_tx(tx);
    }
    else
    {
        // Dispatch Tx to child fork node
        PushTx(forkHash.ToString(),tx);
    }
}

void CDbpService::HandleAddedSysCmd(const CMvDbpSysCmd& cmd)
{
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    if(setThisNodeForks.find(forkHash.ToString()) != setThisNodeForks.end())
    {
        // THIS FORK NODE Handle this TODO
        print_syscmd(cmd);
    }
    else
    {
        // Dispatch SysCmd to child fork node
        PushSysCmd(forkHash.ToString(),cmd);
    }
}

void CDbpService::HandleAddedBlockCmd(const CMvDbpBlockCmd& cmd)
{
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    if(setThisNodeForks.find(forkHash.ToString()) != setThisNodeForks.end())
    {
        // THIS FORK NODE Handle this TODO
        print_blockcmd(cmd);
    }
    else
    {
        // Dispatch BlockCmd to child fork node
        PushBlockCmd(forkHash.ToString(),cmd);
    }
}

void CDbpService::HandleAddedTxCmd(const CMvDbpTxCmd& cmd)
{
    uint256 forkHash(std::vector<unsigned char>(cmd.fork.begin(),cmd.fork.end()));

    if(setThisNodeForks.find(forkHash.ToString()) != setThisNodeForks.end())
    {
        // THIS FORK NODE Handle this TODO
        print_txcmd(cmd);
    }
    else
    {
        // Dispatch TxCmd to child fork node
        PushTxCmd(forkHash.ToString(),cmd);
    }
}

bool CDbpService::HandleEvent(CMvEventDbpAdded& event)
{
    if(event.data.name == "all-block")
    {
        CMvDbpBlock block = boost::any_cast<CMvDbpBlock>(event.data.anyAddedObj);
        HandleAddedBlock(block);
    }
    else if(event.data.name == "all-tx")
    {
        CMvDbpTransaction tx = boost::any_cast<CMvDbpTransaction>(event.data.anyAddedObj);
        HandleAddedTx(tx);
    }
    else if(event.data.name == "sys-cmd")
    {
        CMvDbpSysCmd cmd = boost::any_cast<CMvDbpSysCmd>(event.data.anyAddedObj);
        HandleAddedSysCmd(cmd);
    }
    else if(event.data.name == "block-cmd")
    {
        CMvDbpBlockCmd cmd = boost::any_cast<CMvDbpBlockCmd>(event.data.anyAddedObj);
        HandleAddedBlockCmd(cmd);
    }
    else if(event.data.name == "tx-cmd")
    {
        CMvDbpTxCmd cmd = boost::any_cast<CMvDbpTxCmd>(event.data.anyAddedObj);
        HandleAddedTxCmd(cmd);
    }
    else
    {
        return false;
    }
    
    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpConnect& event)
{
    bool isReconnect = event.data.isReconnect;
    
    if (isReconnect)
    {
        UpdateChildNodeForks(event.strSessionId,event.data.forks);
        
        // reply normal
        CMvEventDbpConnected eventConnected(event.strSessionId);
        eventConnected.data.session = event.data.session;
        pDbpServer->DispatchEvent(&eventConnected);
    }
    else
    {
        if (event.data.version != 1)
        {
            // reply failed
            std::vector<int> versions{1};
            CMvEventDbpFailed eventFailed(event.strSessionId);
            eventFailed.data.reason = "001";
            eventFailed.data.versions = versions;
            eventFailed.data.session = event.data.session;
            pDbpServer->DispatchEvent(&eventFailed);
        }
        else
        {
            
            UpdateChildNodeForks(event.strSessionId,event.data.forks);
            
            // reply normal
            CMvEventDbpConnected eventConnected(event.strSessionId);
            eventConnected.data.session = event.data.session;
            pDbpServer->DispatchEvent(&eventConnected);
        }
    }

    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpSub& event)
{
    std::string id = event.data.id;
    std::string topicName = event.data.name;

    if (!IsTopicExist(topicName))
    {
        // reply nosub
        CMvEventDbpNoSub eventNoSub(event.strSessionId);
        eventNoSub.data.id = event.data.id;
        pDbpServer->DispatchEvent(&eventNoSub);
    }
    else
    {
        SubTopic(id, event.strSessionId, topicName);

        // reply ready
        CMvEventDbpReady eventReady(event.strSessionId);
        eventReady.data.id = id;
        pDbpServer->DispatchEvent(&eventReady);
    }

    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpUnSub& event)
{
    UnSubTopic(event.data.id);
    return true;
}

void CDbpService::HandleGetTransaction(CMvEventDbpMethod& event)
{
    std::string id = event.data.id;
    std::string txid = boost::any_cast<std::string> 
     (event.data.params["hash"]);

    uint256 txHash(txid);
    CTransaction tx;
    uint256 forkHash;
    int blockHeight;

    if (pService->GetTransaction(txHash, tx, forkHash, blockHeight))
    {
        CMvDbpTransaction dbpTx;
        CreateDbpTransaction(tx, forkHash, 0, dbpTx);

        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = id;
        eventResult.data.anyResultObjs.push_back(dbpTx);
        pDbpServer->DispatchEvent(&eventResult);
    }
    else
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = id;
        eventResult.data.error = "404";
        pDbpServer->DispatchEvent(&eventResult);
    }
}

void CDbpService::HandleSendTransaction(CMvEventDbpMethod& event)
{
    std::string data = boost::any_cast 
        <std::string>(event.data.params["data"]);

    std::vector<unsigned char> txData(data.begin(), data.end());
    walleve::CWalleveBufStream ss;
    ss.Write((char *)&txData[0], txData.size());

    CTransaction rawTx;
    try
    {
        ss >> rawTx;
    }
    catch (const std::exception& e)
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = event.data.id;
        eventResult.data.error = "400";
        pDbpServer->DispatchEvent(&eventResult);
        return;
    }

    MvErr err = pService->SendTransaction(rawTx);
    if (err == MV_OK)
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = event.data.id;

        CMvDbpSendTransactionRet sendTxRet;
        sendTxRet.hash = data;
        sendTxRet.result = "succeed";
        eventResult.data.anyResultObjs.push_back(sendTxRet);

        pDbpServer->DispatchEvent(&eventResult);
    }
    else
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = event.data.id;

        CMvDbpSendTransactionRet sendTxRet;
        sendTxRet.hash = data;
        sendTxRet.result = "failed";
        sendTxRet.reason = std::string(MvErrString(err));
        eventResult.data.anyResultObjs.push_back(sendTxRet);

        pDbpServer->DispatchEvent(&eventResult);
    }
}

bool CDbpService::IsTopicExist(const std::string& topic)
{
    return mapTopicIds.find(topic) != mapTopicIds.end();
}

void CDbpService::SubTopic(const std::string& id, const std::string& session, const std::string& topic)
{
    mapTopicIds[topic].insert(id);
    mapIdSubedSession.insert(std::make_pair(id, session));
}

void CDbpService::UnSubTopic(const std::string& id)
{
    for(auto& kv : mapTopicIds)
    {
        kv.second.erase(id);
    }
    mapIdSubedSession.erase(id);
}

void CDbpService::RemoveSession(const std::string& session)
{
    std::vector<std::string> vBeDeletedIds;
    for(const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string valueSession = kv.second;
        if(valueSession == session)
        {
            vBeDeletedIds.push_back(id);
        }
    }

    for(const auto& id : vBeDeletedIds)
    {
        UnSubTopic(id);
    }
}

bool CDbpService::IsEmpty(const uint256& hash)
{
    static const std::string EMPTY_HASH("0000000000000000000000000000000000000000000000000000000000000000");
    return hash.ToString() == EMPTY_HASH;
}

bool CDbpService::IsForkHash(const uint256& hash)
{
    std::vector<std::pair<uint256,CProfile>> forks;
    pService->ListFork(forks);

    for(const auto& fork : forks)
    {
        if(fork.first == hash)
        {
            return true;
        }
    }

    return false;
}

void CDbpService::TrySwitchFork(const uint256& blockHash,uint256& forkHash)
{
    auto it = mapForkPoint.find(blockHash.ToString());
    if(it != mapForkPoint.end())
    {
        auto value = it->second; 
        forkHash = value.first;
    } 
}

bool CDbpService::CalcForkPoints(const uint256& forkHash)
{
    std::vector<std::pair<uint256,int>> vAncestors;
    std::vector<std::pair<int,uint256>> vSublines;
    std::vector<std::pair<uint256,uint256>> path;
    if(!pService->GetForkGenealogy(forkHash,vAncestors,vSublines))
    {
        return false;
    }

    std::vector<std::pair<uint256,uint256>> forkAncestors;
    for(int i = vAncestors.size() - 1; i >= 0; i--)
    {
        CBlock block;
        uint256 tempFork;
        int nHeight = 0;
        pService->GetBlock(vAncestors[i].first,block,tempFork,nHeight);
        forkAncestors.push_back(std::make_pair(vAncestors[i].first,block.hashPrev));
    }

    path = forkAncestors;
    CBlock block;
    uint256 tempFork;
    int nHeight = 0;
    pService->GetBlock(forkHash,block,tempFork,nHeight);
    path.push_back(std::make_pair(forkHash,block.hashPrev));

    for(const auto& fork : path)
    {
        mapForkPoint.insert(std::make_pair(fork.second.ToString(), 
            std::make_pair(fork.first,fork.second)));
    }
    
    return true;
}

bool CDbpService::GetBlocks(const uint256& forkHash, const uint256& startHash, int32 n, std::vector<CMvDbpBlock>& blocks)
{
    uint256 connectForkHash = forkHash;
    uint256 blockHash = startHash;

    if (IsEmpty(connectForkHash))
    {
        connectForkHash = pCoreProtocol->GetGenesisBlockHash();
    }

    if(!IsForkHash(connectForkHash))
    {
        std::cerr << "connect fork hash is not a fork hash.\n";
        return false;
    }

    if (IsEmpty(blockHash))
    {
        blockHash = pCoreProtocol->GetGenesisBlockHash();
    }

    int blockHeight = 0;
    uint256 tempForkHash;
    if (!pService->GetBlockLocation(blockHash, tempForkHash, blockHeight))
    {
        return false;
    }

    if(!CalcForkPoints(connectForkHash))
    {
        std::cerr << "CalcForkPoint failed.\n";
        return false;
    }

    const std::size_t nonExtendBlockMaxNum = n;
    std::size_t nonExtendBlockCount = 0;
    
    pService->GetBlockLocation(blockHash, tempForkHash, blockHeight);
    
    std::vector<uint256> blocksHash;
    while (nonExtendBlockCount < nonExtendBlockMaxNum && 
            pService->GetBlockHash(tempForkHash, blockHeight, blocksHash))
    {
        for(int i = 0; i < blocksHash.size(); ++i)
        {
            CBlockEx block;
            int height;
            pService->GetBlockEx(blocksHash[i], block, tempForkHash, height);
            if (block.nType != CBlock::BLOCK_EXTENDED)
            {
                nonExtendBlockCount++;
            }

            CMvDbpBlock DbpBlock;
            CreateDbpBlock(block, tempForkHash, height, DbpBlock);
            blocks.push_back(DbpBlock);
        }
        
        TrySwitchFork(blocksHash[0],tempForkHash);
        blockHeight++;
        blocksHash.clear(); blocksHash.shrink_to_fit();
    }

    return true;
}

void CDbpService::HandleGetBlocks(CMvEventDbpMethod& event)
{
    std::string forkid = boost::any_cast<std::string>(event.data.params["forkid"]);
    std::string blockHash = boost::any_cast<std::string>(event.data.params["hash"]);
    std::string num = boost::any_cast<std::string>(event.data.params["number"]);
    int32 blockNum = boost::lexical_cast<int32>(num);
    
    uint256 startBlockHash(std::vector<unsigned char>(blockHash.begin(), blockHash.end()));
    uint256 forkHash;
    forkHash.SetHex(forkid);
    std::vector<CMvDbpBlock> blocks;
    if (GetBlocks(forkHash, startBlockHash, blockNum, blocks))
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = event.data.id;

        for (auto& block : blocks)
        {
            eventResult.data.anyResultObjs.push_back(block);
        }

        pDbpServer->DispatchEvent(&eventResult);
    }
    else
    {
        CMvEventDbpMethodResult eventResult(event.strSessionId);
        eventResult.data.id = event.data.id;
        eventResult.data.error = "400";
        pDbpServer->DispatchEvent(&eventResult);
    }
}

bool CDbpService::HandleEvent(CMvEventDbpRegisterForkID& event)
{
    std::string& forkid = event.data.forkid;
    if(!forkid.empty())
    {
        setThisNodeForks.insert(forkid);
    }
    else
    {
        UpdateChildNodeForksToParent();
    }
    
    return true;
}

void CDbpService::HandleRegisterFork(CMvEventDbpMethod& event)
{
    std::string forkid = boost::any_cast<std::string>(event.data.params["forkid"]);
    UpdateChildNodeForks(event.strSessionId,forkid);

    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpRegisterForkIDRet ret;
    ret.forkid = forkid;
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);

    UpdateChildNodeForksToParent();    
}

void CDbpService::HandleSendBlock(CMvEventDbpMethod& event)
{
    std::string id = boost::any_cast<std::string>(event.data.params["id"]);
    CMvDbpBlock block = boost::any_cast<CMvDbpBlock>(event.data.params["data"]);
    
    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpSendBlockRet ret;
    ret.hash = std::string(block.hash.begin(), block.hash.end()); 
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);


    // TO DO

    SendBlockToParent(id, block);
}

void CDbpService::HandleSendTx(CMvEventDbpMethod& event)
{
    std::string id = boost::any_cast<std::string>(event.data.params["id"]);
    CMvDbpTransaction tx = boost::any_cast<CMvDbpTransaction>(event.data.params["data"]);

    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpSendTxRet ret;
    ret.hash = std::string(tx.hash.begin(), tx.hash.end()); 
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);


    // TODO

    SendTxToParent(id, tx);
    
}

void CDbpService::HandleSendBlockNotice(CMvEventDbpMethod& event)
{
    std::string forkid = boost::any_cast<std::string>(event.data.params["forkid"]);
    std::string height = boost::any_cast<std::string>(event.data.params["height"]);
    std::string hash = boost::any_cast<std::string>(event.data.params["hash"]);
    
    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpSendBlockNoticeRet ret;
    ret.hash = hash;
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);

    // TO DO

    SendBlockNoticeToParent(forkid,height,hash);
}

void CDbpService::HandleSendTxNotice(CMvEventDbpMethod& event)
{
    std::string forkid = boost::any_cast<std::string>(event.data.params["forkid"]);
    std::string hash = boost::any_cast<std::string>(event.data.params["hash"]);

    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpSendTxNoticeRet ret;
    ret.hash = hash;
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);

    // TO DO

    SendTxNoticeToParent(forkid,hash);
}

void CDbpService::HandleGetSNBlocks(CMvEventDbpMethod& event)
{
    std::string forkid = boost::any_cast<std::string>(event.data.params["forkid"]);
    std::string hash = boost::any_cast<std::string>(event.data.params["hash"]);
    std::string number = boost::any_cast<std::string>(event.data.params["number"]);
    int32 blockNum = boost::lexical_cast<int32>(number);

    CMvEventDbpMethodResult eventResult(event.strSessionId);
    eventResult.data.id = event.data.id;
    CMvDbpGetBlocksRet ret;
    ret.hash = hash;
    eventResult.data.anyResultObjs.push_back(ret);
    pDbpServer->DispatchEvent(&eventResult);

    // TO DO

    GetBlocksFromParent(forkid,hash,blockNum);
}

bool CDbpService::HandleEvent(CMvEventDbpMethod& event)
{
    if (event.data.method == CMvDbpMethod::LwsMethod::GET_BLOCKS)
    {
        HandleGetBlocks(event);
    }
    else if (event.data.method == CMvDbpMethod::LwsMethod::GET_TRANSACTION)
    {
        HandleGetTransaction(event);
    }
    else if (event.data.method == CMvDbpMethod::LwsMethod::SEND_TRANSACTION)
    {
        HandleSendTransaction(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::REGISTER_FORK)
    {
        HandleRegisterFork(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::SEND_BLOCK)
    {
        HandleSendBlock(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::SEND_TX)
    {
        HandleSendTx(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::SEND_BLOCK_NOTICE)
    {
        HandleSendBlockNotice(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::SEND_TX_NOTICE)
    {
        HandleSendTxNotice(event);
    }
    else if(event.data.method == CMvDbpMethod::SNMethod::GET_BLOCKS_SN)
    {
        HandleGetSNBlocks(event);
    }
    else
    {
        return false;
    }

    return true;
}

void CDbpService::CreateDbpBlock(const CBlockEx& blockDetail, const uint256& forkHash,
                                 int blockHeight, CMvDbpBlock& block)
{
    block.nVersion = blockDetail.nVersion;
    block.nType = blockDetail.nType;
    block.nTimeStamp = blockDetail.nTimeStamp;

    walleve::CWalleveODataStream hashPrevStream(block.hashPrev);
    blockDetail.hashPrev.ToDataStream(hashPrevStream);

    walleve::CWalleveODataStream hashMerkleStream(block.hashMerkle);
    blockDetail.hashMerkle.ToDataStream(hashMerkleStream);

    block.vchProof = blockDetail.vchProof;
    block.vchSig = blockDetail.vchSig;

    // txMint
    CreateDbpTransaction(blockDetail.txMint, forkHash, blockDetail.txMint.GetChange(0), block.txMint);

    // vtx
    int k = 0;
    for (const auto& tx : blockDetail.vtx)
    {
        CMvDbpTransaction dbpTx;
        int64 nValueIn = blockDetail.vTxContxt[k++].GetValueIn();
        CreateDbpTransaction(tx, forkHash, tx.GetChange(nValueIn), dbpTx);
        block.vtx.push_back(dbpTx);
    }

    block.nHeight = blockHeight;
    walleve::CWalleveODataStream hashStream(block.hash);
    blockDetail.GetHash().ToDataStream(hashStream);

    walleve::CWalleveODataStream forkStream(block.fork);
    forkHash.ToDataStream(forkStream);
}

void CDbpService::CreateDbpTransaction(const CTransaction& tx, const uint256& forkHash, int64 nChange, CMvDbpTransaction& dbptx)
{
    dbptx.nVersion = tx.nVersion;
    dbptx.nType = tx.nType;
    dbptx.nLockUntil = tx.nLockUntil;

    walleve::CWalleveODataStream hashAnchorStream(dbptx.hashAnchor);
    tx.hashAnchor.ToDataStream(hashAnchorStream);

    for (const auto& input : tx.vInput)
    {
        CMvDbpTxIn txin;
        txin.n = input.prevout.n;

        walleve::CWalleveODataStream txInHashStream(txin.hash);
        input.prevout.hash.ToDataStream(txInHashStream);

        dbptx.vInput.push_back(txin);
    }

    dbptx.cDestination.prefix = tx.sendTo.prefix;
    dbptx.cDestination.size = tx.sendTo.DESTINATION_SIZE;

    walleve::CWalleveODataStream sendtoStream(dbptx.cDestination.data);
    tx.sendTo.data.ToDataStream(sendtoStream);

    dbptx.nAmount = tx.nAmount;
    dbptx.nTxFee = tx.nTxFee;
    dbptx.nChange = nChange;

    dbptx.vchData = tx.vchData;
    dbptx.vchSig = tx.vchSig;

    walleve::CWalleveODataStream hashStream(dbptx.hash);
    tx.GetHash().ToDataStream(hashStream);

    walleve::CWalleveODataStream forkStream(dbptx.fork);
    forkHash.ToDataStream(forkStream);
}

void CDbpService::PushBlock(const std::string& forkid, const CMvDbpBlock& block)
{
    const auto& allBlockIds = mapTopicIds["all-block"];   
    for (const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string session = kv.second;

        if (allBlockIds.find(id) != allBlockIds.end())
        {
            CMvEventDbpAdded eventAdded(session);
            eventAdded.data.id = id;
            eventAdded.data.forkid = forkid;
            eventAdded.data.name = "all-block";
            eventAdded.data.anyAddedObj = block;
            pDbpServer->DispatchEvent(&eventAdded);
        }
    }
}

void CDbpService::PushTx(const std::string& forkid, const CMvDbpTransaction& dbptx)
{
    const auto& allTxIds = mapTopicIds["all-tx"];
    for (const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string session = kv.second;

        if (allTxIds.find(id) != allTxIds.end())
        {
            CMvEventDbpAdded eventAdded(session);
            eventAdded.data.id = id;
            eventAdded.data.forkid = forkid;
            eventAdded.data.name = "all-tx";
            eventAdded.data.anyAddedObj = dbptx;
            pDbpServer->DispatchEvent(&eventAdded);
        }
    }
}

void CDbpService::PushSysCmd(const std::string& forkid, const CMvDbpSysCmd& syscmd)
{
    const auto& sysCmdIds = mapTopicIds["sys-cmd"];
    for (const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string session = kv.second;

        if (sysCmdIds.find(id) != sysCmdIds.end())
        {
            CMvEventDbpAdded eventAdded(session);
            eventAdded.data.id = id;
            eventAdded.data.forkid = forkid;
            eventAdded.data.name = "sys-cmd";
            eventAdded.data.anyAddedObj = syscmd;
            pDbpServer->DispatchEvent(&eventAdded);
        }
    }
}

void CDbpService::PushTxCmd(const std::string& forkid, const CMvDbpTxCmd& txcmd)
{
    const auto& txCmdIds = mapTopicIds["tx-cmd"];
    for (const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string session = kv.second;

        if (txCmdIds.find(id) != txCmdIds.end())
        {
            CMvEventDbpAdded eventAdded(session);
            eventAdded.data.id = id;
            eventAdded.data.forkid = forkid;
            eventAdded.data.name = "tx-cmd";
            eventAdded.data.anyAddedObj = txcmd;
            pDbpServer->DispatchEvent(&eventAdded);
        }
    }
}

void CDbpService::PushBlockCmd(const std::string& forkid, const CMvDbpBlockCmd& blockcmd)
{
    const auto& blockCmdIds = mapTopicIds["block-cmd"];
    for (const auto& kv : mapIdSubedSession)
    {
        std::string id = kv.first;
        std::string session = kv.second;

        if (blockCmdIds.find(id) != blockCmdIds.end())
        {
            CMvEventDbpAdded eventAdded(session);
            eventAdded.data.id = id;
            eventAdded.data.forkid = forkid;
            eventAdded.data.name = "block-cmd";
            eventAdded.data.anyAddedObj = blockcmd;
            pDbpServer->DispatchEvent(&eventAdded);
        }
    }
}

void CDbpService::UpdateChildNodeForks(const std::string& session, const std::string& forks)
{
    std::vector<std::string> vForks = CDbpUtils::Split(forks,';');
    ForksType setForks;
    for(const auto& fork : vForks)
    {
        setForks.insert(fork);
    }
    
    if(mapSessionChildNodeForks.count(session) == 0)
    {
        mapSessionChildNodeForks[session] = setForks;
    }
    else
    {
        auto& forks = mapSessionChildNodeForks[session];
        forks.insert(setForks.begin(),setForks.end());
    }
}

void CDbpService::UpdateChildNodeForksToParent()
{
    for(const auto& kv : mapSessionChildNodeForks)
    {
        std::string session = kv.first;
        auto forks = kv.second;
        for(const std::string& forkid : forks)
        {
            CMvEventDbpRegisterForkID eventRegister("");
            eventRegister.data.forkid = forkid;
            pDbpClient->DispatchEvent(&eventRegister);
        }
    }

    for(const std::string& forkid : setThisNodeForks)
    {
        CMvEventDbpRegisterForkID eventRegister("");
        eventRegister.data.forkid = forkid;
        pDbpClient->DispatchEvent(&eventRegister);
    }
}

void CDbpService::SendBlockToParent(const std::string& id, const CMvDbpBlock& block)
{
    CMvEventDbpSendBlock eventSendBlock("");
    eventSendBlock.data.id = id;
    eventSendBlock.data.block = block;
    pDbpClient->DispatchEvent(&eventSendBlock);
}

void CDbpService::SendTxToParent(const std::string& id, const CMvDbpTransaction& tx)
{
    CMvEventDbpSendTx eventSendTx("");
    eventSendTx.data.id = id;
    eventSendTx.data.tx = tx;
    pDbpClient->DispatchEvent(&eventSendTx);
}

void CDbpService::SendBlockNoticeToParent(const std::string& forkid, const std::string& height, const std::string& hash)
{
    uint256 forkid256(std::vector<uint8>(forkid.begin(), forkid.end()));
    uint256 hash256(std::vector<uint8>(hash.begin(), hash.end()));
    
    CMvEventDbpSendBlockNotice eventSendBlockNotice("");
    eventSendBlockNotice.data.forkid = forkid256.ToString();
    eventSendBlockNotice.data.height = height;
    eventSendBlockNotice.data.hash = hash256.ToString();
    pDbpClient->DispatchEvent(&eventSendBlockNotice);
}

void CDbpService::SendTxNoticeToParent(const std::string& forkid, const std::string& hash)
{
    uint256 forkid256(std::vector<uint8>(forkid.begin(), forkid.end()));
    uint256 hash256(std::vector<uint8>(hash.begin(), hash.end()));

    CMvEventDbpSendTxNotice eventSendTxNotice("");
    eventSendTxNotice.data.forkid = forkid256.ToString();
    eventSendTxNotice.data.hash = hash256.ToString();
    pDbpClient->DispatchEvent(&eventSendTxNotice);
}

void CDbpService::GetBlocksFromParent(const std::string& forkid, const std::string& hash, int32 num)
{
    uint256 forkid256(std::vector<uint8>(forkid.begin(), forkid.end()));
    uint256 hash256(std::vector<uint8>(hash.begin(), hash.end()));
    
    CMvEventDbpGetBlocks eventGetBlocks("");
    eventGetBlocks.data.forkid = forkid256.ToString();
    eventGetBlocks.data.hash = hash256.ToString();
    eventGetBlocks.data.number = num;
    pDbpClient->DispatchEvent(&eventGetBlocks);
}


bool CDbpService::HandleEvent(CMvEventDbpUpdateNewBlock& event)
{
    // get details about new block
    CBlockEx& newBlock = event.data;
    uint256 forkHash;
    int blockHeight = 0;
    if (pService->GetBlockLocation(newBlock.GetHash(),forkHash,blockHeight))
    {
        CMvDbpBlock block;
        CreateDbpBlock(newBlock, forkHash, blockHeight, block);
        PushBlock(forkHash.ToString(),block);
    }

    return true;
}

bool CDbpService::HandleEvent(CMvEventDbpUpdateNewTx& event)
{
    decltype(event.data)& newtx = event.data;
    uint256& hashFork = event.hashFork;
    int64& change = event.nChange;

    CMvDbpTransaction dbpTx;
    CreateDbpTransaction(newtx, hashFork, change, dbpTx);
    PushTx(hashFork.ToString(),dbpTx);

    return true;
}

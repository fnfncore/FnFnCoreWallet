// Copyright (c) 2017-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef MULTIVERSE_RPCMOD_H
#define MULTIVERSE_RPCMOD_H

#include "json/json_spirit.h"
#include <boost/function.hpp>
#include <thread>

#include "walleve/walleve.h"

#include "event.h"
#include "mvbase.h"
#include "rpc/rpc.h"
#include "event.h"

namespace multiverse
{

class CRPCMod : public walleve::IIOModule, virtual public walleve::CWalleveHttpEventListener, virtual public CMvRPCModEventListener
{
public:
    CRPCMod();
    ~CRPCMod();
    bool HandleEvent(walleve::CWalleveEventHttpReq& eventHttpReq) override;
    bool HandleEvent(walleve::CWalleveEventHttpBroken& eventHttpBroken) override;
    bool HandleEvent(CMvEventRPCModResponse& eventRPCModResponse) override;

protected:
    struct CWork
    {
        size_t nWorkId;
        size_t nRemainder;
        bool fArray;
        rpc::CRPCReqVec vecReq;
        rpc::CRPCRespVec vecResp;
    };

protected:
    bool WalleveHandleInitialize() override;
    void WalleveHandleDeinitialize() override;
    void JsonReply(uint64 nNonce, const std::string& result);

    bool CheckVersion(std::string& strVersion);
    void AssignWork(const uint64 nNonce, const CWork& work);

protected:
    walleve::IIOProc* pHttpServer;
    walleve::IIOModule* pRPCModWorker;

    std::map<uint64, std::list<CWork>> mapWork;
    size_t nWorkId;
};

class CRPCModWorker : public walleve::IIOModule, virtual public CMvRPCModEventListener
{
    typedef rpc::CRPCResultPtr (CRPCModWorker::*RPCFunc)(rpc::CRPCParamPtr param);

public:
    CRPCModWorker(const uint nThreadIn = std::thread::hardware_concurrency() / 2 + 1, const bool fAffinity = false);
    ~CRPCModWorker();
    bool HandleEvent(CMvEventRPCModRequest& eventRPCModRequest) override;

protected:
    struct CDestFork
    {
        CDestination dest;
        uint256 hashFork;
        friend inline bool operator<(const CDestFork& lhs, const CDestFork& rhs)
        {
            return (lhs.dest < rhs.dest) || (lhs.dest == rhs.dest && lhs.hashFork < rhs.hashFork);
        }
    };

    struct CDestMutex
    {
        size_t nRef = 0;
        mutable boost::mutex mtx;
    };
    typedef std::shared_ptr<CDestMutex> CDestMutexPtr;

    class CDestForkLock
    {
    public:
        CDestForkLock(const CDestFork& destForkIn, boost::mutex& destForkMutexIn,
                      std::map<CDestFork, CDestMutexPtr>& mapDestMutexIn)
        : destFork(destForkIn), destForkMutex(destForkMutexIn), mapDestMutex(mapDestMutexIn)
        {
            {
                boost::unique_lock<boost::mutex> lock(destForkMutex);
                auto it = mapDestMutex.find(destFork);
                if (it == mapDestMutex.end())
                {
                    it = mapDestMutex.insert(make_pair(destFork, CDestMutexPtr(new CDestMutex))).first;
                }
                spDestMutex = it->second;
                ++spDestMutex->nRef;
            }
            spDestMutex->mtx.lock();
        }
        ~CDestForkLock()
        {
            spDestMutex->mtx.unlock();
            {
                boost::unique_lock<boost::mutex> lock(destForkMutex);
                if (--spDestMutex->nRef == 0)
                {
                    mapDestMutex.erase(destFork);
                }
            }
        }
    protected:
        const CDestFork& destFork;
        std::map<CDestFork, CDestMutexPtr>& mapDestMutex;
        boost::mutex& destForkMutex;
        CDestMutexPtr spDestMutex;
    };

protected:
    bool WalleveHandleInitialize() override;
    void WalleveHandleDeinitialize() override;

    const CMvNetworkConfig* WalleveConfig();
    int GetInt(const rpc::CRPCInt64& i, int valDefault);
    unsigned int GetUint(const rpc::CRPCUint64& i, unsigned int valDefault);
    const bool GetForkHashOfDef(const rpc::CRPCString& hex, uint256& hashFork);
    bool CheckWalletError(MvErr err);
    multiverse::crypto::CPubKey GetPubKey(const std::string& addr);
    void ListDestination(std::vector<CDestination>& vDestination);

private:
    /* System */
    rpc::CRPCResultPtr RPCHelp(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCStop(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCVersion(rpc::CRPCParamPtr param);
    /* Network */
    rpc::CRPCResultPtr RPCGetPeerCount(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCListPeer(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCAddNode(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCRemoveNode(rpc::CRPCParamPtr param);
    /* Worldline & TxPool */
    rpc::CRPCResultPtr RPCGetForkCount(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCListFork(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetForkGenealogy(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetBlockLocation(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetBlockCount(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetBlockHash(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetBlock(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetTxPool(rpc::CRPCParamPtr param);
    // CRPCResultPtr RPCRemovePendingTx(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetTransaction(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCSendTransaction(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetForkHeight(rpc::CRPCParamPtr param);
    /* Wallet */
    rpc::CRPCResultPtr RPCListKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetNewKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCEncryptKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCLockKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCUnlockKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCImportPrivKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCImportKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCExportKey(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCAddNewTemplate(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCImportTemplate(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCExportTemplate(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCValidateAddress(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCResyncWallet(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetBalance(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCListTransaction(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCSendFrom(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCCreateTransaction(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCSignTransaction(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCSignMessage(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCListAddress(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCExportWallet(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCImportWallet(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCMakeOrigin(rpc::CRPCParamPtr param);
    /* Util */
    rpc::CRPCResultPtr RPCVerifyMessage(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCMakeKeyPair(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetPubKeyAddress(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCGetTemplateAddress(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCMakeTemplate(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCDecodeTransaction(rpc::CRPCParamPtr param);
    /* Mint */
    rpc::CRPCResultPtr RPCGetWork(rpc::CRPCParamPtr param);
    rpc::CRPCResultPtr RPCSubmitWork(rpc::CRPCParamPtr param);

public:
    virtual rpc::CRPCResultPtr SnRPCStop(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetForkCount(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCListFork(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetBlockLocation(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetBlockCount(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetBlockHash(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetBlock(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetTxPool(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetTransaction(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCGetForkHeight(rpc::CRPCParamPtr param);
    virtual rpc::CRPCResultPtr SnRPCSendTransaction(rpc::CRPCParamPtr param);

protected:
    ICoreProtocol* pCoreProtocol;
    IService* pService;
    walleve::IIOModule* pRPCMod;

    mutable boost::mutex destForkMutex;
    std::map<CDestFork, CDestMutexPtr> mapDestMutex;
    std::map<std::string, RPCFunc> mapRPCFunc;
};

class CSnRPCModWorker : public CRPCModWorker, virtual public CDBPEventListener
{
public:
    CSnRPCModWorker(const uint nThreadIn = 1, const bool fAffinity = false);
    ~CSnRPCModWorker();
    rpc::CRPCResultPtr SnRPCStop(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetForkCount(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCListFork(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetBlockLocation(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetBlockCount(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetBlockHash(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetBlock(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetTxPool(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetTransaction(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCGetForkHeight(rpc::CRPCParamPtr param) override;
    rpc::CRPCResultPtr SnRPCSendTransaction(rpc::CRPCParamPtr param) override;

protected:
    bool WalleveHandleInitialize() override;
    void WalleveHandleDeinitialize() override;
    uint64 GenNonce();
    void DelCompltUntilByNonce(uint64 nNonce);

protected:
    walleve::IIOModule* pDbpService;
};

} // namespace multiverse

#endif //MULTIVERSE_RPCMOD_H

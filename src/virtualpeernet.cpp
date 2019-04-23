// Copyright (c) 2017-2018 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "virtualpeernet.h"
#include "walleve/peernet/peer.h"

#include <thread>

using namespace multiverse;
using namespace walleve;

const std::string CVirtualPeerNet::SENDER_NETCHN = "netchannel";
const std::string CVirtualPeerNet::SENDER_DBPSVC = "dbpservice";

CVirtualPeerNet::CVirtualPeerNet()
: CMvPeerNet("virtualpeernet")
{
    pDbpService = NULL;
    pCoreProtocol = NULL;
    pForkManager = NULL;
    typeNode = SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN;
}

CVirtualPeerNet::~CVirtualPeerNet()
{
}

//set node type as FNFN or not, must be invoked by dbpservice first
void CVirtualPeerNet::SetNodeTypeAsFnfn(bool fIsFnfnNode)
{
    if(fIsFnfnNode)
    {
        typeNode = SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN;
    }
    else
    {
        typeNode = SUPER_NODE_TYPE::SUPER_NODE_TYPE_UNKN;
    }
}

//set node type as ROOT or FORK, must be called
// followed by the calling to the above (caller is dbpservice)
void CVirtualPeerNet::SetNodeTypeAsSuperNode(bool fIsRootNode)
{
    if(fIsRootNode)
    {
        typeNode = SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT;
    }
    else
    {
        typeNode = SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK;
    }
}

void CVirtualPeerNet::EnableSuperNode(bool fIsFork)
{
    typeNode= fIsFork ? SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK : SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT;
}

bool CVirtualPeerNet::WalleveHandleInitialize()
{
    CMvPeerNet::WalleveHandleInitialize();

    if (!WalleveGetObject("dbpservice", pDbpService))
    {
        WalleveLog("Failed to request DBP service\n");
        return false;
    }

    if(!WalleveGetObject("coreprotocol", pCoreProtocol))
    {
        WalleveLog("Failed to request coreprotocol\n");
        return false;
    }

    if(!WalleveGetObject("forkmanager", pForkManager))
    {
        WalleveLog("Failed to request forkmanager\n");
        return false;
    }

    return true;
}

void CVirtualPeerNet::WalleveHandleDeinitialize()
{
    CMvPeerNet::WalleveHandleDeinitialize();

    pDbpService = NULL;
    pCoreProtocol = NULL;
    pForkManager = NULL;
}

//must be invoked by dbpservice only to notify netchannel
// to active a pseudo peer just existing at top root node
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerActive& eventActive)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        if(!HandleForkPeerActive(eventActive))
        {
            return false;
        }
    }
    return true;
}

//must be invoked by dbpservice only to notify netchannel
// to deactive a pseudo peer just existing at top root node
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerDeactive& eventDeactive)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        if(!HandleForkPeerDeactive(eventDeactive))
        {
            return false;
        }
    }
    return true;
}

//reward event generated by fork nodes accumulate up to root node
bool CVirtualPeerNet::HandleEvent(walleve::CWalleveEventPeerNetReward& eventReward)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT
       || typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CPeerNet::HandleEvent(eventReward);
    }
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        walleve::CWalleveEventPeerNetReward* pEvent = new walleve::CWalleveEventPeerNetReward(eventReward);
        if(!pEvent)
        {
            return false;
        }
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//close event generated by fork nodes accumulate up to root node
bool CVirtualPeerNet::HandleEvent(walleve::CWalleveEventPeerNetClose& eventClose)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT
       || typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        std::cout << "net close thread id " << std::this_thread::get_id() << " [vpeernet]\n";
        return CPeerNet::HandleEvent(eventClose);
    }
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        walleve::CWalleveEventPeerNetClose* pEvent = new walleve::CWalleveEventPeerNetClose(eventClose);
        if(!pEvent)
        {
            return false;
        }
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//message pump for SUB event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerSubscribe& eventSubscribe)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventSubscribe);
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventSubscribe.sender)
        {
            return CMvPeerNet::HandleEvent(eventSubscribe);
        }

        if(SENDER_DBPSVC == eventSubscribe.sender)
        {
            vector<uint256> vHashFork = eventSubscribe.data;
            vector<uint256> vFork;
            vector<uint256> vMyFork;
            for (auto subHash = vHashFork.cbegin(); subHash != vHashFork.cend(); ++subHash)
            {
                if(IsMainFork(*subHash) || pForkManager->IsAllowed(*subHash))
                {
                    vMyFork.push_back(*subHash);
                }
                else
                {
                    vFork.push_back(*subHash);
                }
            }

            if (!vMyFork.empty())
            {
                network::CMvEventPeerSubscribe* pEvent = new network::CMvEventPeerSubscribe(eventSubscribe.nNonce, eventSubscribe.hashFork);
                if (!pEvent)
                {
                    return false;
                }

                pEvent->data = vMyFork;
                pNetChannel->PostEvent(pEvent);
            }

            if (!vFork.empty())
            { 
                network::CMvEventPeerSubscribe event(eventSubscribe.nNonce, eventSubscribe.hashFork);
                event.data = vFork;
                return CMvPeerNet::HandleEvent(event);
            }

            return true;
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerSubscribe* pEvent = new network::CMvEventPeerSubscribe(eventSubscribe);
        if(!pEvent)
        {
            return false;
        }

        if(SENDER_NETCHN == eventSubscribe.sender)
        {
            pDbpService->PostEvent(pEvent);
        }

        if(SENDER_DBPSVC == eventSubscribe.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for UNSUB event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerUnsubscribe& eventUnsubscribe)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventUnsubscribe);
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventUnsubscribe.sender)
        {
            return CMvPeerNet::HandleEvent(eventUnsubscribe);
        }

        if (SENDER_DBPSVC == eventUnsubscribe.sender)
        {
            vector<uint256> vHashFork = eventUnsubscribe.data;
            vector<uint256> vFork;
            vector<uint256> vMyFork;
            for (auto subHash = vHashFork.cbegin(); subHash != vHashFork.cend(); ++subHash)
            {
                if (IsMainFork(*subHash) || pForkManager->IsAllowed(*subHash))
                {
                    vMyFork.push_back(*subHash);
                }
                else
                {
                    vFork.push_back(*subHash);
                }
            }
            
            if(!vMyFork.empty())
            {
                network::CMvEventPeerUnsubscribe* pEvent = new network::CMvEventPeerUnsubscribe(eventUnsubscribe.nNonce, eventUnsubscribe.hashFork);
                if (!pEvent)
                {
                    return false;
                }

                pEvent->data = vMyFork;
                pNetChannel->PostEvent(pEvent);
            }
            
            if(!vFork.empty())
            {
                network::CMvEventPeerUnsubscribe event(eventUnsubscribe.nNonce, eventUnsubscribe.hashFork);
                event.data = vFork;
                return CMvPeerNet::HandleEvent(event);
            }
            return true;
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerUnsubscribe* pEvent = new network::CMvEventPeerUnsubscribe(eventUnsubscribe);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventUnsubscribe.sender)
        {
            pDbpService->PostEvent(pEvent);
        }

        if(SENDER_DBPSVC == eventUnsubscribe.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for INV event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerInv& eventInv)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        if(eventInv.nNonce != std::numeric_limits<uint64>::max())
        {
            return CMvPeerNet::HandleEvent(eventInv);
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventInv.sender)
        {
            if(std::numeric_limits<uint64>::max() != eventInv.nNonce)
            {
                return CMvPeerNet::HandleEvent(eventInv);
            }

            if(std::numeric_limits<uint64>::max() == eventInv.nNonce)
            {
                network::CMvEventPeerInv* pEvent = new network::CMvEventPeerInv(eventInv);
                if(!pEvent)
                {
                    return false;
                }

                pDbpService->PostEvent(pEvent);
                return true;
            }
        }

        if (SENDER_DBPSVC == eventInv.sender)
        {
            if (IsMainFork(eventInv.hashFork) || pForkManager->IsAllowed(eventInv.hashFork))
            {
                network::CMvEventPeerInv* pEvent = new network::CMvEventPeerInv(eventInv);
                if (!pEvent)
                {
                    return false;
                }
                pNetChannel->PostEvent(pEvent);
                return true;
            }

            return CMvPeerNet::HandleEvent(eventInv);
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerInv* pEvent = new network::CMvEventPeerInv(eventInv);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventInv.sender)
        {
            pDbpService->PostEvent(pEvent);
        }
        else if(SENDER_DBPSVC == eventInv.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for GETDATA event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerGetData& eventGetData)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventGetData);
    }

    if (typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if (SENDER_NETCHN == eventGetData.sender)
        {
            uint64 nNonce = eventGetData.nNonce;
            const uint256& hashFork = eventGetData.hashFork;

            std::set<uint256> setInvHash;
            for (const auto& inv : eventGetData.data)
            {
                setInvHash.insert(inv.nHash);
            }

            mapThisNodeGetData[std::make_pair(hashFork, nNonce)] = setInvHash;

            return CMvPeerNet::HandleEvent(eventGetData);
        }

        if(SENDER_DBPSVC == eventGetData.sender)
        {
            if(std::numeric_limits<uint64>::max() != eventGetData.nNonce)
            {
                return CMvPeerNet::HandleEventForkNode(eventGetData);
            }

            if (std::numeric_limits<uint64>::max() == eventGetData.nNonce)
            {
                network::CMvEventPeerGetData* pEvent = new network::CMvEventPeerGetData(eventGetData);
                if (!pEvent)
                {
                    return false;
                }
                pEvent->sender = "virtualpeernet";
                pNetChannel->PostEvent(pEvent);
                return true;
            }

            return true;
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerGetData* pEvent = new network::CMvEventPeerGetData(eventGetData);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventGetData.sender)
        {
            pDbpService->PostEvent(pEvent);
        }
        else if(SENDER_DBPSVC == eventGetData.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for GETBLOCKS event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerGetBlocks& eventGetBlocks)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventGetBlocks);
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventGetBlocks.sender)
        {
            return CMvPeerNet::HandleEvent(eventGetBlocks);
        }

        if(SENDER_DBPSVC == eventGetBlocks.sender)
        {
            if (IsMainFork(eventGetBlocks.hashFork) || pForkManager->IsAllowed(eventGetBlocks.hashFork))
            {
                network::CMvEventPeerGetBlocks* pEvent = new network::CMvEventPeerGetBlocks(eventGetBlocks);
                pEvent->sender = "virtualpeernet";
                pNetChannel->PostEvent(pEvent);
                return true;
            }

            return CMvPeerNet::HandleEvent(eventGetBlocks);
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerGetBlocks* pEvent = new network::CMvEventPeerGetBlocks(eventGetBlocks);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventGetBlocks.sender)
        {
            pDbpService->PostEvent(pEvent);
        }
        else if(SENDER_DBPSVC == eventGetBlocks.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for TX event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerTx& eventTx)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventTx);
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventTx.sender)
        {
            return CMvPeerNet::HandleEvent(eventTx);
        }

        if(SENDER_DBPSVC == eventTx.sender)
        {
            return true; // TODO: send logic
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerTx* pEvent = new network::CMvEventPeerTx(eventTx);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventTx.sender)
        {
            pDbpService->PostEvent(pEvent);
        }
        else if(SENDER_DBPSVC == eventTx.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//message pump for BLOCK event overrided from base class to route related p2p event
bool CVirtualPeerNet::HandleEvent(network::CMvEventPeerBlock& eventBlock)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FNFN)
    {
        return CMvPeerNet::HandleEvent(eventBlock);
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        if(SENDER_NETCHN == eventBlock.sender)
        {
            if(std::numeric_limits<uint64>::max() != eventBlock.nNonce)
            {
                return CMvPeerNet::HandleEvent(eventBlock);
            }

            if(std::numeric_limits<uint64>::max() == eventBlock.nNonce)
            {
                network::CMvEventPeerBlock *pEvent = new network::CMvEventPeerBlock(eventBlock);
                if(!pEvent)
                {
                    return false;
                }

                pDbpService->PostEvent(pEvent);
                return true;
            }
        }

        if(SENDER_DBPSVC == eventBlock.sender)
        {
            return true; // TODO: send logic
        }
    }

    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_FORK)
    {
        network::CMvEventPeerBlock* pEvent = new network::CMvEventPeerBlock(eventBlock);
        if(!pEvent)
        {
            return false;
        }
        if(SENDER_NETCHN == eventBlock.sender)
        {
            pDbpService->PostEvent(pEvent);
        }
        else if(SENDER_DBPSVC == eventBlock.sender)
        {
            pNetChannel->PostEvent(pEvent);
        }
    }
    return true;
}

//only available at the level of root node which delivers ACTIVE event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandlePeerHandshakedForForkNode(const network::CMvEventPeerActive& peerActive)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerActive* pEvent = new CMvEventPeerActive(peerActive);
        if(!pEvent)
        {
            return false;
        }
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers DEACTIVE event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::DestroyPeerForForkNode(const network::CMvEventPeerDeactive& peerDeactive)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        network::CMvEventPeerDeactive* pEvent = new network::CMvEventPeerDeactive(peerDeactive);
        if(!pEvent)
        {
            return false;
        }
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers SUB event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerSub(const uint64& nNonce, const uint256& hashFork, vector<uint256>& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerSubscribe* pEvent = new CMvEventPeerSubscribe(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers UNSUB event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerUnSub(const uint64& nNonce, const uint256& hashFork, vector<uint256>& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerUnsubscribe* pEvent = new CMvEventPeerUnsubscribe(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers GETBLOCKS event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerGetBlocks(const uint64& nNonce, const uint256& hashFork, CBlockLocator& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerGetBlocks* pEvent = new CMvEventPeerGetBlocks(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers INV event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerInv(const uint64& nNonce, const uint256& hashFork, vector<CInv>& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerInv* pEvent = new CMvEventPeerInv(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers GETDATA event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerGetData(const uint64& nNonce, const uint256& hashFork, vector<CInv>& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerGetData* pEvent = new CMvEventPeerGetData(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers BLOCK event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerBlock(const uint64& nNonce, const uint256& hashFork, CBlock& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerBlock* pEvent = new CMvEventPeerBlock(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

//only available at the level of root node which delivers TX event to super node cluster
//by hook member function in terms of template method in design pattern
bool CVirtualPeerNet::HandleRootPeerTx(const uint64& nNonce, const uint256& hashFork, CTransaction& data)
{
    if(typeNode == SUPER_NODE_TYPE::SUPER_NODE_TYPE_ROOT)
    {
        CMvEventPeerTx* pEvent = new CMvEventPeerTx(nNonce, hashFork);
        if(!pEvent)
        {
            return false;
        }
        pEvent->data = data;
        pDbpService->PostEvent(pEvent);
    }
    return true;
}

bool CVirtualPeerNet::IsMainFork(const uint256& hashFork)
{
    return hashFork == pCoreProtocol->GetGenesisBlockHash();
}

bool CVirtualPeerNet::IsMyFork(const uint256& hashFork)
{
    return pForkManager->IsAllowed(hashFork);
}

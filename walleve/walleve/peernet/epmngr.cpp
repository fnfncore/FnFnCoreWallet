// Copyright (c) 2016-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php

#include "epmngr.h"
#include "walleve/util.h"
#include <vector>
#include <boost/foreach.hpp>

using namespace std;
using namespace walleve;
using boost::asio::ip::tcp;

///////////////////////////////
// CConnAttempt

CConnAttempt::CConnAttempt()
: nAttempts(0),nStartIndex(0),nStartTime(0) 
{
}

bool CConnAttempt::Attempt(int64 ts)
{
    int64 offset = (ts - nStartTime) / COUNTER_INTERVAL;
    if (offset >= COUNTER_NUM * 2)
    {
        arrayAttempt[0] = 1;
        for (int i = 1;i < COUNTER_NUM;i++)
        {
            arrayAttempt[i] = 0;
        }
        nAttempts = 1;
        nStartIndex = 0;
        nStartTime = ts;
        return true;
    }

    while (offset >= COUNTER_NUM)
    {
        nAttempts -= arrayAttempt[nStartIndex];
        arrayAttempt[nStartIndex] = 0;
        nStartTime += COUNTER_INTERVAL;
        nStartIndex = (nStartIndex + 1) & COUNTER_MASK;
        offset--;
    }

    arrayAttempt[(nStartIndex + offset) & COUNTER_MASK]++;

    return (++nAttempts <= ATTEMPT_LIMIT); 
}

///////////////////////////////
// CAddressStatus

CAddressStatus::CAddressStatus()
: nScore(0),nLastSeen(),nBanTo(0),nConnections(0) 
{
}

bool CAddressStatus::InBoundAttempt(int64 ts)
{
    nLastSeen = ts;
    if (connAttempt.Attempt(ts))
    {
        return (ts > nBanTo);
    }
    
    Penalize(ATTEMPT_PENALTY,ts); 
    return false;
}

bool CAddressStatus::AddConnection(bool fInBound)
{
    if (nConnections >= (fInBound ? CONNECTION_LIMIT : 1))
    {
        return false;
    }
    nConnections++;
    return true;
}

void CAddressStatus::RemoveConnection()
{
    nConnections--;
}

void CAddressStatus::Reward(int nPoints,int64 ts)
{
    nScore += nPoints;
    if (nScore > MAX_SCORE)
    {
        nScore = MAX_SCORE;
    }
    nLastSeen = ts;
}

void CAddressStatus::Penalize(int nPoints,int64 ts)
{
    nScore -= nPoints;
    if (nScore < MIN_SCORE)
    { 
        nScore = MIN_SCORE;
    }
    
    if (nScore < 0)
    {
        int64 bantime = BANTIME_BASE << (11 * nScore / MIN_SCORE);
        nBanTo = (ts > nBanTo ? ts : nBanTo) + bantime;
    } 
}

///////////////////////////////
// CEndpointManager

void CEndpointManager::Clear()
{
    mapAddressStatus.clear();
    mngrNode.Clear();
    bimapRemoteEPMac.clear();
}

int CEndpointManager::GetEndpointScore(const tcp::endpoint& ep)
{
    return mapAddressStatus[bimapRemoteEPMac.left.at(ep)].nScore;
}

void CEndpointManager::GetBanned(std::vector<CAddressBanned>& vBanned)
{
    int64 now = GetTime();
    map<CMacAddress,CAddressStatus>::iterator it = mapAddressStatus.begin();
    while (it != mapAddressStatus.end())
    {
        CAddressStatus& status = (*it).second;
        if (now < status.nBanTo)
        {
            vBanned.push_back(CAddressBanned((*it).first,status.nScore,status.nBanTo - now));
        }
        ++it;
    }
}

void CEndpointManager::SetBan(std::vector<CMacAddress>& vAddrToBan,int64 nBanTime)
{
    int64 now = GetTime();
    BOOST_FOREACH(const CMacAddress& addr,vAddrToBan)
    {
        CAddressStatus& status = mapAddressStatus[addr];
        status.nBanTo = now + nBanTime;
        status.nLastSeen = now;
        mngrNode.Ban(addr,status.nBanTo);
    }
}

void CEndpointManager::ClearBanned(vector<CMacAddress>& vAddrToClear)
{
    int64 now = GetTime();
    BOOST_FOREACH(const CMacAddress& addr,vAddrToClear)
    {
        map<CMacAddress,CAddressStatus>::iterator it = mapAddressStatus.find(addr);
        if (it != mapAddressStatus.end() && now < (*it).second.nBanTo)
        {
            mapAddressStatus.erase(it);
        }
    }
}

void CEndpointManager::ClearAllBanned()
{
    int64 now = GetTime();
    map<CMacAddress,CAddressStatus>::iterator it = mapAddressStatus.begin();
    while (it != mapAddressStatus.end())
    {
        if (now < (*it).second.nBanTo)
        {
            mapAddressStatus.erase(it++);
        }
        else
        {
            ++it;
        }
    }
}

void CEndpointManager::AddNewOutBound(const tcp::endpoint& ep,const string& strName,
                                      const boost::any& data)
{
    mngrNode.AddNew(ep,strName,data);
}

void CEndpointManager::RemoveOutBound(const tcp::endpoint& ep)
{
    mngrNode.Remove(ep);
}

string CEndpointManager::GetOutBoundName(const boost::asio::ip::tcp::endpoint& ep)
{
    return mngrNode.GetName(ep);
}

bool CEndpointManager::GetOutBoundData(const tcp::endpoint& ep,boost::any& dataRet)
{
    return mngrNode.GetData(ep,dataRet);
}

bool CEndpointManager::SetOutBoundData(const tcp::endpoint& ep,const boost::any& dataIn)
{
    return mngrNode.SetData(ep,dataIn);
}

bool CEndpointManager::GetOutBoundMacAddress(const boost::asio::ip::tcp::endpoint& ep,CMacAddress& addr)
{
    return mngrNode.GetMacAddress(ep, addr);
}

bool CEndpointManager::SetOutBoundMacAddress(const boost::asio::ip::tcp::endpoint& ep,const CMacAddress& addr)
{
    return mngrNode.SetMacAddress(ep, addr);
}

bool CEndpointManager::FetchOutBound(tcp::endpoint& ep)
{
    while (mngrNode.Employ(ep))
    {
        auto iter = bimapRemoteEPMac.left.find(ep);
        if(iter != bimapRemoteEPMac.left.end())
        {
            CAddressStatus& status = mapAddressStatus[bimapRemoteEPMac.left.at(ep)];
            if (status.AddConnection(false))
            {
                return true;
            }
            mngrNode.Dismiss(ep,false);
        }
        else
        {
            CAddressStatus& status = mapAddressStatus[CMacAddress()];
            if (status.AddConnection(false))
            {
                return true;
            }
            mngrNode.Dismiss(ep,false);
        }
    }
    return false;
}

bool CEndpointManager::AcceptInBound(const tcp::endpoint& ep)
{
    int64 now = GetTime();
    CAddressStatus& status = mapAddressStatus[bimapRemoteEPMac.left.at(ep)];
    return (status.InBoundAttempt(now) && status.AddConnection(true));
}

void CEndpointManager::RewardEndpoint(const tcp::endpoint& ep,Bonus bonus)
{
    const int award[NUM_BONUS] = {1,2,3,5};
    int index = (int)bonus; 
    if (index < 0 || index >= NUM_BONUS)
    {
        index = 0;
    }
    CAddressStatus& status = mapAddressStatus[bimapRemoteEPMac.left.at(ep)];
    status.Reward(award[index],GetTime());

    CleanInactiveAddress();
}

void CEndpointManager::CloseEndpoint(const tcp::endpoint& ep,CloseReason reason)
{
    int64 now = GetTime();
    /*
        HOST_CLOSE => 0 points,
        CONNECT_FAILURE => 1 points,
        NETWORK_ERROR => 2 points,
        RESPONSE_FAILURE => 2 points,
        PROTOCOL_INVALID => 10 points,
        DDOS_ATTACK => 25 points
    */
    const int lost[NUM_CLOSEREASONS] = {0,1,2,2,10,25};
    int index = (int)reason;
    if (index < 0 || index >= NUM_CLOSEREASONS)
    {
        index = 0;
    }
    CAddressStatus& status = mapAddressStatus[bimapRemoteEPMac.left.at(ep)];
    status.Penalize(lost[index],now);
    mngrNode.Dismiss(ep,(reason == NETWORK_ERROR)); 
    status.RemoveConnection();

    if (now < status.nBanTo)
    {
        mngrNode.Ban(bimapRemoteEPMac.left.at(ep),status.nBanTo);
    }

    CleanInactiveAddress();
}

void CEndpointManager::RetrieveGoodNode(vector<CNodeAvail>& vGoodNode,
                                        int64 nActiveTime,size_t nMaxCount)
{
    vector<CNode> vNode;
    mngrNode.Retrieve(vNode);
    int64 nActive = GetTime() - nActiveTime;
    multimap<int,CNodeAvail> mapScore;
    BOOST_FOREACH(const CNode& node,vNode)
    {
        const CMacAddress& addr = node.macAddr;
        map<CMacAddress,CAddressStatus>::iterator it = mapAddressStatus.find(addr);
        if (it != mapAddressStatus.end() 
            && (*it).second.nLastSeen > nActive && (*it).second.nScore >= 0)
        {
            mapScore.insert(make_pair(-(*it).second.nScore,CNodeAvail(node,(*it).second.nLastSeen)));
        }
    }

    for (multimap<int,CNodeAvail>::iterator it = mapScore.begin();
         it != mapScore.end() && vGoodNode.size() < nMaxCount;++it)
    {
        vGoodNode.push_back((*it).second);
    }
}

void CEndpointManager::CleanInactiveAddress()
{
    if (mapAddressStatus.size() <= MAX_ADDRESS_COUNT)
    {
        return;
    }
    
    int64 inactive = GetTime() - MAX_INACTIVE_TIME; 
    //multimap<int64,walleve::CMacAddress> mapLastSeen;
    std::vector<std::pair<int64,walleve::CMacAddress>> vLastSeen;
    map<walleve::CMacAddress,CAddressStatus>::iterator it = mapAddressStatus.begin();
    while (it != mapAddressStatus.end())
    {
        CAddressStatus& status = (*it).second;
        if (status.nLastSeen > inactive)
        {
            //mapLastSeen.insert(make_pair(status.nLastSeen,(*it).first));
            vLastSeen.push_back(make_pair(status.nLastSeen,(*it).first));
            ++it;
        }
        else
        {
            mapAddressStatus.erase(it++);
        }
    }

    //multimap<int64,CMacAddress>::iterator mi = mapLastSeen.begin();
    auto mi = vLastSeen.begin();
    while (mapAddressStatus.size() > MAX_ADDRESS_COUNT && mi != vLastSeen.end())
    {
        mapAddressStatus.erase((*mi).second);
        ++mi;
    }
}

void CEndpointManager::AddNewEndPointMac(const boost::asio::ip::tcp::endpoint& ep, const walleve::CMacAddress& addr)
{
    bimapRemoteEPMac.insert(position_pair(ep, addr));
    auto iter = mapAddressStatus.find(CMacAddress());
    if(iter != mapAddressStatus.end())
    {
        mapAddressStatus[addr] = iter->second;
        mapAddressStatus.erase(iter);
    }
}

void CEndpointManager::RemoveEndPointMac(const boost::asio::ip::tcp::endpoint& ep)
{
    auto it =  bimapRemoteEPMac.left.find(ep);
    if(it != bimapRemoteEPMac.left.end())
    {
        bimapRemoteEPMac.left.erase(it);
    }
}


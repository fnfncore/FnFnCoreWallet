// Copyright (c) 2017-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "network.h"
#include "version.h"
#include <boost/bind.hpp>
#include <boost/any.hpp>

using namespace std;
using namespace walleve;
using namespace multiverse;
using boost::asio::ip::tcp;

//////////////////////////////
// CNetwork 

CNetwork::CNetwork()
{
}

CNetwork::~CNetwork()
{
}

bool CNetwork::WalleveHandleInitialize()
{
    Configure(NetworkConfig()->nMagicNum,PROTO_VERSION,network::NODE_NETWORK | network::NODE_DELEGATED,
              FormatSubVersion(),NetworkConfig()->pathRoot.generic_string(),
              !NetworkConfig()->vConnectTo.empty(), NetworkConfig()->nodeKey);

    CPeerNetConfig config;
    if (NetworkConfig()->fListen || NetworkConfig()->fListen4)
    {
        config.vecService.push_back(CPeerService(tcp::endpoint(tcp::v4(), NetworkConfig()->nPort),
                                                 NetworkConfig()->nMaxInBounds));
    }
    if(NetworkConfig()->fListen6)
    {
        config.vecService.push_back(CPeerService(tcp::endpoint(tcp::v6(), NetworkConfig()->nPort),
                                                 NetworkConfig()->nMaxInBounds));
    }
    config.nMaxOutBounds = NetworkConfig()->nMaxOutBounds;
    config.nPortDefault = NetworkConfig()->nPort;
    for(const string& conn : NetworkConfig()->vConnectTo)
    {
        config.vecNode.push_back(CNetHost(conn,config.nPortDefault,conn,
                                          boost::any(uint64(network::NODE_NETWORK))));
    }
    if (config.vecNode.empty())
    {
        for(const string& seed : NetworkConfig()->vDNSeed)
        {
            // HACK: dnseed port is different from peer port
            //       dnseed port should be hardcode rather than in configuration
            config.vecNode.push_back(CNetHost(seed,config.nPortDefault,"dnseed",
                                              boost::any(uint64(network::NODE_NETWORK))));
        }
        for(const string& node : NetworkConfig()->vNode)
        {
            config.vecNode.push_back(CNetHost(node,config.nPortDefault,node,
                                              boost::any(uint64(network::NODE_NETWORK))));
        }
    }

    if(NetworkConfig()->fListen || NetworkConfig()->fListen4 || NetworkConfig()->fListen6)
    {
        config.gateWayNode = CNetHost(NetworkConfig()->strGateWay, config.nPortDefault, NetworkConfig()->strGateWay,
                                              boost::any(uint64(network::NODE_NETWORK)));
    }

    ConfigNetwork(config);

    return CVirtualPeerNet::WalleveHandleInitialize();
}

void CNetwork::WalleveHandleDeinitialize()
{
    CVirtualPeerNet::WalleveHandleDeinitialize();
}

bool CNetwork::CheckPeerVersion(uint32 nVersionIn,uint64 nServiceIn,const string& subVersionIn)
{
    (void)subVersionIn;
    if (nVersionIn < MIN_PROTO_VERSION || (nServiceIn & network::NODE_NETWORK) == 0)
    {
        return false;
    }
    return true;
}

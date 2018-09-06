#ifndef WALLEVE_DBP_SERVER_H
#define WALLEVE_DBP_SERVER_H

#include "walleve/netio/ioproc.h"
#include "walleve/dbp/dbpevent.h"

#include <boost/bimap.hpp>
#include <boost/any.hpp>

namespace dbp{
    class Base;
}

namespace google {
    namespace protobuf{
        class Any;
    }
}

namespace walleve{

class CDbpServer;


class CDbpHostConfig
{
public:
    CDbpHostConfig() {}
    CDbpHostConfig(const boost::asio::ip::tcp::endpoint& epHostIn,unsigned int nMaxConnectionsIn,unsigned int nSessionTimeoutIn, 
                    const CIOSSLOption& optSSLIn,const std::map<std::string,std::string>& mapUserPassIn,
                    const std::vector<std::string> vAllowMaskIn,const std::string& strIOModuleIn)
    : epHost(epHostIn),
      nMaxConnections(nMaxConnectionsIn),
      nSessionTimeout(nSessionTimeoutIn),
      optSSL(optSSLIn),
      mapUserPass(mapUserPassIn),
      vAllowMask(vAllowMaskIn),
      strIOModule(strIOModuleIn)
    {
    }
public:
    boost::asio::ip::tcp::endpoint epHost;
    unsigned int nMaxConnections;
    unsigned int nSessionTimeout;
    CIOSSLOption optSSL;
    std::map<std::string,std::string> mapUserPass;
    std::vector<std::string> vAllowMask;
    std::string strIOModule;
};

class CDbpProfile
{
public:
    CDbpProfile() : pIOModule(NULL),pSSLContext(NULL) {}
public:
    IIOModule *pIOModule;
    boost::asio::ssl::context* pSSLContext;
    std::map<std::string,std::string> mapAuthrizeUser;
    std::vector<std::string> vAllowMask;
    unsigned int nMaxConnections;
    unsigned int nSessionTimeout;
};

class CDbpClient
{
public:
    CDbpClient(CDbpServer *pServerIn,CDbpProfile *pProfileIn,
                CIOClient* pClientIn,uint64 nonce);
    ~CDbpClient();
    CDbpProfile *GetProfile();
    uint64 GetNonce();
    bool IsEventStream();
    void SetEventStream();
    void Activate();
    void SendResponse(CWalleveDbpConnected &body);
    void SendResponse(CWalleveDbpFailed& body);
    void SendResponse(CWalleveDbpNoSub& body);
    void SendResponse(CWalleveDbpReady& body);
    void SendResponse(CWalleveDbpAdded& body);
    void SendResponse(CWalleveDbpMethodResult& body);
    void SendPing(const std::string& id);
    void SendPong(const std::string& id);
    void SendNocActivePing(const std::string& id);
    void SendResponse(int statusCode,const std::string& description);
    void SendMessage(dbp::Base* pBaseMsg);
    void SendPingNoActiveMessage(dbp::Base* pBaseMsg);
    void SendAddedNoActiveMessage(dbp::Base* pBaseMsg);

protected:
    void StartReadHeader();
    void StartReadPayload(std::size_t nLength);

    void HandleReadHeader(std::size_t nTransferred);
    void HandleReadPayload(std::size_t nTransferred, uint32_t len);
    void HandleReadCompleted(uint32_t len);
    void HandleWritenResponse(std::size_t nTransferred);
    void HandleWritenResponse(std::size_t nTransferred, int type);
private:
protected:
    CDbpServer* pServer;
    CDbpProfile *pProfile;
    CIOClient* pClient;
    uint64 nNonce;
    bool fEventStream;
    CWalleveBufStream ssSend;
    CWalleveBufStream ssRecv;

    CWalleveBufStream ssPingSend;
    CWalleveBufStream ssAddedSend;

};

class CSessionProfile
{
public:
    CDbpClient* pDbpClient;
    std::string sessionId;
    uint64 timestamp;
};

class CDbpServer : public CIOProc, virtual public CWalleveDBPEventListener
{
public:
    CDbpServer();
    virtual ~CDbpServer();
    virtual CIOClient* CreateIOClient(CIOContainer *pContainer) override;
    
    void HandleClientRecv(CDbpClient *pDbpClient, const boost::any& anyObj);
    void HandleClientSent(CDbpClient *pDbpClient);
    void HandleClientError(CDbpClient *pDbpClient);

    void HandleClientConnect(CDbpClient *pDbpClient,google::protobuf::Any* any);
    void HandleClientSub(CDbpClient *pDbpClient,google::protobuf::Any* any);
    void HandleClientUnSub(CDbpClient *pDbpClient,google::protobuf::Any* any);
    void HandleClientMethod(CDbpClient *pDbpClient,google::protobuf::Any* any);
    void HandleClientPing(CDbpClient *pDbpClient,google::protobuf::Any* any);
    void HandleClientPong(CDbpClient *pDbpClient,google::protobuf::Any* any);
    
    void RespondError(CDbpClient *pDbpClient,int nStatusCode,const std::string& strError = "");
    void RespondFailed(CDbpClient* pDbpClient);
    
    void AddNewHost(const CDbpHostConfig& confHost);
protected:
    bool WalleveHandleInitialize() override;
    void WalleveHandleDeinitialize() override;
    void EnterLoop() override;
    void LeaveLoop() override;

    bool ClientAccepted(const boost::asio::ip::tcp::endpoint& epService,CIOClient *pClient) override;

    bool CreateProfile(const CDbpHostConfig& confHost);
    CDbpClient* AddNewClient(CIOClient *pClient,CDbpProfile *pDbpProfile);
    void RemoveClient(CDbpClient *pDbpClient);
    
    bool HandleEvent(CWalleveEventDbpConnected& event) override;
    bool HandleEvent(CWalleveEventDbpFailed& event) override;
    bool HandleEvent(CWalleveEventDbpNoSub& event) override;
    bool HandleEvent(CWalleveEventDbpReady& event) override;
    bool HandleEvent(CWalleveEventDbpAdded& event) override;
    bool HandleEvent(CWalleveEventDbpMethodResult& event) override;
    bool HandleEvent(CWalleveEventDbpPing& event) override;

    bool IsSessionTimeOut(CDbpClient* pDbpClient);
    bool IsSessionReconnect(const std::string & session);
    bool IsSessionExist(const std::string& session);
    bool HaveAssociatedSessionOf(CDbpClient* pDbpClient);

    std::string GenerateSessionId();
    void CreateSession(const std::string& session,CDbpClient* pDbpClient);
    void UpdateSession(const std::string& session,CDbpClient* pDbpClient);

    void SendPingHandler(const boost::system::error_code& err,CDbpClient *pDbpClient); 

protected:
    std::vector<CDbpHostConfig> vecHostConfig;
    std::map<boost::asio::ip::tcp::endpoint,CDbpProfile> mapProfile;
    std::map<uint64,CDbpClient*> mapClient; // nonce => CDbpClient
   
    typedef boost::bimap<std::string,CDbpClient*> SessionClientBimapType; 
    typedef SessionClientBimapType::value_type  position_pair;
    SessionClientBimapType sessionClientBimap; //session id <=> CDbpClient
    std::map<std::string,CSessionProfile> sessionProfileMap; // session id => session profile

    std::shared_ptr<boost::asio::deadline_timer> pingTimerPtr_;
};
} //namespace walleve
#endif //WALLEVE_DBP_SERVER_H
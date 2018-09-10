#ifndef  WALLEVE_DBP_EVENT_H
#define  WALLEVE_DBP_EVENT_H

#include "walleve/event/event.h"
#include "walleve/dbp/dbptype.h"

namespace walleve{

enum {
    WALLEVE_EVENT_DBP_REQ,
    WALLEVE_EVENT_DBP_RSP,
    WALLEVE_EVENT_DBP_CONNECT,
    WALLEVE_EVENT_DBP_CONNECTED,
    WALLEVE_EVENT_DBP_FAILED,
    WALLEVE_EVENT_DBP_SUB,
    WALLEVE_EVENT_DBP_UNSUB,
    WALLEVE_EVENT_DBP_NOSUB,
    WALLEVE_EVENT_DBP_READY,
    WALLEVE_EVENT_DBP_ADDED,
    WALLEVE_EVENT_DBP_METHOD,
    WALLEVE_EVENT_DBP_RESULT,

    WALLEVE_EVENT_DBP_PING,
    WALLEVE_EVENT_DBP_PONG,

    WALLEVE_EVENT_DBP_BROKEN
};

class CWalleveDBPEventListener;


#define TYPE_WALLEVE_DBP_EVENT(type,body) 	\
	CWalleveEventCategory<type,CWalleveDBPEventListener,body,bool>

typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_REQ,CWalleveDbpRequest) CWalleveEventDbpRequest;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_RSP,CWalleveDbpRespond) CWalleveEventDbpRespond;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_CONNECT,CWalleveDbpConnect) CWalleveEventDbpConnect;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_CONNECTED,CWalleveDbpConnected) CWalleveEventDbpConnected;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_FAILED,CWalleveDbpFailed) CWalleveEventDbpFailed;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_SUB,CWalleveDbpSub) CWalleveEventDbpSub;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_UNSUB,CWalleveDbpUnSub) CWalleveEventDbpUnSub;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_NOSUB,CWalleveDbpNoSub) CWalleveEventDbpNoSub;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_READY,CWalleveDbpReady) CWalleveEventDbpReady;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_ADDED,CWalleveDbpAdded) CWalleveEventDbpAdded;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_METHOD,CWalleveDbpMethod) CWalleveEventDbpMethod;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_RESULT,CWalleveDbpMethodResult) CWalleveEventDbpMethodResult;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_BROKEN,CWalleveDbpBroken) CWalleveEventDbpBroken;

// HeartBeats
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_PING,CWalleveDbpPing) CWalleveEventDbpPing;
typedef TYPE_WALLEVE_DBP_EVENT(WALLEVE_EVENT_DBP_PONG,CWalleveDbpPong) CWalleveEventDbpPong;


class CWalleveDBPEventListener : virtual public CWalleveEventListener
{
public:
    virtual ~CWalleveDBPEventListener() {}
    DECLARE_EVENTHANDLER(CWalleveEventDbpRequest);
    DECLARE_EVENTHANDLER(CWalleveEventDbpRespond);
    DECLARE_EVENTHANDLER(CWalleveEventDbpConnect);
    DECLARE_EVENTHANDLER(CWalleveEventDbpConnected);
    DECLARE_EVENTHANDLER(CWalleveEventDbpFailed);
    DECLARE_EVENTHANDLER(CWalleveEventDbpSub);
    DECLARE_EVENTHANDLER(CWalleveEventDbpUnSub);
    DECLARE_EVENTHANDLER(CWalleveEventDbpNoSub);
    DECLARE_EVENTHANDLER(CWalleveEventDbpReady);
    DECLARE_EVENTHANDLER(CWalleveEventDbpAdded);
    DECLARE_EVENTHANDLER(CWalleveEventDbpMethod);
    DECLARE_EVENTHANDLER(CWalleveEventDbpMethodResult);
    DECLARE_EVENTHANDLER(CWalleveEventDbpBroken);

    DECLARE_EVENTHANDLER(CWalleveEventDbpPing);
    DECLARE_EVENTHANDLER(CWalleveEventDbpPong);
};

}// namespace walleve
#endif // WALLEVE_DBP_EVENT_H
#define BROKER -1
// ClientId
#define PUBCLIENTID_0 0
#define SUBCLIENTID_1 1


#define MAXCLIENTS 3
#define MAXMESSAGES 5
#define MAXSUBSCRIPTIONS 1
#define MAXSESSIONS 2


/***
UPDATE
***/
#define SUBSCRIBEACL 1
#define PUBLISHACL 2
#define READACL 4
#define STOREACL 8
#define LOADACL 16


// session（will message）
typedef Message{
    short topic = -1; // topic=0 
    short mid = -1;
    short QoS = -1; // 0,1,2
    short srcClientId = -1; //PUBCLIENTID_0、 SUBCLIENTID_1
    short srcClientIndex = -1;
    short origin = -1; // 0: broker; 1: publisher; 
    bool retained = false;
}


// 
typedef RetainedMessage{
    short topic = -1; // topic=0 
    short mid = -1;
    short QoS = -1; // 0,1,2
    short srcClientId = -1; 
    short srcClientIndex = -1;
    bool retained = true;
}


typedef Subscription{
    short topic = -1;
}


// clientId
typedef Session{
    short clientId = -1;
    short clientIndex = -1;
    bool cleanStart;
    bool connected = false;

    // session，publisherqos2，subscriberbrokerqos1、2
    Message messages[MAXMESSAGES];
    short messagesLen = 0;
    Subscription subscriptions[MAXSUBSCRIPTIONS];
    short subscriptionsLen = 0;

    Message willmessage;
    
}

// username
typedef Client{
    short username;
    short password;
    short clientId;
    bool connected = false;

    /***
    UPDATE
    ***/
    short acl = PUBLISHACL + SUBSCRIBEACL + READACL;
    short aclTruth = PUBLISHACL + SUBSCRIBEACL + READACL;
    //Session session;
}





bool BadDisconnect;
bool hijacked;
short GlobalMid;
Client Clients[MAXCLIENTS];
Session Sessions[MAXSESSIONS];
// Sessionssession
RetainedMessage RetainedMessages;


/******************** sub read *************************/
atomic{
    bool hasSubscription = false;
    j = 0;
    // Traverse the subscription tree of {sess} and check if it is subscribed to the topic of message
    do
    :: j < MAXSUBSCRIPTIONS ->
        if
        :: (Sessions[sess].subscriptions[j].topic == {msg}.topic) ->
            hasSubscription = true;
            break;
        :: else -> skip;
        fi;
        j = j + 1;
    :: else -> 
        goto nextClients;
    od;

    nextClients:
    skip;
}


/******************** sub add *************************/
atomic{
    localClientId = Clients[index].clientId;
    if
        :: (Sessions[localClientId].subscriptionsLen < MAXSUBSCRIPTIONS) ->
            Sessions[localClientId].subscriptions[Sessions[localClientId].subscriptionsLen].topic = t;
            Sessions[localClientId].subscriptionsLen = Sessions[localClientId].subscriptionsLen + 1;
        :: else -> skip;
    fi;
}


/******************** sub remove *************************/
atomic{
    localClientId = Clients[index].clientId;
    j = 0;
    do
        :: j < MAXSUBSCRIPTIONS ->
            if
                :: (Sessions[localClientId].subscriptions[j].topic == t) ->
                    Sessions[localClientId].subscriptions[j].topic = -1;
                    break;
                :: else -> skip;
            fi;
            j = j + 1;
        :: else -> 
            break;
    od;
}

/******************** Session read *************************/
atomic{
sess = Sessions[clientId];
}
/******************** Session write *************************/
atomic{
    localClientId = Clients[index].clientId;
    i = 0;
    do
        :: i < MAXMESSAGES ->
            Sessions[localClientId].messages[i].topic = -1;
            Sessions[localClientId].messages[i].mid = -1;
            Sessions[localClientId].messages[i].QoS = -1;
            Sessions[localClientId].messages[i].srcClientId = -1;
            Sessions[localClientId].messages[i].srcClientIndex = -1;
            Sessions[localClientId].messages[i].origin = -1;
            i = i + 1;
        :: else -> break;
    od;  
    Sessions[localClientId].messagesLen = 0;
    i = 0;
    do
        :: i < MAXSUBSCRIPTIONS ->
            Sessions[localClientId].subscriptions[i].topic = -1;
            i = i + 1;
        :: else -> break;
    od;  
    Sessions[localClientId].subscriptionsLen = 0;
    // will message
    Sessions[localClientId].willmessage.topic = -1;
    Sessions[localClientId].willmessage.mid = -1;
    Sessions[localClientId].willmessage.QoS = -1;
    Sessions[localClientId].willmessage.srcClientId = -1;
    Sessions[localClientId].willmessage.srcClientIndex = -1;
    Sessions[localClientId].willmessage.origin = -1;
}

/******************** msgs queue read *************************/
atomic{
i = 0;
do
    :: i < MAXMESSAGES ->
        if
            :: (Sessions[localClientId].messages[i].topic != -1 && Sessions[localClientId].messages[i].origin == 0) ->
                if
                    :: (Sessions[localClientId].messages[i].QoS == 0) ->
                        printf("Bad QoS0 message stored in session from broker!\n");
                        break;
                    :: else ->
                        Message message;
                        message.topic = Sessions[localClientId].messages[i].topic;
                        message.mid = Sessions[localClientId].messages[i].mid;
                        message.QoS = Sessions[localClientId].messages[i].QoS;
                        message.srcClientId = Sessions[localClientId].messages[i].srcClientId;
                        message.srcClientIndex = Sessions[localClientId].messages[i].srcClientIndex;
                fi;
            :: (Sessions[localClientId].messages[i].topic != -1 && Sessions[localClientId].messages[i].origin == 1 && (Sessions[localClientId].messages[i].QoS == 0 || Sessions[localClientId].messages[i].QoS == 1)) ->
                printf("Bad QoS0 or QoS1 message stored in session from publisher!\n");
                break;
            :: else -> skip;
        fi;
        i = i + 1;
    :: else -> break;
od;
}

/******************** msgs queue add *************************/
atomic{
    localClientId = Clients[index].clientId;
    if
        :: Sessions[localClientId].messagesLen < MAXMESSAGES ->
            lastMessage = Sessions[localClientId].messagesLen;
            Sessions[localClientId].messages[lastMessage].topic = t;
            Sessions[localClientId].messages[lastMessage].mid = GlobalMid;
            GlobalMid = GlobalMid + 1;
            Sessions[localClientId].messages[lastMessage].QoS = qos;
            Sessions[localClientId].messages[lastMessage].srcClientId = localClientId;
            Sessions[localClientId].messages[lastMessage].srcClientIndex = index;
            Sessions[localClientId].messages[lastMessage].origin = 1;
            Sessions[localClientId].messagesLen = Sessions[localClientId].messagesLen + 1;
        :: else ->
            skip;
    fi;
}
/******************** msgs queue remove *************************/
atomic{
    localClientId = Clients[index].clientId;
    if
        :: (Sessions[localClientId].messagesLen > 0) ->
            lastMessage = Sessions[localClientId].messagesLen - 1;
            Sessions[localClientId].messages[lastMessage].topic = -1;
            Sessions[localClientId].messages[lastMessage].mid = -1;
            Sessions[localClientId].messages[lastMessage].QoS = -1;
            Sessions[localClientId].messages[lastMessage].srcClientId = -1;
            Sessions[localClientId].messages[lastMessage].srcClientIndex = -1;
            Sessions[localClientId].messages[lastMessage].origin = -1;
            Sessions[localClientId].messagesLen = Sessions[localClientId].messagesLen - 1;       
        :: else -> skip;
    fi;

    PUBREL_end(index);
}
/******************** retained read *************************/
atomic{
if
    :: (RetainedMessages.topic != -1 && RetainedMessages.topic == t) ->
        Message message;
        message.topic = RetainedMessages.topic;
        message.mid = RetainedMessages.mid;
        message.QoS = RetainedMessages.QoS;
        message.srcClientId = RetainedMessages.srcClientId;
        message.srcClientIndex = RetainedMessages.srcClientId;
    :: else -> skip;
fi;
}
/******************** retained add *************************/
atomic{
    localClientId = Clients[index].clientId;
    Message message;
    message.topic = t;
    message.mid = GlobalMid;
    GlobalMid = GlobalMid + 1;
    message.QoS = qos;
    message.srcClientId = localClientId;
    message.srcClientIndex = index;

    RetainedMessages.topic = t;
    RetainedMessages.mid = message.mid;
    RetainedMessages.QoS = qos;
    RetainedMessages.srcClientId = localClientId;
    RetainedMessages.srcClientIndex = index;
}
/******************** retained remove *************************/
atomic{
    RetainedMessages.topic = -1;
    RetainedMessages.mid = -1;
    RetainedMessages.QoS = -1;
    RetainedMessages.srcClientId = -1;
    RetainedMessages.srcClientIndex = -1;
}
/******************** permission remove *************************/
inline ACL_revoke(index, revokeAcl){
    atomic{
        if
            // SUBSCRIBEACL = 1
            :: (revokeAcl == SUBSCRIBEACL && (Clients[index].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - SUBSCRIBEACL;
            // PUBLISHACL = 2
            :: (revokeAcl == PUBLISHACL && (Clients[index].aclTruth & PUBLISHACL) == PUBLISHACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - PUBLISHACL;
            :: (revokeAcl == READACL && (Clients[index].aclTruth & READACL) == READACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - READACL;
            :: (revokeAcl == LOADACL && (Clients[index].aclTruth & LOADACL) == LOADACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - LOADACL;
            :: (revokeAcl == STOREACL && (Clients[index].aclTruth & STOREACL) == STOREACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - STOREACL;
            :: else -> skip;
        fi;
    }
}

/******************** permission check *************************/
inline Authorization_allowed(index, topic, Acl, rt){
    atomic{
        if
            :: ((Clients[index].acl & Acl) == Acl) ->
                rt = true;
            :: else ->
                rt = false;
        fi;
    }
}

/******************** will read *************************/
atomic{
msg = Sessions[clientId].willmessage;
}
/******************** will add *************************/
atomic{
    localClientId = Clients[index].clientId;
    if
        // publisherwill message，subscriber，will
        :: (localClientId != SUBCLIENTID_1) ->
            Sessions[localClientId].willmessage.topic = 0;
            Sessions[localClientId].willmessage.mid = GlobalMid;
            GlobalMid = GlobalMid + 1;
            // qoswill message
            Sessions[localClientId].willmessage.QoS = 0;
            Sessions[localClientId].willmessage.srcClientId = localClientId;
            Sessions[localClientId].willmessage.srcClientIndex = index;
            Sessions[localClientId].willmessage.origin = 1;
            printf("Message_%d: Will message created!\n",Sessions[localClientId].willmessage.mid);
        :: else -> skip;
    fi;
}

/******************** will remove *************************/
atomic{
    Sessions[localClientId].willmessage.topic = -1;
    Sessions[localClientId].willmessage.mid = -1;
    Sessions[localClientId].willmessage.QoS = -1;
    Sessions[localClientId].willmessage.srcClientId = -1;
    Sessions[localClientId].willmessage.srcClientIndex = -1;
    Sessions[localClientId].willmessage.origin = -1;
}

/******************** deliver *************************/
atomic{
    Deliver(msg, sess);
}

inline Deliver(msg, subscriber){
    atomic{
        bool flag = false;
        if
            :: (msg.srcClientId != -1) ->
                if
                    :: (msg.retained == true) ->
                        if
                            :: (((Clients[msg.srcClientIndex].aclTruth & PUBLISHACL) == PUBLISHACL) &&  ((Clients[Sessions[subscriber].clientIndex].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL)) ->
                                flag = true;
                            :: else -> skip;
                        fi;
                    :: else ->
                        if
                            :: (((Clients[Sessions[msg.srcClientId].clientIndex].aclTruth & PUBLISHACL) == PUBLISHACL) &&  ((Clients[Sessions[subscriber].clientIndex].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL)) ->
                                flag = true;
                            :: else -> skip;
                        fi;
                fi;
            :: else -> skip;
        fi;
        printf("Message_%d: Message Delivered!\n", msg.mid);
        printf("Message Delivery: Topic = %d; QoS = %d; FROM = SESSION_%d; TO = SESSION_%d\n", msg.topic, msg.QoS, msg.srcClientId, subscriber);
        assert(flag == true);
    }
}







/******************** Skeleton Code *************************/

proctype ProcessPublisher2(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    bool authorization_result = false;
    short publishedMessages = 0;
    // 、、
    short canConnect = 2;
    do
        :: 
            atomic{
                if
                    ::(Clients[index].connected == false && Sessions[Clients[index].clientId].connected == true&& BadDisconnect == false) ->
                    
                        printf("PUBLISHER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                        CONNECT_entry_point(index);
                        printf("PUBLISHER_%d: connected\n", index);
                        canConnect = canConnect - 1;
                        hijacked = true;
                fi;
            }
        :: 
            atomic{
                if        
                    ::(Clients[index].connected == false && Sessions[Clients[index].clientId].connected == false) ->
                        skip;
                fi;
            }
        :: 
            atomic{
                if        
                    ::(Clients[index].connected == true) ->
                        break;
                fi;
            }
    od;

}


proctype ProcessPublisher(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    short lastMessage = 0;
    bool authorization_result = false;
    short publishedMessages = 0;
    // 、、
    short canConnect = 2;
    do
        ::
            atomic{
                if
                    :: (Clients[index].connected == false && canConnect >= 0 && BadDisconnect == false && hijacked == false) ->
                        printf("PUBLISHER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                        CONNECT_entry_point(index);
                        printf("PUBLISHER_%d: connected\n", index);
                        canConnect = canConnect - 1;
                        BadDisconnect = true;
                fi;
            }
        :: 
            atomic{
                if
                    :: (Clients[index].connected == true && publishedMessages < 1) ->
                        PUBLISH_entry_point(Clients[index].clientId, 0); 
                        publishedMessages = publishedMessages + 1;
                        BadDisconnect = false;

                fi;
            }
        :: 
            atomic{ 
                if
                   ::  (Clients[index].connected == true && Sessions[Clients[index].clientId].messagesLen > 0) -> 
                        printf("PUBLISHER_%d: send 'PUBREL'\n", index);
                        PUBREL_entry_point(index); 
                        printf("PUBLISHER_%d: pubrel complete\n", index);
                        BadDisconnect = false;

                fi;
            }
        :: 
            atomic{ 
                if
                    ::  (Clients[index].connected == true && BadDisconnect == false) -> 
                        printf("PUBLISHER_%d: send 'DISCONNECT'\n", index);
                        DISCONNECT_entry_point(index); 
                        printf("PUBLISHER_%d: disconnected\n", index);
                        canConnect = canConnect - 1;
                        BadDisconnect = true;
                fi;
            }
        /*
            TODO: ACL
        */
        ::
            atomic{
                if
                    :: (Clients[index].connected == true && (Clients[index].aclTruth & PUBLISHACL) == PUBLISHACL) ->
                        ACL_revoke(index, PUBLISHACL);
                        printf("PUBLISHER_%d: revoke PUBLISHACL\n", index);
                        BadDisconnect = false;
                fi;
            }

        :: else -> break;
    od;
}

proctype ProcessSubscriber(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    short lastMessage = 0;
    bool authorization_result = false;
    // 、、
    short canConnect = 2;

    do
        :: (Clients[index].connected == false && canConnect >= 0 && BadDisconnect == false) ->
            atomic{
                printf("SUBSCRIBER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                CONNECT_entry_point(index);
                printf("SUBSCRIBER_%d: connected\n", index);
                canConnect = canConnect - 1;
                BadDisconnect = true;
            }
        :: 
            atomic{ 
                if
                   ::  (Clients[index].connected == true  && Sessions[Clients[index].clientId].subscriptionsLen < MAXSUBSCRIPTIONS) -> 
                        printf("SUBSCRIBER_%d: send 'SUBSCRIBE'\n", index);
                        SUBSCRIBE_entry_point(index, 0); 
                        printf("SUBSCRIBER_%d: subscribed\n", index);
                        BadDisconnect = false;

                fi;
            }
        :: 
            atomic{ 
                if
                    ::  (Clients[index].connected == true && BadDisconnect == false) -> 
                        printf("SUBSCRIBER_%d: send 'DISCONNECT'\n", index);
                        DISCONNECT_entry_point(index); 
                        printf("SUBSCRIBER_%d: disconnected\n", index);
                        canConnect = canConnect - 1;
                        BadDisconnect = true;
                fi;
            }
        /*
            TODO: ACL
        */
        ::
            atomic{
                if
                    :: (Clients[index].connected == true && (Clients[index].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL && (Clients[index].aclTruth & READACL) == READACL) ->
                        /***
                        UPDATE
                        ***/                    
                        ACL_revoke(index, SUBSCRIBEACL);
                        ACL_revoke(index, READACL);
                        printf("SUBSCRIBER_%d: revoke SUBSCRIBEACL\n", index);
                        BadDisconnect = false;
                fi;
            }
        :: else -> break;
    od;
}


init {
    atomic{
        short m = 0;
        do
            :: (m < MAXCLIENTS) ->
                Clients[m].connected = false;
                m = m + 1;
            :: else -> break;
        od;
        BadDisconnect = false;
        hijacked = false;
        GlobalMid = 0;

        Clients[0].username = 0;
        Clients[0].password = 0;
        Clients[0].clientId = PUBCLIENTID_0;

        Clients[1].username = 1;
        Clients[1].password = 1;
        Clients[1].clientId = SUBCLIENTID_1;

        Clients[2].username = 2;
        Clients[2].password = 2;
        Clients[2].clientId = PUBCLIENTID_0;
        Clients[2].acl = 0;
        Clients[2].aclTruth = 0;
    }

    run ProcessPublisher(0);
    run ProcessSubscriber(1);
    run ProcessPublisher2(2);
    
}

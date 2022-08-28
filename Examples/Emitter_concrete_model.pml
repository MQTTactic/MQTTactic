#define BROKER -1
// ClientId
#define PUBCLIENTID_0 0
#define SUBCLIENTID_1 1


#define MAXCLIENTS 3
#define MAXMESSAGES 5
#define MAXSUBSCRIPTIONS 1
#define MAXSESSIONS 2


#define SUBSCRIBEACL 1
#define PUBLISHACL 2
#define STOREACL 4
#define LOADACL 8






// session（will message）
typedef Message{
    short topic = -1; // topic=0 
    short QoS = -1; // 0,1,2
    short srcClientId = -1; //PUBCLIENTID_0、 SUBCLIENTID_1
    short srcClientIndex = -1;
    short origin = -1; // 0: broker; 1: publisher; 
    bool retained = false;
}


// 
typedef RetainedMessage{
    short topic = -1; // topic=0 
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
    /*
        TODO:
        acl = {PUBLISH=2, SUBSCRIBER=1} 1 + 2 = 3
        ，ACL，。
        e.g. mosquitto_acl(PUBLISH/SUBSCRIBE/READ)
    */
    short acl = PUBLISHACL + SUBSCRIBEACL + STOREACL + LOADACL;
    short aclTruth = PUBLISHACL + SUBSCRIBEACL + STOREACL + LOADACL;
    //Session session;
}





bool BadDisconnect;
Client Clients[MAXCLIENTS];
Session Sessions[MAXSESSIONS];
// Sessionssession
/*
    TODO: topic=0，topicretained messages
*/
RetainedMessage RetainedMessages;



/******************** CONNECT *************************/
inline CONNECT_entry_point(index){
    atomic{
        /*
            TODO:
            
        */
        // Authentication_UserPass_allowed();
        CONNECT_auth_success(index);
    }
}

inline CONNECT_auth_success(index){
    atomic{
        localClientId = Clients[index].clientId;
        if
            :: Sessions[localClientId].connected == true ->
                printf("PUBLISHER_%d: A client already online with the same clientId, DISCONNECT the old client.\n", index);
                Clients[Sessions[localClientId].clientIndex].connected = false;
            :: else -> skip;
        fi;
        Sessions[localClientId].clientId = Clients[index].clientId;
        Sessions[localClientId].clientIndex = index;
        if
            :: CONNECT_cleanStart_true(index);
            // :: CONNECT_cleanStart_false(index);
                 
        fi;
    }
}

inline CONNECT_cleanStart_true(index){
    atomic{
if
:: handle__connect_cleanStartT_Type_0(index);
fi;
    }
}

inline CONNECT_cleanStart_false(index){
    atomic{
skip;
    }
}


inline CONNECT_will_message(index){
    atomic{
        localClientId = Clients[index].clientId;
        if
            // publisherwill message，subscriber，will
            :: (localClientId != SUBCLIENTID_1) ->
                Sessions[localClientId].willmessage.topic = 0;
                // qoswill message
                Sessions[localClientId].willmessage.QoS = 0;
                Sessions[localClientId].willmessage.srcClientId = localClientId;
                Sessions[localClientId].willmessage.srcClientIndex = index;
                Sessions[localClientId].willmessage.origin = 1;
            :: else -> skip;
        fi;

        CONNECT_end(index);
    }
}

inline CONNECT_end(index){
    atomic{
        localClientId = Clients[index].clientId;
        Sessions[localClientId].connected = true;
        Clients[index].connected = true;
    }
}


/******************** PUBLISH *************************/
inline PUBLISH_entry_point(index, t){
    atomic{
        PUBLISH(index, t);
    }
}
inline PUBLISH(index, t){
    atomic{
        localClientId = Clients[index].clientId;
        if
            // :: PUBLISH_QoS0_step2(index, t);
            // :: PUBLISH_QoS1_step2(index, t);
            // :: (Sessions[localClientId].messagesLen < MAXMESSAGES) -> PUBLISH_QoS2_step2(index, t);
            :: PUBLISH_retained_QoS0_step2(index, t);
        fi;

    }
}
inline PUBLISH_QoS0_step2(index, t){
    atomic{
skip;
    }
}

inline PUBLISH_QoS1_step2(index, t){
    atomic{
skip;
    }
}

inline PUBLISH_QoS2_step2(index, t){
    atomic{
skip;
    }
}


inline PUBLISH_retained_QoS0_step2(index, t){
    atomic{
if
:: handle__publish_qos0_retained_Type_0(index, t);
fi;
    }
}



inline PUBLISH_end(){
    atomic{
        skip;
    }
}


/******************** PUBREL *************************/
/*
    TODO: topic，PUBREL，Publishersession
*/
inline PUBREL_entry_point(index){
    atomic{
        PUBREL(index);
    }
}
inline PUBREL(index){
    atomic{
skip;
    }
}

inline PUBREL_end(index){
    atomic{
        skip;
    }
}


/******************** SUBSCRIBE *************************/
inline SUBSCRIBE_entry_point(index, t){
    atomic{
        SUBSCRIBE(index, t);
    }
}
inline SUBSCRIBE(index, t){
    atomic{
if
:: handle__subscribe_Type_0(index, t);
fi;
    }
}
inline SUBSCRIBE_end(index, t){
    atomic{
        skip;
    }
}


/******************** UNSUBSCRIBE *************************/
inline UNSUBSCRIBE_entry_point(index, t){
    atomic{
        UNSUBSCRIBE(index, t);
    }
}
inline UNSUBSCRIBE(index, t){
    atomic{
if
:: handle__unsubscribe_Type_1(index, t);
fi;
    }
}
inline UNSUBSCRIBE_end(index, t){
    atomic{
        skip;
    }
}


/******************** DISCONNECT *************************/
inline DISCONNECT_entry_point(index){
    atomic{
        DISCONNECT(index);
    }
}
inline DISCONNECT(index){
    atomic{
if
:: handle__disconnect_Type_0(index);
fi;
    }
}
inline DISCONNECT_end(){
    atomic{
        skip;
    }
}



/******************** ACL revoke *************************/
inline ACL_revoke(index, revokeAcl){
    atomic{
if
:: ACL_revoke_(index, revokeAcl);
fi;
    }
}




/******************** ACL checker *************************/
inline Authentication_UserPass_allowed(){
    atomic{
        skip;
    }
}
inline Authorization_subscribe_allowed(index, topic, rt){
    atomic{
        if
            :: ((Clients[index].acl & SUBSCRIBEACL) == SUBSCRIBEACL) ->
                rt = true;
            :: else ->
                rt = false;
        fi;
    }
}

inline Authorization_publish_allowed(index, topic, rt){
    atomic{
        if
            :: ((Clients[index].acl & PUBLISHACL) == PUBLISHACL) ->
                rt = true;
            :: else -> 
                rt = false;
        fi;
    }
}


inline Authorization_load_allowed(index, topic, rt){
    atomic{
        if
            :: ((Clients[index].acl & LOADACL) == LOADACL) ->
                rt = true;
            :: else -> 
                rt = false;
        fi;
    }
}

inline Authorization_store_allowed(index, topic, rt){
    atomic{
        if
            :: ((Clients[index].acl & STOREACL) == STOREACL) ->
                rt = true;
            :: else -> 
                rt = false;
        fi;
    }
}


/******************** Deliver *************************/
inline Deliver_to_Subscribers(message){
    atomic{
        short i_1 = 0;
        printf("Message to subscribers: Topic = %d; QoS = %d; FROM = SESSION_%d; \n", message.topic, message.QoS, message.srcClientId);
        do
            :: i_1 < MAXSESSIONS ->
                bool hasSubscription = false;
                j = 0;
                if
                    // session，cleanStart=true, disconnect，
                    :: (Sessions[i_1].clientId == -1) ->
                        goto nextClients;
                    :: else -> skip;
                fi;
                // Clients[i_1] ，messagetopic
                do
                    :: j < MAXSUBSCRIPTIONS ->
                        if
                            :: (Sessions[i_1].subscriptions[j].topic == message.topic) ->
                                hasSubscription = true;
                                break;
                            :: else -> skip;
                        fi;
                        j = j + 1;
                    :: else -> 
                        goto nextClients;
                od;

                if
                    // 
                    :: (hasSubscription == true && Sessions[i_1].connected == true) ->
                        Deliver(message, i_1);
                    // QoS1，2session
                    :: (hasSubscription == true && Sessions[i_1].connected == false && (message.QoS == 1 || message.QoS == 2)) ->
                        if
                            :: Sessions[i_1].messagesLen < MAXMESSAGES ->
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].topic = message.topic;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].QoS = message.QoS;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientId = message.srcClientId;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientIndex = message.srcClientIndex;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].origin = 0; // brokersubscriber
                                Sessions[i_1].messagesLen = Sessions[i_1].messagesLen + 1;
                            :: else ->
                                printf("SESSION_%d: can not store more qos1,2 messages\n", i_1);

                        fi;
                    :: else -> skip;
                fi;

                nextClients:
                    skip;
                i_1 = i_1 + 1;
            :: else -> break;
        od;  
        Deliver_to_Subscribers_inserted_end_1:
            skip;
    }
}

inline handle__publish_qos0_retained_Type_0(index, t){
 atomic{
printf("Enter function handle__publish_qos0_retained_Type_0\n");
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS0 retained message\n", index);
        Message message;
        message.topic = t;
        message.QoS = 0;
        message.srcClientId = localClientId;
        message.srcClientIndex = index;
        authorization_result = false;
        Authorization_publish_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_0_Type_0
            :: else -> skip;
        fi;
        authorization_result = false;
        Authorization_store_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_1_Type_0
            :: else -> skip;
        fi;
        Deliver_to_Subscribers(message);
        RetainedMessages.topic = t;
        RetainedMessages.QoS = 0;
        RetainedMessages.srcClientId = localClientId;
        RetainedMessages.srcClientIndex = index;
LABEL_0_Type_0:
 skip; 

LABEL_1_Type_0:
 skip; 

        PUBLISH_end();

}
}

inline handle__connect_cleanStartT_Type_0(index){
 atomic{
printf("Enter function handle__connect_cleanStartT_Type_0\n");
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = true;
        printf("with cleanStart = true\n" );



        // oldsession，session
        i = 0;
        do
            :: i < MAXMESSAGES ->
                Sessions[localClientId].messages[i].topic = -1;
                Sessions[localClientId].messages[i].QoS = -1;
                Sessions[localClientId].messages[i].srcClientId = -1;
                Sessions[localClientId].messages[i].srcClientIndex = -1;
                Sessions[localClientId].messages[i].origin = -1;
                i = i + 1;
            :: else -> break;
        od;  
        Sessions[localClientId].messagesLen = 0;
        i = 0;
        // 
        do
            :: i < MAXSUBSCRIPTIONS ->
                Sessions[localClientId].subscriptions[i].topic = -1;
                i = i + 1;
            :: else -> break;
        od;  
        Sessions[localClientId].subscriptionsLen = 0;
        // will message
        Sessions[localClientId].willmessage.topic = -1;
        Sessions[localClientId].willmessage.QoS = -1;
        Sessions[localClientId].willmessage.srcClientId = -1;
        Sessions[localClientId].willmessage.srcClientIndex = -1;
        Sessions[localClientId].willmessage.origin = -1;
        CONNECT_will_message(index);

}
}

inline handle__disconnect_Type_0(index){
 atomic{
printf("Enter function handle__disconnect_Type_0\n");
        if
            :: (Sessions[Clients[index].clientId].willmessage.topic != -1) ->

        authorization_result = false;
        Authorization_publish_allowed(Sessions[Clients[index].clientId].willmessage.srcClientIndex, Sessions[Clients[index].clientId].willmessage.topic, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_3_Type_0
            :: else -> skip;
        fi;

        authorization_result = false;
        Authorization_store_allowed(Sessions[Clients[index].clientId].willmessage.srcClientIndex, Sessions[Clients[index].clientId].willmessage.topic, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_4_Type_0
            :: else -> skip;
        fi;
        if
            :: Sessions[Clients[index].clientId].willmessage.topic != -1 ->
                Deliver_to_Subscribers(Sessions[Clients[index].clientId].willmessage);
            :: else -> skip;
        fi;
LABEL_3_Type_0:
LABEL_4_Type_0:
skip; 
                    :: else -> skip;
                fi;

        localClientId = Clients[index].clientId;
        if
            :: Sessions[localClientId].connected == true ->
                if
                    :: Sessions[localClientId].willmessage.topic != -1 ->
                        Sessions[localClientId].willmessage.topic = -1;
                        Sessions[localClientId].willmessage.QoS = -1;
                        Sessions[localClientId].willmessage.srcClientId = -1;
                        Sessions[localClientId].willmessage.srcClientIndex = -1;
                        Sessions[localClientId].willmessage.origin = -1;
                    :: else -> skip;
                fi;
                Sessions[localClientId].connected = false;
                Clients[index].connected = false;
            :: else -> printf("WRONG: %d has not connected to the broker!", index);
                //assert(false);
        fi;
        DISCONNECT_end();

}
}

inline handle__subscribe_Type_0(index, t){
 atomic{
printf("Enter function handle__subscribe_Type_0\n");
        authorization_result = false;
        Authorization_subscribe_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_6_Type_0
            :: else -> skip;
        fi;
        localClientId = Clients[index].clientId;
        if
            :: (Sessions[localClientId].subscriptionsLen < MAXSUBSCRIPTIONS) ->
                Sessions[localClientId].subscriptions[Sessions[localClientId].subscriptionsLen].topic = t;
                Sessions[localClientId].subscriptionsLen = Sessions[localClientId].subscriptionsLen + 1;
                if
                    :: (RetainedMessages.topic != -1 && RetainedMessages.topic == t) ->
        authorization_result = false;
        Authorization_load_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_7_Type_0
            :: else -> skip;
        fi;
                        Deliver(RetainedMessages, localClientId);
LABEL_7_Type_0:
 skip; 

                    :: else -> skip;
                fi;
            :: else -> skip;
        fi;
LABEL_6_Type_0:
 skip; 

        SUBSCRIBE_end(index, t);

}
}

inline handle__unsubscribe_Type_1(index, t){
 atomic{
printf("Enter function handle__unsubscribe_Type_1\n");
        authorization_result = false;
        Authorization_subscribe_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_15_Type_1
            :: else -> skip;
        fi;
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
LABEL_15_Type_1:
 skip; 

        UNSUBSCRIBE_end(index, t);

}
}

inline ACL_revoke_(index, revokeAcl){
 atomic{
printf("Enter function ACL_revoke_\n");
        if
            // SUBSCRIBEACL = 1
            :: (revokeAcl == SUBSCRIBEACL && (Clients[index].acl & SUBSCRIBEACL) == SUBSCRIBEACL) ->
                Clients[index].acl = Clients[index].acl - SUBSCRIBEACL;
            // PUBLISHACL = 2
            :: (revokeAcl == PUBLISHACL && (Clients[index].acl & PUBLISHACL) == PUBLISHACL) ->
                Clients[index].acl = Clients[index].acl - PUBLISHACL;

            :: (revokeAcl == LOADACL && (Clients[index].acl & LOADACL) == LOADACL) ->
                Clients[index].acl = Clients[index].acl - LOADACL;
            :: (revokeAcl == STOREACL && (Clients[index].acl & STOREACL) == STOREACL) ->
                Clients[index].acl = Clients[index].acl - STOREACL;
            :: else -> skip;
        fi;
        if
            // SUBSCRIBEACL = 1
            :: (revokeAcl == SUBSCRIBEACL && (Clients[index].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - SUBSCRIBEACL;
            // PUBLISHACL = 2
            :: (revokeAcl == PUBLISHACL && (Clients[index].aclTruth & PUBLISHACL) == PUBLISHACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - PUBLISHACL;

            :: (revokeAcl == LOADACL && (Clients[index].aclTruth & LOADACL) == LOADACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - LOADACL;
            :: (revokeAcl == STOREACL && (Clients[index].aclTruth & STOREACL) == STOREACL) ->
                Clients[index].aclTruth = Clients[index].aclTruth - STOREACL;
            :: else -> skip;
        fi;

}
}

inline Deliver(message, subscriber){
    atomic{
        bool flag = false;
        if
            :: (message.srcClientId != -1) ->
                if
                    :: (message.retained == true) ->
                        if
                            :: (((Clients[message.srcClientIndex].aclTruth & PUBLISHACL) == PUBLISHACL) &&  ((Clients[Sessions[subscriber].clientIndex].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL)) ->
                                flag = true;
                            :: else -> skip;
                        fi;
                    :: else ->
                        if
                            :: (((Clients[Sessions[message.srcClientId].clientIndex].aclTruth & PUBLISHACL) == PUBLISHACL) &&  ((Clients[Sessions[subscriber].clientIndex].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL)) ->
                                flag = true;
                            :: else -> skip;
                        fi;
                fi;
            :: else -> skip;
        fi;
        printf("Message Delivery: Topic = %d; QoS = %d; FROM = SESSION_%d; TO = SESSION_%d\n", message.topic, message.QoS, message.srcClientId, subscriber);
        assert(flag == true);
    }
}


proctype ProcessPublisher2(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    bool authorization_result = false;
    short publishedMessages = 0;
    // 、、
    short canConnect = 2;
    // 
    bool badReconnect = false;
    do
        :: (Clients[index].connected == false && Sessions[Clients[index].clientId].connected == true) ->
            atomic{
                printf("PUBLISHER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                CONNECT_entry_point(index);
                printf("PUBLISHER_%d: connected\n", index);
                canConnect = canConnect - 1;
                badReconnect = true;
            }
        :: (Clients[index].connected == false && Sessions[Clients[index].clientId].connected == false) ->
            atomic{
                skip;
            }
        :: else -> break;
    od;

}


proctype ProcessPublisher(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    bool authorization_result = false;
    short publishedMessages = 0;
    // 、、
    short canConnect = 2;
    // 
    bool badReconnect = false;
    do
        ::
            atomic{
                if
                    :: (Clients[index].connected == false && canConnect >= 0 && badReconnect == false) ->
                        printf("PUBLISHER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                        CONNECT_entry_point(index);
                        printf("PUBLISHER_%d: connected\n", index);
                        canConnect = canConnect - 1;
                        badReconnect = true;
                        BadDisconnect = false;
                fi;
            }
        :: 
            atomic{
                if
                    :: (Clients[index].connected == true && publishedMessages < 1) ->
                        PUBLISH_entry_point(Clients[index].clientId, 0); 
                        publishedMessages = publishedMessages + 1;
                        BadDisconnect = false;
                        badReconnect = false;
                fi;
            }
        :: 
            atomic{ 
                if
                   ::  (Clients[index].connected == true  && Sessions[Clients[index].clientId].messagesLen > 0) -> 
                        printf("PUBLISHER_%d: send 'PUBREL'\n", index);
                        PUBREL_entry_point(index); 
                        printf("PUBLISHER_%d: pubrel complete\n", index);
                        BadDisconnect = false;
                        badReconnect = false;
                fi;
            }
        // :: 
        //     atomic{ 
        //         if
        //             ::  (Clients[index].connected == true && badReconnect == false) -> 
        //                 printf("PUBLISHER_%d: send 'DISCONNECT'\n", index);
        //                 DISCONNECT_entry_point(index); 
        //                 printf("PUBLISHER_%d: disconnected\n", index);
        //                 BadDisconnect = false;
        //                 canConnect = canConnect - 1;
        //         fi;
        //     }
        /*
            TODO: ACL
        */
        ::
            atomic{ 
                if
                    :: (Clients[index].connected == true && (Clients[index].aclTruth & PUBLISHACL) == PUBLISHACL) ->
                        ACL_revoke(index, PUBLISHACL);
                        printf("PUBLISHER_%d: revoke PUBLISHACL\n", index);
                fi;
            }

        :: else -> break;
    od;
}

proctype ProcessSubscriber(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    bool authorization_result = false;
    // 、、
    short canConnect = 2;
    // 
    bool badReconnect = false;
    do
        :: (Clients[index].connected == false && canConnect >= 0 && badReconnect == false && BadDisconnect == false) ->
            atomic{
                printf("SUBSCRIBER_%d: send 'CONNCET' with {username:`%d`, password:`%d`, clientId:`%d`}\n", index, Clients[index].username, Clients[index].password, Clients[index].clientId);
                CONNECT_entry_point(index);
                printf("SUBSCRIBER_%d: connected\n", index);
                canConnect = canConnect - 1;
                badReconnect = true;
            }

        :: (Clients[index].connected == true) ->
            if
                ::  (Sessions[Clients[index].clientId].subscriptionsLen < MAXSUBSCRIPTIONS) -> 
                    atomic{ 
                        printf("SUBSCRIBER_%d: send 'SUBSCRIBE'\n", index);
                        SUBSCRIBE_entry_point(index, 0); 
                        printf("SUBSCRIBER_%d: subscribed\n", index);
                        badReconnect = false;
                    }
                ::  (badReconnect == false) -> 
                    atomic{ 
                        printf("SUBSCRIBER_%d: send 'DISCONNECT'\n", index);
                        DISCONNECT_entry_point(index); 
                        printf("SUBSCRIBER_%d: disconnected\n", index);
                        canConnect = canConnect - 1;
                        BadDisconnect = true;
                    }
                /*
                    TODO: ACL
                */
                :: (Clients[index].aclTruth != 0 && (Clients[index].aclTruth & SUBSCRIBEACL) == SUBSCRIBEACL) -> 
                    atomic{ 
                        ACL_revoke(index, SUBSCRIBEACL);
                        printf("SUBSCRIBER_%d: revoke SUBSCRIBEACL\n", index);
                    }
                :: else -> skip;
            fi;
        :: else -> break;
    od;
}


init {
    atomic{
        short m = 0;
        do
            :: (m < MAXCLIENTS) ->
                Clients[m].connected = false;
                Clients[m].acl = PUBLISHACL + SUBSCRIBEACL + STOREACL + LOADACL;
                m = m + 1;
            :: else -> break;
        od;
        BadDisconnect = false;
        Clients[0].username = 0;
        Clients[0].password = 0;
        Clients[0].clientId = PUBCLIENTID_0;

        Clients[1].username = 1;
        Clients[1].password = 1;
        Clients[1].clientId = SUBCLIENTID_1;

        Clients[2].username = 2;
        Clients[2].password = 2;
        Clients[2].clientId = PUBCLIENTID_0;
        Clients[2].acl = SUBSCRIBEACL;
        Clients[2].aclTruth = SUBSCRIBEACL;
    }

    run ProcessPublisher(0);
    run ProcessSubscriber(1);
    //run ProcessPublisher2(2);
    
}

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


// 存储在session内的消息（包括will message）
typedef Message{
    short topic = -1; // 暂时只有一个topic=0 即可
    short mid = -1;
    short QoS = -1; // 0,1,2
    short srcClientId = -1; //PUBCLIENTID_0、 SUBCLIENTID_1
    short srcClientIndex = -1;
    short origin = -1; // 表示消息从0: broker; 1: publisher; 发出的
    bool retained = false;
}


// 全局消息
typedef RetainedMessage{
    short topic = -1; // 暂时只有一个topic=0 即可
    short mid = -1;
    short QoS = -1; // 0,1,2
    short srcClientId = -1; 
    short srcClientIndex = -1;
    bool retained = true;
}


typedef Subscription{
    short topic = -1;
}


// 唯一clientId
typedef Session{
    short clientId = -1;
    short clientIndex = -1;
    bool cleanStart;
    bool connected = false;

    // 存储再session中的未确认消息队列，对于publisher是发布的qos2消息，对于subscriber是收到broker的qos1、2消息
    Message messages[MAXMESSAGES];
    short messagesLen = 0;
    Subscription subscriptions[MAXSUBSCRIPTIONS];
    short subscriptionsLen = 0;

    Message willmessage;
    
}

// 唯一username
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
// Sessions数组用于保存已连接客户端的session
/*
    TODO: 目前就一个topic=0，后续增加topic可能需要增加retained messages
*/
RetainedMessage RetainedMessages;




/******************** CONNECT *************************/
inline CONNECT_entry_point(index){
    atomic{
        /*
            TODO:
            这里暂时假设直接认证成功
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
            :: CONNECT_cleanStart_false(index);
                 
        fi;
    }
}

inline CONNECT_cleanStart_true(index){
    atomic{
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = true;
        printf("with cleanStart = true\n" );



        // 清空oldsession的未确认消息，创建新session
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
        // 清空订阅关系
        do
            :: i < MAXSUBSCRIPTIONS ->
                Sessions[localClientId].subscriptions[i].topic = -1;
                i = i + 1;
            :: else -> break;
        od;  
        Sessions[localClientId].subscriptionsLen = 0;
        // 清除will message
        Sessions[localClientId].willmessage.topic = -1;
        Sessions[localClientId].willmessage.mid = -1;
        Sessions[localClientId].willmessage.QoS = -1;
        Sessions[localClientId].willmessage.srcClientId = -1;
        Sessions[localClientId].willmessage.srcClientIndex = -1;
        Sessions[localClientId].willmessage.origin = -1;
        CONNECT_will_message(index);
    }
}

inline CONNECT_cleanStart_false(index){
    atomic{
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = false;
        printf("with cleanStart = false\n" );

        i = 0;
        do
            :: i < MAXMESSAGES ->
                if
                    // 如果是Broker向订阅者发送的消息未确认，则Broker重发这些消息
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
                                Deliver(Sessions[localClientId].messages[i], localClientId);
                        fi;
                    :: (Sessions[localClientId].messages[i].topic != -1 && Sessions[localClientId].messages[i].origin == 1 && (Sessions[localClientId].messages[i].QoS == 0 || Sessions[localClientId].messages[i].QoS == 1)) ->
                        printf("Bad QoS0 or QoS1 message stored in session from publisher!\n");
                        break;
                    :: else -> skip;
                fi;
                i = i + 1;
            :: else -> break;
        od;

        CONNECT_will_message(index);
    }
}


inline CONNECT_will_message(index){
    atomic{
        localClientId = Clients[index].clientId;
        if
            // 如果是publisher就创建一个will message，subscriber假设只订阅不发布，所以不创建will
            :: (localClientId != SUBCLIENTID_1) ->
                Sessions[localClientId].willmessage.topic = 0;
                Sessions[localClientId].willmessage.mid = GlobalMid;
                GlobalMid = GlobalMid + 1;
                // 因为不同qos的will message没有意义
                Sessions[localClientId].willmessage.QoS = 0;
                Sessions[localClientId].willmessage.srcClientId = localClientId;
                Sessions[localClientId].willmessage.srcClientIndex = index;
                Sessions[localClientId].willmessage.origin = 1;
                printf("Message_%d: Will message created!\n",Sessions[localClientId].willmessage.mid);
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
            :: PUBLISH_QoS0_step2(index, t);
            :: PUBLISH_QoS1_step2(index, t);
            :: (Sessions[localClientId].messagesLen < MAXMESSAGES) -> PUBLISH_QoS2_step2(index, t);
            :: PUBLISH_retained_QoS0_step2(index, t);
        fi;

    }
}
inline PUBLISH_QoS0_step2(index, t){
    atomic{
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS0 message\n", index);
        Message message;
        message.topic = t;
        message.mid = GlobalMid;
        GlobalMid = GlobalMid + 1;
        message.QoS = 0;
        message.srcClientId = localClientId;
        message.srcClientIndex = index;
        printf("Message_%d: QoS0 message created!\n", message.mid);
        Deliver_to_Subscribers(message);
        PUBLISH_end();
    }
}

inline PUBLISH_QoS1_step2(index, t){
    atomic{
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS1 message\n", index);
        Message message;
        message.topic = t;
        message.mid = GlobalMid;
        GlobalMid = GlobalMid + 1;
        message.QoS = 1;
        message.srcClientId = localClientId;
        message.srcClientIndex = index;
        printf("Message_%d: QoS1 message created!\n", message.mid);
        Deliver_to_Subscribers(message);
        PUBLISH_end();
    }
}

inline PUBLISH_QoS2_step2(index, t){
    atomic{
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS2 message\n", index);
        if
            :: Sessions[localClientId].messagesLen < MAXMESSAGES ->
                lastMessage = Sessions[localClientId].messagesLen;
                Sessions[localClientId].messages[lastMessage].topic = t;
                Sessions[localClientId].messages[lastMessage].mid = GlobalMid;
                GlobalMid = GlobalMid + 1;
                Sessions[localClientId].messages[lastMessage].QoS = 2;
                Sessions[localClientId].messages[lastMessage].srcClientId = localClientId;
                Sessions[localClientId].messages[lastMessage].srcClientIndex = index;
                Sessions[localClientId].messages[lastMessage].origin = 1;
                Sessions[localClientId].messagesLen = Sessions[localClientId].messagesLen + 1;
                printf("Message_%d: QoS2 message created!\n", Sessions[localClientId].messages[lastMessage].mid);
                /***
                UPDATE
                ***/
                Deliver_to_Subscribers(Sessions[localClientId].messages[lastMessage]);
            :: else ->
                printf("Publisher_%d: can not store more qos1,2 messages\n", localClientId);
        fi;
        PUBLISH_end();
    }
}


inline PUBLISH_retained_QoS0_step2(index, t){
    atomic{
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS0 retained message\n", index);
        Message message;
        message.topic = t;
        message.mid = GlobalMid;
        GlobalMid = GlobalMid + 1;
        message.QoS = 0;
        message.srcClientId = localClientId;
        message.srcClientIndex = index;
        printf("Message_%d: Retained message created!\n", message.mid);
        Deliver_to_Subscribers(message);
        RetainedMessages.topic = t;
        RetainedMessages.mid = message.mid;
        RetainedMessages.QoS = 0;
        RetainedMessages.srcClientId = localClientId;
        RetainedMessages.srcClientIndex = index;
        PUBLISH_end();
    }
}



inline PUBLISH_end(){
    atomic{
        skip;
    }
}


/******************** PUBREL *************************/
/*
    TODO: 依然简化为只有一个topic，PUBREL简化为进先出，确认Publisher的session中未确认消息队列
*/
inline PUBREL_entry_point(index){
    atomic{
        PUBREL(index);
    }
}
inline PUBREL(index){
    atomic{
        localClientId = Clients[index].clientId;
        if
            :: (Sessions[localClientId].messagesLen > 0) ->
                lastMessage = Sessions[localClientId].messagesLen - 1;
                if
                    :: (Sessions[localClientId].messages[lastMessage].topic != -1 && Sessions[localClientId].messages[lastMessage].QoS == 2) ->
                        /***
                        UPDATE
                        ***/
                        //Deliver_to_Subscribers(Sessions[localClientId].messages[lastMessage])
                    :: else -> skip;  
                fi;

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
        localClientId = Clients[index].clientId;
        if
            :: (Sessions[localClientId].subscriptionsLen < MAXSUBSCRIPTIONS) ->
                Sessions[localClientId].subscriptions[Sessions[localClientId].subscriptionsLen].topic = t;
                Sessions[localClientId].subscriptionsLen = Sessions[localClientId].subscriptionsLen + 1;
                if
                    :: (RetainedMessages.topic != -1 && RetainedMessages.topic == t) ->
                        Message message;
                        message.topic = RetainedMessages.topic;
                        message.mid = RetainedMessages.mid;
                        message.QoS = RetainedMessages.QoS;
                        message.srcClientId = RetainedMessages.srcClientId;
                        message.srcClientIndex = RetainedMessages.srcClientId;
                        Deliver(message, localClientId);
                    :: else -> skip;
                fi;
            :: else -> skip;
        fi;
        SUBSCRIBE_end(index, t);
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
        UNSUBSCRIBE_end(index, t);
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
            :: Sessions[Clients[index].clientId].willmessage.topic != -1 ->
                Deliver_to_Subscribers(Sessions[Clients[index].clientId].willmessage);
            :: else -> skip;
        fi;
        localClientId = Clients[index].clientId;
        if
            :: Sessions[localClientId].connected == true ->
                if
                    :: Sessions[localClientId].willmessage.topic != -1 ->
                        Sessions[localClientId].willmessage.topic = -1;
                        Sessions[localClientId].willmessage.mid = -1;
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
inline DISCONNECT_end(){
    atomic{
        skip;
    }
}



/******************** ACL revoke *************************/
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


inline Authorization_read_allowed(index, topic, rt){
    atomic{
        if
            :: ((Clients[index].acl & READACL) == READACL) ->
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
inline Deliver_to_Subscribers(msg){
    atomic{
        short i_1 = 0;
        do
            :: i_1 < MAXSESSIONS ->
                bool hasSubscription = false;
                j = 0;
                if
                    // session是空的，或者由于cleanStart=true, disconnect，没有清空
                    :: (Sessions[i_1].clientId == -1) ->
                        goto nextClients;
                    :: else -> skip;
                fi;
                // 遍历Clients[i_1] 的订阅树，查看是否订阅message的topic
                do
                    :: j < MAXSUBSCRIPTIONS ->
                        if
                            :: (Sessions[i_1].subscriptions[j].topic == msg.topic) ->
                                hasSubscription = true;
                                break;
                            :: else -> skip;
                        fi;
                        j = j + 1;
                    :: else -> 
                        goto nextClients;
                od;
                /***
                UPDATE
                ***/
/*------------------------------Mosquitto-BEGIN---------------------------------*/
                if
                    // session是空的，或者由于cleanStart=true, disconnect，没有清空
                    :: (Sessions[i_1].clientId != -1) ->
                        authorization_result = false;
                        Authorization_read_allowed(Sessions[i_1].clientIndex, msg.topic, authorization_result);
                        if
                            :: (authorization_result == false) ->
                                printf("Authorization failed!\n");
                                goto Deliver_to_Subscribers_inserted_end_1;
                            :: else -> skip;
                        fi;
                    :: else -> skip;
                fi;
/*------------------------------Mosquitto-END---------------------------------*/

                if
                    // 如果订阅者在线则直接投递
                    :: (hasSubscription == true && Sessions[i_1].connected == true) ->
                        Deliver(msg, i_1);
                    // 如果订阅者不在线则将QoS1，2的消息存放在订阅者session中
                    :: (hasSubscription == true && Sessions[i_1].connected == false && (msg.QoS == 1 || msg.QoS == 2)) ->
                        if
                            :: Sessions[i_1].messagesLen < MAXMESSAGES ->
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].topic = msg.topic;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].mid = msg.mid;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].QoS = msg.QoS;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientId = msg.srcClientId;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientIndex = msg.srcClientIndex;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].origin = 0; // 表示从broker向subscriber发送的消息
                                Sessions[i_1].messagesLen = Sessions[i_1].messagesLen + 1;
                                printf("Message_%d: Message stored!\n", msg.mid);
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


proctype ProcessPublisher2(short index){
    short i = 0;
    short j = 0;
    short localClientId;
    bool authorization_result = false;
    short publishedMessages = 0;
    // 只允许登录一次、下线一次、再次登录
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
    // 只允许登录一次、下线一次、再次登录
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
            TODO: ACL需定制化
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
    // 只允许登录一次、下线一次、再次登录
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
            TODO: ACL需定制化
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

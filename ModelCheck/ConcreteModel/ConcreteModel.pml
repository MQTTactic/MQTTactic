#define BROKER -1

#define PUBCLIENTID_0 0
#define SUBCLIENTID_1 1
#define MAXCLIENTS 3
#define MAXMESSAGES 5
#define MAXSUBSCRIPTIONS 1
#define MAXSESSIONS 2
#define SUBSCRIBEACL 1
#define PUBLISHACL 2
#define READACL 4

typedef Message{
    short topic = -1; 
    short QoS = -1; 
    short srcClientId = -1; 
    short srcClientIndex = -1;
    short origin = -1; 
    bool retained = false;
}

typedef RetainedMessage{
    short topic = -1; 
    short QoS = -1; 
    short srcClientId = -1; 
    short srcClientIndex = -1;
    bool retained = true;
}
typedef Subscription{
    short topic = -1;
}

typedef Session{
    short clientId = -1;
    short clientIndex = -1;
    bool cleanStart;
    bool connected = false;
    
    Message messages[MAXMESSAGES];
    short messagesLen = 0;
    Subscription subscriptions[MAXSUBSCRIPTIONS];
    short subscriptionsLen = 0;
    Message willmessage;
}

typedef Client{
    short username;
    short password;
    short clientId;
    bool connected = false;
    

    short acl = PUBLISHACL + SUBSCRIBEACL + READACL;
    short aclTruth = PUBLISHACL + SUBSCRIBEACL + READACL;
    
}
bool BadDisconnect;
Client Clients[MAXCLIENTS];
Session Sessions[MAXSESSIONS];



RetainedMessage RetainedMessages;

inline CONNECT_entry_point(index){
    atomic{
        

        
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
if
:: handle__connect_cleanStartT_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47(index);
:: handle__connect_cleanStartT_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29(index);
fi;
    }
}
inline CONNECT_cleanStart_false(index){
    atomic{
if
:: handle__connect_cleanStartF_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47(index);
:: handle__connect_cleanStartF_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29(index);
fi;
    }
}
inline CONNECT_will_message(index){
    atomic{
        localClientId = Clients[index].clientId;
        if
            
            :: (localClientId != SUBCLIENTID_1) ->
                Sessions[localClientId].willmessage.topic = 0;
                
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
if
:: handle__publish_qos0_Type_7(index, t);
fi;
    }
}
inline PUBLISH_QoS1_step2(index, t){
    atomic{
if
:: handle__publish_qos1_Type_0(index, t);
fi;
    }
}
inline PUBLISH_QoS2_step2(index, t){
    atomic{
if
:: handle__publish_qos2_Type_2(index, t);
fi;
    }
}
inline PUBLISH_retained_QoS0_step2(index, t){
    atomic{
if
:: handle__publish_qos0_retained_Type_7(index, t);
fi;
    }
}
inline PUBLISH_end(){
    atomic{
        skip;
    }
}



inline PUBREL_entry_point(index){
    atomic{
        PUBREL(index);
    }
}
inline PUBREL(index){
    atomic{
if
:: handle__pubrel_Type_0(index);
fi;
    }
}
inline PUBREL_end(index){
    atomic{
        skip;
    }
}

inline SUBSCRIBE_entry_point(index, t){
    atomic{
        SUBSCRIBE(index, t);
    }
}
inline SUBSCRIBE(index, t){
    atomic{
if
:: handle__subscribe_Type_2_3_4_5_7_8_9_10_11_12_13_14(index, t);
fi;
    }
}
inline SUBSCRIBE_end(index, t){
    atomic{
        skip;
    }
}

inline UNSUBSCRIBE_entry_point(index, t){
    atomic{
        UNSUBSCRIBE(index, t);
    }
}
inline UNSUBSCRIBE(index, t){
    atomic{
if
:: handle__unsubscribe_Type_2(index, t);
fi;
    }
}
inline UNSUBSCRIBE_end(index, t){
    atomic{
        skip;
    }
}

inline DISCONNECT_entry_point(index){
    atomic{
        DISCONNECT(index);
    }
}
inline DISCONNECT(index){
    atomic{
if
:: handle__disconnect_Type_0_Type_1(index);
fi;
    }
}
inline DISCONNECT_end(){
    atomic{
        skip;
    }
}

inline ACL_revoke(index, revokeAcl){
    atomic{
if
:: ACL_revoke_Type_0(index, revokeAcl);
fi;
    }
}

inline Authentication_UserPass_allowed(){
    atomic{
        skip;
    }
}
inline Authorization_subscribe_allowed(index, topic, rt){
    atomic{
        if
            :: (Clients[index].acl != 0 && Clients[index].acl != 2 && Clients[index].acl != 4 && Clients[index].acl != 6) ->
                rt = true;
            :: else ->
                rt = false;
        fi;
    }
}
inline Authorization_publish_allowed(index, topic, rt){
    atomic{
        if
            :: (Clients[index].acl != 0 && Clients[index].acl != 1 && Clients[index].acl != 4 && Clients[index].acl != 5) ->
                rt = true;
            :: else -> 
                rt = false;
        fi;
    }
}
inline Authorization_read_allowed(index, topic, rt){
    atomic{
        if
            :: (Clients[index].acl >= 4) ->
                rt = true;
            :: else ->
                rt = false;
        fi;
    }
}

inline Deliver_to_Subscribers(message){
    atomic{
        short i_1 = 0;
        printf("Message to subscribers: Topic = %d; QoS = %d; FROM = SESSION_%d; \n", message.topic, message.QoS, message.srcClientId);
        do
            :: i_1 < MAXSESSIONS ->
                bool hasSubscription = false;
                j = 0;
                if
                    
                    :: (Sessions[i_1].clientId == -1) ->
                        goto nextClients;
                    :: else -> skip;
                fi;
                
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
                    
                    :: (Sessions[i_1].clientId != -1) ->
                        authorization_result = false;
                        Authorization_read_allowed(Sessions[i_1].clientIndex, message.topic, authorization_result);
                        if
                            :: (authorization_result == false) ->
                                printf("Authorization failed!\n");
                                goto Deliver_to_Subscribers_inserted_end_1;
                            :: else -> skip;
                        fi;
                    :: else -> skip;
                fi;

                if
                    
                    :: (hasSubscription == true && Sessions[i_1].connected == true) ->
                        Deliver(message, i_1);
                    
                    :: (hasSubscription == true && Sessions[i_1].connected == false && (message.QoS == 1 || message.QoS == 2)) ->
                        if
                            :: Sessions[i_1].messagesLen < MAXMESSAGES ->
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].topic = message.topic;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].QoS = message.QoS;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientId = message.srcClientId;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].srcClientIndex = message.srcClientIndex;
                                Sessions[i_1].messages[Sessions[i_1].messagesLen].origin = 0; 
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
inline handle__publish_qos0_Type_7(index, t){
 atomic{
printf("Enter function handle__publish_qos0_Type_7\n");
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS0 message\n", index);
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
                goto LABEL_1_Type_7
            :: else -> skip;
        fi;
        Deliver_to_Subscribers(message);
LABEL_1_Type_7:
 skip; 
        PUBLISH_end();
}
}
inline handle__publish_qos1_Type_0(index, t){
 atomic{
printf("Enter function handle__publish_qos1_Type_0\n");
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS1 message\n", index);
        Message message;
        message.topic = t;
        message.QoS = 1;
        message.srcClientId = localClientId;
        message.srcClientIndex = index;
        authorization_result = false;
        Authorization_publish_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_2_Type_0
            :: else -> skip;
        fi;
        Deliver_to_Subscribers(message);
LABEL_2_Type_0:
 skip; 
        PUBLISH_end();
}
}
inline handle__publish_qos2_Type_2(index, t){
 atomic{
printf("Enter function handle__publish_qos2_Type_2\n");
        localClientId = Clients[index].clientId;
        printf("PUBLISHER_%d: publish a QoS2 message\n", index);
        if
            :: Sessions[localClientId].messagesLen < MAXMESSAGES ->
                Message message;
                message.topic = t;
                message.QoS = 2;
                message.srcClientId = localClientId;
                message.srcClientIndex = index;
        authorization_result = false;
        Authorization_publish_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_4_Type_2
            :: else -> skip;
        fi;
                Deliver_to_Subscribers(message);
LABEL_4_Type_2:
 skip; 
                Sessions[localClientId].messages[Sessions[localClientId].messagesLen].topic = t;
                Sessions[localClientId].messages[Sessions[localClientId].messagesLen].QoS = 2;
                Sessions[localClientId].messages[Sessions[localClientId].messagesLen].srcClientId = localClientId;
                Sessions[localClientId].messages[Sessions[localClientId].messagesLen].srcClientIndex = index;
                Sessions[localClientId].messages[Sessions[localClientId].messagesLen].origin = 1;
                Sessions[localClientId].messagesLen = Sessions[localClientId].messagesLen + 1;
            :: else ->
                printf("Publisher_%d: can not store more qos1,2 messages\n", localClientId);
        fi;
        

        PUBLISH_end();
}
}
inline handle__publish_qos0_retained_Type_7(index, t){
 atomic{
printf("Enter function handle__publish_qos0_retained_Type_7\n");
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
                goto LABEL_7_Type_7
            :: else -> skip;
        fi;
        Deliver_to_Subscribers(message);
        RetainedMessages.topic = t;
        RetainedMessages.QoS = 0;
        RetainedMessages.srcClientId = localClientId;
        RetainedMessages.srcClientIndex = index;
LABEL_7_Type_7:
 skip; 
        PUBLISH_end();
}
}
inline handle__connect_cleanStartT_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47(index){
 atomic{
printf("Enter function handle__connect_cleanStartT_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47\n");
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = true;
        printf("with cleanStart = true\n" );
        
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
        
        do
            :: i < MAXSUBSCRIPTIONS ->
                Sessions[localClientId].subscriptions[i].topic = -1;
                i = i + 1;
            :: else -> break;
        od;  
        Sessions[localClientId].subscriptionsLen = 0;
        
        Sessions[localClientId].willmessage.topic = -1;
        Sessions[localClientId].willmessage.QoS = -1;
        Sessions[localClientId].willmessage.srcClientId = -1;
        Sessions[localClientId].willmessage.srcClientIndex = -1;
        Sessions[localClientId].willmessage.origin = -1;
        CONNECT_will_message(index);
}
}
inline handle__connect_cleanStartT_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29(index){
 atomic{
printf("Enter function handle__connect_cleanStartT_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29\n");
        if
            :: Sessions[Clients[index].clientId].willmessage.topic != -1 ->
                Deliver_to_Subscribers(Sessions[Clients[index].clientId].willmessage);
            :: else -> skip;
        fi;
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = true;
        printf("with cleanStart = true\n" );
        
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
        
        do
            :: i < MAXSUBSCRIPTIONS ->
                Sessions[localClientId].subscriptions[i].topic = -1;
                i = i + 1;
            :: else -> break;
        od;  
        Sessions[localClientId].subscriptionsLen = 0;
        
        Sessions[localClientId].willmessage.topic = -1;
        Sessions[localClientId].willmessage.QoS = -1;
        Sessions[localClientId].willmessage.srcClientId = -1;
        Sessions[localClientId].willmessage.srcClientIndex = -1;
        Sessions[localClientId].willmessage.origin = -1;
        CONNECT_will_message(index);
}
}
inline handle__connect_cleanStartF_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47(index){
 atomic{
printf("Enter function handle__connect_cleanStartF_Type_0_4_12_16_32_34_38_40_Type_18_22_26_30_41_43_45_47\n");
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = false;
        printf("with cleanStart = false\n" );
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
                                message.QoS = Sessions[localClientId].messages[i].QoS;
                                message.srcClientId = Sessions[localClientId].messages[i].srcClientId;
                                message.srcClientIndex = Sessions[localClientId].messages[i].srcClientIndex;
                                Deliver(message, localClientId);
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
inline handle__connect_cleanStartF_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29(index){
 atomic{
printf("Enter function handle__connect_cleanStartF_Type_1_5_13_17_Type_2_14_33_39_Type_3_15_Type_6_10_35_37_Type_7_11_Type_8_36_Type_9_Type_19_23_27_31_Type_20_28_42_46_Type_21_29\n");
        if
            :: Sessions[Clients[index].clientId].willmessage.topic != -1 ->
                Deliver_to_Subscribers(Sessions[Clients[index].clientId].willmessage);
            :: else -> skip;
        fi;
        localClientId = Clients[index].clientId;
        Sessions[localClientId].cleanStart = false;
        printf("with cleanStart = false\n" );
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
                                message.QoS = Sessions[localClientId].messages[i].QoS;
                                message.srcClientId = Sessions[localClientId].messages[i].srcClientId;
                                message.srcClientIndex = Sessions[localClientId].messages[i].srcClientIndex;
                                Deliver(message, localClientId);
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
inline handle__disconnect_Type_0_Type_1(index){
 atomic{
printf("Enter function handle__disconnect_Type_0_Type_1\n");
        localClientId = Clients[index].clientId;
        if
            :: Sessions[localClientId].connected == true ->
                if
                    :: Sessions[localClientId].willmessage.topic != -1 ->
                        Message message;
                        message.topic = Sessions[localClientId].willmessage.topic;
                        message.QoS = Sessions[localClientId].willmessage.QoS;
                        message.srcClientId = Sessions[localClientId].willmessage.srcClientId;  
                        message.srcClientIndex = Sessions[localClientId].willmessage.srcClientIndex;
                        printf("PUBLISHER_%d: Send the will message to subscriber\n", index);
                        Deliver_to_Subscribers(message);
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
                
        fi;
        DISCONNECT_end();
        

}
}
inline handle__pubrel_Type_0(index){
 atomic{
printf("Enter function handle__pubrel_Type_0\n");
        localClientId = Clients[index].clientId;
        short lastMessage = 0;
        if
            :: (Sessions[localClientId].messagesLen > 0) ->
                lastMessage = Sessions[localClientId].messagesLen - 1;
                Sessions[localClientId].messages[lastMessage].topic = -1;
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
inline handle__subscribe_Type_2_3_4_5_7_8_9_10_11_12_13_14(index, t){
 atomic{
printf("Enter function handle__subscribe_Type_2_3_4_5_7_8_9_10_11_12_13_14\n");
        authorization_result = false;
        Authorization_subscribe_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_31_Type_2_3_4_5_7_8_9_10_11_12_13_14
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
        Authorization_read_allowed(index, t, authorization_result);
        if
            :: (authorization_result == false) ->
                printf("Authorization failed!\n");
                goto LABEL_32_Type_2_3_4_5_7_8_9_10_11_12_13_14
            :: else -> skip;
        fi;
                        Deliver(RetainedMessages, localClientId);
LABEL_32_Type_2_3_4_5_7_8_9_10_11_12_13_14:
 skip; 
                    :: else -> skip;
                fi;
            :: else -> skip;
        fi;
LABEL_31_Type_2_3_4_5_7_8_9_10_11_12_13_14:
 skip; 
        SUBSCRIBE_end(index, t);
}
}
inline handle__unsubscribe_Type_2(index, t){
 atomic{
printf("Enter function handle__unsubscribe_Type_2\n");
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
inline ACL_revoke_Type_0(index, revokeAcl){
 atomic{
printf("Enter function ACL_revoke_Type_0\n");
        if
            
            :: (revokeAcl == SUBSCRIBEACL && Clients[index].acl != 0 && Clients[index].acl != 2 && Clients[index].acl != 4 && Clients[index].acl != 6) ->
                Clients[index].acl = Clients[index].acl - SUBSCRIBEACL;
            
            :: (revokeAcl == PUBLISHACL && Clients[index].acl != 0 && Clients[index].acl != 1 && Clients[index].acl != 4 && Clients[index].acl != 5) ->
                Clients[index].acl = Clients[index].acl - PUBLISHACL;
            
            :: (revokeAcl == READACL && Clients[index].acl >= 4) ->
                Clients[index].acl = Clients[index].acl - READACL;
            :: else -> skip;
        fi;
        if
            
            :: (revokeAcl == SUBSCRIBEACL && Clients[index].aclTruth != 0 && Clients[index].aclTruth != 2 && Clients[index].aclTruth != 4 && Clients[index].aclTruth != 6) ->
                Clients[index].aclTruth = Clients[index].aclTruth - SUBSCRIBEACL;
            
            :: (revokeAcl == PUBLISHACL && Clients[index].aclTruth != 0 && Clients[index].aclTruth != 1 && Clients[index].aclTruth != 4 && Clients[index].aclTruth != 5) ->
                Clients[index].aclTruth = Clients[index].aclTruth - PUBLISHACL;
            
            :: (revokeAcl == READACL && Clients[index].aclTruth >= 4) ->
                Clients[index].aclTruth = Clients[index].aclTruth - READACL;
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
                            :: ((Clients[message.srcClientIndex].aclTruth != 0 && Clients[message.srcClientIndex].aclTruth != 1 && Clients[message.srcClientIndex].aclTruth != 4 && Clients[message.srcClientIndex].aclTruth != 5) &&  (Clients[Sessions[subscriber].clientIndex].aclTruth >= 4)) ->
                                flag = true;
                            :: else -> skip;
                        fi;
                    :: else ->
                        if
                            :: ((Clients[Sessions[message.srcClientId].clientIndex].aclTruth != 0 && Clients[Sessions[message.srcClientId].clientIndex].aclTruth != 1 && Clients[Sessions[message.srcClientId].clientIndex].aclTruth != 4 && Clients[Sessions[message.srcClientId].clientIndex].aclTruth != 5) &&  (Clients[Sessions[subscriber].clientIndex].aclTruth >= 4)) ->
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
    
    short canConnect = 2;
    
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
    
    short canConnect = 2;
    
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
        :: 
            atomic{ 
                if
                    ::  (Clients[index].connected == true && badReconnect == false) -> 
                        printf("PUBLISHER_%d: send 'DISCONNECT'\n", index);
                        DISCONNECT_entry_point(index); 
                        printf("PUBLISHER_%d: disconnected\n", index);
                        BadDisconnect = false;
                        canConnect = canConnect - 1;
                fi;
            }
        

        ::
            atomic{ 
                if
                    :: (Clients[index].connected == true && Clients[index].aclTruth != 0 && Clients[index].aclTruth != 1 && Clients[index].aclTruth != 4 && Clients[index].aclTruth != 5) ->
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
    
    short canConnect = 2;
    
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
                

                :: (Clients[index].aclTruth != 0 && Clients[index].aclTruth != 2 && Clients[index].aclTruth != 4 && Clients[index].aclTruth != 6) -> 
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
                Clients[m].acl = PUBLISHACL + SUBSCRIBEACL + READACL;
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
        Clients[2].acl = READACL;
        Clients[2].aclTruth = READACL;
    }
    run ProcessPublisher(0);
    run ProcessSubscriber(1);
    
}

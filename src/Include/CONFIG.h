
using namespace std;

// handlers
std::string handle__connect = "_ZN10MqttPacket13handleConnectEv";
std::string handle__publish = "_ZN10MqttPacket13handlePublishEv";
std::string handle__pubrel = "_ZN10MqttPacket12handlePubRelEv";
std::string handle__subscribe = "_ZN10MqttPacket15handleSubscribeEv";
std::string handle__unsubscribe = "_ZN10MqttPacket17handleUnsubscribeEv";
std::string handle__disconnect = "_ZN10MqttPacket16handleDisconnectEv";
std::string handle__ACL_revoke = "";
// handlers_end
std::string send__connack = "_ZN7ConnAckC2E18ConnAckReturnCodesb";
std::string send__puback = "_ZN6PubAckC2Et";
std::string send__pubrec = "_ZN6PubRecC2Et";
std::string send__pubcomp = "_ZN7PubCompC2Et";
std::string send__suback = "_ZN6SubAckC2EtRKNSt7__cxx114listIcSaIcEEE";
std::string send__unsuback = "_ZN8UnsubAckC2Et";
// key operations
std::string acl_check = "_ZN14Authentication8aclCheckERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEES7_S7_RKSt6vectorIS5_SaIS5_EE9AclAccesscb";
std::string deliver_to_subscribers = "_ZN17SubscriptionStore24queuePacketAtSubscribersERKSt6vectorINSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEESaIS6_EER10MqttPacketb+_ZN10ThreadData19removeQueuedClientsEv";
std::string deliver = "_ZN6Client15writeMqttPacketERK10MqttPacket";
std::string sub_add = "_ZN16SubscriptionNode13addSubscriberERKSt10shared_ptrI7SessionEc";
std::string sub_remove = "_ZN16SubscriptionNode16removeSubscriberERKSt10shared_ptrI7SessionEZN16SubscriptionNode18cleanSubscriptionsEv+_ZN16SubscriptionNode18cleanSubscriptionsEv";
std::string acl_revoke = "";

config = {
    # handlers
    "handle__connect": "_ZN10MqttPacket13handleConnectEv",
    "handle__publish": "_ZN10MqttPacket13handlePublishEv",
    "handle__pubrel": "_ZN10MqttPacket12handlePubRelEv",
    "handle__subscribe": "_ZN10MqttPacket15handleSubscribeEv",
    "handle__unsubscribe": "_ZN10MqttPacket17handleUnsubscribeEv",
    "handle__disconnect": "_ZN10MqttPacket16handleDisconnectEv",
    "handle__ACL_revoke": "",
    # handlers_end
    "send__connack": "_ZN7ConnAckC2E18ConnAckReturnCodesb",
    "send__puback": "_ZN6PubAckC2Et",
    "send__pubrec": "_ZN6PubRecC2Et",
    "send__pubcomp": "_ZN7PubCompC2Et",
    "send__suback": "_ZN6SubAckC2EtRKNSt7__cxx114listIcSaIcEEE",
    "send__unsuback": "_ZN8UnsubAckC2Et",
    # key operations
    "acl_check": "_ZN14Authentication8aclCheckERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEES7_S7_RKSt6vectorIS5_SaIS5_EE9AclAccesscb",
    "deliver_to_subscribers": "_ZN17SubscriptionStore24queuePacketAtSubscribersERKSt6vectorINSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEESaIS6_EER10MqttPacketb+_ZN10ThreadData19removeQueuedClientsEv",
    "deliver": "_ZN6Client15writeMqttPacketERK10MqttPacket",
    "sub_add": "_ZN16SubscriptionNode13addSubscriberERKSt10shared_ptrI7SessionEc",
    "sub_remove": "_ZN16SubscriptionNode16removeSubscriberERKSt10shared_ptrI7SessionEZN16SubscriptionNode18cleanSubscriptionsEv+_ZN16SubscriptionNode18cleanSubscriptionsEv",
    "acl_revoke": "acl_revoke",

    # authorization
    "acl_check_pattern": '(AclAccess::write|AclAccess::subscribe|AclAccess::read)',
    "authorization_pub": "AclAccess::write",
    "authorization_sub": "AclAccess::subscribe",
    "authorization_read": "AclAccess::read",
    "authorization_store": "security.AllowStore",
    "authorization_load": "security.AllowLoad",
}


.PHONY:clean


CFGPass.so: CFGPass.cpp
	clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o CFGPass.so

SCA: CFGPass.so
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket13handleConnectEv" -enable-new-pm=0 2> handle__connect.output
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket13handlePublishEv" -enable-new-pm=0 2> handle__publish.output
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket12handlePubRelEv" -enable-new-pm=0 2> handle__pubrel.output
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket15handleSubscribeEv" -enable-new-pm=0 2> handle__subscribe.output
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket17handleUnsubscribeEv" -enable-new-pm=0 2> handle__unsubscribe.output
	opt -load ./CFGPass.so -CFG ./FlashMQ_qos0.bc -Handler="_ZN10MqttPacket16handleDisconnectEv" -enable-new-pm=0 2> handle__disconnect.output


clean:
	rm -rf *.o
	rm -rf ../bin/*.so

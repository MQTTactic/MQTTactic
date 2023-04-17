## MQTTactic
The MQTTactic is our tool for evaluating the security of the MQTT Broker with static analyses. More details and instructions will be uploaded/updated later.



### 0x01 LLVM IR generation

We provide the detailed technical guidance and examples for LLVM IR generation online (https://github.com/MQTTactic/LLVM-IR-generation), which include environment configuration, all necessary commands to run the tool. The LLVM IR is the input of our MQTTactic.

### 0x02 Getting started
#### 1. Install
* The MQTTactic works on LLVM IR, So LLVM must be available in your system. Currently, the supported LLVM versions are `llvm-9`, `llvm-10`, `llvm-11`, `llvm-12`, and `llvm-13`.
* Haybale for symbolic execution<br>
`git clone https://github.com/MQTTactic/Haybale`


#### 2. Usage
* Configuration
	A simple example can be found in `Include/`.
* CFG analysis
```
$ clang  -Wl,-znodelete -fno-rtti -fPIC -shared AllFunctions.cpp -o AllFunctions.so
$ opt -load ./AllFunctions.so -funcs ./complete.bc -enable-new-pm=0 -o complete.bc 2> ./ALLFunctions


$ clang  -Wl,-znodelete -fno-rtti -fPIC -shared CFGPass.cpp -o CFGPass.so
$ opt -load ./CFGPass.so -CFG ./complete.bc -enable-new-pm=0 -o /dev/null 2> OUTPUT/xxx.output
```

* Symbolic Execution
```
$ cd SymbolicExecution/ && cargo build
$ cd target/debug/
$ ./SE "handle__pubrel" "{config_handle__pubrel}" "{type_num}" "{LLVM_bitcode_dir}" > ModelCheck/SymbolicExecutionResults/handle__pubrel/Type-{type_num}.log 2>&1
```

* Model Check
```
spin -a ConcreteModel.pml
mkdir build
gcc -DMEMLIM=16384 -DVECTORSZ=4096 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan ../pan.c
./pan -m40000 -E -c0 -e -n  > result.txt
```


### 0x03 A running example




### 0x04 Proof of Concept (PoC)

#### PoC exploit on Flaw 1
<img src="Figures/Fig_flaw_pubrel_qos2.png" alt="Flaw 1" style="zoom: 67%;" />

> $S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $A_1$ -> $A_2$ -> $S_4$ -> $C_2$ -> $S_5$


To exploit the Flaw 1, we deployed the Mosquitto
broker in our testing server, used the popular MQTT client
[MQTTX](https://github.com/emqx/MQTTX) to simulate the victim smart door, and wrote
another malicious MQTT client to act as the malicious user,
which was programmed to stall after receiving the PUBREC
packet from the broker (i.e., stall at the step $S_3$) and to
continue the message processing under manual instruction.
To strike the PoC attack, we first authorized the malicious
client with the right to PUBLISH message to the topic
that the MQTTX client (the smart door) subscribes to. Then,
we started the attack by sending an “unlock door” command
within a QoS 2 message to the broker. After the steps of
$S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $A_1$, the malicious client stalls. We, then,
reconfigured the Mosquitto broker to remove the malicious
client’s access right (step $A_2$), simulating the real-world
scenario where an Airbnb guest checks out and loses access
to the smart door. Next, we instructed the malicious client
to send the PUBREL packet (step $S_4$), which triggers the
following steps of $C_2$ -> $S_5$ -> $S_6$, and found that the smart
door was unlocked successfully after receiving the command
in the QoS 2 message M.

#### PoC exploit on Flaw 2
<img src="Figures/Fig_flaw_QoS1_retry.png" alt="Flaw 1" style="zoom:67%;" />

> $A_1$ -> $S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $S_4$ -> $A_2$ -> $A_3$ -> $S_5$ -> $S_6$


We confirmed Flaw 2 is exploitable
in a smart home system and has a real-world impact. We
used Mosquitto and two MQTTX clients to simulate the
vulnerable MQTT broker, a malicious Airbnb guest, and the
victim smart backdoor, respectively. At first, we authorized
the malicious guest to control the smart backdoor, simulat-
ing that the guest possesses access right to the backdoor
during his stay. Then, we cut off the connection between
the smart backdoor and the broker ($A_1$), simulating that
the guest turns off the WiFi networ, which enforces the
smart backdoor to go offline. Then, we let the malicious
guest PUBLISH a QoS 1 message ($S_1$) containing an
“unlocking” command to the smart backdoor, which caused
the system to stall after executing the actions of $C_1$ -> $S_2$ -> $S_3$ -> $S_4$. We then reconfigured the Mosquitto to remove
the guest’s access right, simulating that the guest checks
out and loses control of the smart backdoor ($A_2$). Later,
we recovered the connection between the smart backdoor
and the broker, simulating that a victim guest checks in
(e.g., from the front door) and turns on the WiFi network
($A_3$). At last, we found that the smart backdoor received
the “unlocking” command from the earlier QoS 1 message
after it reconnects to Mosquitto ($S_5$ -> $S_6$), indicating the
malicious guest was able to leverage Flaw 2 to unlock a
smart door that he was not entitled to control.

#### PoC exploit on Flaw 3
<img src="Figures/Fig_flaw_QoS2_retry.png" alt="Flaw 1" style="zoom:67%;" />

> $A_1$ -> $S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $S_4$ -> $A_2$ -> $A_3$ -> $S_5$ -> $S_6$ -> $S_7$ -> $S_8$

Due to the “exactly once delivery” feature in QoS 2
messaging, if the target client is offline, the
broker would retry to deliver the message M to the client
when the client reconnects (i.e., $S_5$ -> $S_7$ -> $S_8$). However, we
found the delivery retry mechanism in QoS 2 has the same
problem of that in the QoS 1 messaging as elaborated in
the Flaw 2. The exploiting and mitigation to the Flaw
3 are also similar to that of the Flaw 2.


#### PoC exploit on Flaw 4
<img src="Figures/Fig_flaw_alias.png" alt="Flaw 1" style="zoom:67%;" />

> $S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $A_1$ -> $S_4$ -> $S_5$


We also confirmed Flaw 4 in a sim-
ulated smart home system containing the vulnerable broker
(VolantMQ) and two MQTTX clients (the malicious user
and the victim IoT device). First,
we used the [auth http plugin](https://gitlab.com/VolantMQ/vlplugin/auth/http) (used by VolantMQ for
authentication and authorization) to authorize the malicious
user to control the victim IoT device. Then, we used the
malicious MQTTX client to send a PUBLISH packet with
both topic name and topic alias, resulting in the
VolantMQ broker recording a mapping from the topic
name to topic alias ($S_1$ -> $C_1$ -> $S_2$ -> $S_3$). After that, we
revoked the permission from the malicious user ($A_1$), and
found that the IoT device could still receive the later mes-
sage sent by the unauthorized malicious user only with the
topic alias ($S_4$ -> $S_5$).

#### PoC exploit on Flaw 5
<img src="Figures/Fig_flaw_clientID_hijack.png" alt="Flaw 1" style="zoom:67%;" />

> $S_1$ -> $C_1$ -> $S_2$ -> $S_3$ -> $A_1$ -> $S_4$ -> $C_2$ -> $S_5$

As shown
in the Figure, we used the Mosquitto as the flawed broker
and three MQTTX clients as the victim user, the victim
device and the malicious user. First, we let the victim user
client, the Mosquitto broker and the victim device client to
communicate following the steps of $S_1$ -> $C_1$ -> $S_2$ -> $S_3$. Then,
we used the malicious user client to send a new CONNECT
packet using the victim user’s clientID ($S_4$). Since the
following step $C_2$ checks the permission of the owner of
the Will message (the victim user), not the trigger (the
malicious user), the Mosquitto broker allowed the delivery
of the Will message ($S_4$).

#### PoC exploit on Flaw 6
<img src="Figures/Fig_flaw_no_check_will_msg.png" alt="Flaw 1" style="zoom:67%;" />

> $S_1$ -> $S_2$ -> $S_3$ -> $A_1$ -> $S_4$

We used
hmq as the vulnerable broker and two MQTTX clients to simulate the attacker and the victim device. We let the
victim client subscribes to the topic “smartdoor”. Then, we
used the attacker client to send to the broker a CONNECT
packet containing a Will message that carries a command
payload of “unlocking” and a topic of “smartdoor”. Note
that, we did not authorize the attacker client the access
right to the topic “smartdoor”. After we cut off the network
of the attacker client ($A_1$), the victim client received the
“unlocking” command successfully.

#### PoC exploit on Flaw 7
<img src="Figures/Fig_flaw_two_queues.png" alt="Flaw 1" style="zoom:67%;" />

We confirmed Flaw 7 on Mosquitto
(capacity of InflightQueue n = 20 by default) following
the steps shown in the Figure — a malicious user, who
was authorized to control two IoT devices (associated with
topic A and B, respectively) at first, was able to control
the device B after his permission to control device B was
revoked.

### Existing Flaws
> Y. Jia, L. Xing, Y. Mao, D. Zhao, X. Wang, S. Zhao, and Y. Zhang,"Burglars' IoT Paradise: Understanding and Mitigating Security Risks of General Messaging Protocols on IoT Clouds,” in Proceedings of the 41st IEEE Symposium on Security and Privacy, 2020, pp. 465–481.
> 
Jia et al. identified several flaws in different commercial MQTT brokers through manual analyses, Among all the security flaws identified in [1], four of them are authorization-related flaws (our goal), which were also identified by MQTTactic, i.e., Flaw 8:
Unauthorized subscription via ClientID hijacking; Flaw
9: Unauthorized trigger of the Retained message; Flaw
10: Un-updated subscription; Flaw 11: Unauthorized trigger
of the Will message.

* **Flaw 8**
<img src="Figures/Fig_flaw_clientID_hijack_recover_subscription.png" alt="Flaw 8" style="zoom:67%;" />

* **Flaw 9**
<img src="Figures/Fig_flaw_retained_message.png" alt="Flaw 9" style="zoom:67%;" />

* **Flaw 10**
<img src="Figures/Fig_flaw_read_permission_left.png" alt="Flaw 10" style="zoom:67%;" />

* **Flaw 11**
<img src="Figures/Fig_flaw_will_message.png" alt="Flaw 11" style="zoom:67%;" />
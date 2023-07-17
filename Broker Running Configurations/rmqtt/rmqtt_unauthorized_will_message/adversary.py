import paho.mqtt.client as mqtt
import paho.mqtt.packettypes as PacketTypes
import paho.mqtt.properties as p
import ssl


def connect_callback_v3(client, userdata, flags, reasonCode):
    print("Connected with result code " + str(reasonCode))


def connect_callback(client, userdata, flags, reasonCode, properties):
    print("Connected with result code " + str(reasonCode))
    # pubProperty = p.Properties(PacketTypes.PacketTypes.PUBLISH)
    # pubProperty.ResponseTopic = "test/321"
    # pubProperty.CorrelationData = b'wan'
    # client.publish(topic="test/123", payload="close", qos=1, properties=pubProperty)


def on_message(client, userdata, message):
    print("Received message '" + str(message.payload) + "' on topic '" + message.topic + "' with QoS " + str(message.qos))


def publish_callback(client, userdata, mid):
    print("mid: ", mid)


def pubMain():
    client = mqtt.Client(client_id="test123123", protocol=mqtt.MQTTv5)
    client.username_pw_set(username="admin-user", password="admin-password")
    client.on_connect = connect_callback

    try:
        conProperty = p.Properties(PacketTypes.PacketTypes.CONNECT)
        # conProperty.TopicAliasMaximum = 100
        # conProperty.SessionExpiryInterval = 100000
        pubProperty = p.Properties(PacketTypes.PacketTypes.PUBLISH)
        # pubProperty.TopicAlias = 2
        client.connect(host="test.mosquitto.org", port=1883)
        client.loop_start()
        while (input() != "fxxk"):
            client.publish(topic="test", payload="falkjkj", qos=2, retain=False)
    except Exception as e:
        print(e)
        client.disconnect()


def pubCleanStartMain():
    client = mqtt.Client(client_id="test", protocol=mqtt.MQTTv5)
    client.username_pw_set(username="user1", password="pass1")
    client.on_connect = connect_callback
    client.on_publish = publish_callback

    try:
        conProperty = p.Properties(PacketTypes.PacketTypes.CONNECT)
        # conProperty.TopicAliasMaximum = 100
        conProperty.SessionExpiryInterval = 100000
        pubProperty = p.Properties(PacketTypes.PacketTypes.PUBLISH)
        # pubProperty.TopicAlias = 2
        client.connect(host="192.168.84.132", port=1883, keepalive=60, clean_start=False, properties=conProperty)
        client.publish(topic="message/cmd", payload="open", qos=2, properties=pubProperty)
        client.loop_forever()
    except Exception as e:
        print(e)
        client.disconnect()


def subMain():
    client = mqtt.Client(client_id="admin", protocol=mqtt.MQTTv5)
    client.username_pw_set(username="admin-user", password="admin-password")
    client.reconnect_delay_set(1000, 2000)
    client.on_connect = connect_callback
    client.on_message = on_message
    try:
        conProperty = p.Properties(PacketTypes.PacketTypes.CONNECT)
        # conProperty.TopicAliasMaximum = 100
        conProperty.SessionExpiryInterval = 100000
        #client.connect(host="127.0.0.1", port=1883, keepalive=60, clean_start=False, properties=conProperty)
        client.connect(host="192.168.140.128", port=1883, keepalive=60)
        client.subscribe(topic="test", qos=2)
        client.loop_forever()
    except:
        client.disconnect()


def dosMain():
    client = mqtt.Client(client_id="rmqtt_user1", protocol=mqtt.MQTTv5)
    client.username_pw_set(username="user1", password="pass1")
    client.on_connect = connect_callback
    client.on_message = on_message
    try:
        client.connect(host="192.168.8.102", port=1883)
        client.loop_forever()
    except:
        client.disconnect()


def cleanStartMain():
    client = mqtt.Client(client_id="rmqtt_user1", protocol=mqtt.MQTTv5)
    client.username_pw_set(username="user1", password="pass1")
    client.on_connect = connect_callback
    client.will_set(topic="testtopic", payload="mywill")
    client.on_message = on_message
    try:
        client.connect(host="192.168.8.102", port=1883)
        client.loop_forever()
        x = input('puse')
        if x != '':
            exit()
    except:
        print('except')
        client.disconnect()


if __name__ == "__main__":
    cleanStartMain()

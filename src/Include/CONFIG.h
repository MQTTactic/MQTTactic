using namespace std;
namespace mqttactic
{
static std::string handle__connect = "handle__connect";
static std::string handle__publish = "handle__publish";
static std::string handle__pubrel = "handle__pubrel";
static std::string handle__subscribe = "handle__subscribe";
static std::string handle__unsubscribe = "handle__unsubscribe";
static std::string handle__disconnect = "handle__disconnect";
static std::string handle__authorize = "";
static string handle__revoke = "";
static std::string permission_check = "mosquitto_acl_check";
static std::string Subs = "mosquitto__subhier::subs";
static std::string RetainedMsg = "mosquitto_db::retains";
static std::string WillMsg = "mosquitto::will";
static std::string MsgQue = "mosquitto_msg_data::inflight+mosquitto_msg_data::queued";
static std::string Msg = "mosquitto__packet::payload";
static std::string Session = "mosquitto";
static std::string Permission = "Authentication::aclTree";
static std::string authorization_pub = "MOSQ_ACL_WRITE";
static std::string authorization_sub = "MOSQ_ACL_SUBSCRIBE";
static std::string authorization_read = "MOSQ_ACL_READ";
static std::string authorization_store = "";
static std::string authorization_load = "";

}  // namespace mqttactic

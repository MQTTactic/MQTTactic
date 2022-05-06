import semmle.code.cpp.pointsto.PointsTo
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.ir.implementation.aliased_ssa.Instruction
class SubscriptionConfiguration extends DataFlow::Configuration {
  SubscriptionConfiguration() { this = "SubscriptionConfiguration" }
  override predicate isSource(DataFlow::Node source) {
    exists(VariableAccess subs_access |
      subs_access.getTarget().hasQualifiedName(_, "Authentication", "aclTree") and
      subs_access = source.asExpr()
    )
  }
  override predicate isSink(DataFlow::Node sink) {
    exists(AssignExpr assign |
      assign.getLValue().getAChild*() = sink.asExpr() or assign.getLValue() = sink.asExpr()
    )
    or
    exists(FunctionCall fc |
      (fc.getTarget().getName() = "erase" or fc.getTarget().getName() = "operator=") and
      fieldAccessMatch(fc.getQualifier(), sink.asExpr())
    )
  }
}
predicate fieldAccessMatch(Expr fa, Expr key_var_access) {
  fa = key_var_access
  or
  fa.(VariableAccess).getQualifier() = key_var_access
  or
  fieldAccessMatch(fa.(VariableAccess).getQualifier().(FieldAccess), key_var_access)
  or
  fa.(VariableAccess).getQualifier() instanceof ArrayExpr and
  (
    fa.(VariableAccess).getQualifier().(ArrayExpr).getArrayBase() = key_var_access or
    fieldAccessMatch(fa.(VariableAccess).getQualifier().(ArrayExpr).getArrayBase(), key_var_access)
  )
  or
  fieldAccessMatch(fa.(OverloadedArrayExpr).getQualifier(), key_var_access)
  or
  fieldAccessMatch(fa.(OverloadedPointerDereferenceExpr).getQualifier(), key_var_access)
}
from DataFlow::Node source, DataFlow::Node sink, SubscriptionConfiguration config
where config.hasFlow(source, sink)
select source, sink, sink.getLocation()

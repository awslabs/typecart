module Types {
  import CommonTypes

  type Principal = string

  datatype Effect = ALLOW | DENY

  datatype StatementBlock = StatementBlock(pid: CommonTypes.Option<Principal>, effect: Effect, action: string, resource: string)

  datatype PolicyBlock = PolicyBlock(id: CommonTypes.Option<string>, statement: StatementBlock)

  datatype Policy = Policy(issuer : Principal, policyBlock : PolicyBlock)

  datatype Request = Request(principal : Principal, action: string, resource: string, filler: string)

  datatype Answer = ALLOW | DENY
}


module CommonTypes {
  datatype Option<+U> = None() | Some(val: U)
}

module Spec {
  import Types

  function EvalStatementAndRequest(statement : Types.StatementBlock, request : Types.Request) : Types.Answer {
    if statement.pid.Some? && statement.pid.val == request.principal
       && statement.action == request.action
       && statement.resource == request.resource
       && statement.effect == Types.Effect.ALLOW then Types.Answer.ALLOW
    else Types.Answer.DENY
  }

  function Eval(policies : seq<Types.Policy>, request : Types.Request) : Types.Answer
  {
    if |policies| == 0 then Types.Answer.DENY
    else if |policies| == 1 then
      EvalStatementAndRequest(policies[0].policyBlock.statement, request)
    else
    if EvalStatementAndRequest(policies[0].policyBlock.statement, request).DENY? then Types.Answer.DENY
    else Eval(policies[1..], request)
  }
}

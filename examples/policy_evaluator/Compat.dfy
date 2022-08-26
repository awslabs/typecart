include "typecartOutput/joint.dfy"
include "typecartOutput/old.dfy"
include "typecartOutput/new.dfy"
include "typecartOutput/combine.dfy"

module Compat {

    import Old
    import New
    import Joint
    import Combine

    /* Translate version */
    lemma EvalStatementAndRequest(statement: Old.Types.StatementBlock, request: Old.Types.Request)
      ensures Combine.Types.TranslateAnswer(Old.Spec.EvalStatementAndRequest(statement, request))
           == New.Spec.EvalStatementAndRequest(Combine.Types.TranslateStatementBlock(statement), Combine.Types.TranslateRequest(request));
    {}
    
    lemma Eval(policies: seq<Old.Types.Policy>, request: Old.Types.Request)
      ensures Combine.Types.TranslateAnswer(Old.Spec.Eval(policies, request)) == 
              New.Spec.Eval(Combine.MapBuiltinTypes.Seq(Combine.Types.TranslatePolicy, policies), Combine.Types.TranslateRequest(request))
    {
      if |policies| == 0 {
      } else {
        if |policies| == 1 {
        } else {
          if Old.Spec.EvalStatementAndRequest(policies[0].policyBlock.statement, request).DENY? {
            EvalStatementAndRequest(policies[0].policyBlock.statement, request);
          } else {
            Eval(policies[1..],request);
            assert Combine.MapBuiltinTypes.Seq(Combine.Types.TranslatePolicy, policies[1..])
              == Combine.MapBuiltinTypes.Seq(Combine.Types.TranslatePolicy, policies)[1..]; 
          }
        }
      }
    }

    /* Relate version */
    lemma RelateEvalStatementAndRequest(statement_O: Old.Types.StatementBlock, request_O: Old.Types.Request, statement_N: New.Types.StatementBlock, request_N: New.Types.Request)
      requires Combine.Types.T_StatementBlock(statement_O, statement_N)
      requires Combine.Types.T_Request(request_O, request_N)
      ensures Combine.Types.T_Answer(Old.Spec.EvalStatementAndRequest(statement_O, request_O), New.Spec.EvalStatementAndRequest(statement_N, request_N))
    {}
    
    lemma RelateEval(policies_O: seq<Old.Types.Policy>, request_O: Old.Types.Request, policies_N: seq<New.Types.Policy>, request_N: New.Types.Request)
      requires Combine.RelateBuiltinTypes.Seq((sq_O: Old.Types.Policy, sq_N: New.Types.Policy) => Combine.Types.T_Policy(sq_O, sq_N), policies_O, policies_N)
      requires Combine.Types.T_Request(request_O, request_N)
      ensures Combine.Types.T_Answer(Old.Spec.Eval(policies_O, request_O), New.Spec.Eval(policies_N, request_N))
    {
      if |policies_O| == 0 {
      } else {
        if |policies_O| == 1 {
        } else {
          if Old.Spec.EvalStatementAndRequest(policies_O[0].policyBlock.statement, request_O).DENY? {
            RelateEvalStatementAndRequest(policies_O[0].policyBlock.statement, request_O, policies_N[0].policyBlock.statement, request_N);
          } else {
            RelateEval(policies_O[1..],request_O,policies_N[1..],request_N);
          }
        }
      }
    }


}


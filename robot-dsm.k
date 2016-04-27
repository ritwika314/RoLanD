requires "robot-syntax.k"

module ROBOT-DSM
  imports ROBOT-SYNTAX
  
  syntax Stage ::= "Preprocessing"
                 | "Simulation"

  syntax State ::= "Discrete"
                 | "Progress"

 
  configuration
    <T>
      <robots>
        <robot multiplicity = "*">
          <k> $PGM:K  </k>
          <env> .Map </env>
          <id> 0 </id>
          <period> 0 </period>
        </robot>
      </robots>
      
      <mw> .Map </mw>
      <timeout> .Map </timeout>
      <time> 0 </time>
      <code> .K </code>
      <nbots> 1 </nbots>
      <state> Discrete </state>
      <stage> Preprocessing </stage>
    </T>


  syntax Val  ::= Int | Bool | String
  syntax Vals ::= List{Val, ","}
  syntax Exp  ::= Val
  syntax KResult ::= Val

  syntax KItem ::= "endMW"
  syntax KItem ::= undefined(Type)

  /*Sequential composition*/
  rule S1:Stmt S2:Stmts => S1 ~> S2                    [structural]
  rule V1:VarDecl V2:VarDecls => V1 ~> V2              [structural]

  /*Variable Declaration*/
  rule <robot>...
         <k> T:Type X:Id; => . ...</k>
         <env>... .Map => X |-> undefined(T) ...</env>
       ...</robot>

  rule <robot>...
         <k> T:Type X:Id = V:Val; => . ...</k>
         <env>... .Map => X |-> V ...</env>
       ...</robot>

  /*Preprocessing stage*/
  rule SD:SharedDecls V:VarDecls SF:StepFunc N:Nbots
       => SD ~> V ~> SF ~> N

  rule <robot>...
         <k> MW {Vs:VarDecls} => Vs ~> endMW...</k>
       ...</robot>
       <stage> Preprocessing </stage>

  rule <robot>...
         <k> endMW =>. ...</k>
         <env> ENV => .Map </env>
       ...</robot>
       <mw> .Map => ENV </mw>
       <stage> Preprocessing </stage>

  rule <robot>...
         <k> SF:StepFunc => . ...</k>
       ...</robot>
       <code> . => SF </code>
       <stage> Preprocessing </stage>

  syntax PWrapper ::= pw(Periods)
  syntax DWrapper ::= dw(Delays)
  syntax Val ::= simEnv(Int, PWrapper, DWrapper)
  rule <robot>...
         <k> Sim N:Int {Ps} {Ds}; => simEnv(N, pw(Ps), dw(Ds)) ... </k>
       ...</robot>
       <stage> Preprocessing </stage>
                
  rule <robot>...
         <k> simEnv(N, pw(P:Int, Ps:Periods), dw(D:Int, Ds:Delays)) => simEnv(N -Int 1, pw(Ps), dw(Ds)) ...</k>
         <env> E </env>
       ...</robot>
       (.Bag => <robot> ...
                  <period> P </period>
                  <env> E </env>
                  <id> I </id>
                ...</robot>)
       <timeout> ... .Map => I |-> D ...</timeout>
       <nbots> I:Int => I +Int 1 </nbots>
       <stage> Preprocessing </stage>                 requires N =/=K 1

  rule <robot>...
        <k> simEnv(1, pw(P:Int), dw(D:Int)) => C ...</k>
        <period> _ => P </period>
        <id> I </id>
       ...</robot>
       <code> C </code>
       <timeout> ... .Map => I |-> D ...</timeout>
       <stage> Preprocessing => Simulation </stage>

  /*Simulation stage*/

  syntax Int ::= findMin(List, Int)                                            [function]
  rule findMin(L:Int, Ls:List, R:Int) => findMin(Ls, minInt(L,R))
  rule findMin(.List, R:Int) => R 
  
  rule  <timeout> TO:Map </timeout>
        <state> Discrete => Progress </state>
        <time> T => findMin(values(TO),10000) </time>                           requires T =/=K findMin(values(TO), 10000) 


endmodule

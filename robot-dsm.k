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
          <localtime> 0 </localtime>
        </robot>
      </robots>
      
      <mw> .Map </mw>
      <timeout> .Map </timeout>
      <time> 0 </time>
      <code> .K </code>
      <nbots> 1 </nbots>
      <livebots> 0 </livebots>
      <state> Progress </state>
      <stage> Preprocessing </stage>
    </T>


  syntax Val  ::= Int | Bool | String
  syntax Vals ::= List{Val, ","}
  syntax Exp  ::= Val
  syntax KResult ::= Val

  syntax KItem ::= "endMW"
                 | "sleep"
  syntax KItem ::= undefined(Type)

  /*Sequential composition*/
  rule .Stmts => .                                     [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss                      [structural]
  rule .VarDecls => .                                  [structural]
  rule V:VarDecl Vs:VarDecls => V ~> Vs                [structural]

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
  rule SDs:SharedDecls VDs:VarDecls SF:StepFunc N:Nbots
       => SDs ~> VDs ~> SF ~> N

  rule <robot>...
         <k> MW {VDs:VarDecls} => VDs ~> endMW...</k>
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
                  <k> .K </k>
                  <period> P </period>
                  <env> E </env>
                  <id> I </id>
                ...</robot>)
       <timeout> ... .Map => I |-> D ...</timeout>
       <nbots> I:Int => I +Int 1 </nbots>
       <stage> Preprocessing </stage>                 requires N =/=K 1

  rule <robot>...
        <k> simEnv(1, pw(P:Int), dw(D:Int)) =>. ...</k>
        <period> _ => P </period>
        <id> I </id>
       ...</robot>
       <code> C </code>
       <timeout> ... .Map => I |-> D ...</timeout>
       <stage> Preprocessing => Simulation </stage> 

  /*Simulation stage*/

  syntax Int ::= findMin(List)                        [function]                            
               | "Nat"
  rule findMin(.List) => Nat
  rule findMin(ListItem(I)) => I
  rule findMin(ListItem(I) Ls:List) => minInt(I, findMin(Ls))


  /*Time progress transition*/  
  rule <timeout> TO:Map </timeout>
       <state> Progress => Discrete </state>
       <time> T => findMin(values(TO)) </time>                           
       <stage> Simulation </stage>                                       requires T =/=K findMin(values(TO))

  /*Discrete time transition*/ 
  rule <robot>...
         <k> .K => Code ~> sleep </k>
         <localtime> LocalTime => CurTime </localtime>
         <id> ID </id>
       ...</robot>
       <timeout>... ID |-> CurTime ...</timeout>
       <code> Code </code>
       <time> CurTime </time>
       <livebots> LBots:Int => LBots +Int 1 </livebots>
       <state> Discrete </state>
       <stage> Simulation </stage>                                      requires LocalTime <Int CurTime

  syntax KItem ::= closure(Exp, Stmts, Events) 
  rule <robot>...
         <k> Step(){X:Id() {pre (E:Exp); eff {Ss:Stmts}} Evs:Events} => closure(E, Ss, Evs) ... </k>
       ...</robot>

  context closure(HOLE:Exp, Ss, Evs)




endmodule

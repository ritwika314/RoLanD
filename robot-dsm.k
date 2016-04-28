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
      
      <mwEnv> .Map </mwEnv>
      <store> .Map </store>
      <nextLoc> 0 </nextLoc>
      <timeout> .Map </timeout>
      <time> 0 </time>
      <varCode> .K </varCode>
      <stepCode> .K </stepCode>
      <nbots> 1 </nbots>
      <livebots> 0 </livebots>
      <initialized> 0 </initialized>
      <state> Progress </state>
      <stage> Preprocessing </stage>
    </T>


  syntax Val  ::= Int | Bool | String
  syntax Vals ::= List{Val, ","}
  syntax Exp  ::= Val
  syntax KResult ::= Val

  syntax KItem ::= "endMW"
                 | "sleep"
                 | "initialized"
  syntax KItem ::= undefined(Type)

  // Sequential composition
  rule .Stmts => .                                     [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss                      [structural]
  rule .VarDecls => .                                  [structural]
  rule V:VarDecl Vs:VarDecls => V ~> Vs                [structural]

  // Variable Declaration
  rule <robot>...
         <k> T:Type X:Id; => . ...</k>
         <env> Env => Env[X <- L] </env>
       ...</robot>
       <store> ... .Map => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <robot>...
         <k> T:Type X:Id = V:Val; => . ...</k>
         <env> Env => Env[X <- L]</env>
       ...</robot>
       <store> ... .Map => L |-> V ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


  // Preprocessing stage
  rule <k> SDs:SharedDecls VDs:VarDecls SF:StepFunc N:Nbots
           => SDs ~> N ...</k>
       <varCode> .K => VDs </varCode>
       <stepCode> .K => SF </stepCode>
       <stage> Preprocessing </stage>

  rule <robot>...
         <k> MW {VDs:VarDecls} => VDs ~> endMW...</k>
       ...</robot>
       <stage> Preprocessing </stage>

  rule <robot>...
         <k> endMW =>. ...</k>
         <env> ENV </env>
       ...</robot>
       <mwEnv> .Map => ENV </mwEnv>
       <stage> Preprocessing </stage>

  syntax PWrapper ::= pw(Periods)
  syntax DWrapper ::= dw(Delays)
  syntax Val ::= simEnv(Int, PWrapper, DWrapper)
  rule <robot>...
         <k> Sim N:Int {Ps} {Ds}; => simEnv(N, pw(Ps), dw(Ds)) ...</k>
       ...</robot>
       <stage> Preprocessing </stage>
                
  rule <robot>...
         <k> simEnv(N, pw(P:Int, Ps:Periods), dw(D:Int, Ds:Delays)) => simEnv(N -Int 1, pw(Ps), dw(Ds)) ...</k>
         <env> E </env>
       ...</robot>
       (.Bag => <robot> ...
                  <k> VC ~> initialized </k>
                  <period> P </period>
                  <env> E </env>
                  <id> I </id>
                ...</robot>)
       <timeout> ... .Map => I |-> D ...</timeout>
       <nbots> I:Int => I +Int 1 </nbots>
       <varCode> VC </varCode>
       <stage> Preprocessing </stage>                 requires N =/=K 1

  rule <robot>...
        <k> simEnv(1, pw(P:Int), dw(D:Int)) => VC ~> initialized...</k>
        <period> _ => P </period>
        <id> I </id>
       ...</robot>
       <varCode> VC </varCode>
       <timeout> ... .Map => I |-> D ...</timeout>
       <stage> Preprocessing </stage>

  rule <k> initialized => . ...</k>
       <initialized> N => N +Int 1 </initialized> 

  rule <nbots> N </nbots>
       <initialized> N </initialized>
       <stage> Preprocessing => Simulation </stage>

  // Simulation stage
  syntax Int ::= findMin(List)                        [function]                            
               | "Nat"
  rule findMin(.List) => Nat
  rule findMin(ListItem(I)) => I
  rule findMin(ListItem(I) Ls:List) => minInt(I, findMin(Ls))

  // Time progress transition  
  rule <timeout> TO:Map </timeout>
       <state> Progress => Discrete </state>
       <time> T => findMin(values(TO)) </time>                           
       <stage> Simulation </stage>                                       requires T <Int findMin(values(TO)) andBool T <=Int 60

  // Discrete time transition
  rule <robot>...
         <k> .K => Code </k>
         <localtime> LocalTime => CurTime </localtime>
         <id> ID </id>
       ...</robot>
       <timeout>... ID |-> CurTime ...</timeout>
       <stepCode> Code </stepCode>
       <time> CurTime </time>
       <livebots> LBots:Int => LBots +Int 1 </livebots>
       <state> Discrete </state>
       <stage> Simulation </stage>                                       requires LocalTime <Int CurTime

  // Variable lookup
  rule <robot>...
         <k> X:Id => V ...</k>
         <env>... X |-> L ...</env>
       ...</robot>
       <store>... L |-> V:Val ...</store>

  // Assignment
  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)
  context (HOLE => lvalue(HOLE)) = _
 
  rule <k> lvalue(X:Id => loc(L)) ...</k>
       <env>... X |-> L:Int ...</env>

  rule <k> loc(L) = V:Val => V ...</k>
       <store> ... L |-> (_ => V) ...</store>

  // Expression Statements
  rule _:Val ; => .
  

  // Arithmetic Operator
  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2

  // Equality
  rule V1:Val == V2:Val => V1 ==K V2

  // Logical Operator
  rule not T => notBool(T)
  rule true and E => E
  rule false and _ => false

  // Evaluating Events one by one
  rule Step(){Evs:Events} => Evs ~> sleep
  
  rule .Events => .

  syntax KItem ::= closure(Exp, Stmts, Events) 
  rule X:Id() {pre (E:Exp); eff {Ss:Stmts}} Evs:Events => closure(E, Ss, Evs)

  context closure(HOLE:Exp, Ss, Evs)

  rule closure(true, Ss, Evs) => Ss
  rule closure(false, Ss, Evs) => Evs

  rule <robot>...
         <k> sleep =>. ...</k>
         <period> P </period>
         <id> ID </id>
       ...</robot>
       <livebots> N => N -Int 1 </livebots>
       <timeout>... ID |-> (T => T +Int P) ...</timeout>

  // After robots finishes, set Discrete to Progress
  rule <livebots> 0 </livebots>
       <timeout> TO </timeout>
       <time> CT </time>
       <state> Discrete => Progress </state>                 requires  CT <Int findMin(values(TO))


endmodule

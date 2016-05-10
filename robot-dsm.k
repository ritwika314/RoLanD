requires "robot-syntax.k"

module ROBOT-DSM
  imports ROBOT-SYNTAX
  
  syntax Stage ::= "Preprocessing"
                 | "Simulation"

  syntax State ::= "Discrete"
                 | "Progress"

  syntax LockReqState ::= "Request"
                        | "Acquire"
                        | "Release"
  configuration
    <T>
      <robots>
        <robot multiplicity = "*">
          <k> $PGM:K  </k>
          <env> .Map </env>
          <id> 0 </id>
          <period> 0 </period>
          <localTime> 0 </localTime>
          <lockReqState> .K </lockReqState>
        </robot>
      </robots>
      
      // memory related cells
      <mwEnv> .Map </mwEnv>
      <store> .Map </store>
      <nextLoc> 0 </nextLoc>
      // calendar automata
      <timeout>
        <event multiplicity = "*">
          <eventType> .K </eventType>
          <eventId> 0 </eventId>
          <eventTimeout> 0 </eventTimeout>
        </event>
      </timeout>
      <time> 0 </time>
      <maxTime> 0 </maxTime>
      <state> Progress </state>
      // global lock req queue
      <lockReqs> .List </lockReqs>
      // robot
      <nbots> 1 </nbots>
      <livebots> 0 </livebots>
      <initialized> 0 </initialized>
      // random delay
      <delay> 0 </delay>
      // code shared among robots
      <varCode> .K </varCode>
      <stepCode> .K </stepCode>
      // execution stage
      <stage> Preprocessing </stage>
    </T>


  syntax Val  ::= Int | Bool | String
  syntax Vals ::= List{Val, ","}
  syntax Exp  ::= Val
  syntax KResult ::= Val
  syntax EventType ::= "NodeAct" | "LockAct"
  //Event - EventType, EventId, Timeout
  syntax Event ::= "event" "(" EventType "," Int "," Int ")"

  // Sequential composition
  rule .Stmts => .                                     [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss                      [structural]
  rule .VarDecls => .                                  [structural]
  rule V:VarDecl Vs:VarDecls => V ~> Vs                [structural]

  // Variable Declaration
  syntax KItem ::= undefined(Type)
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

  syntax KItem ::= "endMW"
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

  syntax KItem ::= "initialized"

  rule <robot>...
         <k> Sim N {P:Int, Ps:Periods} {D:Int, Ds:Delays} MT:Int; => Sim N -Int 1 {Ps} {Ds} MT; ...</k>
         <env> E </env>
       ...</robot>
       (.Bag => <robot>...
                  <k> VC ~> initialized </k>
                  <env> E </env>
                  <id> ID </id>
                  <period> P </period>
                  <lockReqState> Release </lockReqState>
                ...</robot>)
       <timeout> ...
         (.Bag => <event>...
                    <eventType> NodeAct </eventType>
                    <eventId> ID </eventId>
                    <eventTimeout> D </eventTimeout>
                  ...</event>)
       ...</timeout>
       <nbots> ID:Int => ID +Int 1 </nbots>
       <varCode> VC </varCode>
       <stage> Preprocessing </stage>                 requires N =/=K 1

  rule <robot>...
        <k> Sim 1 {P:Int} {D:Int} MT; => VC ~> initialized...</k>
        <period> _ => P </period>
        <id> ID </id>
        <lockReqState> _ => Release </lockReqState>
       ...</robot>
       <varCode> VC </varCode>
       <timeout>... 
         (.Bag => <event>...
                    <eventType> NodeAct </eventType>
                    <eventId> ID </eventId>
                    <eventTimeout> D </eventTimeout>
                  ...</event>)
       ...</timeout>
       <maxTime> 0 => MT </maxTime>
       <stage> Preprocessing </stage>

  rule <k> initialized => . ...</k>
       <initialized> N => N +Int 1 </initialized> 

  rule <nbots> N </nbots>
       <initialized> N </initialized>
       <delay> 0 => randomRandom(10) +Int 1 </delay>
       <stage> Preprocessing => Simulation </stage>

  // Simulation stage
  syntax Int ::= findMin(Bag)                                                      [function]
               | findMin(Bag, Int)                                                 [function]
               | "Nat"
  rule findMin(.Bag) => Nat
  rule findMin(<event>...<eventTimeout> To </eventTimeout> ...</event> Ts:Bag) => findMin(Ts, To)
  rule findMin(.Bag, Tmin) => Tmin
  rule findMin(<event>...<eventTimeout> To </eventTimeout> ...</event> Ts:Bag, Tmin) 
       => findMin(Ts, Tmin)                                                        requires Tmin <=Int To
  rule findMin(<event>...<eventTimeout> To </eventTimeout> ...</event> Ts:Bag, Tmin)
       => findMin(Ts, To)                                                          requires Tmin >Int To

  // Time progress transition  
  rule <timeout> TO:Bag </timeout>
       <state> Progress => Discrete </state>
       <time> T => findMin(TO) </time>
       <maxTime> MT </maxTime>                           
       <stage> Simulation </stage>                                                 requires T <Int findMin(TO) andBool T <=Int MT

  // Discrete time transition
  syntax KItem ::= "acquireLock"
  rule <robot>...
         <k> .K => acquireLock ~> Code </k>
         <localTime> LocalTime => GlobalTime </localTime>
         <id> ID </id>
       ...</robot>
       <timeout>...
         (<event>...
           <eventType> NodeAct </eventType>
           <eventId> ID </eventId>
           <eventTimeout> GlobalTime </eventTimeout>
          ...</event>) => .Bag
       ...</timeout>
       <stepCode> Code </stepCode>
       <time> GlobalTime </time>
       <livebots> LBots:Int => LBots +Int 1 </livebots>
       <state> Discrete </state>
       <stage> Simulation </stage>                                  requires LocalTime <Int GlobalTime

  rule <timeout>...
         (<event>...
           <eventType> LockAct </eventType>
           <eventId> ID </eventId>
           <eventTimeout> GlobalTime </eventTimeout>
          ...</event> => .Bag)
       </timeout>
       <time> GlobalTime </time>
       <lockReqs> ... .List => ListItem(ID) </lockReqs>

  rule <robot>...
         <k> acquireLock => . ...</k>
         <id> ID </id>
         <lockReqState> Request => Acquire </lockReqState>
       ...</robot>
       <lockReqs> ListItem(ID) ... </lockReqs>
  
  rule <robot>...
         <k> acquireLock => . ...</k>
         <id> ID </id>
       ...</robot>
       <lockReqs> ListItem(ID2) ...</lockReqs>                     requires ID =/=Int ID2

  rule <robot>...
         <k> acquireLock => . ...</k>
       ...</robot>
       <lockReqs> .List </lockReqs>
          

  // Variable lookup
  rule <robot>...
         <k> X:Id => V ...</k>
         <env>... X |-> L ...</env>
       ...</robot>
       <store>... L |-> V:Val ...</store>

  rule <robot>...
         <k> robotIndex:Id => ID ...</k>
         <id> ID </id>
       ...</robot>

  rule <robot>...
         <k> NumBots:Id => N </k>
       ...</robot>
       <nbots> N </nbots>

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
  syntax KItem ::= "sleep"
                 | "releaseLock"
  rule Step(){Evs:Events} => Evs ~> releaseLock ~> sleep
  
  rule .Events => .

  syntax KItem ::= closure(Exp, Stmts, Events) 
  rule X:Id() {pre (E:Exp); eff {Ss:Stmts}} Evs:Events => closure(E, Ss, Evs)

  context closure(HOLE:Exp, Ss, Evs)

  rule closure(true, Ss, Evs) => Ss
  rule closure(false, Ss, Evs) => Evs

  rule <robot>...
         <k> releaseLock =>. ...</k>
         <id> ID </id>
         <lockReqState> Acquire => Release </lockReqState>
       ...</robot>
       <lockReqs> ListItem(ID) => .List ... </lockReqs>

  rule <robot>...
         <k> releaseLock =>. ...</k>
         <id> ID </id>
         <lockReqState> LRS </lockReqState>
       ...</robot>                                               requires LRS =/=K Acquire

  rule <robot>...
         <k> sleep =>. ...</k>
         <period> P </period>
         <id> ID </id>
         <localTime> LT </localTime>
       ...</robot>
       <livebots> N => N -Int 1 </livebots>
       <timeout>... 
         (.Bag => <event>...
                    <eventType> NodeAct </eventType>
                    <eventId> ID </eventId>
                    <eventTimeout> LT +Int P </eventTimeout> 
                  ...</event>)
       ...</timeout>

  // After robots finish, set Discrete to Progress
  rule <livebots> 0 </livebots>
       <timeout> TO </timeout>
       <time> GT </time>
       <state> Discrete => Progress </state>                    requires  GT <Int findMin(TO)

  // Lock semantics
  rule <robot>...
         <k> atomic{Ss:Stmts} => . ...</k>
         <id> ID </id>
         <localTime> LT </localTime>
         <lockReqState> Release => Request </lockReqState>
       ...</robot>
       <timeout>...
         (.Bag => <event>...
                    <eventType> LockAct </eventType>
                    <eventId> ID </eventId>
                    <eventTimeout> LT +Int D </eventTimeout>
                  ...</event>)
       ...</timeout>
       <delay> D => randomRandom(10) +Int 1 </delay>

  rule <robot>...
         <k> atomic{Ss:Stmts} => . ...</k>
         <id> ID </id>
         <lockReqState> Request </lockReqState>
       ...</robot>

  rule <robot>...
         <k> atomic{Ss:Stmts} => Ss ...</k>
         <id> ID </id>
         <lockReqState> Acquire </lockReqState>
       ...</robot>

endmodule

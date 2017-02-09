require "../patterns/race/race-verifier.k"


module RACE-SPEC 
imports RACE-VERIFIER 

rule 
<reached> ... 
 P:List (.List => ?_:List) 
... </reached>

<agent><id> I1:Int </id>
<target>
<k>  
<obstacle> 
O:List 
</obstacle>
<k>
UpdateTarget(_, _ ,T1 , 0) => . ...
</k>
</agent>
 
requires notBool (T1 in P)

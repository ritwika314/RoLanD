module ROBOT-SYNTAX

  syntax Sim     ::= SharedDecls BotCode Nbots

  //For initializing the number of robots and corresponding periods
  syntax Nbots   ::= "Sim" Int "{" Periods "}" "{" Delays "}" ";"
  //The unit for period/delay is ms
  syntax Periods ::= List{Int,","}
  syntax Delays  ::= List{Int,","}

  syntax SharedDecls ::= MwDecl
 
  syntax BotCode  ::= VarDecls StepFunc         [klabel('BotCodeWithVarDecl)]
                    | StepFunc
  syntax StepFunc ::= "Step()" "{" Events "}"

  syntax MwDecl   ::= "MW" "{" "}"
                    | "MW" "{" VarDecls "}"

  syntax VarDecl  ::= Type Id ";"
                    | Type Id "=" Exp ";"       [strict(3)]
  
  syntax VarDecls ::= VarDecl
                    | VarDecl VarDecls          [klabel('VarDeclConcat)] 

  syntax Type    ::= "int" | "float" | "boolean"

  syntax Event   ::= Id "()" "{" "pre" "(" Exp ")" ";" "eff" Block "}"
  syntax Events  ::= List{Event,""}             [klabel('EventList)]

  syntax Exp     ::= Bool | Int | Float | Id
                   | "(" Exp ")"   [bracket]
                   | Exp "*" Exp   [strict, left]
                   > Exp "+" Exp   [strict, left]
                   | Exp "-" Exp   [strict, left]
                   > Exp "<"  Exp  [seqstrict, non-assoc]
                   | Exp "<=" Exp  [seqstrict, non-assoc]
                   | Exp ">"  Exp  [seqstrict, non-assoc]
                   | Exp ">=" Exp  [seqstrict, non-assoc]
                   | Exp "==" Exp  [seqstrict, non-assoc]
                   > "not" Exp     [strict]
                   > Exp "and" Exp [strict(1), left]
                   > Exp "=" Exp   [strict(2), right]

  syntax Block ::= "{" "}"
                 | "{" Stmts "}"

  syntax Stmt  ::= Block
                 | Exp ";"                             [strict] 
                 | "atomic" Block // shared memory communication
                 | "if" "(" Exp ")" Block "else" Block [strict(1)]

  syntax Stmts ::= Stmt
                 | Stmt Stmts                          [klabel('StmtConcat)]

endmodule

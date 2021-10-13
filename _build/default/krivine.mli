exception Error
type inst =
  | LDV of value
  | ACCESS of int
  | GRAB
  | PUSH of inst list
  | LET
  | ENDLET
  | ADD
  | SUB
and value =
  | VInt of int
  | VClos of inst list * value list
  | VEnv of value list
  | VInst of inst list
  | VUnknown of value list * value list * inst list

type environment = value list
val interpreter : inst list -> value

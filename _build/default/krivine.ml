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

let interpreter code =
  let stk = [] in
  let (env: environment) = [] in
  let rec loop s e c = match s, e, c with
    | s, e, LDV n::cs -> loop (n::s) e cs

    | VInt a::VInt b::ss, e, ADD::cs -> loop (VInt(a + b)::ss) e cs
    | VInt a::VInt b::ss, e, SUB::cs -> loop (VInt(a - b)::ss) e cs

    | (v::s), e, LET::cs -> loop s (v::e) cs
    | s, (_::e), ENDLET::cs -> loop s e cs

    | s, e, ACCESS(n)::_ -> begin match List.nth e n with
                            | VClos(c', e') -> loop s e' c'
                            | _ -> raise Error
                            end

    | VClos(c', e')::ss, e, GRAB::cs -> loop ss (VClos(c', e')::e) cs

    | s, e, PUSH c'::cs -> loop (VClos(c', e)::s) e cs

    | s, e, c -> VUnknown (s, e, c)
  in loop stk env code

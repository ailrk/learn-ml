exception Error

(* Note the debrujin index starts from 0 *)
type inst =
  | LDV of value
  | ACCESS of int
  | CLOSURE of inst list
  | LET
  | ENDLET

  (* function calls *)
  | APPLY
  | TAILAPPLY (* case for handling extra return frame *)
  | RETURN

  (* basic arithmetics*)
  | ADD
  | SUB
and value =
  | VInt of int
  | VClos of inst list * value list
  | VEnv of value list
  | VInst of inst list

  (* debugging case *)
  | VUnknown of value list * value list * inst list

type environment = value list

let interpreter code =
  let stk = [] in
  let (env: environment) = [] in
  let rec loop s e c = match s, e, c with
    | s, e, LDV n::cs -> loop (n::s) e cs
    | VInt(a)::VInt(b)::s, e, ADD::cs ->
        loop (VInt(a + b)::s) e cs

    | VInt(a)::VInt(b)::s, e, SUB::cs ->
        loop (VInt(a - b)::s) e cs

    | s, e, ACCESS(n)::cs -> loop (List.nth e n::s) e cs
    | (v::s), e, LET::cs -> loop s (v::e) cs
    | s, (_::e), ENDLET::cs -> loop s e cs
    | s, e, CLOSURE c'::cs -> loop (VClos(c', e)::s) e cs

    | (v::VClos(c', e')::ss), _, (TAILAPPLY::_) -> loop ss (v::e') c'
    | (v::VClos(c', e')::ss), e, (APPLY::cs) ->
        loop (VInst(cs)::(VEnv e)::ss) (v::e') c'

    | (v::(VInst(c))::(VEnv e')::ss), _, RETURN::_ ->
        loop (v::ss) e' c

    | (v::_), _, [] -> v
    | s, e, c -> VUnknown (s, e, c)
  in loop stk env code

(* ****************************************************************************
  Krivine machine only suuports call by name semantics, but a realistic call
  by name language needs to have at least two more features to be efficient:
    1. Strict operations on primitives.
    2. Sharing with lazy evalution.

  Translation:
    C(n) = ACCESS(n)    -- get the nth thunk from the environment.
      ^
    C(\a) = GRAB;C(a)   -- pop one argument and add it to the environment.
    C(a b) = PUSH(C(b));C(a)    -- push a thunk for code c.

  Push Enter:
      to evaluate (\.\.b) a1 a2:
        push a1; push a2; enter (\.\.b);
          grab a1; grab a2; eval b;
  Comparing with eval-apply model,  push enter builds less intermediate
  closures and perform less return from callee to caller.
 *)


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

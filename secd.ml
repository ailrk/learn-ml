(* ****************************************************************************
   SPJ wrote an article about comparision between push enter and eval apply.
   https://www.cs.tufts.edu/comp/150FP/archive/simon-peyton-jones/eval-apply-jfp.pdf
   Krivine's machine implements call by name semantics for lambda calculus.
   It also has three stacks: S, E, C
   for SECD, S, E holds value. But for krivine machine, S, E always hold thunk
   e.g a c[e]
   thunks won't evauluate until they are used.

   SECD machine follows apply eval model, and krivine machine uses push enter
   model.

   Call by name application forms a tree of spines: a node represents the
   application that uses an closure and an argument.
          @
        /   \
       @     a2[e2]     The stack encodes the spine of applications
     /   \              env and code encodes terms at bottom left of each
   n[e]  a1[e1]         spine.
   ^
  ---    -----------
  code      stack

  ACCESS(n)
          @
        /   \
       @     a2[e2]
     /   \
(\a)[e']  a1[e1]

 GRAB
           @
      /         \
 a[a1[e1].e']   a2[e2]
*)

(* ****************************************************************************
  SECD machine is a abstract machine for call-by-value semantics. It was first
  invented by Peter J Ladin in 1964 in his paper mechanical evaluation of
  expressions.

  Original SECD machine had four stacks: Stack, environment, code, dump. Modern
  SECD machine simplify the design and reduce the amount of stacks required
  to three. Namely we only need S: stack, E: environment, C: code. D: Dump was
  used for implementing function calls, but we can just use stack to do that
  alreay.
 *)

(* ****************************************************************************
   A naive SECD machine that just implements the base line semantics.
   environments for closure replace bound variables.
   We use deburjin index for representing variables. This way we don't need
   to worry about name capturing.
*)


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

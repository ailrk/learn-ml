(*****************************************************************************
   Reduction
   - operatonal semantics: relates programs to the result of their evaluation
     1. simple.
     2. too concrete, hard to prove some properties.
   - denotational semantics: map program to math structure (called domain)
     1. more abstract. Can prove hard properties very concisely.
     2. harder to establish.
    ML Call by value, definition of evaluated forms:
      v ::= λx.a
          | Cⁿ v₁...vₙ                -- constructed value
          | Cⁿ v₁...vₖ where k < n    -- partially applied constant
     - small step decution semantics
       - defined by a set of redexes.
     - σ reduction describes how to reduce primitives.
     - refexes: partial function from programs to programs.
                (reducable expression)
 *)

(* Follows the reduction semantics closely.
     rules for call by value evaluation order.
          e₁ → e₁'                        e₂ → e₂'
      ---------------- (app-left)     --------------- (app-right)
       e₁ e₂ → e₁' e₂                   v e₂ →  v e₂'
 *)

(*****************************************************************************
  reduction rules for call by value semantics, v is evaluated before app.
  ---------- (βᵥ) --------------- (Letᵥ) --------------- (fⁿ v₁‥vₙ→a,a)∈δf
  (λx.e)v→e[x←v]   let x=v in e→e[x←v]         fⁿ v₁ ‥ vₙ → e
  Practical langauges need both beta and segma reductions.
 *)


open Syntax
exception Reduce

let rec evaluated = function
  | Fun _ -> true
  | c -> partial_apply 0 c
and partial_apply n = function
  | Const c -> (c.constr || c.arity > n)
  | App (f, v) -> evaluated v && partial_apply (n + 1) f
  | _ -> false

let union f g a = try g a with Reduce -> f a

let delta =
  let plus = Const { name = Name "+"; arity = 2; constr = false }, ( + ) in
  let times = Const { name = Name "*"; arity = 2; constr = false }, ( * ) in
  let int n = Const { name = Int n; arity = 0; constr = true } in
  let binop (op, opfunc) = function
    | App (App (Const { name = Name _; arity = 2; _ } as c,
                Const { name = Int u; _}),
           Const { name = Int v; _}) when c == op -> int (opfunc u v)
    | _ -> raise Reduce in
  let rules = List.map binop [plus; times] in
  List.fold_right union rules (fun _ -> raise Reduce)

let rec subst x v e = (* subst e with v *)
  assert (evaluated e);
  match e with
  | Var y -> if y = x then v else e
  | Const _ as c -> c
  | Fun (y, e1) -> if x = y then e else Fun (y, subst y v e1)
  | App (e1, e2) -> App (subst x v e1,  subst x v e2)
  | Let (y, e1, e2) -> if x = y then Let (y, subst y v e1, e2)
                                else Let (y, subst y v e1, subst y v e2)

let beta = function
  | App (Fun (x, e), v) when evaluated v -> subst x v e
  | Let (x, v, e) when evaluated v -> subst x v e
  | _ -> raise Reduce

let reduce = List.fold_right union [delta; beta] (fun _ -> raise Reduce)



(****************************************************************************
   Big step semantics
   small step semantics (reduction semantics) is concise and modular. But it
   has some drawbacks:
     1. values are subset of programs
     2. poor performance.
  Introducing big step sematnics: program evaluated in an environment. We
  can jump to conclusion instead of following reduction steps precisely. This
  makes big step semantics less interesting in a theoritical point of view.
    ρ := ∅ | ρ, x → v
    v := ⟨ λx. a, ρ⟩ | Cⁿ v₁‥vₙ | cⁿ v₁‥vₖ where k < n
    r : v | error
  Big step semantics are defined by a set of inference rules that the language
  has. Some inferences can lead to errors.
  Actually we can categorize rules in to 3 groups:
    1. eval rules
    2. error rules
    3. error propagatoin

  ρ ⊢ a ⇓ v                 ρ ⊢ a ⇓ error                    ρ⊢a⇓V  f¹ v→v'
-------------eval-const  -------------- eval-const-error  ------------eval-prim
 ρ ⊢ C¹ a ⇓ C¹ v           ⊢ c a ⇓ error                    ρ⊢f¹ a ⇓ v'
 ρ⊢a⇓V    f¹ v→~v'             z∈Dom(ρ)
---------------eval-error   -------------eval-var  ------------------ eval-fun
    ρ⊢f¹ a ⇓ error            ρ ⊢ z⇓ρ(z)              e ⊢ λx.a ⇓ ⟨λx. a, ρ⟩
    ρ ⊢ a ⇓ ⟨λx.a₀, ρ₀⟩     ρ⊢a'⇓v    ρ₀, x→v⊢a₀:v'
   ------------------------------------------------ eval-app
                ρ⊢ a a' ⇓ v'
    ρ⊢a ⇓ C₁ v₁                         ρ⊢a⇓ error
   -------------- eval-app-error     ---------------- eval-app error left
   ρ⊢a a' ⇓ error                       ρ⊢a a' ⇓ error
          ρ⊢a⇓⟨λx.a₀, ρ₀⟩         ρ⊢a' ⇓ error
   ---------------------------------------------- eval-app-error-right
              ρ⊢a a' ⇓ error
   ρ⊢a ⇓ v     ρ, x→v ⊢a'⇓v'                  ρ⊢a ⇓ error
------------------------------ eval-let    ----------------- eval-let-error
    ρ ⊢let x = a in a' ⇓ v'                ρ⊢let x = a in a' ⇓ error
 *)


open Syntax
type env = (string * value) list
and value =
  | Closure of var * expr * env
  | Constant of constant * value list
type result = Error | Value of value
module type BigStepEval = sig val eval : env -> expr -> result end
module BigStep : BigStepEval

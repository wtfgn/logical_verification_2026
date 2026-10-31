/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  -- Step 1: Observed a function form σ → τ
  -- ⇒ σ := α → β → γ, τ := β → α → γ
  -- ⇒ fun f ↦ _
  --
  -- Step 2: Continue recursively with the placeholder of type τ
  -- ⇒ σ := β, τ = α → γ
  -- ⇒ fun b ↦ _
  --
  -- Step 3: Continue recursively with the placeholder of type τ
  -- ⇒ σ := α, τ := γ
  -- ⇒ fun a → _
  --
  -- Step 4: Combine everything to get the final term
  -- Or you can also write `fun f b a => f a b`
  fun f => fun b => fun a => f a b
 

def projFst : α → α → α :=
  -- Both `a` and `a'` have type `α`,
  -- so we can return either one of them.
  -- Here we choose to return the first argument.
  fun a => fun a' => a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun a a' => a'

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  -- You may also return `g a b`
  fun f => fun a => fun g => fun b => g a


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-

––––––––––––––––– VAR   ––––––––– VAR 
C ⊢ f : α → β → γ       C ⊢ a : α
–––––––––––––––––––––––––––––––––––– VAR      ––––––––––––––––––––––––––––– VAR  
C ⊢ f a : β → γ                                         C ⊢ b : β
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– APP
C, f : α → β → γ, b : β, a : α ⊢ f a b : γ
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
C, f : α → β → γ, b : β ⊢ (fun (a : α) ↦ f a b) : α → γ 
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
C, f : α → β → γ ⊢ (fun (b :β) (a : α) ↦ f a b) : β → α → γ
––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
⊢ (fun (f : α → β → γ) (b : β) (a : α) ↦ f a b) : (α → β → γ) → β → α → γ 

-/
end LoVe

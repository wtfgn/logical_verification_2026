/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: A Type of Terms

Recall the type of terms from question 3 of exercise 5: -/

inductive Term : Type where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1. Define an inductive predicate `IsLam` that returns `True` if its
argument is of the form `Term.lam …` and that returns `False` otherwise. -/

-- enter your definition here
inductive IsLam : Term → Prop where
  | lam : ∀ (x : String) (t : Term), IsLam (Term.lam x t)

/- 1.2. Validate your answer to question 1.1 by proving the following
theorems: -/

theorem IsLam_lam (s : String) (t : Term) :
    IsLam (Term.lam s t) :=
  IsLam.lam s t

theorem not_IsLamVar (s : String) :
    ¬ IsLam (Term.var s) := by
  intro h
  contradiction

theorem not_IsLam_app (t u : Term) :
    ¬ IsLam (Term.app t u) := by
  intro h
  cases h
  

/- 1.3. Define an inductive predicate `IsApp` that returns `True` if its
argument is of the form `Term.app …` and that returns `False` otherwise. -/

-- enter your definition here
inductive IsApp : Term → Prop where
  | app : ∀ (t₁ : Term) (t₂ : Term), IsApp (Term.app t₁ t₂)

/- 1.4. Define an inductive predicate `IsLamFree` that is true if and only if
its argument is a term that contains no λ-expressions. -/

-- enter your definition here
inductive IsLamFree : Term → Prop
  | var (s : String) : IsLamFree (Term.var s)
  | app (t₁ t₂ : Term) : IsLamFree t₁ → IsLamFree t₂ → IsLamFree (Term.app t₁ t₂)

/- ## Question 2: Transitive Closure

In mathematics, the transitive closure `R⁺` of a binary relation `R` over a
set `A` can be defined as the smallest solution satisfying the following rules:

    (base) for all `a, b ∈ A`, if `a R b`, then `a R⁺ b`;
    (step) for all `a, b, c ∈ A`, if `a R b` and `b R⁺ c`, then `a R⁺ c`.

In Lean, we can define this notion as follows, by identifying the set `A` with
the type `α`: -/

inductive TCV1 {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α)   : R a b → TCV1 R a b
  | step (a b c : α) : R a b → TCV1 R b c → TCV1 R a c

/- 2.1. Rule `(step)` makes it convenient to extend transitive chains by adding
links to the left. Another way to define the transitive closure `R⁺` would use
replace `(step)` with the following right-leaning rule:

    (pets) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R c`, then `a R⁺ c`.

Define a predicate `TCV2` that embodies this alternative definition. -/

-- enter your definition here
inductive TCV2 {α :Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α) : R a b → TCV2 R a b
  | step (a b c : α) : TCV2 R a b → R b c → TCV2 R a c

/- 2.2. Yet another definition of the transitive closure `R⁺` would use the
following symmetric rule instead of `(step)` or `(pets)`:

    (trans) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R⁺ c`, then `a R⁺ c`.

Define a predicate `TCV3` that embodies this alternative definition. -/

inductive TCV3 {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α) : R a b → TCV3 R a b
  | step (a b c : α) : TCV3 R a b → TCV3 R b c → TCV3 R a c

/- 2.3. Prove that `(step)` also holds as a theorem about `TCV3`. -/

theorem TCV3_step {α : Type} (R : α → α → Prop) (a b c : α) (rab : R a b)
      (tbc : TCV3 R b c) :
    TCV3 R a c := by
  apply TCV3.step a b c
  constructor
  assumption'

/- 2.4. Prove the following theorem by rule induction: -/

theorem TCV1_pets {α : Type} (R : α → α → Prop) (c : α) :
    ∀a b, TCV1 R a b → R b c → TCV1 R a c := by
  intro a b h h2
  induction h with
  | base a b hab => 
      exact TCV1.step a b c hab (TCV1.base b c h2)
  | step a b d hab hbd ih =>
     apply TCV1.step a b c hab
     exact ih h2

/- ## Question 3: Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop where
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- 3.1. Define a similar predicate for odd numbers by completing the Lean
definition below. The definition should distinguish two cases, like `Even`, and
should not rely on `Even`. -/

inductive Odd : ℕ → Prop where
  | one : Odd 1
  | add_two (k : ℕ) : Odd k → Odd (k + 2)

/- 3.2. Give proof terms for the following propositions, based on your answer
to question 2.1. -/

theorem Odd_3 :
    Odd 3 := by
  apply Odd.add_two 1
  exact Odd.one
  

theorem Odd_5 :
    Odd 5 := by
  apply Odd.add_two 3
  exact Odd_3

/- 3.3. Prove the following theorem by rule induction: -/

theorem Even_Odd {n : ℕ} (heven : Even n) :
    Odd (n + 1) := by
  induction heven with
  | zero =>
      simp
      exact Odd.one
  | add_two a a_ih a_ih'  =>
      apply Odd.add_two (a + 1) a_ih'

/- 3.4. prove the same theorem again, this time as a "paper" proof. this is a
good exercise to develop a deeper understanding of how rule induction works.
follow the guidelines given in question 1.4 of exercise 5. -/

-- enter your paper proof here

/-
Proof: ∀ n ∈ ℕ, Even n → Odd (n + 1)
We perform rule induction of the hypothesis h : Even n.

Base case (Even.zero): n = 0:
  Then n + 1 = 1, and Odd 1 holds by the constructor Odd.one.
Inductive step (Even.add_two): n = k + 2 for some k ∈ ℕ
  Our goal is to show: Even (k + 2) → Odd ((k + 2) + 1) = Odd (k + 3).
  Notice that (k + 3) = (k + 1) + 2. By the inductive hypothesis, Odd (k + 1).
  Thus, we can apply the constructor Odd.add_two to Odd (k + 1) to obtain Odd (k + 3).
-/

/- 3.5. Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → False`. -/

theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
    ¬ Odd n :=
  sorry

end LoVe

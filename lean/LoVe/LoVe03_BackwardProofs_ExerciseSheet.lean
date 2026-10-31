/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a := by
  intro a
  exact a

theorem K (a b : Prop) :
    a → b → b := by
  intro _ b
  exact b

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c := by
  intro h b a
  apply h 
  exact a
  exact b

theorem proj_fst (a : Prop) :
    a → a → a := by
  intro a₁ a₂
  exact a₁

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a := by
  intro a₁ a₂
  exact a₂

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c := by
  intro h₁ a h₂ b
  apply h₂
  exact a

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a := by
  intro hab hnb hna
  apply hnb
  apply hab
  exact hna

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) := 
  ⟨ by
    intro h
    apply And.intro
    . exact fun x => (h x).left
    . exact fun x => (h x).right
  , by
    intro h
    exact fun x => ⟨h.left x, h.right x⟩
    ⟩


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mul, ih, add]

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mul, ih, add_succ, add_assoc, add]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := by
  induction n with
  | zero =>
      simp [mul, mul_zero]
  | succ n ih =>
      simp [mul, ih, mul_succ, add_comm]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mul, ih, mul_add]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
    add (mul n l) (mul n m) = mul (add l m) n := by
  rw [mul_comm _ n, mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

#check False.elim

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce := by
  rw [ExcludedMiddle, Peirce]
  intro h a b h1
  apply Or.elim $ h a 
  . exact fun ha => ha
  . intro hna
    exact h1 fun a => False.elim $ hna a



/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation := by
  rw [Peirce, DoubleNegation]
  intro h a hnna
  rw [Not, Not] at hnna
  apply h a False
  intro hna
  apply False.elim
  apply hnna
  exact hna


/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  sorry

end SorryTheorems

end BackwardProofs

end LoVe

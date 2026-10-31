/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume h : a
  show a from h

theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from habc ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from ha1

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from ha2


theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from
    hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  show False from
    hnb (hab ha)
  

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  ⟨ assume hpq : ∀x, p x ∧ q x
    have hp : ∀x, p x :=
      fix x : α
      (hpq x).left
    have hq : ∀x, q x :=
      fix x : α
      (hpq x).right
    show (∀x, p x) ∧ (∀x, q x) from
      ⟨hp, hq⟩
  , assume hpq : (∀x, p x) ∧ (∀x, q x)
    have hp : ∀x, p x :=
      hpq.left
    have hq : ∀x, q x :=
      hpq.right
    fix x : α
    show p x ∧ q x from
      ⟨hp x, hq x⟩
  ⟩

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hex : ∃x, ∀y, p x y
  fix y : α
  show ∃x, p x y from
    Exists.elim hex (
      fix a : α
      assume hpay : ∀y, p a y
      show ∃x, p x y from
        Exists.intro a (hpay y)
    )


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
      simp [add_mul]
    _ = a * a + a * b + b * a + b * b := by
      simp [mul_add]
      ac_rfl
    _ = a * a + a * b + a * b + b * b := by
      simp [mul_comm]
    _ = a * a + 2 * a * b + b * b := by
      simp [Nat.two_mul, add_mul, add_assoc]
      


/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
    simp [add_mul]
  have h2 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b := by
    simp [mul_add]
    ac_rfl
  have h3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b := by
    simp [mul_comm]
  have h4 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b := by
    simp [Nat.two_mul, add_mul, add_assoc]
  show (a + b) * (a + b) = a * a + 2 * a * b + b * b from
    h1 |>.trans h2 |>.trans h3 |>.trans h4

/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False := by
  have hwrong : (∀x, x = 0 ∧ True) ↔ True :=
    All.one_point_wrong 0 (fun _ ↦ True)
  simp at hwrong
  have hone_eq_zero : 1 = 0 :=
    hwrong 1
  cases hone_eq_zero
 

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False := by
  have hwrong : (∃x, x ≠ 0) ↔ False :=
    Exists.one_point_wrong 0 (fun _ ↦ False)
  simp at hwrong
  have hone_eq_zero : 1 = 0 :=
    hwrong 1
  cases hone_eq_zero
  

end LoVe

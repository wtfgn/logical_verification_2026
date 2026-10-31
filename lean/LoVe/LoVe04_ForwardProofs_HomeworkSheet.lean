/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,

Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4: Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    · intro hna
      apply False.elim
      apply hna
      exact ha
    · intro hb
      exact hb

/- 1.1. Prove the same theorem again, this time by providing a proof term.

Hint: There is an easy way. -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun p q hnpq a => Or.elim hnpq 
    (fun hnp => False.elim $ hnp a)
    (fun hq => hq)

/- 1.2. Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a : Prop
  fix b : Prop
  assume hor : ¬ a ∨ b
  Or.elim hor
    (assume hna : ¬ a
     assume ha : a 
     False.elim $ hna ha
    )
    (assume hb : b
     assume ha : a
     show b from hb
    )


  


/- ## Question 2: More Logic Puzzles

Recall the following tactical proof: -/

theorem weak_peirce :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  by
    intro a b habaab
    apply habaab
    intro habaa
    apply habaa
    intro ha
    apply habaab
    intro haba
    apply ha

/- 2.1. Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem weak_peirce_term :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fun p q h => h (fun hpqp => hpqp (fun hpq => h (fun _ => hpq)))

/- 2.2. Prove the same theorem again, this time by providing a structured
proof, with `fix`, `assume`, and `show`. -/

theorem weak_peirce_struct :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fix p : Prop
  fix q : Prop
  assume h : ((((p → q) → p) → p) → q)
  show q from
    by
      apply h
      intro hpqp 
      apply hpqp
      intro hp
      apply h 
      intro hpq
      apply hp
      
    
    



/- ## Question 3: Connectives and Quantifiers

3.1. Supply a structured proof of the commutativity of `∧` under an `∃`
quantifier, using no other theorems than the introduction and elimination rules
for `∃`, `∧`, and `↔`. -/

theorem And_comm_under_Exists {α : Type} (p q : α → Prop) :
    (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
  Iff.intro
    (assume hex : ∃x, p x ∧ q x
     Exists.elim hex (
       fix x : α
       assume hpaq : p x ∧ q x
       show ∃x, q x ∧ p x from
         Exists.intro x (And.intro hpaq.right hpaq.left)
       )
    )
    (assume hex : ∃x, q x ∧ p x
     Exists.elim hex (
       fix x : α
       assume hqap : q x ∧ p x
       show ∃x, p x ∧ q x from
         Exists.intro x (And.intro hqap.right hqap.left)
       )
    )

/- 3.2. Supply a structured proof of the commutativity of `∨` under a `∀`
quantifier, using no other theorems than the introduction and elimination rules
for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
    (assume hall : ∀x, p x ∨ q x
     fix x : α
     Or.elim (hall x)
      (assume hpx : p x
       Or.intro_right (q x) hpx)
      (assume hqx : q x
       Or.intro_left (p x) hqx))
    (assume hall :∀ x, q x ∨ p x
     fix x : α
     Or.elim (hall x)
      (assume hqx : q x
       Or.intro_right (p x) hqx)
      (assume hpx : p x
       Or.intro_left (q x) hpx))

/- 3.3. We have proved or stated three of the six possible implications between
`ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the exercise of lecture 3.
Prove the three missing implications using structured proofs, exploiting the
three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  assume hDN : ∀a : Prop, (¬¬ a) → a
  show ∀a b : Prop, ((a → b) → a) → a by
    intro a b h
    apply hDN a
    intro hna
    apply hna
    apply h
    intro a'
    exact False.elim (hna a')
    


theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume hP : ∀a b : Prop, ((a → b) → a) → a
  show ∀a : Prop, a ∨ ¬ a by
    intro a
    apply hP (a ∨ ¬ a) False
    intro h
    apply Or.inr
    intro ha
    apply h
    apply Or.inl
    exact ha
    -- exact hP (a ∨ ¬ a) False (fun h => Or.inr (fun ha => h (Or.inl ha)))

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume hEM : ∀a : Prop, a ∨ ¬ a
  show ∀a : Prop, (¬¬ a) → a by
    intro a hnn
    apply Or.elim (hEM a)
    intro ha
    exact ha
    intro hna
    exact False.elim (hnn hna)

end BackwardProofs

end LoVe

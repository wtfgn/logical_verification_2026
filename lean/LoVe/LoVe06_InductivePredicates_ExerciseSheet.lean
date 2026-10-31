/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
    Odd 1 := by
  intro h
  cases h

/- 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here
theorem Odd_3 :
    Odd 3 := by
  intro h
  cases h with
  | add_two _ h_even =>
      cases h_even

theorem Odd_5:
    Odd 5 := by
  intro h
  cases h with
  | add_two _ h_even =>
      cases h_even with
      | add_two _ h_even' =>
          cases h_even'

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => by
      apply Even.add_two
      simp
      apply Even_two_times


/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop where
  -- enter the missing cases here

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  sorry

theorem ServAhead_advServ :
    ServAhead Score.advServ :=
  sorry

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv :=
  sorry

theorem ServAhead_gameServ :
    ServAhead Score.gameServ :=
  sorry

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv :=
  sorry

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : BinaryTree α, IsFull (mirror t) → IsFull t := by
  intro t h
  induction t with
  | nil => exact IsFull.nil
  | node =>
    have fmt := IsFull_mirror _ h
    simpa [mirror_mirror] using fmt
      

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : BinaryTree α → BinaryTree β 
  | .nil => .nil
  | .node x l r => .node (f x) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : BinaryTree α, Tree.map f t = BinaryTree.nil ↔ t = BinaryTree.nil := by
  intro t
  cases t <;> simp [Tree.map]

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_mirror {α β : Type} (f : α → β) :
    ∀t : BinaryTree α, IsFull t → IsFull (Tree.map f t) := by
  intro t hFull
  induction hFull with 
  | nil =>
      simp [Tree.map]
      exact IsFull.nil
  | node x l r hl hr hiff hl_ih hr_ih =>
      simp [Tree.map]
      apply IsFull.node
      assumption'
      exact
        ⟨ by
            intro h_map_left_nil
            simp [Tree.map_eq_empty_iff] at *
            exact hiff.mp h_map_left_nil
        , by
            intro h_map_right_nil
            simp [Tree.map_eq_empty_iff] at *
            exact hiff.mpr h_map_right_nil
        ⟩
end LoVe

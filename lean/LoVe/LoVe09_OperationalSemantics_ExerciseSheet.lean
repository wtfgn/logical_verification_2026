/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type where
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop where
  -- enter the missing `assign` rule here
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- enter the missing `seq` rule here
  | seq (S T t s u) (hs : BigStep (S, s) t) (ht : BigStep (T, t) u) :
    BigStep (S; T, s) u
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- enter the missing `loop` rules here
  | loop_zero (S s) :
    BigStep (Stmt.loop S, s) s
  | loop_succ (S s t u) (hs : BigStep (S, s) t) (ht : BigStep (Stmt.loop S, t) u) :
    BigStep (Stmt.loop S, s) u

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] := by
  apply Iff.intro
  . intro h
    cases h
    rfl
  . intro h
    subst h
    apply BigStep.assign

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s := by
  apply Iff.intro
  . intro h
    cases h
    trivial
  . intro h
    cases h with
    | intro h_t_eq_s hBs =>
        subst h_t_eq_s
        apply BigStep.assert
        exact hBs
    
    

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | seq =>
        apply Exists.intro 
        apply And.intro
        assumption'
  . intro h
    cases h with
    | intro s' h' =>
        apply BigStep.seq
        try assumption'
        . exact h'.left
        . exact h'.right
    -- | intro s' h' =>
    --     cases h' with
    --     | intro =>
    --         apply BigStep.seq
    --         assumption'



theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) := by
  apply Iff.intro
  . intro hloop
    cases hloop with
    | loop_zero =>
        apply Or.inl
        rfl
    | loop_succ _ _ t =>
        apply Or.inr 
        apply Exists.intro t
        apply And.intro
        assumption'
    
  . intro hor
    cases hor with
    | inl hsu =>
        simp [hsu]
        apply BigStep.loop_zero
    | inr hex =>
        cases hex with
        | intro t hand =>
            apply BigStep.loop_succ
            try assumption'
            . exact hand.left
            . exact hand.right

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | choice _ _ _ i hless =>
        apply Exists.intro i
        apply Exists.intro hless
        assumption
  . intro h
    cases h with
    | intro hi hex =>
        cases hex with
        | intro hless hbody =>
            apply BigStep.choice
            assumption'

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    GCL.Stmt.assign x a
  | S; T =>
    gcl_of S;
    gcl_of T
  | Stmt.ifThenElse B S T  =>
    GCL.Stmt.choice [
      GCL.Stmt.assert B; gcl_of S,
      GCL.Stmt.assert (fun s ↦ ¬ B s); gcl_of T
    ]
  | Stmt.whileDo B S =>
    GCL.Stmt.loop
      (GCL.Stmt.assert B; gcl_of S);
    GCL.Stmt.assert (fun s ↦ ¬ B s)

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- enter your answer here

-- * `GCL.Stmt.loop (GCL.Stmt.assert (fun _ ↦ False))`
-- * `GCL.Stmt.assign "x" (fun s ↦ s "x")` -/


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip := by
  intro s t
  apply Iff.intro
  . intro h
    cases h
    simp
  . intro h
    cases h
    simp

theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | seq S T s t u hs ht  =>
        cases hs
        exact ht
  . intro h
    apply BigStep.seq
    try assumption'
    apply BigStep.skip

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | seq S T s t' u hs ht =>
        cases ht
        exact hs
  . intro h
    apply BigStep.seq
    try assumption'
    apply BigStep.skip

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | if_false _ _ _ _ _ hcond hbody =>
        cases hbody
        apply BigStep.while_false
        exact hcond
    | if_true _ _ _ _ _ hcond hbody =>
        cases hbody with
        | seq S T s t' u hs ht =>
            apply BigStep.while_true
            assumption'
  . intro h
    cases h with
    | while_false _ _ _ hcond =>
        apply BigStep.if_false
        try assumption'
        apply BigStep.skip
    | while_true _ _ _ _ _ hcond hbody hrest =>
        apply BigStep.if_true
        try assumption'
        apply BigStep.seq
        assumption'
        

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  sorry

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  sorry

end LoVe

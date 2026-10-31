/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Arithmetic Expressions

Recall the type of arithmetic expressions from lecture 2 and its evaluation
function: -/

#check AExp
#check eval

/- Let us introduce the following abbreviation for an environment that maps
variable names to values: -/

def Envir : Type :=
  String → ℤ

namespace AExp

/- 1.1. Complete the following Lean definition of a big-step-style semantics
for arithmetic expressions. The predicate `BigStep` (`⟹`) relates an arithmetic
expression, an environment, and the value to which the expression evaluates in
the given environment: -/

inductive BigStep : AExp × Envir → ℤ → Prop where
  | num (i env) : BigStep (AExp.num i, env) i
  | var (s env) : BigStep (AExp.var s, env) (env s)
  | add (a₁ a₂ env i₁ i₂)
      (h₁ : BigStep (a₁, env) i₁)
      (h₂ : BigStep (a₂, env) i₂) :
    BigStep (AExp.add a₁ a₂, env) (i₁ + i₂)
  | sub (a₁ a₂ env i₁ i₂)
      (h₁ : BigStep (a₁, env) i₁)
      (h₂ : BigStep (a₂, env) i₂) :
    BigStep (AExp.sub a₁ a₂, env) (i₁ - i₂)
  | mul (a₁ a₂ env i₁ i₂)
      (h₁ : BigStep (a₁, env) i₁)
      (h₂ : BigStep (a₂, env) i₂) :
    BigStep (AExp.mul a₁ a₂, env) (i₁ * i₂)
  | div (a₁ a₂ env i₁ i₂)
      (h₁ : BigStep (a₁, env) i₁)
      (h₂ : BigStep (a₂, env) i₂)
      (h : i₂ ≠ 0) :
    BigStep (AExp.div a₁ a₂, env) (i₁ / i₂)

infix:60 " ⟹ " => BigStep

/- 1.2. Prove the following theorem to validate your definition above.

Hint: It may help to first prove
`(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2`. -/

theorem BigStep_add_two_two (env : Envir) :
    (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 := by
  apply BigStep.add (AExp.num 2) (AExp.num 2) env 2 2 <;>
  apply BigStep.num 2 env




/- 1.3. Prove that the big-step semantics is sound with respect to the `eval`
function: -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
    eval (Prod.snd aenv) (Prod.fst aenv) = i := by
  induction hstep with
  | num i env =>
      simp [eval]
  | var s env =>
      simp [eval]
  | add a₁ a₂ env i₁ i₂ h₁ h₂ h₁_ih h₂_ih =>
      simp [eval, h₁_ih, h₂_ih]
  | sub a₁ a₂ env i₁ i₂ h₁ h₂ h₁_ih h₂_ih =>
      simp [eval, h₁_ih, h₂_ih]
  | mul a₁ a₂ env i₁ i₂ h₁ h₂ h₁_ih h₂_ih =>
      simp [eval, h₁_ih, h₂_ih]
  | div a₁ a₂ env i₁ i₂ h₁ h₂ h h₁_ih h₂_ih =>
      simp [eval, h₁_ih, h₂_ih]


end AExp


/- ## Question 2: Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

namespace REPEAT

inductive Stmt : Type where
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`.

2.1. Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s):
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S s T t u)
      (hs : BigStep (S, s) t)
      (ht : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | unlessDo_true (B S s)
      (hcond : B s) :
    BigStep (Stmt.unlessDo B S, s) s
  | unlessDo_false (B S s t)
      (hcond : ¬ B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.unlessDo B S, s) t
  | repeat_zero (S s) :
    BigStep (Stmt.repeat 0 S, s) s
  | repeat_succ (n S s t u)
      (hbody : BigStep (S, s) t)
      (hloop : BigStep (Stmt.repeat n S, t) u) :
    BigStep (Stmt.repeat (n + 1) S, s) u
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- 2.2. Complete the following definition of a small-step semantics: -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | unlessDo_true (B S s) (hcond : B s) :
    SmallStep (Stmt.unlessDo B S, s) (Stmt.skip, s)
  | unlessDo_false (B S s) (hcond : ¬ B s) :
    SmallStep (Stmt.unlessDo B S, s) (S, s)
  | repeat_zero (S s):
    SmallStep (Stmt.repeat 0 S, s) (Stmt.skip, s)
  | repeat_succ (n S s) :
    SmallStep (Stmt.repeat (n + 1) S, s) (S; Stmt.repeat n S, s)

-- enter the missing cases here

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

/- 2.3. We will now attempt to prove termination of the REPEAT language. More
precisely, we will show that there cannot be infinite chains of the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : Stmt → ℕ
  | Stmt.skip         => 0
  | Stmt.assign _ _     => 1
  | Stmt.seq S T       => mess S + mess T + 1
  | Stmt.unlessDo _ S => mess S + 1
  | Stmt.repeat n S     => n * (mess S + 2) + 1
-- enter the missing cases here
/-
For the `repeat` case, here is the derivation
For the base case (repeat_zero):
  repeat 0 S ⟹ skip
  By the definition of mess, the measure should be strictly decreasing with
  each small-step transition. Therefore, we have:
    mess(repeat 0 S) > mess(skip)
    mess(repeat 0 S) > 0
  i.e. the value must ≥ 1. The simplest choice that works uniformly is
    mess(repeat 0 S) = 1 

For the step case (repeat_succ):
  repeat (n + 1) S ⟹ S; repeat n S
  Again, by the definition of mess, we have:
    mess(repeat (n + 1) S) > mess(S; repeat n S)
    mess(repeat (n + 1) S) > mess(S) + mess(repeat n S) + 1 (given by seq)
  The required relation becomes:
    mess(repeat (n + 1) S) ≥ mess(S) + mess(repeat n S) + 1 + 1 
  The simplest choice that works uniformly is
    mess(repeat (n + 1) S) = mess(S) + mess(repeat n S) + 2

  By solving the recurrence relation:
    mess(repeat 0 S) = 1
    mess(repeat (n + 1) S) = mess(S) + mess(repeat n S) + 2
  we have:
    mess(repeat n S) = n * (mess(S) + 2) + 1
-/

/- You can validate your answer as follows. Consider the following program
`S₀`: -/

def incr (x : String) : Stmt :=
  Stmt.assign x (fun s ↦ s x + 1)

def S₀ : Stmt :=
  Stmt.repeat 1 (incr "m"; incr "n")

/- Check that `mess` strictly decreases with each step of its small-step
evaluation: -/

def S₁ : Stmt :=
  (incr "m"; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₂ : Stmt :=
  (Stmt.skip; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₃ : Stmt :=
  incr "n"; Stmt.repeat 0 (incr "m"; incr "n")

def S₄ : Stmt :=
  Stmt.skip; Stmt.repeat 0 (incr "m"; incr "n")

def S₅ : Stmt :=
  Stmt.repeat 0 (incr "m"; incr "n")

def S₆ : Stmt :=
  Stmt.skip

#eval mess S₀   -- result: e.g., 6
#eval mess S₁   -- result: e.g., 5
#eval mess S₂   -- result: e.g., 4
#eval mess S₃   -- result: e.g., 3
#eval mess S₄   -- result: e.g., 2
#eval mess S₅   -- result: e.g., 1
#eval mess S₆   -- result: e.g., 0

/- 2.4. Prove that the measure decreases with each small-step transition. If
necessary, revise your answer to question 2.3. -/

theorem SmallStep_mess_decreases {Ss Tt : Stmt × State} (h : Ss ⇒ Tt) :
    mess (Prod.fst Ss) > mess (Prod.fst Tt) := by
  cases h <;> simp [mess]
  case seq_step S S' T s s' hS =>
    simp [SmallStep_mess_decreases hS]
  case repeat_succ n S s => 
    linarith



/- 2.5. Prove the following inversion rule for the big-step semantics of
`unless`. -/

theorem BigStep_ite_iff {B S s t} :
    (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | unlessDo_true B S s hcond =>
        left
        apply And.intro
        . exact hcond
        . rfl
    | unlessDo_false B S s t hcond hbody =>
        right
        apply And.intro
        . exact hcond
        . exact hbody
  . intro h
    cases h with
    | inr h' =>
        apply BigStep.unlessDo_false
        . exact h'.left
        . exact h'.right
    | inl h' => 
        have hcond : B s := h'.left
        have hst : s = t := h'.right
        subst hst
        apply BigStep.unlessDo_true
        exact hcond



/- 2.6. Prove the following inversion rule for the big-step semantics of
`repeat`. -/

theorem BigStep_repeat_iff {n S s u} :
    (Stmt.repeat n S, s) ⟹ u ↔
    (n = 0 ∧ u = s)
    ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) := by
  apply Iff.intro
  . intro h
    cases h with
    | repeat_zero S s =>
        left
        trivial
    | repeat_succ n S s t u hobdy hloop =>
        right
        apply Exists.intro n
        apply Exists.intro t
        apply And.intro
        . rfl
        apply And.intro
        . exact hobdy
        . exact hloop
  . intro h
    cases h with
    | inr h =>
        have ⟨n', t, hn, hbody, hloop⟩ := h
        induction n with
        | zero =>
            contradiction
        | succ n ih =>
            apply BigStep.repeat_succ n S s t u
            assumption'
            have h' : n = n' := by
              linarith
            subst h'
            exact hloop
    | inl h =>
        have hzero : n = 0 := h.left
        have hst : u = s := h.right
        simp [hzero, hst]
        apply BigStep.repeat_zero

end REPEAT


/- ## Question 3: Semantics of Regular Expressions

Regular expressions are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `Regex` to represent the following grammar:

    R  ::=  ∅       -- `nothing`: matches nothing
         |  ε       -- `empty`: matches the empty string
         |  a       -- `atom`: matches the atom `a`
         |  R ⬝ R    -- `concat`: matches the concatenation of two regexes
         |  R + R   -- `alt`: matches either of two regexes
         |  R*      -- `star`: matches arbitrary many repetitions of a Regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive Regex (α : Type) : Type where
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- The `Matches r s` predicate indicates that the regular expression `r` matches
the string `s` (where the string is a sequence of atoms). -/

inductive Matches {α : Type} : Regex α → List α → Prop where
  | empty :
    Matches Regex.empty []
  | atom (a : α) :
    Matches (Regex.atom a) [a]
  | concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
      (h₂ : Matches r₂ s₂) :
    Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
  | alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
    Matches (Regex.alt r₁ r₂) s
  | alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
    Matches (Regex.alt r₁ r₂) s
  | star_base (r : Regex α) :
    Matches (Regex.star r) []
  | star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
      (h₂ : Matches (Regex.star r) s') :
    Matches (Regex.star r) (s ++ s')

/- The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

3.1. Explain why there is no rule for `nothing`. -/

-- enter your answer here
/-
Because that regular expression is defined to match no string at all.
The predicate `Matches` is the smallest relation closed under the given constructors.
If we add a rule such as
`| nothing (s : List α) : Matches Regex.nothing s`
then `nothing` would match every (or some) string, whcihc contradicts its intended meaning.
By simply omitting any constructor that mentions `Regex.nothing`, the inductive defintion
guarantees:
`∀ s, ¬ Matches Regex.nothing s`
-/

/- 3.2. Prove the following inversion rules. -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
    Matches (Regex.atom a) s ↔ s = [a] := by
  apply Iff.intro
  . intro h
    cases h
    rfl
  . intro h
    subst h
    apply Matches.atom
    
     

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
    ¬ Matches Regex.nothing s := by
  intro h
  cases h

@[simp] theorem Matches_empty {α : Type} {s : List α} :
    Matches Regex.empty s ↔ s = [] := by
  apply Iff.intro
  . intro h
    cases h
    rfl
  . intro h
    subst h
    apply Matches.empty

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.concat r₁ r₂) s
    ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) := by
  apply Iff.intro
  . intro h
    cases h with
    | concat r₁ r₂ s₁ s₂ h₁ h₂ =>
        apply Exists.intro s₁
        apply Exists.intro s₂
        trivial
  . intro h
    obtain ⟨s₁, s₂, h₁, h₂, hst⟩ := h
    subst hst
    apply Matches.concat
    assumption'

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) := by
  apply Iff.intro
  . intro h
    cases h with
    | alt_left r₁ r₂ s h =>
        left
        exact h
    | alt_right r₁ r₂ s h =>
        right
        exact h
  . intro h
    cases h with
    | inl h =>
        apply Matches.alt_left
        exact h
    | inr h =>
        apply Matches.alt_right
        exact h


/- 3.3. Prove the following inversion rule. -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
    Matches (Regex.star r) s ↔
    s = []
    ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂) := by
  apply Iff.intro
  . intro h
    cases h with
    | star_base r =>
        left
        rfl
    | star_step r s₁ s₂ h₁ h₂ =>
        right
        apply Exists.intro s₁
        apply Exists.intro s₂
        trivial
  . intro h
    cases h with
    | inr h =>
        obtain ⟨s₁, s₂, h₁, h₂, hst⟩ := h
        subst hst
        apply Matches.star_step
        assumption'
    | inl h =>
        subst h
        apply Matches.star_base

end LoVe

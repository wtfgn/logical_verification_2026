module

-- set_option pp.all true

@[expose]
public def incr : Nat → Nat
  | 0 => 1
  | n + 1 => incr n + 1

#print incr

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

def map (f : α → β) (n : Nat) : (v : Vect α n) → Vect β n
  | .nil       => .nil
  | .cons a as => .cons (f a) (map f _ as)

def head {α : Type} {n : Nat} (v : Vect α n) (h : n > 0) : α :=
  match v with
  | Vect.nil => False.elim (Nat.not_lt_zero _ h)
  | Vect.cons x xs => x

#print head
#print head.match_1
#print Vect.casesOn
#print Vect.rec

-- def head {α : Type} {n : Nat} (v : Vector α n) (h : n > 0) : α :=
--   -- 1. We match on 'v' but return a FUNCTION: (n > 0) → α
--   -- match (fun (m = n) v (m > 0) → α) with
--   match , v with
--
--   | Vector.nil =>
--     -- Inside here, Lean knows m = 0. The expected type is now: (0 > 0) → α
--     fun h0 => False.elim (Nat.not_lt_zero _ h0)
--
--   | Vector.cons x xs =>
--     -- Inside here, Lean knows m = k + 1. The expected type is: (k + 1 > 0) → α
--     fun _ => x

-- 2. We immediately apply the resulting function to our original hypothesis 'h'
-- h

-- example (x : Bool) :
--     match x with
--     | true  => String
--     | false => Nat
--   :=
--   match x with
--   | true => "hello"
--   | false => (42: Nat)

#print map
#print Vect.brecOn
#print map._f
#print map.match_1
#print Vect.below
#print Vect.rec

def viaCases (n : Nat) (v : Vect α n) : Vect α n :=
  Vect.casesOn (motive := fun _ _ => Vect α n) v .nil (fun a as => .cons a as)
-- error: Vect.nil has type Vect ?m 0 but is expected to have type Vect α n

module

import LoVe.test

#print incr

theorem incr_eq_plus1 : incr = (· + 1) := by
  funext n
  induction n <;> simp [incr, *]

import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by

  have helper : √(4 + √(16 + 16 * a)) = 6 - √(1 + √(1 + a))
  apply Eq.symm <;> try linarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 + √(16 + 16 * a)), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + √(1 + a))]
  have helper2 := congr_arg (fun x : ℝ => x ^ 2) helper
  field_simp at helper2 <;>
  ring_nf at helper2 ⊢
  field_simp [(show 16 + a * 16 = 16 * (1 + a) by ring)] at helper2
  rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_cast, Real.sqrt_sq] at helper2
  repeat' nlinarith[Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg <| 1 + √(1+a)]
  have helper3 : √(1 + √(1 + a)) = 2 := by nlinarith [Real.sqrt_nonneg (1 + √(1 + a)), Real.sq_sqrt (show 0 ≤ (1 + √(1 + a)) by positivity)]
  have helper4: √(1 + a) = 3 := by
    nlinarith
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + a by linarith [Real.sqrt_pos.1 (by linarith)])]
import Mathlib
open BigOperators Real Nat Topology

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa
  (a b : ℝ) :
  abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by

  rw [div_add_div _ _ (by positivity) (by positivity)]
  cases abs_cases (a + b) <;> cases abs_cases a <;>
   cases abs_cases b <;>
     all_goals rw [div_le_div_iff] <;>
     nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
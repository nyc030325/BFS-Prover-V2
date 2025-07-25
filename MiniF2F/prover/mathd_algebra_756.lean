import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_756
  (a b : ℝ)
  (h₀ : (2:ℝ)^a = 32)
  (h₁ : a^b = 125) :
  b^a = 243 := by

  have field := congr_arg Real.log h₀
  simp [Real.log_rpow, show (32 : ℝ) = 2 ^ 5 by norm_cast] at field
  cases field <;> norm_num at * <;> aesop
  have := congr_arg Real.log h₁
  simp [Real.log_rpow, show (125 : ℝ) = 5 ^ 3 by norm_num1, show (243 : ℝ) = 3 ^ 5 by norm_num1, Real.log_pow] at this
  aesop
      <;> norm_cast
  try linarith [h₀]
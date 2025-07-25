import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_598
  (a b c d : ℝ)
  (h₁ : ((4:ℝ)^a) = 5)
  (h₂ : ((5:ℝ)^b) = 6)
  (h₃ : ((6:ℝ)^c) = 7)
  (h₄ : ((7:ℝ)^d) = 8) :
  a * b * c * d = 3 / 2 := by

  apply_fun Real.log at h₁ h₂ h₃ h₄
  field_simp[Real.log_rpow] at*
  rw [← eq_div_iff] at h₁ h₂ h₃ h₄ <;> norm_num
  field_simp [*] at * <;> ring
  rw[show Real.log 8 = Real.log (2 ^ 3) by norm_num, show Real.log 4 = Real.log (2 ^ 2) by norm_num,
    Real.log_pow, Real.log_pow] <;> norm_num <;> ring
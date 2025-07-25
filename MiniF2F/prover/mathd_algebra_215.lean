import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_215
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + 3)^2 = 121) :
  ∑ k in S, k = -6 := by

  have hs : S = {-14, 8}
  ext x <;> aesop
  exacts [
     by apply or_iff_not_imp_right.2; intro h; apply mul_left_cancel₀ (sub_ne_zero_of_ne h) <;> nlinarith,
     by norm_num,
     by norm_num, 
     by rw [hs]; norm_num]
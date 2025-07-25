import Mathlib
open BigOperators Real Nat Topology

theorem algebra_amgm_sum1toneqn_prod1tonleq1
  (a : ℕ → NNReal)
  (n : ℕ)
  (h₀ : ∑ x in Finset.range n, a x = n) :
  ∏ x in Finset.range n, a x ≤ 1 := by

  have g := h₀
  revert h₀
  intro amgm
  let S := Finset.range n
  by_cases h1 : n = 0
  simp[h1]
  have hn  : 0 < n := by omega
  let μ := (fun (x : ℕ) => (a x : ℝ))
  let w : ℕ → ℝ := fun _ => 1
  have w_nonneg : ∀ i, 0 ≤ w i
  simp [w, zero_le_one]
  have w_pos  : 0 < ∏ i in Finset.range n, w i
  all_goals aesop (add simp w)
  have w_nonneg : ∀ x ∈ S, 0 ≤ w x
  any_goals simp [w]
  have w_pos  : 0 < ∏ x ∈ S, w x
  simp [w]
  have amgm_real  : (∏ x ∈ S, μ x ^ (w x : ℝ)) ^ ((∑ x ∈ S, (w x : ℝ))⁻¹) ≤ (∑ x ∈ S, (w x * μ x : ℝ)) / (∑ x ∈ S, (w x : ℝ))
  apply Real.geom_mean_le_arith_mean
  exact w_nonneg
  simp [w, S, hn]
  field_simp[μ]
  simp [μ, w, S] at amgm_real
  norm_cast at amgm_real
  simp[ amgm] at amgm_real
  by_cases H : ∏ a_1 ∈ Finset.range n, a a_1 = 0
  simp [H]
  simp [← NNReal.coe_le_coe, amgm] at amgm_real
  rw  [div_self] at amgm_real
  apply le_of_not_lt
  all_goals aesop (add simp NNReal)
  rw[←NNReal.coe_one] at amgm_real
  norm_cast at amgm_real
  contrapose! amgm_real
  erw [ Real.one_lt_rpow_iff]
  left
  all_goals aesop (add simp [Finset.range])
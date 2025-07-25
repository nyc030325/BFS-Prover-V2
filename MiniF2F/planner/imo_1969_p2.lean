import Mathlib
import Aesop

open BigOperators Real Nat Topology Int

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Parser Elab Tactic

elab "focus' " tacs:tacticSeq1Indented : tactic => do
  match tacs.raw[0] with
  | .node _ _ args =>
    for tac in args do
      if tac[0].isMissing then continue
      focus (evalTactic tac)
  | _ => unreachable!

macro "by' " tacs:tacticSeq1Indented : term =>
  `(term| by focus' $tacs)
  

theorem imo_1969_p2
  (m n : ℝ)
  (k : ℕ)
  (a : ℕ → ℝ)
  (y : ℝ → ℝ)
  (h₀ : 0 < k)
  (h₁ : ∀ x, y x = ∑ i in Finset.range k, ((Real.cos (a i + x)) / (2^i)))
  (h₂ : y m = 0)
  (h₃ : y n = 0) :
  ∃ t : ℤ, m - n = t * Real.pi := by'

  suffices h_cos_add : ∀ i x, Real.cos (a i + x) = Real.cos (a i) * Real.cos x - Real.sin (a i) * Real.sin x
  suffices h_y_sum_expanded : ∀ (x : ℝ), y x = ∑ i in (Finset.range k : Finset ℕ), (Real.cos (a i) * Real.cos x - Real.sin (a i) * Real.sin x) / ((2 : ℕ) ^ i : ℝ)
  suffices h_y_sum_split : ∀ (x : ℝ), y x = (∑ i in (Finset.range k : Finset ℕ), Real.cos (a i) * Real.cos x / ((2 : ℕ) ^ i : ℝ)) - (∑ i in (Finset.range k : Finset ℕ), Real.sin (a i) * Real.sin x / ((2 : ℕ) ^ i : ℝ))
  suffices h_y_expand : ∀ (x : ℝ), y x = (∑ i in (Finset.range k : Finset ℕ), Real.cos (a i) / ((2 : ℕ) ^ i : ℝ)) * Real.cos x - (∑ i in (Finset.range k : Finset ℕ), Real.sin (a i) / ((2 : ℕ) ^ i : ℝ)) * Real.sin x
  suffices h_k_ge_one : 1 ≤ k
  suffices h_complex_repr : (⟨∑ i in (Finset.range k : Finset ℕ), Real.cos (a i) / ((2 : ℕ) ^ i : ℝ), ∑ i in (Finset.range k : Finset ℕ), Real.sin (a i) / ((2 : ℕ) ^ i : ℝ)⟩ : ℂ) = ∑ i in (Finset.range k : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)
  suffices h_sum_split : (∑ i in (Finset.range k : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)) = Complex.exp (↑(a 0) * Complex.I) + ∑ i in (Finset.Icc 1 (k-1) : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)
  suffices h_abs_head : Complex.abs (Complex.exp (↑(a 0) * Complex.I)) = 1
  suffices h_tail_geom_sum_val : (∑ i in (Finset.Icc 1 (k - 1) : Finset ℕ), 1 / ((2 : ℕ) ^ i : ℝ)) = 1 - 1 / (2 : ℝ) ^ (k - 1)
  suffices h_abs_tail_le : Complex.abs (∑ i in (Finset.Icc 1 (k-1) : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)) ≤ 1 - 1 / (2 : ℝ) ^ (k - 1)
  suffices h_abs_tail_lt_one : Complex.abs (∑ i in (Finset.Icc 1 (k-1) : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)) < 1
  suffices h_abs_ge_by_rev_triangle : Complex.abs (∑ i in (Finset.range k : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)) ≥ 1 - Complex.abs (∑ i in (Finset.Icc 1 (k-1) : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ))
  suffices h_abs_ge_final : Complex.abs (∑ i in (Finset.range k : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ)) ≥ 1 / (2 : ℝ) ^ (k-1)
  suffices h_abs_gt_zero : 0 < Complex.abs (∑ i in (Finset.range k : Finset ℕ), Complex.exp (↑(a i) * Complex.I) / ↑(((2 : ℕ) ^ i) : ℝ))
  suffices h_complex_val_ne_zero : (⟨∑ i in (Finset.range k : Finset ℕ), Real.cos (a i) / ((2 : ℕ) ^ i : ℝ), ∑ i in (Finset.range k : Finset ℕ), Real.sin (a i) / ((2 : ℕ) ^ i : ℝ)⟩ : ℂ) ≠ 0
  suffices h_coeffs_polar : ∃ (R  b : ℝ), 0 < R ∧ (∑ i in (Finset.range k : Finset ℕ), Real.cos (a i) / ((2 : ℕ) ^ i : ℝ)) = R * Real.cos  b ∧ (∑ i in (Finset.range k : Finset ℕ), Real.sin (a i) / ((2 : ℕ) ^ i : ℝ)) = R * Real.sin  b
  suffices h_y_rewritten_with_polar : ∃ (R  a : ℝ), 0 < R ∧ ∀ x, y x = R * Real.cos  a * Real.cos x - R * Real.sin  a * Real.sin x
  suffices h_y_collapsed_to_single_cos : ∃ (R  a : ℝ), 0 < R ∧ ∀ x, y x = R * Real.cos (x +  a)
  suffices h_y_is_sinusoid : ∃ (R a : ℝ), 0 < R ∧ (∀ x, y x = R * Real.cos (x - a))
  suffices h_roots_exist : ∃ (R a : ℝ), 0 < R ∧ y m = R * Real.cos (m - a) ∧ y n = R * Real.cos (n - a)
  suffices h_cos_zero : ∃ (R a : ℝ), 0 < R ∧ Real.cos (m - a) = 0 ∧ Real.cos (n - a) = 0
  suffices h_roots_in_pi_half_multiples : ∃ (a : ℝ) (t₁ t₂ : ℤ), m - a = (2 * (t₁ : ℝ) + 1) * Real.pi / 2 ∧ n - a = (2 * (t₂ : ℝ) + 1) * Real.pi / 2
  suffices h_m_minus_n_form : ∃ t₁ t₂ : ℤ, m - n = ((2 * (t₁ : ℝ) + 1) * Real.pi / 2) - ((2 * (t₂ : ℝ) + 1) * Real.pi / 2)
  suffices h_m_minus_n_simplified : ∃ t₁ t₂ : ℤ, m - n = (↑(t₁ - t₂) : ℝ) * Real.pi

  tauto  <;> ring
  rcases h_m_minus_n_form with ⟨s,t,h_form⟩
    <;> use s, t
    <;> field_simp at h_form ⊢
    <;> nlinarith [Real.pi_pos]
  obtain ⟨ a, t₁, t₂, heq₁, heq₂ ⟩ := h_roots_in_pi_half_multiples
  <;>
  exists t₁, t₂
  <;> linarith [heq₁, heq₂, Real.pi_pos ]
  rcases h_cos_zero with ⟨t, a, h, hcos, hsin⟩
  rw [Real.cos_eq_zero_iff] at hcos hsin
  rcases hcos with ⟨t₁, ht⟩  <;>  rcases hsin with ⟨t₂, hs⟩  <;>  exact ⟨a, t₁, t₂, ht,  hs⟩
  obtain ⟨R, a, hzero, h⟩ := h_roots_exist
  use R, a, hzero
  constructor <;> nlinarith [h₁]
  rcases h_y_is_sinusoid with ⟨R, a, hv, hi⟩ <;> exact ⟨R, a, hv, hi m, hi n⟩
  obtain ⟨R, a, h_R_a⟩ := h_y_collapsed_to_single_cos
  use R, -a, h_R_a.1, by (intro x; simp [h_R_a.2, cos_add, cos_sub])
  rcases h_y_rewritten_with_polar with ⟨R, a', h_R_pos, h_y_⟩
  use R, a', h_R_pos <;> intros <;> simp [h_y_, cos_add] <;> ring
  rcases h_coeffs_polar with ⟨R, θ, h_pos_R, equiv_iff₁, equiv_iff₂⟩ <;> (use R, θ; aesop)
  rewrite [Complex.ext_iff] at *
  let z := (∑ i ∈ Finset.range k, cos (a i) / ↑2 ^ i, ∑ i ∈ Finset.range k, sin (a i) / ↑2 ^ i)
  refine ⟨Complex.abs ((∑ i ∈ Finset.range k, Complex.exp (↑(a i) * Complex.I) / ↑(↑2 ^ i))),Complex.arg ((∑ i ∈ Finset.range k, Complex.exp (↑(a i) * Complex.I) / ↑(↑2 ^ i))),?_,?_,?_⟩ <;> aesop
  aesop (add safe Complex.ext_iff)
  apply lt_of_lt_of_le (by positivity) h_abs_ge_final
  linarith [h_abs_ge_by_rev_triangle, h_abs_tail_lt_one]
  rw [h_sum_split]
  clear h_abs_head h_tail_geom_sum_val h_y_sum_expanded h_sum_split h_complex_repr h_y_expand h_y_sum_split
  set z := Complex.exp ((a 0 : ℝ) * Complex.I) with h_z
  clear h_k_ge_one  h₀
  have  : z = Complex.exp ((a 0 : ℂ) * Complex.I)
  simpa [h_z] using h_z
  set w : ℂ := (∑ i ∈ Finset.Icc 1 (k - 1),
        Complex.exp ((a i : ℝ) * Complex.I) / ((2 : ℕ) : ℝ) ^ i )
  clear_value z
  clear_value w
  apply  le_of_sub_nonneg
  simp [Complex.abs_eq_sqrt_sq_add_sq] at h_abs_tail_le ⊢
  simp [this, Complex.exp_re, Complex.exp_im] at *
  rw [add_comm, ← sub_le_iff_le_add]
  apply le_of_sub_nonneg
  set x := ∑ i ∈ Finset.Icc 1 (k - 1), (Complex.exp ((a i:ℝ) * Complex.I) / 2 ^ i).re
  on_goal 1 => field_simp [Real.sqrt_le_left] at *
  apply le_of_sub_nonneg
  repeat' apply sub_nonneg_of_le <;> norm_num
  rw[← sub_le_iff_le_add']
  apply le_of_pow_le_pow_left two_ne_zero (by positivity)
  field_simp [h_abs_tail_le]
  let y := ∑ i in Finset.Icc 1 (k - 1), (Complex.exp ((a i : ℝ) * Complex.I) / 2 ^ i).im
  have hyp := sq_nonneg (cos (a 0) * y - sin (a 0) * x)
  nontriviality ℝ
  nlinarith [Real.sqrt_nonneg <| x ^ 2 + (∑ i ∈ Finset.Icc 1 (k - 1), (Complex.exp (↑(a i) * Complex.I) / 2 ^ i).im) ^ 2,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ x ^ 2 + (∑ i ∈ Finset.Icc 1 (k - 1), (Complex.exp (↑(a i) * Complex.I) / 2 ^ i).im) ^ 2), pow_two_nonneg (cos (a 0) - y), pow_two_nonneg (sin (a 0) - x),
              Real.sin_sq_add_cos_sq (a 0 :ℝ) ]
  apply lt_of_le_of_lt h_abs_tail_le
  exact sub_lt_self 1 <| one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) (k - 1))
  nth_rw 1 [←h_tail_geom_sum_val]
  convert Complex.abs.sum_le _ _
  simp [Complex.abs_eq_sqrt_sq_add_sq, h_abs_head]
  clear h₀ h₁ h₂ h₃ h_cos_add h_y_sum_expanded h_y_sum_split h_y_expand h_k_ge_one h_complex_repr h_sum_split h_abs_head
  induction k <;> simp [Finset.sum_Icc_succ_top, *]
  induction ‹ℕ› <;> simp_all [Finset.sum_Icc_succ_top]
  norm_num [← pow_succ, ← inv_div] <;> ring_nf
  rw [Complex.abs_exp_ofReal_mul_I]  <;> norm_num
  have  : Finset.range k = {0} ∪ Finset.Icc 1 (k-1)
  ext x<;> simp [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]
  first | omega | constructor
  rw [this,Finset.sum_union]
  simp [add_comm]
  aesop
  field_simp [Complex.exp_mul_I] <;> simp [Complex.ext_iff]
  classical
    constructor <;> simp [div_eq_mul_inv]
  congr with x <;> simp [mul_comm, mul_assoc, mul_left_comm]
  field_simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, mul_inv_rev,
    mul_comm, ← pow_mul]
  norm_cast at * <;>     simp [mul_pow] <;> ring
  simp [pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num ]
  exact Or.inl (by (rw [← pow_mul]; ring))
  simp [mul_comm, div_eq_mul_inv]
  congr with x  <;> simp [mul_comm ((2:ℝ)^x), Complex.cos_ofReal_re,Complex.sin_ofReal_re] <;> ring
  field_simp [mul_right_comm (sin (a x))] <;> ring
  simp [ mul_assoc, mul_comm, mul_left_comm]
  simp [← mul_assoc ]
    <;> norm_cast
    <;> (try simp)
  exact Or.inl (by rw [← mul_pow]; ring)
  linarith [show (0 : ℕ) < k from h₀]
  intros x  <;> have h₁ := h_y_sum_split x <;> simp [Finset.sum_mul, mul_assoc] at * <;> ring
  convert h₁ using 2 <;> field_simp <;>
  abel
  rintro x <;> try rw [h_y_sum_expanded] <;> simp [Finset.sum_sub_distrib]
  simp [div_eq_mul_inv, Finset.sum_sub_distrib, mul_assoc]
  rewrite [← Finset.sum_sub_distrib]
  focus all_goals
    congr
    with x _
    ring
  simp_all [Finset.sum_congr]
  intro w b<;> simp [cos_add]
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


theorem mathd_numbertheory_764
  (p : ℕ)
  (h₀ : Nat.Prime p)
  (h₁ : 7 ≤ p) :
  ∑ k in Finset.Icc 1 (p-2), ((k: ZMod p)⁻¹ * ((k: ZMod p) + 1)⁻¹) = 2 := by'

  suffices h_all_k_ne_zero : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), (k : ZMod p) ≠ 0
  suffices h_lhs_times_k : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), (k : ZMod p) * ((k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = ((k : ZMod p) + 1)⁻¹
  suffices h_rhs_times_k_distrib : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), (k : ZMod p) * ((k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹) = 1 - (k : ZMod p) * ((k : ZMod p) + 1)⁻¹
  suffices h_rhs_simplified : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), 1 - (k : ZMod p) * ((k : ZMod p) + 1)⁻¹ = ((k : ZMod p) + 1)⁻¹
  suffices h_sides_equal_after_mul : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), (k : ZMod p) * ((k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = (k : ZMod p) * ((k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹)
  suffices h_partial_fraction : ∀ k ∈ (Finset.Icc 1 (p - 2) : Finset ℕ), ((k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹
  suffices h_sum_rewritten : ∑ k in (Finset.Icc 1 (p - 2) : Finset ℕ), ((k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = ∑ k in (Finset.Icc 1 (p - 2) : Finset ℕ), ((k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹)
  suffices h_sum_rewritten : ∑ k in (Finset.Icc 1 (p - 2) : Finset ℕ), ((k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹) = ∑ k in Finset.Icc 1 (p - 2), (((k : ℕ) : ZMod p)⁻¹ - ((((k + 1) : ℕ) : ZMod p)⁻¹))
  suffices h_telescope_applied : ∑ k in Finset.Icc 1 (p - 2), (((k : ℕ) : ZMod p)⁻¹ - ((((k + 1) : ℕ) : ZMod p)⁻¹)) = ((1 : ZMod p)⁻¹) - ((((p - 2) + 1 : ℕ) : ZMod p)⁻¹)
  suffices h_simplify_rhs : ((((p - 2) + 1 : ℕ) : ZMod p)⁻¹) = (((p - 1) : ℕ) : ZMod p)⁻¹
  suffices h_telescoping_sum : ∑ k in (Finset.Icc 1 (p - 2) : Finset ℕ), ((k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹) = (1 : ZMod p)⁻¹ - ((p - 1 : ZMod p))⁻¹
  suffices h_p_minus_one_eq_neg_one : ((p - 1) : ZMod p) = -1
  suffices h_p_minus_one_inv_eq_neg_one : ((p - 1) : ZMod p)⁻¹ = -1
  suffices h_one_inv_eq_one : (1 : ZMod p)⁻¹ = 1
  suffices h_final_calc : (1 : ZMod p) - (-1 : ZMod p) = 2

  all_goals aesop?
  norm_num
  field_simp
  rw [h_p_minus_one_eq_neg_one]
  have := Fact.mk h₀
  field_simp
  cases p with
  | zero => contradiction
  | succ n => simp [Nat.Prime.ne_one h₀]
  convert h_telescope_applied
  cases p
  norm_num [Nat.zero_eq] at *
  simp only [Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one]
  cases ‹ℕ› <;> simp at * <;> aesop
  congr 3 <;> omega
  clear h_sum_rewritten
  clear h_partial_fraction h_sum_rewritten
  clear h_sides_equal_after_mul h_rhs_simplified h_all_k_ne_zero h_lhs_times_k h_rhs_times_k_distrib
  induction (p - 2) <;> simp_all
  rw [Finset.sum_Icc_succ_top _, Finset.sum_Icc_succ_top] <;> aesop
  rw [← sub_sub, sub_eq_iff_eq_add]
  any_goals simp [sub_add_cancel]
  linear_combination a + (1 - 1)
  simp_rw [Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl h_partial_fraction
  intro k h_k_in_Icc_p_1
  have h_sides_equal := h_sides_equal_after_mul k h_k_in_Icc_p_1
  rcases eq_or_ne k 0 with (rfl | h_ne_zero)
  aesop
  let kk : ZMod p := (k:ℤ)
  have hp : Fact p.Prime := ⟨h₀⟩
  have hk0  : (k : ZMod p) ≠ 0
  all_goals aesop
  apply mul_left_cancel₀ hk0 (by simp [h_sides_equal])
  simp_all[inv_mul_eq_div, mul_div_assoc]
  intro k hk
  have mul_inv_eq_inv_mul (a : ZMod p) (h : a ≠ 0)  : a⁻¹ * (a : ZMod p) = 1
  rw [mul_comm]
  have hp : Fact p.Prime := ⟨h₀⟩
  simp [mul_inv_eq_one,h]
  have : ((k : ZMod p) + 1)⁻¹ * ((k : ZMod p) + 1 ) = 1
  apply mul_inv_eq_inv_mul
  rw [Finset.mem_Icc, Nat.add_one_le_iff] at hk
  contrapose! h_all_k_ne_zero
  use k + 1
  constructor
  have h_add_eq_zero_iff := ZMod.natCast_zmod_eq_zero_iff_dvd (k + 1) p
  refine Finset.mem_Icc.mpr ?_
  norm_cast at h_all_k_ne_zero h_add_eq_zero_iff
  have hhk : k ≥ 1
  linarith
  constructor
  linarith only [hhk]
  apply Nat.le_sub_of_add_le
  by_contra
  simp_all_arith
  absurd h_add_eq_zero_iff
  have hhk₂ : k + 1 ≤ p - 1
  rewrite [Nat.le_sub_iff_add_le]
  have hhk₂: 2 ≤ k + 1
  linarith
  have hhk₃:= _root_.add_le_add ((Nat.le_succ 1) : 1 ≤ 2) hhk₂
  revert p hhk₃
  aesop (add simp [hhk₂])
  have hhk₄ : k + 1 < 7 + (k + 1)
  linarith
  omega
  linarith
  rw [Nat.dvd_iff_mod_eq_zero]
  nth_rw 1 [← Nat.div_add_mod (k + 1) p]
  have h_pp : p % p = 0 := Nat.mod_self p
  rw [add_comm] at *
  have _  : p > 0
  exact Nat.Prime.pos h₀
  revert h_add_eq_zero_iff
  aesop
  have u : (k + 1) % p = k + 1
  apply Nat.mod_eq_of_lt
  omega
  have kk : k + 1 = 0
  linarith
  simp [Nat.add_eq_zero_iff] at kk
  rw [Nat.cast_add, Nat.cast_one]
  assumption
  nth_rw 1 [← this]
  have this₂  : (k : ZMod p) * ((k : ZMod p) + 1)⁻¹ * ((k : ZMod p) + 1) = (k : ZMod p)
  rw [mul_assoc, this,mul_one]
  have lhs_eq_one := Eq.symm <| this
  have hh : (k: ZMod p) * ((k: ZMod p) +  1)⁻¹ = (((k: ZMod p) +  1)⁻¹ * (k: ZMod p))
  ring_nf
  rw [hh]
  nth_rw 2 [←mul_one ((k:ZMod p) + 1)⁻¹]
  ring_nf
  intro k hind
  rcases h₀.eq_two_or_odd with hs | hs
  rw [ hs ] at h₁ <;> omega
  rcases eq_or_ne k 0 with rfl | hd
  group <;> simp at * <;> norm_num at * <;> apply h_all_k_ne_zero 0
  field_simp  at *
  field_simp[hs] at * <;> ring_nf
  field_simp [h₀.ne_zero, h₁] at h_all_k_ne_zero h_lhs_times_k ⊢ <;> ring_nf
  replace h₀  : Fact p.Prime := ⟨h₀⟩
  apply mul_inv_cancel
  aesop
  intro k hind
  replace h₀ : Fact p.Prime := ⟨h₀⟩
  have := h_all_k_ne_zero k hind
  rcases eq_or_ne (↑k + 1 : ZMod p) 0 with h1 | h1
  field_simp
  simp [*]
  field_simp
  intro y _
  any_goals aesop (add simp [Finset.mem_Icc])
  apply Nat.Prime.not_dvd_one h₀
  apply_fun ZMod.val at a
  rw [ZMod.val_zero, ZMod.val_natCast]  at a
  have q  : p ∣ y
  refine Nat.dvd_of_mod_eq_zero a <;> assumption
  classical
    have : y ≥ p := Nat.le_of_dvd left q
    omega
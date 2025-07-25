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


theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2
  (n : ℕ)
  (h₀ : 0 < n) :
  (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := by'

  suffices h_val_two_plus_one : ∀ k : ℕ, 1 ≤ k → padicValNat 2 (3 ^ (2 ^ k) + 1) = 1
  suffices h_factorization_relation : ∀ k : ℕ, 1 ≤ k → 3 ^ (2 ^ (k + 1)) - 1 = (3 ^ (2 ^ k) - 1) * (3 ^ (2 ^ k) + 1)
  suffices h_padic_val_recurrence : ∀ k : ℕ, 1 ≤ k → padicValNat 2 (3 ^ (2 ^ (k + 1)) - 1) = padicValNat 2 (3 ^ (2 ^ k) - 1) + 1
  suffices h_padic_val_base_case : padicValNat 2 (3 ^ (2 ^ 1) - 1) = 3
  suffices h_padic_val_main_term : padicValNat 2 (3 ^ (2 ^ n) - 1) = n + 2
  suffices h_factorization_form : ∃ k : ℕ, 3 ^ (2 ^ n) - 1 = 2 ^ (n + 2) * k ∧ k % 2 = 1
  suffices h_final_mod_property : ∀ k : ℕ, k % 2 = 1 → (2 ^ (n + 2) * k) % (2 ^ (n + 3)) = 2 ^ (n + 2)

  obtain ⟨m, hm₁, hm₂⟩ := h_factorization_form
  rw [hm₁, h_final_mod_property m hm₂]
  intro k hind
  simp [Nat.mul_mod_mul_left, Nat.pow_mod,
  Nat.pow_succ, hind]
  have h₀' := h₀
  have h_two_pow : 2 ^ (n + 2) ∣ 3 ^ 2 ^ n - 1
  revert h_padic_val_main_term
  cases n <;> simp_all
  set k := ‹ℕ›
  intro h_padic_val_k_succ
  convert_to 2 ^ padicValNat 2 (3 ^ 2 ^ (k + 1) - 1) ∣ 3 ^ 2 ^ (k + 1) - 1
  simp [h_padic_val_k_succ]
  apply pow_padicValNat_dvd
  obtain ⟨c, hc⟩ := h_two_pow
  refine ⟨c, hc, ?_⟩ <;> norm_num
  induction h₀'
  rw [eq_comm] at hc
  revert hc h_padic_val_main_term
  norm_num [h_padic_val_base_case]
  intro _ hc  <;> aesop
  rename_i k hk ih
  cases' k with k
  cases hk
  simp_all [pow_succ]
  rw [padicValNat.mul] at h_padic_val_main_term
  simp [padicValNat.prime_pow, padicValNat.mul] at h_padic_val_main_term
  rcases h_padic_val_main_term with h_eq_zero | h_eq_odd
  simp [h_eq_zero] at hc
  have h_3_pow_gt_one  : 1 < 3 ^ (2 ^ k * 2 * 2)
  norm_num
  omega
  exact h_eq_odd
  refine Ne.symm (NeZero.ne' (2 ^ k * 2 * 2 * 2 * 2))
  intro hc'
  simp [hc'] at h_padic_val_main_term
  induction' n using Nat.case_strong_induction_on with k' h_ind
  cases h₀
  specialize h_padic_val_recurrence k'
  rcases k' with (_ | _ | k₂)
  simp [padicValNat] at * <;> norm_cast
  simp_all [pow_succ, mul_add]
  simp [h_ind _, h_padic_val_recurrence, add_assoc]
  norm_num [padicValNat]
  convert rfl with _ h_prime
  simp [padicValNat] at * <;> norm_cast
  convert rfl
  native_decide
  intro k h_one_le_k
  repeat rw [h_factorization_relation k h_one_le_k]
  specialize h_val_two_plus_one k h_one_le_k
  convert_to padicValNat 2 ((3 ^ 2 ^ k - 1) * (3 ^ 2 ^ k + 1)) = padicValNat 2 (3 ^ 2 ^ k - 1) + padicValNat 2 (3 ^ 2 ^ k + 1)
  rw [h_val_two_plus_one]
  apply padicValNat.mul
  any_goals
    rw [Nat.sub_ne_zero_iff_lt]
    norm_num
  apply Ne.symm (NeZero.ne' (3 ^ 2 ^ k + 1))
  intro k h_two_pow_k
  simp [_root_.pow_add, _root_.pow_mul, Nat.mul_sub_left_distrib]
  zify [pow_two]
  induction h_two_pow_k <;> simp [*, pow_add, pow_mul, Int.ofNat_mul]
  simp [Nat.cast_sub, Nat.cast_pow, sq]
  ring_nf <;> omega
  intro u hu
  induction u <;> simp_all [pow_two, padicValNat]
  simp [← pow_mul, multiplicity, h₀]
  apply le_antisymm
  apply Nat.find_min'
  simp [pow_add, pow_mul, pow_one, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_mod]
  simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  cases' ‹ℕ› with n
  norm_num<;> decide
  simp [Nat.pow_mod, _root_.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
  simp [Nat.mul_mod, Nat.pow_mod]
  norm_num [pow_mul, pow_add, pow_one, Nat.mul_mod, Nat.pow_mod]
  simp [Nat.pow_mod] <;> aesop
  rw [ Nat.pow_mod] at a_1
  classical
    have : 3 ^ 2 ^ n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : 3 ^ 2 ^ n % 4 <;> simp_all (config := {decide := true})
  apply Nat.one_le_iff_ne_zero.mpr
  contrapose! h₀
  rw [Nat.find_eq_iff] at h₀
  simp_all [Nat.one_le_of_lt]
  simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h₀
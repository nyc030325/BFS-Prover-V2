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


theorem induction_pord1p1on2powklt5on2
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k in Finset.Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 := by'

  suffices h_n_ge_2_lemma : ∀ n : ℕ, 2 ≤ n → (∏ k in (Finset.Icc 1 n : Finset ℕ), (1 + (1:ℝ) / 2^k)) ≤ (5/2) * (1 - 1/2^n)
  suffices h_lemma_base_case : (∏ k in (Finset.Icc 1 2 : Finset ℕ), (1 + (1:ℝ) / 2^k)) = (5/2) * (1 - 1 / 2^2)
  suffices h_prod_step (n : ℕ) (hn : 1 ≤ n) : (∏ k in (Finset.Icc 1 (n + 1) : Finset ℕ), (1 + (1:ℝ) / 2^k)) = (∏ k in (Finset.Icc 1 n : Finset ℕ), (1 + (1:ℝ) / 2^k)) * (1 + 1 / 2^(n+1))
  suffices h_algebraic_step (n : ℕ) (hn : 2 ≤ n) : ((5:ℝ)/2 * (1 - 1/2^n)) * (1 + 1/2^(n+1)) ≤ (5/2) * (1 - 1/2^(n+1))
  suffices h_algebraic_expansion (n : ℕ) : (1 - 1/2^n) * (1 + 1/2^(n+1)) = 1 - 1/2^(n+1) - 1/2^(2*n+1)
  suffices h_n1_case : (∏ k in (Finset.Icc 1 1 : Finset ℕ), (1 + (1:ℝ) / 2^k)) = 3/2
  suffices h_final_inequality (n : ℕ) (h_n_pos : 0 < n) : (5/2 : ℝ) * (1 - 1/2^n) < 5/2
  
  rcases em (2 ≤ n) with (h_n_ge_2 | h_n_lt_2)
  have h_almost_done := h_n_ge_2_lemma n h_n_ge_2
  linarith [h_final_inequality n h₀ ,h_almost_done]
  interval_cases n <;> norm_num at * <;> linarith
  cases' n with n <;> simp_all [-one_div,pow_succ] <;> norm_num
  simp only [Finset.Icc_self,Finset.prod_singleton,Nat.div_self,add_zero,one_div]
  norm_num [Nat.div_eq_of_lt,pow_one]
  rcases n.eq_zero_or_pos with (rfl | h_pos) <;> simp [Nat.div_eq_of_lt] <;> ring_nf
  have h_inductive_bound := h_n_ge_2_lemma
  have h_bound : ∏ k ∈ Finset.Icc 1 6, (1 + 1 / 2 ^ k) ≤ 5 / 2 * (1 - 1 / 2 ^ 6)
  all_goals norm_num [Finset.Icc,div_eq_mul_inv]
  simp only [LocallyFiniteOrder.finsetIcc] at * <;> norm_num
  norm_num [List.range',List.map,List.prod] <;> simp
  classical norm_num [Finset.prod_Icc_succ_top] at h_bound
  specialize h_inductive_bound 2
  all_goals ring_nf at *
  specialize h_n_ge_2_lemma 16 (by norm_num)
  simp [Finset.prod_Icc_succ_top,← h_prod_step] at *
  norm_num [mul_comm] at h_lemma_base_case h_n_ge_2_lemma ⊢
  cases h_n_ge_2_lemma <;> aesop
  have h₁ := h_algebraic_step 2 (by decide)
  norm_num1 at h₁ <;> norm_cast
  have h_pro := h_algebraic_step 2
  norm_num at h_pro <;>contrapose h_pro
  have h_le := h_algebraic_step 2
  norm_num [pow_succ] at * <;> native_decide
  cases n <;> norm_num[Nat.div_eq_of_lt] <;> any_goals norm_cast <;>omega
  have h_two_pow_succ : 0 < 2 ^ (n + 1)
  positivity
  have h_two_pow_ge_int_one : 0 < 2 ^ (n + 1)
  exact h_two_pow_succ
  field_simp [pow_succ]
  apply_rules [Nat.div_le_div_left,le_of_not_gt]
  field_simp [Nat.div_eq_of_lt,Nat.div_eq_of_lt] <;> ring_nf <;> norm_num
  simp [inv_mul_eq_div,div_add_div,div_le_iff] <;> norm_cast <;> ring
  induction' hn with n' hd
  field_simp <;> norm_num <;> linarith
  simp [Nat.succ_eq_add_one,pow_add,pow_mul]
  ring_nf at *
  simp [← pow_mul]
  rcases n' with (_ | _ | n') <;> norm_cast <;> ring_nf
  simp [Rat.divInt_eq_div]
  rw [← sub_nonneg ]
  norm_num <;> field_simp [pow_succ] <;> ring_nf <;> norm_num
  simp [Finset.prod_Icc_succ_top _,Nat.div_eq_of_lt]
  ring <;> norm_num [Finset.Icc,Nat.div_eq_of_lt]
  convert rfl <;> norm_num [LocallyFiniteOrder.finsetIcc]
  try norm_num [List.range',List.map]
  intro y hem
  induction' hem with z h
  norm_num [pow_succ,Finset.Icc]
  dsimp [LocallyFiniteOrder.finsetIcc] <;> norm_num [add_comm,mul_comm,mul_add,add_mul]
  norm_num [List.map,List.range',Nat.pow_succ,List.prod_cons,List.prod_nil,one_add_one_eq_two]
  rw [Finset.prod_Icc_succ_top,mul_comm] <;> try linarith
  cases z<;> norm_num at h ⊢
  aesop (add simp [Finset.prod_Icc_succ_top,add_comm])
  ring_nf at *
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1/2) n_1,pow_pos (by norm_num : (0 : ℝ) < 1/4) n_1]
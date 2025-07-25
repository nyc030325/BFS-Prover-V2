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


theorem imo_2001_p6
  (a b c d : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : d < c)
  (h₂ : c < b)
  (h₃ : b < a)
  (h₄ : a * c + b * d = (b + d + a - c) * (b + d + c - a)) :
  ¬ Nat.Prime (a * b + c * d) := by'

  suffices h_rearranged : a^2 - a * c + c^2 = b^2 + b * d + d^2
  suffices h_identity_factored : a * c * (b ^ 2 + b * d + d ^ 2 - (a ^ 2 - a * c + c ^ 2)) = 0
  suffices h_identity : (a * c * (b ^ 2 + b * d + d ^ 2 - (a ^ 2 - a * c + c ^ 2)) = 0) → (a * b + c * d) * (a * d + b * c) = (a * c + b * d) * (a^2 - a * c + c^2)
  suffices h_dvd_prod : a * b + c * d ∣ (a * c + b * d) * (a^2 - a * c + c^2)
  suffices h_prime_implies_dvd_cases1 : Nat.Prime (a * b + c * d) → (a * b + c * d ∣ a * c + b * d) ∨ (a * b + c * d ∣ a^2 - a * c + c^2)
  suffices h_exists_k_and_eq1 : (a * b + c * d ∣ a^2 - a * c + c^2) → ∃ k : ℕ, a^2 - a * c + c^2 = k * (a * b + c * d)
  suffices h_exists_k_and_eq2 : (a * b + c * d ∣ a^2 - a * c + c^2) → ∃ k : ℕ, a * d + b * c = k * (a * c + b * d)
  suffices h_dvd_implies_dvd : (a * b + c * d ∣ a^2 - a * c + c^2) → (a * c + b * d ∣ a * d + b * c)
  suffices h_prime_implies_dvd_cases2 : Nat.Prime (a * b + c * d) → (a * b + c * d ∣ a * c + b * d) ∨ (a * c + b * d ∣ a * d + b * c)
  suffices h_pos_ac_bd : 0 < a * c + b * d
  suffices h_pos_S : 0 < a * d + b * c
  suffices h_case1_implies_le : (a * b + c * d ∣ a * c + b * d) → a * b + c * d ≤ a * c + b * d
  suffices h_equality1 : (a - d) * (b - c) = a * b + c * d - a * c - b * d
  suffices h_inequality1_rearranged : a * b + c * d ≤ a * c + b * d ↔ (a - d) * (b - c) ≤ 0
  suffices h_contradiction1 : 0 < (a - d) * (b - c)
  suffices h_case2_implies_le : (a * c + b * d ∣ a * d + b * c) → a * c + b * d ≤ a * d + b * c
  suffices h_equality2 : (c - d) * (a - b) = a * c + b * d - a * d - b * c
  suffices h_inequality2_rearranged : a * c + b * d ≤ a * d + b * c ↔ (c - d) * (a - b) ≤ 0
  suffices h_contradiction2 : 0 < (c - d) * (a - b)
  suffices h_not_dvd_case2 : ¬ (a * b + c * d ∣ a * c + b * d)
  suffices h_not_dvd_case1 : ¬ (a * c + b * d ∣ a * d + b * c)
  suffices h_absurd_if_prime : Nat.Prime (a * b + c * d) → False
  
  classical
    tauto
  unhygienic aesop
  focus any_goals
    first 
    | omega 
    | aesop
  focus any_goals
    first
    | omega
    | aesop
  apply Nat.mul_pos <;> apply Nat.sub_pos_of_lt <;> tauto
  omega
  zify [h₀.1, h₀.2.1, h₀.2.2, h₀.2.2.1, h₁, h₂, h₃] at h_equality1 ⊢
  rw [sub_mul]
  norm_num at * <;> ring_nf
  focus repeat' rw [Nat.cast_sub]
  simp <;> (ring_nf)
  nlinarith [(show d ≤ c from by omega)]
  simp (config := { contextual := true }) [mul_add, add_mul] at *
  apply le_tsub_of_add_le_right <;>
  focus repeat' nlinarith
  exact fun H => Nat.le_of_dvd h_pos_S H
  apply Nat.mul_pos
  apply Nat.sub_pos_of_lt
  linarith
  exact Nat.zero_lt_sub_of_lt h₂
  constructor <;>
  (
      intro h_w_iff
      rw [h_equality1] at *
      omega
  )
  zify [h₃.le, h₂.le, h₁.le]
  cases h₀
  norm_num [sub_eq_add_neg, mul_add, add_mul]
  repeat rw [Int.ofNat_sub]
  field_simp <;> norm_num <;> nlinarith
  nlinarith
  rw[Nat.le_sub_iff_add_le] <;> try nlinarith
  valid
  intros h_dvd  <;>  apply Nat.le_of_dvd  <;>  try assumption
  nlinarith only[h₀.1,h₀.2.2.1,h₀.2]
  set_option maxSynthPendingDepth 2 in
    nlinarith
  case _ =>
    intro h_prime
    cases' h_prime_implies_dvd_cases1 h_prime with h_dvd h_dvd
    . exact Or.inl h_dvd
    . exact Or.inr (h_dvd_implies_dvd h_dvd)
  intro h_dvd
  cases' h_dvd with j hj
  obtain ⟨k, hr⟩ := h_exists_k_and_eq2 (by rw [hj]; simp [mul_dvd_mul_left])
  erw [hr]
  exact Nat.dvd_mul_left (a * c + b * d) k
  focus all_goals intros; aesop
  obtain ⟨e, dvd⟩ := a_1
  refine' ⟨e, _⟩
  revert b c d a
  rintro a b c d h₁ h₂ h₃ h₀
  unhygienic aesop
  revert h_dvd_prod
  aesop
  simp_all [mul_add, add_mul, add_assoc, add_comm, add_left_comm]
  first | nlinarith | rw [mul_comm] at *
  rintro ⟨k, hk⟩
  refine ⟨k, by rw [hk]; ring⟩
  intro hprime
  exact (Nat.Prime.dvd_mul hprime).1 h_dvd_prod
  first | linarith | apply h_identity at h_identity_factored
  exact ⟨ a*d + b*c, h_identity_factored.symm ⟩
  first |nlinarith|rw [mul_comm]
  first
  |nlinarith
  |simp_all
  let s := b + d
  revert h₄
  revert h_rearranged
  contrapose! h₀
  contrapose! h₀
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  rw [eq_comm]
  set s' := a - c
  unhygienic aesop
  have symm_1 := b * c * d + a * c * d + a * b * d + a * b * c
  symm
  zify at *
  rw [← __1]
  repeat rw [add_mul] at *
  rewrite [add_comm] at *
  simp [sq] at *
  erw [Int.ofNat_sub] at *
  rw [add_comm,mul_comm,mul_comm,mul_comm,mul_comm,mul_comm] <;> ( ring_nf )
  ring_nf at *
  replace __1 := congr_arg (fun x => x * (c : ℤ)) __1
  simp [mul_comm, mul_assoc, mul_left_comm]
  ring_nf at* <;> try omega
  rw [add_comm] at *
  first |nlinarith|simp [sq] at *
  first |nlinarith|symm
  first
  | nlinarith
  | ring
  | done
  norm_cast  at *
  simp [Int.subNatNat_eq_coe] at *
  nlinarith [mul_pos hb hc, mul_pos hb hd, mul_pos hc hd] <;>
  ring
  omega <;> norm_cast at * <;>simp_all
  nlinarith [ha, hb, hc, h₁,h₂]
    <;> norm_cast at * <;> nlinarith
  nlinarith [ha, hb, hc, h₁.le, h₂.le, h₃.le]
  simp [h_rearranged, mul_nonneg, *]
  revert h₁ h₂ h₃ h₄ a b c d
  rintro a b c d ⟨ha, hb, hc, hd⟩ hcd hbc hab H
  revert H
  aesop (add simp [add_comm, add_left_comm, add_assoc])
  zify [ha, hb, hc, hd, hcd, hbc, hab] at H ⊢
  rw [add_comm] at H
  rw [add_comm, sq]
  rw [add_comm] at*
  simp [sq, Nat.cast_sub, ha, hb, hc, hd, hcd, hbc, hab, mul_comm, mul_assoc, mul_left_comm] at H ⊢
  rw [← sub_eq_zero] at H
  repeat rw [Nat.cast_sub] at *
  push_cast at H ⊢
  first |nlinarith|rw [eq_comm] at H
  by_contra L
  rw [Nat.add_comm] at L
  simp [not_le] at L
  ring_nf at H ⊢
  ring_nf at *
  have : b + d + c - a = 0 := by omega
  simp [this, ha.ne'] at H
  first | nlinarith | norm_cast at *
  omega
  gcongr
  linarith
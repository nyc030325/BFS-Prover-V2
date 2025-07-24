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


theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown
  (m n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ x, f x = 4^x + 6^x + 9^x)
  (h₁ : 0 < m ∧ 0 < n)
  (h₂ : m ≤ n) :
  f (2^m)∣f (2^n) := by'

  suffices h_geom_prog_rel : ∀ y : ℕ, 4^y * 9^y = (6^y)^2
  suffices h_inequality : ∀ y : ℕ, 6^y ≤ 4^y + 9^y
  suffices h_f_identity_expanded : ∀ y : ℕ, f (2 * y) = (4^y + 6^y + 9^y) * (4^y + 9^y - 6^y)
  suffices h_f_identity : ∀ y : ℕ, f (2 * y) = f y * (4^y + 9^y - 6^y)
  suffices h_dvd_double : ∀ y : ℕ, f y ∣ f (2 * y)
  suffices h_chain : ∀ i : ℕ, f (2^i) ∣ f (2^(i+1))
  suffices h_dvd_le : ∀ i j : ℕ, i ≤ j → f (2^i) ∣ f (2^j)
  
  case _ =>
    exact h_dvd_le m n h₂
  intro k l hkl
  induction' hkl with q hq ih
  apply Nat.dvd_refl (f (2 ^ k))
  apply Dvd.dvd.trans ih (h_chain q )
  intro i
  have ha := h_dvd_double (2 ^ i)
  norm_num [pow_succ, mul_comm, mul_assoc, mul_left_comm] at * <;> aesop
  intro a_1
  have h := h_f_identity a_1
  simp [h, Nat.dvd_iff_mod_eq_zero,Nat.mod_eq_zero_of_dvd]
  intro z
  specialize h_f_identity_expanded z
  nth_rw 1 [h_f_identity_expanded, h₀ z]
  intro z
  have help := h_geom_prog_rel z
  simp [h₀, ← pow_mul, ← pow_add]
  simp [pow_mul, mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] at help ⊢
  zify [pow_two, pow_add]
  zify [h_inequality z]
  zify at help ⊢ <;> nlinarith
  rintro (_|y) <;> norm_num
  let h_sq := h_geom_prog_rel (y + 1)
  nlinarith [ pow_pos (by norm_num : 0 < 4) (y + 1),
              pow_pos (by norm_num  : 0 < 6) (y + 1),
              pow_pos (by norm_num  : 0 < 9) (y + 1)]
  intro y <;> ring
  <;> norm_cast
  induction y <;>
    simp_all [pow_add, pow_mul, mul_comm, mul_assoc, mul_left_comm]
  ring
  simp_all [pow_mul]
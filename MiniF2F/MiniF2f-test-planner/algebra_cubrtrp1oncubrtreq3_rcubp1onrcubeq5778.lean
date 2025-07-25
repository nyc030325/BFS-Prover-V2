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


theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778
  (r : ℝ) (hr : r ≥ 0)
  (h₀ : r^(1 / 3: ℝ) + 1 / r^(1 / 3: ℝ) = 3) :
  r^3 + 1 / r^3 = 5778 := by'

  suffices h₁ : (r^(1 / 3: ℝ) + 1 / r^(1 / 3: ℝ))^3 = 3^3
  suffices h₂ : (r^(1 / 3: ℝ))^3 + 1 / (r^(1 / 3: ℝ))^3 + 3 * (r^(1 / 3: ℝ) + 1 / r^(1 / 3: ℝ)) = 27
  suffices h₃ : r + 1 / r + 3 * 3 = 27
  suffices h₄ : r + 1 / r = 18
  suffices h₅ : (r + 1 / r)^3 = 18^3
  suffices h₆ : r^3 + 1 / r^3 + 3 * (r + 1 / r) = 5832
  suffices h₇ : r^3 + 1 / r^3 + 3 * 18 = 5832
  suffices h₈ : r^3 + 1 / r^3 = 5778
  
  classical { exact_mod_cast h₈ }
  linarith [(by positivity : 0 ≤ 3)]
  nlinarith [h₃, h₂, h₁, h₀, h₆]
  rw [pow_three] at h₅ <;> ring
  by_cases hr : r = 0 <;> field_simp [hr] at * <;> nlinarith
  rw [pow_three] at* <;> norm_cast
  field_simp [h₄, pow_three]
  nlinarith [h₀, h₁, h₂, h₃] <;> rify at *
  simp_all [← Real.rpow_natCast]
  simp_all [pow_three, add_mul, add_comm, add_assoc, add_left_comm]
  have h0' := congr_arg (fun x => x * x) h₀
  simp only [mul_add, add_mul, add_pow] at h0'
  rcases eq_or_lt_of_le hr with (rfl | h_pos) <;> field_simp [*, pow_three] at *
  nlinarith [sq_nonneg (r ^ (1 / 3) * r ^ (1 / 3) - r ^ (1 / 3)),sq_nonneg (r ^ (1 / 3) * r ^ (1 / 3) - 2),sq_nonneg (r ^ (1 / 3) -1)]
  rw [h₀]
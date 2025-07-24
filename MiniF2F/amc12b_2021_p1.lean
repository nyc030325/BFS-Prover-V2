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


theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
  S.card = 19 := by'

  suffices h₁ : (9 : ℝ) < 3 * Real.pi ∧ 3 * Real.pi < (10 : ℝ)
  suffices h₂ : ∀ (n : ℕ), (↑n : ℝ) < 3 * Real.pi ↔ n ≤ 9
  suffices h₃ : ∀ (x : ℤ), x ∈ S ↔ Int.natAbs x ≤ 9
  suffices h₄ : ∀ (x : ℤ), Int.natAbs x ≤ 9 ↔ -9 ≤ x ∧ x ≤ 9
  suffices h₅ : ∀ (x : ℤ), -9 ≤ x ∧ x ≤ 9 ↔ x ∈ (Finset.Icc (-9) 9 : Finset ℤ)
  suffices h₆ : S = (Finset.Icc (-9) 9 : Finset ℤ)
  suffices h₇ : (Finset.Icc (-9) 9 : Finset ℤ).card = Int.toNat (9 - (-9)) + 1
  suffices h₈ : Int.toNat (9 - (-9)) + 1 = 19
  
  rw [h₆] <;> solve |rfl
  congr <;>
    ring_nf <;>
    simp
  classical exact rfl
  all_goals (
    ext x
    simp only [*] at *
    aesop
  )
  simp [← and_comm]
  exact fun x ↦ ⟨fun h ↦ by omega, fun h ↦ by omega⟩
  intro x <;> rewrite [h₀ x]
  cases x
  simp [h₂] <;> conv => rw [Int.natAbs_ofNat] <;> norm_cast
  try rewrite [← h₂]
  rfl <;> (simp_all; norm_cast)
  all_goals aesop (add simp [Nat.cast_lt])
  have : 0 < 3 * Real.pi := by positivity
  have : (n : ℝ) < 10 := by nlinarith [Real.pi_le_four]
  norm_cast  at *  <;> linarith
  interval_cases n <;> norm_num [left]  <;> linarith [Real.pi_gt_three]
  repeat' constructor <;> norm_num [ Real.pi_gt_three]
  contrapose! h₀
  by_cases hexists : ∃ x : ℤ, x ∈ S ∧ 3 * Real.pi ≤ ↑|x|
  cases' hexists with a hall
  first | exact ⟨a,by aesop⟩ | exact ⟨-a,by aesop⟩
  by_contra hxless
  first
  | nlinarith [Real.pi_gt_three]
  | simp_all
  have : Real.pi < 3.1416 := Real.pi_lt_31416
  all_goals ring_nf at * <;> norm_num1
  nlinarith [Real.pi_pos]
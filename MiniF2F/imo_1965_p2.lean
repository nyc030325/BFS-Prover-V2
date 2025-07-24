import Mathlib
import Aesop

open BigOperators Real Nat Topology

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


theorem imo_1965_p2
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0) :
  x = 0 ∧ y = 0 ∧ z = 0 := by'

  suffices abs_inequality_from_eq1 : |a 0 * x| ≤ |a 1 * y| + |a 2 * z|
  suffices abs_inequality_from_eq2 : |a 4 * y| ≤ |a 3 * x| + |a 5 * z|
  suffices abs_inequality_from_eq3 : |a 8 * z| ≤ |a 6 * x| + |a 7 * y|
  suffices x_max_le_self : (|x| ≥ |y| ∧ |x| ≥ |z|) → |a 0| * |x| ≤ (|a 1| + |a 2|) * |x|
  suffices y_max_le_self : (|y| ≥ |x| ∧ |y| ≥ |z|) → |a 4| * |y| ≤ (|a 3| + |a 5|) * |y|
  suffices z_max_le_self : (|z| ≥ |x| ∧ |z| ≥ |y|) → |a 8| * |z| ≤ (|a 6| + |a 7|) * |z|
  suffices sign_identities_row1 : |a 0| = a 0 ∧ |a 1| = -a 1 ∧ |a 2| = -a 2
  suffices sign_identities_row2 : |a 4| = a 4 ∧ |a 3| = -a 3 ∧ |a 5| = -a 5
  suffices sign_identities_row3 : |a 8| = a 8 ∧ |a 6| = -a 6 ∧ |a 7| = -a 7
  suffices contradiction_from_x_max : (|x| ≥ |y| ∧ |x| ≥ |z|) ∧ x ≠ 0 → a 0 + a 1 + a 2 ≤ 0
  suffices contradiction_from_y_max : (|y| ≥ |x| ∧ |y| ≥ |z|) ∧ y ≠ 0 → a 3 + a 4 + a 5 ≤ 0
  suffices contradiction_from_z_max : (|z| ≥ |x| ∧ |z| ≥ |y|) ∧ z ≠ 0 → a 6 + a 7 + a 8 ≤ 0
  suffices x_max_implies_x_is_zero : (|x| ≥ |y| ∧ |x| ≥ |z|) → x = 0
  suffices y_max_implies_y_is_zero : (|y| ≥ |x| ∧ |y| ≥ |z|) → y = 0
  suffices z_max_implies_z_is_zero : (|z| ≥ |x| ∧ |z| ≥ |y|) → z = 0
  suffices all_zero_if_x_is_max : (|x| ≥ |y| ∧ |x| ≥ |z|) → y = 0 ∧ z = 0
  suffices max_abs_case_disjunction : (|x| ≥ |y| ∧ |x| ≥ |z|) ∨ (|y| ≥ |x| ∧ |y| ≥ |z|) ∨ (|z| ≥ |x| ∧ |z| ≥ |y|)

  by_cases first_case: |x| ≥ |y| ∧ |x| ≥ |z|
  have ⟨y_is_zero, z_is_zero⟩ := all_zero_if_x_is_max first_case
  specialize x_max_implies_x_is_zero first_case <;>
  simp [y_is_zero, z_is_zero, *]
  by_cases second_case : |y| ≥ |x| ∧ |y| ≥ |z|
  have contradiction_from_y_max_if_y_is_max :=
    y_max_implies_y_is_zero second_case
  simp [contradiction_from_y_max_if_y_is_max] at *
  try simp_all
  simp_all only [not_and, not_le, gt_iff_lt]
  any_goals simp [ge_iff_le] at *
  try simp_all [abs_eq_zero]
  by_contra all_lt
  simp [not_or, not_and_or] at *
  obtain  ⟨firstCol, secondCol, thirdCol⟩  :=  all_lt
  apply lt_irrefl |z|
  contrapose! z_max_implies_z_is_zero
  apply False.elim
  first | apply lt_irrefl (|x|) | apply lt_irrefl (|y|) | apply lt_irrefl (|z|)
  have := abs_inequality_from_eq1
  simp_all [abs_mul]
  first | apply lt_irrefl (|x|) | apply lt_irrefl (|y|) | apply lt_irrefl (|z|)
  cases le_total |x| |y| <;> cases le_total |y| |z| <;> cases le_total |z| |x| <;>
    simp [*, abs_nonneg] at * <;>
    linarith
  try intro x_max;aesop
  contrapose! contradiction_from_z_max
  aesop?
  contrapose! contradiction_from_y_max
  exact ⟨contradiction_from_y_max,
        by linarith [h₁.1,  h₂.1,  h₃.1]⟩
  intro abs_x_max
  contrapose! contradiction_from_x_max <;> aesop
  intro
  <;> (try simp_all)
  <;> linarith
  aesop (add simp [le_of_not_lt])
  linarith
  rintro ⟨h, hx⟩
  simp_all [abs_mul, abs_of_pos, abs_of_neg] <;> linarith
  refine' ⟨ abs_of_pos h₀.2.2, _ , _ ⟩ <;> rw [abs_of_neg] <;> linarith
  apply And.intro <;> simp [abs_of_pos, abs_of_neg, *]
  simp [ abs_eq_max_neg, h₀.1, h₁]
  try exact ⟨by linarith, by linarith, by linarith⟩
  aesop (add simp [abs_mul, mul_comm])
  nth_rw 1 [← mul_one |z|]
  nth_rewrite 1 [mul_assoc]
  nlinarith [abs_nonneg (a 6), abs_nonneg (a 7), abs_nonneg (a 8)]
  intros y_max_le_self
  all_goals aesop (add simp [abs_mul])
  simp [abs_of_pos, abs_of_neg, *] at *
  refine le_of_sub_nonneg ?h
  revert abs_inequality_from_eq1 abs_inequality_from_eq2 abs_inequality_from_eq3
  contrapose x_max_le_self
  first | push_neg at * | linarith
  repeat' first |nlinarith|simp_all
  aesop (add simp [abs_mul])
  nlinarith [abs_nonneg (a 0), abs_nonneg  (a 1), abs_nonneg (a 2)]
  rcases abs_cases (a 8 * z) <;> rcases abs_cases (a 6 * x) <;> rcases abs_cases (a 7 * y) <;>
      linarith
  apply le_of_not_lt
  rcases abs_cases (a 0 * x) <;>
  rcases abs_cases (a 1 * y) <;> rcases abs_cases (a 2 * z) <;>
  rcases abs_cases (a 3 * x) <;>
  rcases abs_cases (a 4 * y) <;> rcases abs_cases (a 5 * z) <;>
    linarith
  cases abs_cases (a 0 * x) <;> cases abs_cases (a 1 * y) <;> cases abs_cases (a 2 * z)
  <;> linarith [abs_nonneg (a 1*y), abs_nonneg (a 2 *z)]
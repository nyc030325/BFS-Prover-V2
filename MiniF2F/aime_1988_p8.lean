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


theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by'

  suffices h1 : (14 + 38) * f 14 38 = 38 * f 14 52
  suffices h2 : (14 + 24) * f 14 24 = 24 * f 14 38
  suffices h3 : (14 + 10) * f 14 10 = 10 * f 14 24
  suffices h4 : (10 + 4) * f 10 4 = 4 * f 10 14
  suffices h5 : (4 + 2) * f 4 2 = 2 * f 4 6
  suffices h6 : f 4 2 = 4
  suffices h7 : f 4 6 = 12
  suffices h8 : f 4 10 = 20
  suffices h9 : f 10 14 = 70
  suffices h10 : f 14 24 = 168
  suffices h11 : f 14 38 = 266
  suffices h12 : f 14 52 = 364
  
  convert h12 <;> simp [h₀, h₁, h₂]
  any_goals nlinarith <;>
    aesop
  linarith [h₀ 14 (by decide), h₀ 38 (by decide)]
  norm_num [h₀, h₁, h₂] at * <;> linarith
  norm_num [← h₁] at * <;> linarith
  have h8  := h₂ 4 (6 : ℕ) <;> aesop
  norm_num1 at *
    <;>
    nlinarith
  norm_num at h5 <;> linarith [h₂ 2 4 ⟨by norm_num, by norm_num⟩ ]
  have h6 := h₂ 2 4 (by decide)
  norm_num [h₀ 2 (by decide), h₀ 4 (by decide)] at h6
  have _ := h₂ 2 4
  norm_num [Nat.cast_succ] at *
  try simp_all
  have := h₂ 2 2
  simp_all <;> norm_cast <;> nlinarith
  have h22 := h₁ 2 4
  on_goal 1 => convert h₂ 4 2 using 2 <;> norm_num at *
  have h4 := h₂ 4 10
  norm_num (config := {decide := true}) at *
  norm_num [mul_comm] at h4 ⊢
  have h6 := h₂ 10 4
  norm_num at * <;> linarith [h₀ 10 (by norm_num), h₀ 4 (by norm_num)]
  have h34 := h₂ 10 14
  norm_num at h34 <;> try linarith
  try simp_all
  revert h1 h2 h34
  norm_cast <;> ring
  intro H H'
  intro L
  have T := h₂ 10 14 (by decide) (by decide)
  have L' := h₂ 14 10 (by norm_num) (by norm_num)
  norm_num at * <;>
    linarith [h₀ 10 (by simp), h₀ 14 (by simp), h₀ 24 (by simp), h₁ 10 14 (by simp) (by simp),
    h₁ 14 24 (by simp) (by simp), h₂ 10 14 (by simp) (by simp), h₂ 14 24 (by simp) (by simp)]
  have g := h₂ 14 24
  norm_num [h₀, h₁, h₂] at g ⊢ <;> linarith!
  convert h₂ 14 38 <;> norm_cast
  simp_all [Nat.succ_le_iff]
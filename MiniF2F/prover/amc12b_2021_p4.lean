import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2021_p4
  (m a : ℕ)
  (h₀ : 0 < m ∧ 0 < a)
  (h₁ : ↑m / ↑a = (3:ℝ) / 4) :
  (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76:ℝ) := by

  rcases h₀.1 with _ | m <;> rcases h₀.2 with _ | a <;>
    simp_all (config := {decide := true}) <;>
    field_simp at * <;> linarith
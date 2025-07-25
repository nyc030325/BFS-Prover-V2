import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2020_p6
  (n : ℕ)
  (h₀ : 9 ≤ n) :
  ∃ (x : ℕ), (x : ℝ)^2 = (Nat.factorial (n + 2) - Nat.factorial (n + 1)) / n ! := by

  refine' ⟨n + 1, _⟩ <;> field_simp [Nat.factorial] at * <;> ring
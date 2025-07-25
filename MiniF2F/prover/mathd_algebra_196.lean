import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_196
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ abs (2 - x) = 3) :
  ∑ k in S, k = 4 := by

  suffices S = {5 , -1} by
    rw [this]; norm_num
  apply Finset.ext <;>
  intro x <;>
  simp [abs_eq] at * <;>
  aesop
  exacts [ Or.inr <| show x = -1 from by linarith, Or.inl <| by linarith, Or.inr <| by ring, Or.inl <| by norm_num]
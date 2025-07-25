import Mathlib
open BigOperators Real Nat Topology

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by

  split_ands <;>
  rcases f with ⟨f_re, f_im⟩ <;>
  rcases z with ⟨z_re, z_im⟩ <;>
  simp [Complex.ext_iff] at * <;>
  exact ⟨by linarith, by linarith⟩
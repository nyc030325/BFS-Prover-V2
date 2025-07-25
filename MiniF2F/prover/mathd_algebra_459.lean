import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_459
  (a b c d : ℚ)
  (h₀ : 3 * a = b + c + d)
  (h₁ : 4 * b = a + c + d)
  (h₂ : 2 * c = a + b + d)
  (h₃ : 8 * a + 10 * b + 6 * c = 24) :
  ↑d.den + d.num = 28 := by

  have H := Eq.symm h₃
  simp_all [eq_comm, add_comm, add_left_comm]
  have  : d = 24 / 6 - (a + b + c)
  any_goals linarith!
  aesop <;> norm_cast
  ring_nf at h₀ h₁ h₂ ⊢
  norm_num [add_assoc, add_right_comm, h₁, h₂, h₀]
  norm_num [show c = 4 / 3 by linarith, show b = 4 / 5 by linarith, show a = 1 by linarith ]
  rw [← Rat.cast_ofNat]
    <;> norm_cast
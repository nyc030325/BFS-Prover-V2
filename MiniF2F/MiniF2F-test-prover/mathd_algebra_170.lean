import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_170
  (S : Finset ℤ)
  (h₀ : ∀ (n : ℤ), n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
  S.card = 11 := by

  suffices S = Finset.filter (fun n : ℤ => |n - 2| ≤ (5 + 6 / 10)) (Finset.Icc (-10) 15) by
       rw [this]; try native_decide
  ext b <;> simp_all [abs_le] <;>omega
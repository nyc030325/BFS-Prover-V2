import Mathlib
open BigOperators Real Nat Topology

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by

  rcases ht with ⟨hx, hy, hz⟩
  field_simp [Real.log_mul] at *
  rw [div_eq_iff] at * <;> ring_nf at * <;>
  nlinarith [Real.log_pos (by aesop : (1 : ℝ) < x), Real.log_pos (by aesop : (1 : ℝ) < y),Real.log_pos (by aesop : (1 : ℝ) < z)]
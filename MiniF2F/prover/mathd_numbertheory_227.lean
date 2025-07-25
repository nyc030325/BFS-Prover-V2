import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_227
  (x y n : ℕ+)
  (h₀ : ↑x / (4:ℝ) + y / 6 = (x + y) / n) :
  n = 5 := by

  rcases x with ⟨x, hx⟩ <;> rcases y with ⟨y, hy⟩ <;> rcases n with ⟨n, hn⟩ <;>
    rewrite [← PNat.coe_inj] at *
  field_simp at *<;>
  norm_cast at *
  nlinarith
        [mul_pos hx hn, mul_pos hy hn,
          mul_pos hn  hn]
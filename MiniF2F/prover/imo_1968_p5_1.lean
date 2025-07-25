import Mathlib
open BigOperators Real Nat Topology

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2)) :
  ∃ b > 0, ∀ x, f (x + b) = f x := by

  refine' ⟨2 * a, mul_pos two_pos h₀, fun x => _⟩
  rw [show (x + 2*a) = x+a+a by ring, h₁, h₁]
  ring_nf
    <;> have hx := h₁ (x - a)
    <;> aesop
  ring_nf <;> symm <;> ring
  iterate 2 rw [Real.sqrt]
  congr 1 <;> norm_num <;> ring
  cases max_cases (f (x - a) - (f (x - a)) ^ 2) 0 <;> try simp [*, Real.sq_sqrt] <;> norm_num
  any_goals
      aesop
  congr 1 <;> norm_num
  rw [ Real.sq_sqrt ] <;> nlinarith [sq_nonneg (f (x - a) - 1/2)]
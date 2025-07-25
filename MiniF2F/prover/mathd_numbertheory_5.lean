import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_5
  (n : ℕ)
  (h₀ : 10 ≤ n)
  (h₁ : ∃ x, x^2 = n)
  (h₂ : ∃ t, t^3 = n) :
  64 ≤ n := by

  obtain ⟨⟨a,ha⟩ ,⟨b, hb⟩⟩ := h₁, h₂
  by_contra can
  case intro.intro => 
    have : a ≤ 10 := by nlinarith 
    have : b ≤ 7 := by 
      nlinarith [sq_nonneg (b ^ 2)]
    interval_cases b <;> interval_cases a <;> omega
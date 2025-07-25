import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_559
  (x y : ℕ)
  (h₀ : x % 3 = 2)
  (h₁ : y % 5 = 4)
  (h₂ : x % 10 = y % 10) :
  14 ≤ x := by

  obtain ⟨⟨a,ha⟩ ,⟨b, hb⟩⟩ := h₁, h₂
  by_contra can
  case intro.intro => 
    have : a ≤ 10 := by nlinarith 
    have : b ≤ 7 := by 
      nlinarith [sq_nonneg (b ^ 2)]
    interval_cases b <;> interval_cases a <;> omega
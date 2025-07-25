import Mathlib
open BigOperators Real Nat Topology

theorem amc12_2000_p12
  (a m c : ℕ)
  (h₀ : a + m + c = 12) :
  a*m*c + a*m + m*c + a*c ≤ 112 := by

  obtain ⟨hi, hm, h₂⟩:= h₀
  obtain _ | _ | _ | i := i <;> obtain _ | _ | _ | m := m <;> obtain _ | _ | _ | o := o <;>try omega
  any_goals
    ring_nf at h₁ ⊢; nlinarith;
  ring_nf at * <;> try omega
  nlinarith [mul_nonneg (by positivity : 0 ≤ i) (by positivity : 0 ≤ o), mul_nonneg (by positivity : 0 ≤ m) (by positivity : 0 ≤ i), mul_nonneg (by positivity : 0 ≤ o) (by positivity : 0 ≤ m)]
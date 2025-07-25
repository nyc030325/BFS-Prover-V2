import Mathlib
open BigOperators Real Nat Topology

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1
  (a : ℤ)
  (b : ℤ)
  (h₀ : Odd a)
  (h₁ : 4 ∣ b)
  (h₂ : b >= 0) :
  (a^2 + b^2) % 8 = 1 := by

  rcases h₀ with ⟨a, rfl⟩
    <;> obtain ⟨b, rfl⟩ := h₁
    <;> ring_nf
    <;> repeat' omega
  obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := Int.even_or_odd b <;> obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ := Int.even_or_odd a <;>
         ring_nf at h₂ ⊢ <;> simp [sq, Int.add_emod, Int.mul_emod, Int.emod_emod, h₂] <;> omega
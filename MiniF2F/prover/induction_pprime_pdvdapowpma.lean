import Mathlib
open BigOperators Real Nat Topology

theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by

  rw [Nat.dvd_iff_mod_eq_zero, Nat.sub_mod_eq_zero_of_mod_eq]
  have  : Fact (Nat.Prime p) := ⟨h₁⟩
  repeat rw [← ZMod.natCast_eq_natCast_iff']
  simp [ ZMod.pow_card]
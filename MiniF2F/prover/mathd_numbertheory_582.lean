import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_582
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 3∣n) :
  ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by

  obtain ⟨_, rfl⟩ := h₁ <;> simp [add_comm, add_assoc, Nat.add_mod, Nat.mod_add_mod] <;> omega
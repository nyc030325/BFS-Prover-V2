import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2020_p4
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
  S.card = 100 := by

  classical
  let h₁ : S = Finset.filter (fun (n : ℕ) => 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n) (Finset.Icc 1000 9999) := by aesop
  rw [h₁]; native_decide
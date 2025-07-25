import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2020_p21
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) :
  S.card = 6 := by

  have hc := h₀ 0
  field_simp at * <;> norm_cast at * <;> tauto
  suffices H : S = Finset.filter (fun n : ℕ => n + 1000 = n.sqrt * 70) (Finset.range 50000) by
    rw [H]; native_decide
  ext n<;> aesop
  all_goals 
     have  : n.sqrt * 70 = n + 1000 := by omega 
     nlinarith [Nat.sqrt_le' n, Nat.lt_succ_sqrt n]
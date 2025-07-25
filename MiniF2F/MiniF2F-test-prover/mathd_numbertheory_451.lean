import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_451
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((Nat.divisors m).card = 4 ∧ ∑ p in (Nat.divisors m), p = n)) :
  ∑ k in S, k = 2016 := by

  have hm : S = Finset.filter (λ n => 2010 ≤ n ∧ n ≤ 2019) (Finset.image (λ m : ℕ => ∑ p ∈ m.divisors, p) (Finset.filter (λ m => m.divisors.card = 4) (Finset.image id (Finset.Icc 1 2019))))
  any_goals rw [hm]; native_decide
  ext a <;> aesop
  any_goals use w; aesop
  any_goals tauto
  all_goals 
     by_contra h 
     simp_all [Nat.divisors]
  induction w <;> simp_all [Finset.sum_filter]
  revert left_1 <;> simp_all [Finset.sum_Ico_succ_top]
  obtain _ | _ | _ | _ | n := ‹_› <;> omega
import Mathlib
import Aesop

open BigOperators Real Nat Topology Int

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Parser Elab Tactic

elab "focus' " tacs:tacticSeq1Indented : tactic => do
  match tacs.raw[0] with
  | .node _ _ args =>
    for tac in args do
      if tac[0].isMissing then continue
      focus (evalTactic tac)
  | _ => unreachable!

macro "by' " tacs:tacticSeq1Indented : term =>
  `(term| by focus' $tacs)


theorem mathd_numbertheory_552
  (f g h : ℕ+ → ℕ)
  (h₀ : ∀ x, f x = 12 * x + 7)
  (h₁ : ∀ x, g x = 5 * x + 2)
  (h₂ : ∀ x, h x = Nat.gcd (f x) (g x))
  (h₃ : Fintype (Set.range h)) :
  ∑ k in (Set.range h).toFinset, k = 12 := by'

  suffices h_lin_comb_val : ∀ (x : ℕ+), 5 * f x - 12 * g x = 11
  suffices h_dvd_lin_comb : ∀ (x : ℕ+), (h x) ∣ (5 * f x - 12 * g x)
  suffices h_dvd_11 : ∀ (x : ℕ+), h x ∣ 11
  suffices h_range_subset_divisors : Set.range h ⊆ (Nat.divisors (11 : ℕ))
  suffices h_divisors_11_is_set : (Nat.divisors (11 : ℕ) : Set ℕ) = ({1, 11} : Set ℕ)
  suffices h_range_subset : Set.range h ⊆ ({1, 11} : Set ℕ)
  suffices h_one_is_in_range : 1 ∈ Set.range h
  suffices h_eleven_is_in_range : 11 ∈ Set.range h
  suffices h_range_is_exactly_1_and_11 : Set.range h = ({1, 11} : Set ℕ)

  simp [h_range_is_exactly_1_and_11,pow_two]
  apply Set.Subset.antisymm h_range_subset ?subset
  simp_rw [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff] at *
  rintro x (rfl | rfl) <;> assumption
  obtain ⟨n, hf1⟩ := h_one_is_in_range
  rw [Set.mem_range]
  by_contra he
  erw [Set.range_subset_iff] at h_range_subset
  simp_all [Set.subset_def, h_range_subset]
  have h₁₁ := h_range_subset_divisors 11
  norm_num [h₁, h₀] at h₁₁
  specialize h_range_subset_divisors 4
  simp_all (config := { decide := true })
  classical
    apply Set.mem_range.2
    use 1
    aesop
  rw [h_divisors_11_is_set] at h_range_subset_divisors
  convert h_range_subset_divisors using 2 <;> tauto
  aesop
  simp only [Finset.coe_sort_coe, Set.subset_def, Set.mem_range]
  cases' h_dvd_11 2 with k hk
  rintro i ⟨j, hj⟩
  rw [← hj]
  simp [h_dvd_11 j, Nat.mem_divisors]
  exact (fun x => (h_dvd_lin_comb x).trans (dvd_of_eq (h_lin_comb_val x)))
  intro x_in
  have lhs := h₂ x_in
  have h_dvd₁ : h x_in ∣ f x_in
  first | aesop | rw [lhs]
  apply Nat.gcd_dvd_left
  have h_dvd₂ : h x_in ∣ g x_in
  nth_rw 1 [← one_mul (g x_in)]
  simp_all [h₀, h₁, h₂, h_lin_comb_val] <;> ring_nf
  exact Nat.gcd_dvd_right (7 + x_in * 12) (2 + x_in * 5)
  apply Nat.dvd_sub'
  exact Dvd.dvd.mul_left h_dvd₁ 5
  exact (h_dvd₂).mul_left _
  simp [h₀, h₁, mul_add, mul_comm]
  refine' fun x ↦ by omega
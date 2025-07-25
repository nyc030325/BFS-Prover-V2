import Mathlib
open BigOperators Real Nat Topology

theorem numbertheory_x5neqy2p4
  (x y : ℤ) :
  x^5 ≠ y^2 + 4 := by

  by_contra A_base
  have mod_11 := congr_arg (fun n : ℤ => n % 11) A_base
  simp [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_emod] at mod_11
  (
      have xmod11 := Int.emod_nonneg x (by norm_num : (11 : ℤ) ≠ 0)
      have ymod11 := Int.emod_nonneg y (by norm_num : (11 : ℤ) ≠ 0)
      have x_update := xmod11
      have y_update := ymod11
      have hx := x_update
      have hy := y_update
      have hx' : x % 11 < 11 := by omega
      have hy' : y % 11 < 11 := by omega
      interval_cases x0 : x % 11 <;> interval_cases y0 : y % 11 <;> norm_num at mod_11)
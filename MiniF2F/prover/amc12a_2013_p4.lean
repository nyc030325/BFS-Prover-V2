import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2013_p4 :
  (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5:ℝ) / 3 := by

  classical
    norm_num1 at *
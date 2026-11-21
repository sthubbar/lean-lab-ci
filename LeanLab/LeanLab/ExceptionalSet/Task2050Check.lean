import LeanLab.ExceptionalSet.DQLemma9Decisions

example (x : ℝ) (hx : 64 ≤ x) :
    x ^ (-(1 : ℝ)) ≤ x ^ (-(1 / 3 : ℝ)) / 8 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hmono : (64 : ℝ) ^ (2 / 3 : ℝ) ≤ x ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h64 : (64 : ℝ) ^ (2 / 3 : ℝ) = 16 := by norm_num
  have h23 : 8 ≤ x ^ (2 / 3 : ℝ) := by linarith
  let a : ℝ := x ^ (1 / 3 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsquare : a ^ 2 = x ^ (2 / 3 : ℝ) := by
    dsimp [a]
    calc
      (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ ((1 / 3 : ℝ) * 2) :=
        (Real.rpow_mul hxpos.le _ _).symm
      _ = x ^ (2 / 3 : ℝ) := by congr 1; norm_num
  have h2 : 8 ≤ a ^ 2 := by rw [hsquare]; exact h23
  have h3 : 8 * a ≤ a ^ 3 := by nlinarith
  have hinv : (1 / a ^ 3) ≤ (1 / (8 * a)) :=
    one_div_le_one_div_of_le (by positivity) h3
  have heq1 : a ^ (-(3 : ℝ)) = 1 / a ^ 3 := by
    rw [Real.rpow_neg ha.le]
    simp [pow_succ]
  have heq2 : a ^ (-(1 : ℝ)) = 1 / a := by
    rw [Real.rpow_neg ha.le]
    simp
  have heq3 : x ^ (-(1 : ℝ)) = a ^ (-(3 : ℝ)) := by
    dsimp [a]
    calc
      x ^ (-(1 : ℝ)) = x ^ ((1 / 3 : ℝ) * (-3)) := by congr 1; norm_num
      _ = (x ^ (1 / 3 : ℝ)) ^ (-3) := Real.rpow_mul hxpos.le _ _
  have heq4 : x ^ (-(1 / 3 : ℝ)) = a ^ (-(1 : ℝ)) := by
    dsimp [a]
    calc
      x ^ (-(1 / 3 : ℝ)) = x ^ ((1 / 3 : ℝ) * (-1)) := by congr 1; norm_num
      _ = (x ^ (1 / 3 : ℝ)) ^ (-1) := Real.rpow_mul hxpos.le _ _
  rw [heq3, heq4, heq1, heq2]
  calc
    1 / a ^ 3 ≤ 1 / (8 * a) := hinv
    _ = (1 / a) / 8 := by ring

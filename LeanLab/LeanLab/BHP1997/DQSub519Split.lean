/-
Burst 2026-11-22, BHP1997, unit P1122-0081, split of
`DQLowerExceptionalMeanSquare.sub_519_principal` in `DQLowerExceptional520Split`.
Source: P0069 Baker Harman Pintz 1997, page 52, display 5.19: "Now (5.1) and (5.2) hold a
fortiori if T2 is replaced by a smaller positive number, so the same argument yields (5.19)",
with the same argument the proof of Lemma 29 on pages 43 and 44.

At `z' = z0 = 1/T0^2` the smaller number is `T0^2`. The step is cut along the paper:
* `leaf_char_principal_z0`, LEAF, the Perron step [29] Lemma 3.19 of page 43 and the variant of [8]
  Lemma 2 for `χ0` of page 44, as in `Prep1121LowExc.leaf_char_principal` with `T2` replaced by
  `T0^2` and `z = z0`;
* `kernel_fortiori`, PROVED, the words "a fortiori": a kernel `1/(T^2 + t^2)` with a smaller
  `T` costs at most the factor `S^2 / T^2`;
* `fortiori_52`, PROVED from the existing LEAF `DQLeaf518Split.leaf_518_M1`, display 5.2 for
  b0 with `T2` replaced by `T0^2`, since `T0^2 ≤ T2 = Y/qQ` for large `x`;
* `error_arith_z0`, PROVED, the Perron error `O(Y^ε)` squared and integrated is below
  `z0^2 Y^3 L^(-A)`;
* `sub_519_principal_of_leaves`, PROVED from the above, has exactly the statement of
  `sub_519_principal`, checked by `sub_519_split_twin`.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.DQLowerExceptional520Split

namespace LeanLab.BHP1997.DQLowerExceptionalMeanSquare.Sub519
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators
open MeasureTheory

/-! ### The LEAF -/

/-- LEAF: pages 43 and 44, proof of Lemma 29 for the principal character, rerun at `z' = z0 = 1/T0^2`
with `T2` replaced by `T0^2`, page 52 "the same argument yields (5.19)". Class HARD, CITED
[29] Lemma 3.19 and [8] Lemma 2. P0069 Baker Harman Pintz 1997: by [29] Lemma 3.19 the window
sum of `b χ0` minus the Perron integral over `[1/2-iT0, 1/2+iT0]` is the Perron integral over
`T0 ≤ |t| ≤ Y` plus `O(Y^ε)`; by the variant of [8] Lemma 2 on page 44 and the kernel bound
`|((1+z0)^(1/2+it) - 1)/(1/2+it)|^2 ≪ 1/(T0^4 + t^2)`, which holds since `z0 = 1/T0^2`, the
mean square over `y` in `[Y/2, 3Y]` is `≪ Y^2 ∫_{T0 ≤ |t| ≤ Y} |G(1/2+it, χ0)|^2 /
(T0^4 + t^2) dt`. The Perron error is taken with `ε = 1/100` as in `leaf_char_principal`.
Here `δχ0 = 1`. The constants depend only on `b` and `ε`. -/
theorem leaf_char_principal_z0 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖(∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
          (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t in (-perronT0 x)..(perronT0 x),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * perronZ0 x : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * (x ^ (11 / 20 + ε)) ^ 2 *
          ((∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2)) +
            (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((perronT0 x ^ 2) ^ 2 + t ^ 2))) +
        K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-! ### Proved pieces -/

/-- Page 52, the words "a fortiori": for `0 < T ≤ S`, `1/(T^2 + t^2) ≤ (S^2/T^2)/(S^2 + t^2)`,
so a mean value with kernel `T` is at most `S^2/T^2` times the one with kernel `S`. -/
theorem kernel_fortiori (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {a b T S : ℝ} (hab : a ≤ b) (hT : 0 < T) (hTS : T ≤ S) :
    ∫ t in a..b, g t / (T ^ 2 + t ^ 2) ≤ (S ^ 2 / T ^ 2) * ∫ t in a..b, g t / (S ^ 2 + t ^ 2) := by
  have hS : 0 < S := lt_of_lt_of_le hT hTS
  rw [← intervalIntegral.integral_const_mul]
  have c1 : Continuous (fun t => g t / (T ^ 2 + t ^ 2)) :=
    hg.div (by fun_prop) (fun t => ne_of_gt (by positivity))
  have c2 : Continuous (fun t => S ^ 2 / T ^ 2 * (g t / (S ^ 2 + t ^ 2))) :=
    continuous_const.mul (hg.div (by fun_prop) (fun t => ne_of_gt (by positivity)))
  refine intervalIntegral.integral_mono_on hab (c1.intervalIntegrable _ _)
    (c2.intervalIntegrable _ _) fun t _ => ?_
  have hST2 : T ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hT.le hTS 2
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (hg0 t) (sq_nonneg t)) (sub_nonneg.2 hST2)]

/-- `T0^4 ≤ x^(1/20)` once `log x ≥ 729`: with `u = L^(1/3) ≥ 9`, `4u ≤ u^3/20`. -/
theorem perronT0_pow4_le {x : ℝ} (hx : 0 < x) (hL : 729 ≤ Real.log x) :
    perronT0 x ^ 4 ≤ x ^ (1 / 20 : ℝ) := by
  set L := Real.log x with hLdef
  set u := L ^ (1 / 3 : ℝ) with hu
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ u := Real.rpow_nonneg hL0 _
  have hu3 : u ^ 3 = L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hu9 : 9 ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 3 < 9 ^ 3 := pow_lt_pow_left₀ h hu0 (by norm_num)
    linarith
  unfold perronT0
  rw [← hLdef, ← hu, ← Real.exp_nat_mul, Real.rpow_def_of_pos hx, ← hLdef]
  apply Real.exp_le_exp.mpr
  push_cast
  have h80 : 0 ≤ u * (u ^ 2 - 80) := mul_nonneg hu0 (by nlinarith)
  rw [← hu3]
  nlinarith [h80]

/-- `1 ≤ T0` for `x ≥ 1`. -/
theorem one_le_perronT0 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ perronT0 x := by
  unfold perronT0
  exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx) _)

/-- Page 3, `Q ≤ x^(1/20)`: `Q ≤ Y^(1/16 - 1/10^5) / 2` with `Y = x^(11/20+ε)`. -/
theorem sieveQ_le_rpow {ε x : ℝ} (hε8 : ε ≤ 1/10^8) (hε : 0 < ε) (hx : 1 ≤ x) :
    (sieveQ ε x : ℝ) ≤ x ^ (1 / 20 : ℝ) := by
  set Y := x ^ (11 / 20 + ε) with hY
  have hx0 : 0 ≤ x := by linarith
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hx0 _
  set c : ℝ := 1 / 16 - 1 / 10 ^ 5 with hc
  have hfl : (sieveQ ε x : ℝ) ≤ (Y ^ ((2 : ℝ) * c)) ^ (1 / 2 : ℝ) / 2 := by
    unfold sieveQ
    exact Nat.floor_le (by positivity)
  have e1 : (Y ^ ((2 : ℝ) * c)) ^ (1 / 2 : ℝ) = Y ^ c := by
    rw [← Real.rpow_mul hY0]; congr 1; ring
  rw [e1] at hfl
  have hYc : 0 ≤ Y ^ c := Real.rpow_nonneg hY0 _
  have e2 : Y ^ c = x ^ ((11 / 20 + ε) * c) := by rw [hY, ← Real.rpow_mul hx0]
  have e3 : x ^ ((11 / 20 + ε) * c) ≤ x ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hc]; nlinarith)
  linarith

/-- Page 52, display 5.2 with `T2` replaced by the smaller `T0^2`, "(5.2) holds a fortiori".
PROVED from `DQLeaf518Split.leaf_518_M1` and `kernel_fortiori`, since `T0^2 qQ ≤ Y` for large
`x`: `T0^2 ≤ x^(1/20)` and `q ≤ Q ≤ x^(1/20)`. CONDITIONAL on the cited Theorem 4 and
Lemma 9 through the LEAF `leaf_518_M1`. -/
theorem fortiori_52 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-perronT0 x),
          ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((perronT0 x ^ 2) ^ 2 + t ^ 2)) +
        (∫ t in (perronT0 x)..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((perronT0 x ^ 2) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (perronT0 x ^ 2) ^ 2) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := DQLeaf518Split.leaf_518_M1 h4 h9 ω hω hz hε hε8 A hA
  refine ⟨max C (Real.exp 729), fun x hx q hq1 hqQ => ?_⟩
  have hxC : C ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 729 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hL : 729 ≤ Real.log x := by
    rw [← Real.log_exp 729]; exact Real.log_le_log (Real.exp_pos _) hxe
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hxpos _
  set T := perronT0 x with hTdef
  have hT1 : 1 ≤ T := one_le_perronT0 hx1
  have hT4 : T ^ 4 ≤ x ^ (1 / 20 : ℝ) := perronT0_pow4_le hxpos hL
  have hTT : T ≤ T ^ 4 := by
    calc T = T ^ 1 := (pow_one T).symm
      _ ≤ T ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT2 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  have hx20Y : x ^ (1 / 20 : ℝ) ≤ Y := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hTY : T ≤ Y := by linarith
  have hQ := sieveQ_le_rpow hε8 hε hx1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  set P : ℝ := (q : ℝ) * sieveQ ε x with hP
  have hP0 : 0 < P := by
    have : (1 : ℝ) ≤ sieveQ ε x := le_trans hq1' hqQ'
    positivity
  set X := x ^ (1 / 20 : ℝ) with hXdef
  have hX0 : 0 ≤ X := Real.rpow_nonneg hxpos.le _
  have hX3 : X * X * X ≤ Y := by
    have e : X * X * X = x ^ (3 / 20 : ℝ) := by
      rw [hXdef, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num
    rw [e]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hTP : T ^ 2 * P ≤ Y := by
    have h1 : T ^ 2 ≤ X := le_trans hT2 hT4
    have h2 : P ≤ X * X := by
      rw [hP]
      exact mul_le_mul (le_trans hqQ' hQ) hQ (by positivity) hX0
    calc T ^ 2 * P ≤ X * (X * X) := mul_le_mul h1 h2 hP0.le hX0
      _ = X * X * X := by ring
      _ ≤ Y := hX3
  set S : ℝ := Y / P with hS
  have hTS : T ^ 2 ≤ S := by rw [hS, le_div_iff₀ hP0]; exact hTP
  have hT20 : 0 < T ^ 2 := by positivity
  have hS0 : 0 < S := lt_of_lt_of_le hT20 hTS
  set G : ℝ → ℝ := fun t => ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 with hG
  have hGc : Continuous G :=
    (DQLeaf518Split.dirichlet_poly_continuous (rightInterval ε x)
      (fun m => (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q))).norm.pow 2
  have hG0 : ∀ t, 0 ≤ G t := fun t => by positivity
  have k1 := kernel_fortiori G hGc hG0 (a := -Y) (b := -T) (by linarith) hT20 hTS
  have k2 := kernel_fortiori G hGc hG0 (a := T) (b := Y) hTY hT20 hTS
  have hM := hC x hxC q hq1 hqQ
  have hTe : T = Real.exp (Real.log x ^ (1 / 3 : ℝ)) := rfl
  rw [← hTe, ← hYdef] at hM
  have hR : 0 ≤ S ^ 2 / (T ^ 2) ^ 2 := by positivity
  have hsum := add_le_add k1 k2
  rw [← mul_add] at hsum
  have hM' := mul_le_mul_of_nonneg_left hM hR
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hid : S ^ 2 / (T ^ 2) ^ 2 * (C * (Y / (Y / P) ^ 2) * Real.log x ^ (-A)) =
      C * (Y / (T ^ 2) ^ 2) * Real.log x ^ (-A) := by
    rw [hS]; field_simp
  rw [hid] at hM'
  have hfin : C * (Y / (T ^ 2) ^ 2) * Real.log x ^ (-A) ≤
      max C (Real.exp 729) * (Y / (T ^ 2) ^ 2) * Real.log x ^ (-A) := by
    apply mul_le_mul_of_nonneg_right _ hLA
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  exact le_trans hsum (le_trans hM' hfin)

/-- Page 43, the Perron error `O(Y^ε)` of [29] Lemma 3.19 in 5.19: its mean square
`K Y^(1+1/50)` is below `z0^2 Y^3 L^(-A)` for large `x`, since `z0^(-2) = T0^4 ≤ x^(1/20)`
and `L^A ≤ n! T0`. A pure asymptotic inequality. -/
theorem error_arith_z0 {ε : ℝ} (hε : 0 < ε) :
    ∀ A : ℝ, 0 < A → ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) ≤
        C * perronZ0 x ^ 2 * (x ^ (11 / 20 + ε)) ^ 3 * Real.log x ^ (-A) := by
  intro A hA K hK
  set N : ℝ := ((Nat.ceil (3 * A)).factorial : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨max (K * N) (Real.exp 729), fun x hx => ?_⟩
  have hxe : Real.exp 729 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hL : 729 ≤ Real.log x := by
    rw [← Real.log_exp 729]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hL1 : 1 ≤ Real.log x := by linarith
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx1 (by linarith)
  have hY0 : 0 < Y := by linarith
  set T := perronT0 x with hTdef
  have hT1 : 1 ≤ T := one_le_perronT0 hx1
  have hT0 : 0 < T := by linarith
  have hT4 : T ^ 4 ≤ x ^ (1 / 20 : ℝ) := perronT0_pow4_le hxpos hL
  have hTT : T ≤ T ^ 4 := by
    calc T = T ^ 1 := (pow_one T).symm
      _ ≤ T ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  set X := x ^ (1 / 20 : ℝ) with hXdef
  have hXX : X * X ≤ Y := by
    have e : X * X = x ^ (1 / 10 : ℝ) := by
      rw [hXdef, ← Real.rpow_add hxpos]; norm_num
    rw [e]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  set L := Real.log x with hLdef
  have hLA : L ^ A ≤ N * T := by
    have h := DQLowerExceptionalMeanSquare.log_rpow_le_factorial_mul_T0 (A := A) hL1
    rw [← hLdef, ← hTdef, ← hN] at h
    exact h
  have hLApos : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hY50 : Y ^ (1 / 50 : ℝ) ≤ Y := by
    calc Y ^ (1 / 50 : ℝ) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
      _ = Y := Real.rpow_one Y
  have hY50p : 0 ≤ Y ^ (1 / 50 : ℝ) := Real.rpow_nonneg hY0.le _
  -- `Y^(1/50) T^4 L^A ≤ N Y^2`
  have hkey : Y ^ (1 / 50 : ℝ) * T ^ 4 * L ^ A ≤ N * Y ^ 2 := by
    have h1 : T ^ 4 * L ^ A ≤ N * (T ^ 4 * T) := by
      calc T ^ 4 * L ^ A ≤ T ^ 4 * (N * T) := mul_le_mul_of_nonneg_left hLA (by positivity)
        _ = N * (T ^ 4 * T) := by ring
    have h2 : T ^ 4 * T ≤ Y := by
      calc T ^ 4 * T ≤ X * X := mul_le_mul hT4 (le_trans hTT hT4) hT0.le (by positivity)
        _ ≤ Y := hXX
    calc Y ^ (1 / 50 : ℝ) * T ^ 4 * L ^ A = Y ^ (1 / 50 : ℝ) * (T ^ 4 * L ^ A) := by ring
      _ ≤ Y * (N * Y) := mul_le_mul hY50 (le_trans h1 (mul_le_mul_of_nonneg_left h2 hN0))
          (by positivity) hY0.le
      _ = N * Y ^ 2 := by ring
  have hz : perronZ0 x ^ 2 * T ^ 4 = 1 := by
    unfold perronZ0; rw [← hTdef]; field_simp
  have hLm : L ^ A * L ^ (-A) = 1 := by
    rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ hLApos.ne']
  have hP : 0 ≤ perronZ0 x ^ 2 * Y ^ 3 * L ^ (-A) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  have hW : 0 ≤ Y * perronZ0 x ^ 2 * L ^ (-A) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  have hre : K * (Y ^ (1 / 50 : ℝ) * T ^ 4 * L ^ A) * (Y * perronZ0 x ^ 2 * L ^ (-A)) =
      K * Y * Y ^ (1 / 50 : ℝ) * ((perronZ0 x ^ 2 * T ^ 4) * (L ^ A * L ^ (-A))) := by ring
  rw [hz, hLm, mul_one, mul_one] at hre
  calc K * Y * Y ^ (1 / 50 : ℝ)
      = K * (Y ^ (1 / 50 : ℝ) * T ^ 4 * L ^ A) * (Y * perronZ0 x ^ 2 * L ^ (-A)) := hre.symm
    _ ≤ K * (N * Y ^ 2) * (Y * perronZ0 x ^ 2 * L ^ (-A)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hK) hW
    _ = (K * N) * (perronZ0 x ^ 2 * Y ^ 3 * L ^ (-A)) := by ring
    _ ≤ max (K * N) (Real.exp 729) * (perronZ0 x ^ 2 * Y ^ 3 * L ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hP
    _ = _ := by ring

/-! ### Display 5.19 from the pieces -/

/-- P0069 page 52 display 5.19 at `z' = z0`, the principal character, with exactly the
statement of `sub_519_principal`. PROVED from the LEAF `leaf_char_principal_z0`, the PROVED
`fortiori_52` and `error_arith_z0`, and the PROVED `DQLeaf518Split.leaf_lemma29_integrable`.
CONDITIONAL on the cited Theorem 4 and Lemma 9 and on the LEAFs `leaf_char_principal_z0` and
`DQLeaf518Split.leaf_518_M1`. -/
theorem sub_519_principal_of_leaves (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      IntervalIntegrable (fun y =>
          ‖(∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
            perronW ω ε x q y (perronZ0 x)‖ ^ 2) volume
        (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖(∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
            perronW ω ε x q y (perronZ0 x)‖ ^ 2 ≤
        C * perronZ0 x ^ 2 * (x ^ (11 / 20 + ε)) ^ 3 * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K, hK, C1, hC1⟩ := leaf_char_principal_z0 (lowerShortWeight ω ε) (B := 4) hε
    (lowerShortWeight_divisor_bound ω ε (le_refl 4))
  obtain ⟨C2, hC2⟩ := fortiori_52 h4 h9 ω hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := error_arith_z0 hε A hA K hK
  set D : ℝ := max (max C1 C2) (max C3 (max (K * C2 + C3) 1)) with hD
  refine ⟨D, fun x hx q hq1 hqQ => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hDK : K * C2 + C3 ≤ D :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxone : (1 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hδ : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
  have hz0 : 0 ≤ perronZ0 x := (perronZ0_pos x).le
  refine ⟨?_, ?_⟩
  · have h := DQLeaf518Split.leaf_lemma29_integrable (lowerShortWeight ω ε) ε x hxone q 1
      (perronZ0 x) hz0
    simp only [hδ, one_mul] at h
    unfold perronW lowerG perronT0
    exact h
  · have hP := hC1 x hx1 q hq1 hqQ
    have hF := hC2 x hx2 q hq1 hqQ
    have hE := hC3 x hx3
    set Y := x ^ (11 / 20 + ε) with hYdef
    have hY0 : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
    set T := perronT0 x with hTdef
    have hT0 : 0 < T := by rw [hTdef]; unfold perronT0; positivity
    have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
    have hid : Y ^ 2 * (Y / (T ^ 2) ^ 2) = perronZ0 x ^ 2 * Y ^ 3 := by
      unfold perronZ0; rw [← hTdef]; field_simp
    have hPP : 0 ≤ perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A) := by positivity
    have hFK := mul_le_mul_of_nonneg_left hF (mul_nonneg hK (sq_nonneg Y))
    have e1 : K * Y ^ 2 * (C2 * (Y / (T ^ 2) ^ 2) * Real.log x ^ (-A)) =
        K * C2 * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := by
      rw [← hid]; ring
    rw [e1] at hFK
    have e2 : C3 * perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A) =
        C3 * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := by ring
    rw [e2] at hE
    have hDP := mul_le_mul_of_nonneg_right hDK hPP
    show ∫ y in (Y / 2)..(3 * Y),
        ‖(∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          perronW ω ε x q y (perronZ0 x)‖ ^ 2 ≤
        D * perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)
    unfold perronW lowerG
    rw [← hTdef]
    calc _ ≤ _ := hP
      _ ≤ K * C2 * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) +
          C3 * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := add_le_add hFK hE
      _ = (K * C2 + C3) * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := by ring
      _ ≤ D * (perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := hDP
      _ = D * perronZ0 x ^ 2 * Y ^ 3 * Real.log x ^ (-A) := by ring

/-- Twin check: `sub_519_principal_of_leaves` has exactly the type of `sub_519_principal`. -/
theorem sub_519_split_twin : type_of% @sub_519_principal := @sub_519_principal_of_leaves

end LeanLab.BHP1997.DQLowerExceptionalMeanSquare.Sub519

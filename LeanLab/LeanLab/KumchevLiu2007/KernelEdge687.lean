/-
Kumchev and Liu 2007, P0088, page 7 before display 27.
Elementary dyadic bounds for the square-window kernel tail.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.KumchevLiu2007.KernelSumCount1122
import LeanLab.KumchevLiu2007.Eq33RouteC
import LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases
import Mathlib.Analysis.SpecificLimits.Basic

namespace LeanLab.KumchevLiu2007.Task687
open Real LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators

/-- P0088 page 7 before display 27: a dyadic majorant for one edge weight. -/
theorem edge_dyadic_majorant (b d Y : ℝ) (J : ℕ) (hb : 0 < b) (hb1 : b ≤ 1)
    (_hd : 0 ≤ d) (hY : 0 < Y) (hJ : Y < (2 : ℝ) ^ J) :
    min 1 (1 / (b * (d + 1))) ≤
      (if d < b⁻¹ then 1 else 0) +
      (∑ j ∈ Finset.range J, if d < (2 : ℝ) ^ (j + 1) / b then (1 / 2 : ℝ) ^ j else 0) +
      1 / (b * Y) := by
  classical
  have hsum : 0 ≤ ∑ j ∈ Finset.range J,
      if d < (2 : ℝ) ^ (j + 1) / b then (1 / 2 : ℝ) ^ j else 0 := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hinit : 0 ≤ (if d < b⁻¹ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have htail : 0 ≤ 1 / (b * Y) := by positivity
  by_cases hsmall : d < b⁻¹
  · rw [if_pos hsmall]
    exact (min_le_left _ _).trans (by linarith)
  by_cases hfar : (2 : ℝ) ^ J / b ≤ d
  · have hdY : Y ≤ d := by
      have hp0 : 0 ≤ (2 : ℝ) ^ J := by positivity
      have hp : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ J / b := (le_div_iff₀ hb).mpr (by nlinarith)
      exact hJ.le.trans (hp.trans hfar)
    have hrec : 1 / (b * (d + 1)) ≤ 1 / (b * Y) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact (min_le_right _ _).trans (hrec.trans (by linarith))
  have hbd : 1 ≤ b * d := by
    have := (le_of_not_gt hsmall)
    have : 1 / b ≤ d := by simpa only [one_div] using this
    exact (div_le_iff₀ hb).mp this |>.trans_eq (by ring)
  have hbdJ : b * d < (2 : ℝ) ^ J := by
    have := (not_le.mp hfar)
    have := (lt_div_iff₀ hb).mp this
    nlinarith
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hbd (by norm_num : (1 : ℝ) < 2)
  have hjJ : j < J := by
    by_contra h
    have hh : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hcond : d < (2 : ℝ) ^ (j + 1) / b := by
    rw [lt_div_iff₀ hb]
    nlinarith
  have hw : min 1 (1 / (b * (d + 1))) ≤ (1 / 2 : ℝ) ^ j := by
    refine (min_le_right _ _).trans ?_
    have hden : (2 : ℝ) ^ j ≤ b * (d + 1) := by linarith
    have hh := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) j) hden
    simpa only [one_div_pow, one_pow] using hh
  have hterm : (1 / 2 : ℝ) ^ j ≤
      ∑ i ∈ Finset.range J, if d < (2 : ℝ) ^ (i + 1) / b then (1 / 2 : ℝ) ^ i else 0 := by
    have hh := Finset.single_le_sum
      (f := fun i : ℕ => if d < (2 : ℝ) ^ (i + 1) / b then (1 / 2 : ℝ) ^ i else 0)
      (fun i hi => by split_ifs <;> positivity) (Finset.mem_range.mpr hjJ)
    simpa only [if_pos hcond] using hh
  linarith

/-- P0088 page 7 before display 27: one edge summed over the square window. -/
theorem square_edge_sum_le (Y b r : ℝ) (J : ℕ) (hY : 1 ≤ Y)
    (hb : 0 < b) (hb1 : b ≤ 1) (hJ : Y < (2 : ℝ) ^ J) :
    (∑ m ∈ squareWindow Y,
      min 1 (1 / (b * (|(m : ℝ) ^ 2 - r| + 1)))) ≤
      (4 * (J : ℝ) + 4) / (b * Real.sqrt Y) + 3 := by
  classical
  set R := Real.sqrt Y with hR
  set S := squareWindow Y with hSdef
  let d : ℕ → ℝ := fun m => |(m : ℝ) ^ 2 - r|
  have hY0 : 0 < Y := by linarith
  have hR0 : 0 < R := Real.sqrt_pos.mpr hY0
  have hR1 : 1 ≤ R := by
    have hh := Real.sqrt_le_sqrt hY
    simpa only [Real.sqrt_one] using hh
  have hR2 : R * R = Y := Real.mul_self_sqrt hY0.le
  have hcard : ∀ T : ℝ, 0 ≤ T →
      ((S.filter (fun m => d m < T)).card : ℝ) ≤ 2 * T / R + 1 := by
    intro T hT
    have hh := KernelSumCount1122.card_squares_window (R / 2) (r - T) (2 * T)
      (by linarith) (by linarith) (S.filter (fun m => d m < T)) (fun m hm => ?_)
    · have he : 2 * (R / 2) = R := by ring
      rwa [he] at hh
    · obtain ⟨hmS, hmT⟩ := Finset.mem_filter.mp hm
      have hmwin := (Finset.mem_filter.mp hmS).2
      have hd := abs_lt.mp hmT
      exact ⟨hmwin.1, by linarith [hd.1], by linarith [hd.2]⟩
  have hScard : (S.card : ℝ) ≤ 2 * R := by
    have hsub : S ⊆ Finset.range (⌊R⌋₊ + 1) := fun m hm => (Finset.mem_filter.mp hm).1
    have hh := Finset.card_le_card hsub
    rw [Finset.card_range] at hh
    have hh' : (S.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    have hf := Nat.floor_le hR0.le
    linarith
  have sum_ind (T v : ℝ) :
      (∑ m ∈ S, if d m < T then v else 0) = ((S.filter (fun m => d m < T)).card : ℝ) * v := by
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul]
  have hinner : ((S.filter (fun m => d m < b⁻¹)).card : ℝ) ≤ 2 / (b * R) + 1 := by
    have hh := hcard b⁻¹ (by positivity)
    convert hh using 1
    field_simp
  have hdyadic : ∀ j : ℕ,
      ((S.filter (fun m => d m < (2 : ℝ) ^ (j + 1) / b)).card : ℝ) * (1 / 2 : ℝ) ^ j ≤
        4 / (b * R) + (1 / 2 : ℝ) ^ j := by
    intro j
    have hh := mul_le_mul_of_nonneg_right
      (hcard ((2 : ℝ) ^ (j + 1) / b) (by positivity)) (by positivity : 0 ≤ (1 / 2 : ℝ) ^ j)
    refine hh.trans (le_of_eq ?_)
    rw [pow_succ, one_div_pow]
    field_simp
    ring
  have hdyadicSum :
      (∑ j ∈ Finset.range J,
        ((S.filter (fun m => d m < (2 : ℝ) ^ (j + 1) / b)).card : ℝ) * (1 / 2 : ℝ) ^ j) ≤
        4 * (J : ℝ) / (b * R) + 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (4 / (b * R) + (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum (fun j _ => hdyadic j)
      _ = (J : ℝ) * (4 / (b * R)) + ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 4 * (J : ℝ) / (b * R) + ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by ring
      _ ≤ 4 * (J : ℝ) / (b * R) + 2 := add_le_add le_rfl (sum_geometric_two_le J)
  have htail : (S.card : ℝ) / (b * Y) ≤ 2 / (b * R) := by
    refine (div_le_div_of_nonneg_right hScard (by positivity)).trans (le_of_eq ?_)
    field_simp
    nlinarith [hR2]
  calc
    _ ≤ ∑ m ∈ S, ((if d m < b⁻¹ then 1 else 0) +
        (∑ j ∈ Finset.range J, if d m < (2 : ℝ) ^ (j + 1) / b then (1 / 2 : ℝ) ^ j else 0) +
        1 / (b * Y)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact edge_dyadic_majorant b (d m) Y J hb hb1 (abs_nonneg _) hY0 hJ
    _ = ((S.filter (fun m => d m < b⁻¹)).card : ℝ) +
        (∑ j ∈ Finset.range J,
          ((S.filter (fun m => d m < (2 : ℝ) ^ (j + 1) / b)).card : ℝ) * (1 / 2 : ℝ) ^ j) +
        (S.card : ℝ) / (b * Y) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp_rw [sum_ind]
      simp [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (2 / (b * R) + 1) + (4 * (J : ℝ) / (b * R) + 2) + 2 / (b * R) :=
      add_le_add (add_le_add hinner hdyadicSum) htail
    _ = (4 * (J : ℝ) + 4) / (b * R) + 3 := by ring

/-- P0088 page 7 before display 27: the two square-window edges. -/
theorem edgeDecay_sum_le (X Y b : ℝ) (n : ℕ) (J : ℕ) (hY : 1 ≤ Y)
    (hb : 0 < b) (hb1 : b ≤ 1) (hJ : Y < (2 : ℝ) ^ J) :
    (∑ m ∈ squareWindow Y, KernelSumSplit1122.edgeDecay X Y b n m) ≤
      (8 * (J : ℝ) + 8) / (b * Real.sqrt Y) + 6 := by
  set r1 := (n : ℝ) - (X - Y)
  set r2 := (n : ℝ) - X
  have hterm : ∀ m : ℕ, KernelSumSplit1122.edgeDecay X Y b n m ≤
      min 1 (1 / (b * (|(m : ℝ) ^ 2 - r1| + 1))) +
      min 1 (1 / (b * (|(m : ℝ) ^ 2 - r2| + 1))) := by
    intro m
    have he1 : (n : ℝ) - (m : ℝ) ^ 2 - (X - Y) = -((m : ℝ) ^ 2 - r1) := by dsimp [r1]; ring
    have he2 : (n : ℝ) - (m : ℝ) ^ 2 - X = -((m : ℝ) ^ 2 - r2) := by dsimp [r2]; ring
    unfold KernelSumSplit1122.edgeDecay
    rw [he1, he2, abs_neg, abs_neg]
    have hpos (r : ℝ) : 0 ≤ min 1 (1 / (b * (|(m : ℝ) ^ 2 - r| + 1))) := by
      apply le_min zero_le_one
      positivity
    by_cases hd : |(m : ℝ) ^ 2 - r1| ≤ |(m : ℝ) ^ 2 - r2|
    · rw [min_eq_left hd]
      linarith [hpos r2]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hd))]
      linarith [hpos r1]
  calc
    _ ≤ ∑ m ∈ squareWindow Y,
        (min 1 (1 / (b * (|(m : ℝ) ^ 2 - r1| + 1))) +
        min 1 (1 / (b * (|(m : ℝ) ^ 2 - r2| + 1)))) :=
      Finset.sum_le_sum (fun m _ => hterm m)
    _ = (∑ m ∈ squareWindow Y, min 1 (1 / (b * (|(m : ℝ) ^ 2 - r1| + 1)))) +
        ∑ m ∈ squareWindow Y, min 1 (1 / (b * (|(m : ℝ) ^ 2 - r2| + 1))) :=
      Finset.sum_add_distrib
    _ ≤ ((4 * (J : ℝ) + 4) / (b * Real.sqrt Y) + 3) +
        ((4 * (J : ℝ) + 4) / (b * Real.sqrt Y) + 3) :=
      add_le_add (square_edge_sum_le Y b r1 J hY hb hb1 hJ)
        (square_edge_sum_le Y b r2 J hY hb hb1 hJ)
    _ = (8 * (J : ℝ) + 8) / (b * Real.sqrt Y) + 6 := by ring

end LeanLab.KumchevLiu2007.Task687

#print axioms LeanLab.KumchevLiu2007.Task687.edge_dyadic_majorant

#print axioms LeanLab.KumchevLiu2007.Task687.square_edge_sum_le

#print axioms LeanLab.KumchevLiu2007.Task687.edgeDecay_sum_le

namespace LeanLab.KumchevLiu2007.KernelSumSplit1122

open Real LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor Task687
open scoped BigOperators Topology

/-- LEAF: P0088 page 7, the display before 27, kernel_sum_bound step 3, sum over squares. MEDIUM.
Squares near m2 ~ Y^(1/2) are spaced about Y^(1/2) apart, so at most q Y^(1/2)/P^3 + 1 of them
lie within 1/b of an edge, the rest give a harmonic sum of size q Y^(1/2) log Y / P^3, and
|f2Weight| is O(1/log Y); hence the total is O(Y^(1/2) P^(-2)). -/
theorem outer_square_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ C : ℝ, 0 < C → ∃ C' X0 : ℝ, 0 < C' ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        ∑ m2 ∈ squareWindow (windowY X ε),
            |f2Weight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m2 : ℝ)| *
              (C * (edgeDecay X (windowY X ε) (bq X ε B q) n m2 / Real.log X + windowY X ε / X)) ≤
          C' * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  intro B hB ε hε hε' C hC
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e2 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X ^ B :=
    ((tendsto_rpow_atTop hB).comp Real.tendsto_log_atTop).eventually_ge_atTop 2
  have e3 := (isLittleO_log_rpow_rpow_atTop (2 * B)
    (by norm_num : (0 : ℝ) < 7 / 96)).bound (by norm_num : (0 : ℝ) < 1)
  have e4 : ∀ᶠ X : ℝ in Filter.atTop, Real.exp 1 ≤ X ^ (7 / 96 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 96)).eventually_ge_atTop (Real.exp 1)
  obtain ⟨X1, hbig⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  refine ⟨80 * C, max 9 X1, by positivity, ?_⟩
  intro X hX q hq1 hqP n
  have hX9 : 9 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  obtain ⟨hL1, hP2, habs, he⟩ := hbig X ((le_max_right _ _).trans hX)
  let L := Real.log X
  let P := L ^ B
  let Y := windowY X ε
  let R := Real.sqrt Y
  let T := Y ^ (1 / 4 : ℝ)
  let z := T * P ^ (-2 : ℤ)
  let b := bq X ε B q
  change (∑ m ∈ squareWindow Y, |f2Weight z (m : ℝ)| *
      (C * (edgeDecay X Y b n m / L + Y / X))) ≤ (80 * C) * R * P ^ (-2 : ℤ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hP1 : 1 ≤ P := by dsimp [P, L]; linarith
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hY1 : 1 ≤ Y := Real.one_le_rpow hX1 (by linarith)
  have hY3 : 3 ≤ Y := by
    have h1 : 3 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by nlinarith)
    have h2 : Real.sqrt X ≤ Y := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith
  have hR0 : 0 < R := Real.sqrt_pos.mpr hY0
  have hR1 : 1 ≤ R := by
    have hh := Real.sqrt_le_sqrt hY1
    simpa only [Real.sqrt_one] using hh
  have hR2 : R * R = Y := Real.mul_self_sqrt hY0.le
  have hP2eq : P ^ 2 = L ^ (2 * B) := by
    dsimp [P]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hPsmall : P ^ 2 ≤ X ^ (7 / 96 : ℝ) := by
    rw [hP2eq]
    change ‖L ^ (2 * B)‖ ≤ 1 * ‖X ^ (7 / 96 : ℝ)‖ at habs
    simpa only [Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL0 (2 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 96 : ℝ)), one_mul] using habs
  have hTlo : X ^ (7 / 48 : ℝ) ≤ T := by
    change X ^ (7 / 48 : ℝ) ≤ (X ^ (7 / 12 + ε / 2)) ^ (1 / 4 : ℝ)
    rw [← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have heP : Real.exp 1 * P ^ 2 ≤ T := by
    calc
      _ ≤ X ^ (7 / 96 : ℝ) * X ^ (7 / 96 : ℝ) :=
        mul_le_mul he hPsmall (sq_nonneg P) (Real.rpow_nonneg hX0.le _)
      _ = X ^ (7 / 48 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
      _ ≤ T := hTlo
  have hzEq : z = T / P ^ 2 := by simp only [z, zpow_neg, zpow_ofNat, div_eq_mul_inv]
  have hze : Real.exp 1 ≤ z := by
    rw [hzEq]
    exact (le_div_iff₀ (by positivity : 0 < P ^ 2)).mpr heP
  have hT2 : T ^ 2 = R := by
    dsimp [T, R]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    norm_num
  have hzsq : z ^ 2 = R / P ^ 4 := by
    rw [hzEq, div_pow, hT2]
    congr 1
    ring
  have hP4 : 2 ≤ P ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP2 4
    norm_num at hh
    linarith
  have hf2 : ∀ m ∈ squareWindow Y, |f2Weight z (m : ℝ)| ≤ 2 := by
    intro m hm
    have hmwin := (Finset.mem_filter.mp hm).2
    have hzm : z ≤ Real.sqrt (m : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      rw [hzsq]
      refine le_trans ?_ hmwin.1
      exact div_le_div_of_nonneg_left hR0.le (by norm_num) hP4
    exact KernelSumF2Bound1122.abs_f2Weight_le_two z (m : ℝ) hze hzm
  have hRlo : X ^ (7 / 24 : ℝ) ≤ R := by
    change X ^ (7 / 24 : ℝ) ≤ Real.sqrt (X ^ (7 / 12 + ε / 2))
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hPR : P ^ 2 ≤ R := hPsmall.trans ((Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)).trans hRlo)
  have hYP : Y * P ^ 2 ≤ X := by
    calc
      _ ≤ Y * X ^ (7 / 96 : ℝ) := mul_le_mul_of_nonneg_left hPsmall hY0.le
      _ = X ^ (7 / 12 + ε / 2 + 7 / 96) := by
        change X ^ (7 / 12 + ε / 2) * X ^ (7 / 96 : ℝ) = _
        rw [← Real.rpow_add hX0]
      _ ≤ X := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
          (by linarith : 7 / 12 + ε / 2 + 7 / 96 ≤ (1 : ℝ))
  have hP3Y : P ^ 3 ≤ Y := by
    calc
      P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
      _ = (P ^ 2) ^ 2 := by ring
      _ ≤ (X ^ (7 / 96 : ℝ)) ^ 2 := pow_le_pow_left₀ (sq_nonneg P) hPsmall 2
      _ = X ^ (7 / 48 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        norm_num
      _ ≤ T := hTlo
      _ ≤ Y := by
        change Y ^ (1 / 4 : ℝ) ≤ Y
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hbEq : b = P ^ 3 / ((q : ℝ) * Y) := by
    dsimp [b, bq]
    change (Y * P ^ (-2 : ℤ) / P)⁻¹ / q = _
    rw [zpow_neg, zpow_ofNat]
    field_simp
  have hb0 : 0 < b := by rw [hbEq]; positivity
  have hb1 : b ≤ 1 := by
    rw [hbEq, div_le_one (by positivity)]
    exact hP3Y.trans (le_mul_of_one_le_left hY0.le hq1')
  have hbY : b * Y = P ^ 3 / (q : ℝ) := by rw [hbEq]; field_simp
  have hscale : 1 / (b * R) ≤ R / P ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < b * R) (by positivity : 0 < P ^ 2)]
    have hh : P ^ 2 ≤ b * Y := by
      rw [hbY, le_div_iff₀ hq0]
      have hmul := mul_le_mul_of_nonneg_right hqP (sq_nonneg P)
      nlinarith
    calc
      1 * P ^ 2 ≤ b * Y := by simpa using hh
      _ = b * (R * R) := by rw [hR2]
      _ = R * (b * R) := by ring
  have hsmall : 1 / L ≤ R / P ^ 2 := by
    have hh : 1 ≤ R / P ^ 2 := (one_le_div (by positivity)).mpr hPR
    have hL1' : 1 ≤ L := hL1
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL1').trans (by simpa using hh)
  obtain ⟨J, hJ, hJL⟩ := Prep1122KLLemma34Cases.dyadic_count hY3
  have hYX : Y ≤ X := by
    exact (le_mul_of_one_le_right hY0.le (one_le_pow₀ hP1)).trans hYP
  have hlog : Real.log Y ≤ L := Real.log_le_log hY0 hYX
  have hJ32 : 8 * (J : ℝ) + 8 ≤ 32 * L := by linarith
  have hw : (∑ m ∈ squareWindow Y, edgeDecay X Y b n m) / L ≤ 38 * R / P ^ 2 := by
    have hh := edgeDecay_sum_le X Y b n J hY1 hb0 hb1 hJ
    have hh2 : (8 * (J : ℝ) + 8) / (b * R) + 6 ≤ 32 * L / (b * R) + 6 := by gcongr
    have hh3 := div_le_div_of_nonneg_right (hh.trans hh2) hL0.le
    calc
      _ ≤ (32 * L / (b * R) + 6) / L := hh3
      _ = 32 * (1 / (b * R)) + 6 * (1 / L) := by field_simp
      _ ≤ 32 * (R / P ^ 2) + 6 * (R / P ^ 2) := by gcongr
      _ = 38 * R / P ^ 2 := by ring
  have hcard : ((squareWindow Y).card : ℝ) ≤ 2 * R := by
    have hh := Eq33RouteC.squareWindow_card_le Y
    linarith
  have hYXscale : Y / X ≤ 1 / P ^ 2 := by
    rw [div_le_div_iff₀ hX0 (by positivity)]
    simpa using hYP
  have herr : ((squareWindow Y).card : ℝ) * (Y / X) ≤ 2 * R / P ^ 2 := by
    calc
      _ ≤ (2 * R) * (Y / X) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (2 * R) * (1 / P ^ 2) := mul_le_mul_of_nonneg_left hYXscale (by positivity)
      _ = 2 * R / P ^ 2 := by ring
  calc
    _ ≤ ∑ m ∈ squareWindow Y, 2 * (C * (edgeDecay X Y b n m / L + Y / X)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hp : 0 ≤ C * (edgeDecay X Y b n m / L + Y / X) := by
        have hd := KernelSumPieces1122.edgeDecay_nonneg X Y b n m hb0.le
        positivity
      exact mul_le_mul_of_nonneg_right (hf2 m hm) hp
    _ = 2 * C * ((∑ m ∈ squareWindow Y, edgeDecay X Y b n m) / L +
        ((squareWindow Y).card : ℝ) * (Y / X)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * C * (38 * R / P ^ 2 + 2 * R / P ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hw herr) (by positivity)
    _ = (80 * C) * R * P ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_ofNat]
      ring


end LeanLab.KumchevLiu2007.KernelSumSplit1122

#print axioms LeanLab.KumchevLiu2007.KernelSumSplit1122.outer_square_bound

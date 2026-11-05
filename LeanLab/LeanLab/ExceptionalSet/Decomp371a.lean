import LeanLab.ExceptionalSet.DecompJ200
import LeanLab.ExceptionalSet.BrudernPerelliExplicit

/-!
Task371 decomposes the remaining major arc leaf of P0082.
Source: https://doi.org/10.5802/aif.1621 pages 362 to 365, displays 8 and 23.
The open leaves isolate the coefficient bound, the boundary count and the Fourier identity.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.DecompJ200

/-- P0082 page 372 display 47. On real arguments at least eight, the derivative
of F is at least gamma. Mathlib's mean value theorem gives this growth bound. -/
theorem F_growth (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    γ * (y - x) ≤ F γ y - F γ x := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) :
      HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
    · rfl
    · dsimp [F]; ring
  have hbound (z : ℝ) (hz : 8 ≤ z) :
      γ ≤ deriv (F γ) z := by
    have hz0 : 0 < z := by linarith
    have hL : 1 ≤ Real.log z :=
      hlog8.trans (Real.log_le_log (by norm_num) hz)
    have hF : z ≤ F γ z := by
      calc z = Real.exp (Real.log z) := (Real.exp_log hz0).symm
        _ ≤ Real.exp (Real.log z ^ γ) := by
          apply Real.exp_le_exp.mpr
          simpa only [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le hL hγ.le)
    have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
    rw [(hd z hz).deriv, le_div_iff₀ hz0]
    calc γ * z ≤ γ * F γ z := mul_le_mul_of_nonneg_left hF (by linarith)
      _ ≤ (γ * F γ z) * Real.log z ^ (γ - 1) := le_mul_of_one_le_right (mul_nonneg (by linarith) (Real.exp_pos _).le) hp
      _ = _ := by ring
  apply (convex_Ici (8 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hbound z (interior_subset hz)) x hx y (hx.trans hxy) hxy


/-- P0082 page 365 floor window. Once N is at least eight, its upper floor
restriction excludes every index above N. A unit index step changes F by more than one. -/
theorem window_upper (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 8 ≤ N)
    (n : ℕ) (hn : n ∈ window γ N) : n ≤ N := by
  by_contra hnN
  have hstep : (1 : ℝ) ≤ (n : ℝ) - N := by
    have hr : (N : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : N + 1 ≤ n)
    linarith
  have hg := F_growth γ N n hγ (by exact_mod_cast hN) (by exact_mod_cast (by omega : N ≤ n))
  have hγ0 : 0 ≤ γ := by linarith
  have hgap : 1 < F γ n - F γ N := by
    have hm := mul_le_mul_of_nonneg_left hstep hγ0
    nlinarith
  have hfloor : F γ n < (nu γ n : ℝ) + 1 := by
    simpa only [nu] using Int.lt_floor_add_one (F γ n)
  have hnu : (nu γ n : ℝ) ≤ F γ N := (Finset.mem_filter.mp hn).2.2
  linarith

/-- P0082 page 372 display 47. The derivative of F divided by x is nonnegative
on x at least eight. This supports the index range used on page 365. -/
theorem F_ratio_mono (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    F γ x / x ≤ F γ y / y := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) : HasDerivAt (fun z => F γ z / z)
      (F γ z * (γ * Real.log z ^ (γ - 1) - 1) / z ^ 2) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    have hF : HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
      convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
      · rfl
      · dsimp [F]; ring
    convert hF.div (hasDerivAt_id z) hz0.ne' using 1
    · rfl
    · dsimp
      field_simp
  apply monotoneOn_of_deriv_nonneg (convex_Ici (8 : ℝ))
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => ?_) hx (hx.trans hxy) hxy
  have hz8 : 8 ≤ z := interior_subset hz
  have hL : 1 ≤ Real.log z := hlog8.trans (Real.log_le_log (by norm_num) hz8)
  have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
  rw [(hd z hz8).deriv]
  apply div_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    have hg : 1 ≤ γ * Real.log z ^ (γ - 1) := one_le_mul_of_one_le_of_one_le hγ.le hp
    linarith
  · positivity


/-- P0082 page 365 floor window. For N at least sixteen the lower floor
restriction forces n strictly above N divided by two. -/
theorem window_lower (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N)
    (n : ℕ) (hn : n ∈ window γ N) : N / 2 < n := by
  by_contra hnlow
  have hnN : n ≤ N / 2 := by omega
  let m := max n 8
  have hm8 : 8 ≤ m := Nat.le_max_right _ _
  have hnm : n ≤ m := Nat.le_max_left _ _
  have hmN : 2 * m ≤ N := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hFm : 0 < F γ m := Real.exp_pos _
  have hmono : F γ n ≤ F γ m := by
    by_cases hn0 : n = 0
    · subst n
      have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
      have hpow : 0 ≤ Real.log (m : ℝ) ^ γ := Real.rpow_nonneg hlog _
      simpa only [F, Nat.cast_zero, Real.log_zero, Real.zero_rpow (by linarith : γ ≠ 0), Real.exp_zero]
        using Real.one_le_exp_iff.mpr hpow
    · exact LeanLab.ExceptionalSet.BrudernPerelli1998.F_mono (by linarith) (by omega) hnm
  have hr := F_ratio_mono γ m N hγ (by exact_mod_cast hm8) (by exact_mod_cast (by omega : m ≤ N))
  have hcross : F γ m * N ≤ F γ N * m := (div_le_div_iff₀ hmpos hNpos).mp hr
  have hhalf : F γ m ≤ F γ N / 2 := by
    calc
      _ ≤ F γ N * m / N := (le_div_iff₀ hNpos).mpr hcross
      _ ≤ F γ N / 2 := by
        rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
        have hmNr : 2 * (m : ℝ) ≤ N := by exact_mod_cast hmN
        have hFN : 0 < F γ N := Real.exp_pos _
        nlinarith [mul_le_mul_of_nonneg_left hmNr hFN.le]
  have hfloor : (nu γ n : ℝ) ≤ F γ n := Int.floor_le _
  have hnu : F γ N / 2 < (nu γ n : ℝ) := (Finset.mem_filter.mp hn).2.1
  linarith

/-- P0082 page 365 Lemma 8. The literal floor window lies in the index range
used for the paper's equidistribution and second moment estimates. -/
theorem window_subset_Ioc (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N) :
    window γ N ⊆ Finset.Ioc (N / 2) N := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨window_lower γ hγ N hN n hn,
    window_upper γ hγ N (by omega) n hn⟩

/-- P0082 page 357, the prime sum preceding display 6. Its integer frequencies
make it periodic with period one, as required by the Fourier coefficient argument. -/
theorem Sp_periodic (P X : ℝ) : Function.Periodic (Sp P X) 1 := by
  intro α
  unfold Sp
  apply Finset.sum_congr rfl
  intro p hp
  have he : eC ((α + 1) * (p : ℝ)) = eC (α * (p : ℝ)) := by
    unfold eC
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (((α : ℂ) + 1) * (p : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I * ((α : ℂ) * (p : ℂ)) + (p : ℂ) * (2 * Real.pi * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]

/-- P0082 page 357 major arc definition. Translation by one shifts the integer
numerator by its denominator and preserves both coprimality and arc width. -/
theorem majorArcs_periodic (P X : ℝ) : Function.Periodic (majorArcs P X) 1 := by
  intro α
  apply propext
  constructor
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a - q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_sub_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a + q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_add_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring

/-- P0082 page 362 Lemma 7 versus page 365 Lemma 8. Every member of the
literal floor window lies in the value window used for the coefficient lower bound. -/
theorem window_value_range (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N)
    (n : ℕ) (hn : n ∈ window γ N) : F γ N / 2 < F γ n ∧ F γ n ≤ F γ N := by
  have hnpos : 1 ≤ n := by
    have := window_lower γ hγ N hN n hn
    omega
  exact ⟨lt_of_lt_of_le (Finset.mem_filter.mp hn).2.1 (Int.floor_le _),
    LeanLab.ExceptionalSet.BrudernPerelli1998.F_mono (by linarith) hnpos
      (window_upper γ hγ N (by omega) n hn)⟩

/-- LEAF. P0082 pages 362 to 364, Lemma 7 and display 20. The sum of the adjacent
integer major arc coefficients is large outside the stated sparse exceptional set.
The common kappa is fixed after Lemma 4. The floor window is that of Lemma 8. -/
theorem leaf_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF. P0082 page 364, display 23 and the next paragraph. Lemma 4 gives
O of N times Delta plus N over calE boundary indices. Delta is calE to
minus one eighth, as on page 365. This statement only counts fractional boundaries. -/
theorem leaf_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- LEAF. P0082 pages 357 and 364, displays 8 and 23. Away from the fractional
boundary both kernel weights are one. The major integral is the sum of the
adjacent integer coefficients. The plateau endpoints are included. -/
theorem leaf_major_identity (γ δ κ : ℝ) (N n : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hleft : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ Int.fract (F γ n))
    (hright : Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ))) :
    majorInt γ δ κ N n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) := by
  sorry

/-- Assembly. P0082 page 365, Lemma 8, with the exact statement of
DecompJ200.leaf_major_bound. Conditional on the three open leaves above. -/
theorem major_bound_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := leaf_coefficient_lower γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := leaf_fractional_boundary γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ :=
    hcoeff κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ :=
    hboundary κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c₀, Ba + Bb, hc₀, add_pos hBa hBb, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let A := (window γ N).filter (fun n : ℕ =>
    (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := (window γ N).filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (window γ N).filter (fun n : ℕ =>
      (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hnmajor⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := leaf_major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hnW, by rwa [hid] at hnmajor⟩
  have hcard : (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc
    _ ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
      gcongr
    _ = _ := by ring

end LeanLab.ExceptionalSet.Decomp371a

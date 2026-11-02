import LeanLab.BakerHarmanPintz1997.Decomp90

namespace LeanLab.BakerHarmanPintz1997.DecompJ883
open Finset Real Decomp90
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 21. Explicit Saving Parameter η. -/
theorem fgm_eta (ε : ℝ) (hε : 0 < ε) : 0 < min (ε / 8) (1 / 4) :=
  lt_min (by positivity) (by norm_num)

/-- LEAF. Page 21, Fujii-Gallagher-Montgomery bound. -/
theorem fgm_bound :
  ∃ C_FGM : ℝ, 0 < C_FGM ∧
  ∀ q : ℕ, q ≥ 1 → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
  ∀ N u : ℝ, 1 ≤ N → N ≤ u → u ≤ 2 * N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊u⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) -
    (if χ = 1 then 1 else 0 : ℂ) * (Nat.totient q : ℂ) / (q : ℂ) *
    ∫ y in N..u, (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_FGM * (q : ℝ) ^ (1 / 2 : ℝ) * (|t| + 1) ^ (1 / 2 : ℝ) * log ((q : ℝ) * (|t| + 2)) := by sorry

/-- LEAF. Page 21. Discretization error between discrete sum and integral. -/
theorem fgm_discretization_error :
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
    ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ) := by sorry

/-- LEAF. Page 21. Main integral evaluation bound. -/
theorem fgm_integral_bound :
  ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
  ‖∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ 5 * (N : ℝ) ^ (1 / 2 : ℝ) / (1 + |t|) := by
  intro N N1 hN hNN1 hN1 t
  have hN0 : 0 < N := by linarith
  have hN10 : 0 < N1 := by linarith
  let s : ℂ := (-1 / 2 : ℂ) + (-(t : ℂ) * Complex.I)
  let d : ℂ := s + 1
  have hfun : Set.EqOn
      (fun y : ℝ => (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I))
      (fun y => (y : ℂ) ^ s) (Set.uIcc N N1) := by
    intro y hy
    have hypos : 0 < y := by
      rw [Set.uIcc_of_le hNN1] at hy
      linarith [hy.1]
    dsimp [s]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hypos.ne')]
  have hint : ∫ y in N..N1,
      (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ∫ y in N..N1, (y : ℂ) ^ s :=
    intervalIntegral.integral_congr hfun
  have hvalue : ∫ y in N..N1,
      (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ((N1 : ℂ) ^ d - (N : ℂ) ^ d) / d := by
    calc
      _ = ∫ y in N..N1, (y : ℂ) ^ s := hint
      _ = _ := by
        change (∫ y in N..N1, (y : ℂ) ^ s) =
          ((N1 : ℂ) ^ (s + 1) - (N : ℂ) ^ (s + 1)) / (s + 1)
        exact integral_cpow (a := N) (b := N1) (r := s)
          (Or.inl (by dsimp [s]; norm_num))
  have hdre : d.re = 1 / 2 := by simp [d, s]; ring
  have hdim : d.im = -t := by simp [d, s]
  have hden1 : 1 / 2 ≤ ‖d‖ := by
    have hh := Complex.abs_re_le_norm d
    rw [hdre] at hh
    norm_num at hh
    exact hh
  have hden2 : |t| ≤ ‖d‖ := by
    have hh := Complex.abs_im_le_norm d
    rw [hdim] at hh
    simpa using hh
  have hdenpos : 0 < ‖d‖ := by linarith
  have hnormN1 : ‖(N1 : ℂ) ^ d‖ = N1 ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN10 d, hdre]
  have hnormN : ‖(N : ℂ) ^ d‖ = N ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0 d, hdre]
  have hroot2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  have hNroot : 0 ≤ N ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  have hN1root : N1 ^ (1 / 2 : ℝ) ≤ (2 * N) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN1 (by norm_num)
  have hmulroot : (2 * N) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
  have hnum : ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ ≤
      (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ‖(N1 : ℂ) ^ d‖ + ‖(N : ℂ) ^ d‖ := norm_sub_le _ _
      _ = N1 ^ (1 / 2 : ℝ) + N ^ (1 / 2 : ℝ) := by rw [hnormN1, hnormN]
      _ ≤ (2 * N) ^ (1 / 2 : ℝ) + N ^ (1 / 2 : ℝ) :=
        add_le_add hN1root le_rfl
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) +
          N ^ (1 / 2 : ℝ) := by rw [hmulroot]
      _ ≤ (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by nlinarith [hroot2, hNroot]
  by_cases ht : |t| ≤ 1
  · have hpoint : ∀ y ∈ Set.uIoc N N1, ‖(y : ℂ) ^ s‖ ≤ N ^ (-1 / 2 : ℝ) := by
      intro y hy
      have hyN : N ≤ y := by
        rw [Set.uIoc_of_le hNN1] at hy
        exact hy.1.le
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hyN]) s]
      have hsre : s.re = -1 / 2 := by simp [s]
      rw [hsre]
      exact Real.rpow_le_rpow_of_nonpos hN0 hyN (by norm_num)
    have hsmall : ‖∫ y in N..N1, (y : ℂ) ^ s‖ ≤
        N ^ (-1 / 2 : ℝ) * |N1 - N| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards with y hy
      exact hpoint y hy
    have hlength : |N1 - N| ≤ N := by
      rw [abs_of_nonneg (by linarith : 0 ≤ N1 - N)]
      linarith
    have hpow : N ^ (-1 / 2 : ℝ) * N = N ^ (1 / 2 : ℝ) := by
      calc
        N ^ (-1 / 2 : ℝ) * N =
            N ^ (-1 / 2 : ℝ) * N ^ (1 : ℝ) := by simp
        _ = N ^ ((-1 / 2 : ℝ) + 1) := (Real.rpow_add hN0 _ _).symm
        _ = N ^ (1 / 2 : ℝ) := by congr 1; norm_num
    calc
      _ = ‖∫ y in N..N1, (y : ℂ) ^ s‖ := by rw [hint]
      _ ≤ N ^ (-1 / 2 : ℝ) * |N1 - N| := hsmall
      _ ≤ N ^ (-1 / 2 : ℝ) * N :=
        mul_le_mul_of_nonneg_left hlength (Real.rpow_nonneg hN0.le _)
      _ = N ^ (1 / 2 : ℝ) := hpow
      _ ≤ 5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
        rw [le_div_iff₀ (by positivity : 0 < 1 + |t|)]
        nlinarith [Real.rpow_nonneg hN0.le (1 / 2 : ℝ)]
  · have htlarge : 1 < |t| := lt_of_not_ge ht
    have htpos : 0 < |t| := by linarith
    have hformula : ‖∫ y in N..N1,
        (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖ =
        ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ / ‖d‖ := by
      rw [hvalue, Complex.norm_div]
    have hfirst : ‖(N1 : ℂ) ^ d - (N : ℂ) ^ d‖ / ‖d‖ ≤
        ((5 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) / |t| := by
      apply (div_le_div_iff₀ hdenpos htpos).2
      exact mul_le_mul hnum hden2 (abs_nonneg t) (by positivity)
    have hlast : ((5 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) / |t| ≤
        5 * N ^ (1 / 2 : ℝ) / (1 + |t|) := by
      apply (div_le_div_iff₀ htpos (by positivity : 0 < 1 + |t|)).2
      have hratio : 1 + |t| ≤ 2 * |t| := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hratio (by positivity :
        0 ≤ (5 / 2 : ℝ) * N ^ (1 / 2 : ℝ))]
    exact hformula ▸ hfirst.trans hlast

/-- LEAF. Page 21. Frequency inequality conversion. -/
theorem fgm_frequency_conversion :
  ∀ x N t : ℝ, 2 ≤ x → x ^ (1/4 : ℝ) ≤ N → N ≤ x →
  |t| ^ (1 / 2 : ℝ) * x ^ (1 / 16 : ℝ) < N →
  (|t| + 1) ^ (1 / 2 : ℝ) ≤ 2 * N ^ (1 - 1 / 16 : ℝ) := by
  intro x N t hx hroot hNx hsplit
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ N :=
    (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hroot
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (1 / 16 : ℝ) ≤ x ^ (1 / 16 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hNx (by norm_num)
  have hprod : |t| ^ (1 / 2 : ℝ) * N ^ (1 / 16 : ℝ) < N :=
    (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg t) _)).trans_lt hsplit
  have hsqrt : |t| ^ (1 / 2 : ℝ) < N ^ (15 / 16 : ℝ) := by
    have hden : 0 < N ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hN0 _
    have hdiv := (lt_div_iff₀ hden).2 hprod
    have hid : N / N ^ (1 / 16 : ℝ) = N ^ (15 / 16 : ℝ) := by
      calc
        N / N ^ (1 / 16 : ℝ) = N ^ (1 : ℝ) / N ^ (1 / 16 : ℝ) := by rw [Real.rpow_one]
        _ = N ^ (1 - 1 / 16 : ℝ) := (Real.rpow_sub hN0 1 (1 / 16 : ℝ)).symm
        _ = N ^ (15 / 16 : ℝ) := by congr 1; norm_num
    rwa [hid] at hdiv
  have htsquare : |t| ≤ N ^ (15 / 8 : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg t) _)
      hsqrt.le (by norm_num : (0 : ℝ) ≤ 2)
    have hleft : (|t| ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = |t| := by
      rw [← Real.rpow_mul (abs_nonneg t)]
      norm_num
    have hright : (N ^ (15 / 16 : ℝ)) ^ (2 : ℝ) = N ^ (15 / 8 : ℝ) := by
      rw [← Real.rpow_mul hN0.le]
      norm_num
    calc
      |t| = (|t| ^ (1 / 2 : ℝ)) ^ 2 := hleft.symm
      _ ≤ (N ^ (15 / 16 : ℝ)) ^ 2 := hh
      _ = N ^ (15 / 8 : ℝ) := hright
  have hNpow1 : 1 ≤ N ^ (15 / 8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hpower : (N ^ (15 / 16 : ℝ)) ^ 2 = N ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hbase : |t| + 1 ≤ (2 * N ^ (15 / 16 : ℝ)) ^ 2 := by
    rw [mul_pow, hpower]
    nlinarith
  have hB : 0 ≤ 2 * N ^ (15 / 16 : ℝ) := by positivity
  calc
    (|t| + 1) ^ (1 / 2 : ℝ) = Real.sqrt (|t| + 1) := by rw [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt ((2 * N ^ (15 / 16 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hbase
    _ = 2 * N ^ (15 / 16 : ℝ) := Real.sqrt_sq hB
    _ = 2 * N ^ (1 - 1 / 16 : ℝ) := by congr 2; norm_num

/-- LEAF. Page 21. Combination of remainder bounds. -/
theorem fgm_combine_remainders :
  ∀ C_FGM K_2 N ε : ℝ, 1 ≤ N → 0 < ε →
  C_FGM * N ^ (-1 / 2 : ℝ) * (K_2 * N ^ (ε / 8)) * (2 * N ^ (1 - ε / 4))
  ≤ 2 * C_FGM * K_2 * N ^ (1 / 2 - min (ε / 8) (1 / 4)) := by sorry

/-- LEAF. Page 21. Main decomposition branch -/
theorem fgm_branch :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ N N1 : ℝ, x ^ ε ≤ N → N ≤ x → N ≤ N1 → N1 ≤ 2 * N →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, |t| ≤ x → |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) < N →
      ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
        C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) := by
  exact Decomp90.fgm_branch

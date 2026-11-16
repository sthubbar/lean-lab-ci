/-
Split of `bv_remainder` from `Decomp506b` into its proof steps. The three leaves are the
distribution input for squarefree moduli at level `Y ^ (1 / 9)`, the logarithmic size of
that modulus range, and the large-`X` regime of the parameters. The assembly
`bv_remainder_split` has no sorry of its own: it is bookkeeping, converting the
modulus-weighted discrepancy sum into the unweighted sum inside `remainder` and paying
one logarithmic factor for it.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp506b
import LeanLab.KumchevLiu2007.Decomp542a
import LeanLab.KumchevLiu2007.MaximalBV634
import LeanLab.PNTPort.BV.FromSW
import LeanLab.PNTPort.PsiChi.SiegelWalfisz
import LeanLab.PNTPort.BVMax.Primes

namespace LeanLab.KumchevLiu2007.Task506b

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Divisor-weighted maximal Bombieri--Vinogradov. -/
theorem weighted_maximal_bv (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError T d) ≤ C * T * Real.log T ^ (-A) := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ := maximal_bv_pi (2 * A + 6) (by linarith)
  refine ⟨b, Real.sqrt (Real.exp 48 * (2 + 2 * Real.exp 24) * C),
    max T0 (Real.exp 1), hb, Real.sqrt_pos.mpr (by positivity),
    hT0.trans (le_max_left _ _), ?_⟩
  intro T hT D hD
  have hTbase : T0 ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := hT0.trans hTbase
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hL : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTe
    simpa only [Real.log_exp] using h
  have hlpow : Real.log T ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hroot : Real.sqrt T ≤ T := by
    have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg T]
  have hDT : (D : ℝ) ≤ T := hD.trans ((mul_le_of_le_one_right
    (Real.sqrt_nonneg T) hlpow).trans hroot)
  apply Task542a.weighted_prime_errors_of_sum D T A C hT2 hL hDT hC.le
  simpa only [neg_add_rev, neg_mul, neg_neg, add_comm, sub_eq_add_neg] using hBV T hTbase D hD

/-- LEAF: The divisor-weighted prime error sum over the prime window. -/
theorem prime_window_weighted_bv' (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in Filter.atTop,
      (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d) ≤
        K * errorScale X ε A := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ := weighted_maximal_bv A hA
  let R : ℝ := 32 * (2 * B + 18)
  refine ⟨C * (8 : ℝ) ^ A * R, by dsimp [R]; positivity, ?_⟩
  filter_upwards [Task542a.prime_window_bv_parameters b T0 B ε hb hB hε hε1,
    prime_reciprocal_bound B ε hB hε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop (1 : ℝ)]
    with X hparams hrec hL1 hX
  have hL : 0 < Real.log X := hparams.1
  have hrecR : (∑ p ∈ primeWindow X B ε, (1 : ℝ) / p) ≤ R := by
    apply hrec.2.2.trans
    have hlog := Real.log_le_sub_one_of_pos hL
    apply (div_le_iff₀ hL).mpr
    dsimp [R]
    have hR : (0 : ℝ) ≤ 32 * (2 * B + 18) := by positivity
    nlinarith
  have hpow : (Real.log X / 8) ^ (-A) = (8 : ℝ) ^ A * Real.log X ^ (-A) := by
    rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul]
    ring
  have hlocal (p : ℕ) (hp : p ∈ primeWindow X B ε) :
      (∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
        (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d) ≤
      C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) := by
    obtain ⟨hT, hlog1, hloglo, hloghi, hlevel⟩ := hparams.2 p hp
    have hD : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤
        Real.sqrt (Real.sqrt (Y X ε) / p) * Real.log (Real.sqrt (Y X ε) / p) ^ (-b) :=
      (Nat.floor_le (Real.rpow_nonneg (by unfold Y; exact Real.rpow_nonneg (by linarith : 0 ≤ X) _) _)).trans hlevel
    apply (hBV _ hT _ hD).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← hpow]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hloglo (by linarith)
  calc (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d)
      ≤ ∑ p ∈ primeWindow X B ε,
        C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) :=
        Finset.sum_le_sum hlocal
    _ = (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) *
        ∑ p ∈ primeWindow X B ε, (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) * R :=
      mul_le_mul_of_nonneg_left hrecR (by positivity)
    _ = (C * (8 : ℝ) ^ A * R) * errorScale X ε A := by
      unfold errorScale
      rw [Real.sqrt_eq_rpow]
      ring

/-- LEAF: The full remainder estimate, from the unconditional maximal Bombieri--Vinogradov. -/
theorem bv_remainder_from_maximal' (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨K, hK, hprime⟩ := prime_window_weighted_bv' A B ε hA hB hε hε1
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      ∀ n : ℕ, X < (n : ℝ) → remainder X B ε n ≤ (2 * K + 4) * errorScale X ε A := by
    filter_upwards [hprime, Task542a.rough_level_parameters B ε hB hε hε1,
      Task542a.prime_window_bv_parameters 1 2 B ε (by norm_num) hB hε hε1,
      Task542a.endpoint_correction_bound A B ε hε] with X hp hr hw he
    intro n hXn
    have hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        ∀ p ∈ primeWindow X B ε, d < p ∧
          2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
            (d : ℝ) ≤ Real.sqrt (Y X ε) / p := by
      intro d hd p hpp
      obtain ⟨hT, hlog, hlo, hhi, hlevel⟩ := hw.2 p hpp
      have hdD : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) :=
        (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).trans
          (Nat.floor_le (Real.rpow_nonneg hr.1.le _))
      have hpz := (Finset.mem_filter.mp hpp).2.2.1
      have hdp : d < p := by exact_mod_cast (hdD.trans_lt (hr.2.2.trans_le hpz))
      have hlogpow : Real.log (Real.sqrt (Y X ε) / p) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
      have hroot : Real.sqrt (Real.sqrt (Y X ε) / p) ≤ Real.sqrt (Y X ε) / p := by
        have hh := Real.sq_sqrt (show 0 ≤ Real.sqrt (Y X ε) / p by positivity)
        nlinarith [Real.sqrt_nonneg (Real.sqrt (Y X ε) / p)]
      have hdT := hdD.trans (hlevel.trans ((mul_le_of_le_one_right
        (Real.sqrt_nonneg _) hlogpow).trans hroot))
      exact ⟨hdp, hT, hlog, hdT⟩
    have ht := Task542a.remainder_prime_transfer X B ε n hr.1 hr.2.1 hXn hparams
    nlinarith
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨2 * K + 4, X0, by positivity, ?_⟩
  intro X hX n hn hXn hnhi
  exact hX0 X hX n hXn

/-- LEAF: Step 1 of the split, the distribution input, now proved from the lab's
unconditional Siegel--Walfisz-based Bombieri--Vinogradov. -/
theorem weighted_modulus_discrepancy (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) ≤ C * errorScale X ε (A + 1) := by
  obtain ⟨C, X0, hC, h⟩ := bv_remainder_from_maximal' (A + 1) B ε (by linarith) hB hε hε1
  refine ⟨C, X0, hC, ?_⟩
  intro X hX n hn hXn hnle
  refine (Finset.sum_le_sum ?_).trans (h X hX n hn hXn hnle)
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1R
  have hp : 0 < 1 + Real.log (d : ℝ) := by linarith
  have hle : 1 / (1 + Real.log (d : ℝ)) ≤ 1 := by
    rw [div_le_one hp]
    linarith
  have hnn : 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      |progressionCount X B ε n d - density n d * primeMass X B ε| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg _)
  calc (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |progressionCount X B ε n d - density n d * primeMass X B ε| /
          (1 + Real.log (d : ℝ))
      = ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|) *
            (1 / (1 + Real.log (d : ℝ))) := by ring
    _ ≤ ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|) * 1 :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| := by ring



/-- LEAF: Step 2 of the split, the logarithmic size of the modulus range. With
`D = ⌊Y ^ (1 / 9)⌋` and `Y = X ^ (7 / 12 + ε / 2)`, every modulus `1 ≤ d ≤ D` has
`log d ≤ (8 / 81) log X`, so beyond a threshold `1 + log d ≤ 2 log X`. -/
theorem sieve_level_log_scale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX d hd1 hdD
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hL1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hDpos : (0 : ℝ) < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  have hdle : (d : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
    have h1 : (d : ℝ) ≤ (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hdD
    have h2 : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) := Nat.floor_le hDpos.le
    have h3 : Y X ε ^ (1 / 9 : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
      have hexp : (7 / 12 + ε / 2) * (1 / 9) ≤ 8 / 81 := by linarith
      calc Y X ε ^ (1 / 9 : ℝ) = (X ^ (7 / 12 + ε / 2)) ^ (1 / 9 : ℝ) := rfl
        _ = X ^ ((7 / 12 + ε / 2) * (1 / 9)) := (Real.rpow_mul hX0.le _ _).symm
        _ ≤ X ^ (8 / 81 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hexp
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hlogd : Real.log (d : ℝ) ≤ 8 / 81 * Real.log X := by
    have h := Real.log_le_log hdpos hdle
    rwa [Real.log_rpow hX0] at h
  nlinarith

/-- LEAF: Step 3 of the split, the large-`X` regime of the parameters. Beyond a threshold
`log X ≥ 1`, the ninth power of the window `Y` is at least one, and the error scale at the
parameter `A` is nonnegative. These are the side conditions the assembly uses at every `X`
in the range. -/
theorem sieve_regime (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hlog1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hY1 : 1 ≤ Y X ε := by
    unfold Y
    exact Real.one_le_rpow hX1 (by linarith)
  have hY0 : 0 < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  refine ⟨hlog1, Real.one_le_rpow hY1 (by norm_num), ?_⟩
  unfold errorScale
  have h1 : 0 ≤ Y X ε ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hY1)) _
  have h2 : 0 ≤ Real.log X ^ (-A) :=
    le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog1) _)
  exact mul_nonneg h1 h2

/-- LEAF: Split of `bv_remainder`: the explicit squarefree remainder at level `Y ^ (1 / 9)` is at
most a constant times `Y ^ (1 / 2) * (log X) ^ (-A)`, from the three leaves above and the
definition of `remainder`. -/
theorem bv_remainder_split (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨Cw, Xw, hCw, hw⟩ := weighted_modulus_discrepancy A B ε hA hB hε hε1
  obtain ⟨Xl, hXl, hl⟩ := sieve_level_log_scale ε hε hε1
  obtain ⟨Xr, hXr, hr⟩ := sieve_regime A ε hA hε
  refine ⟨2 * Cw, max Xw (max Xl Xr), by linarith, ?_⟩
  intro X hX n hn hXn hnle
  have hXw : Xw ≤ X := (le_max_left _ _).trans hX
  have hrest : max Xl Xr ≤ X := (le_max_right _ _).trans hX
  have hXl' : Xl ≤ X := (le_max_left _ _).trans hrest
  obtain ⟨hlog1, hY1, hE0⟩ := hr X ((le_max_right _ _).trans hrest)
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlog1
  have hw' := hw X hXw n hn hXn hnle
  unfold remainder
  have hstep : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| ≤
        (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hwpos : 0 < 1 + Real.log (d : ℝ) := by
      have hnn := Real.log_nonneg hd1R
      linarith
    have hwle : 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := hl X hXl' d hd1 hdD
    have hu : 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ)) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hwpos.le
    calc (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
        = ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (1 + Real.log (d : ℝ)) :=
          (div_mul_cancel₀ _ hwpos.ne').symm
      _ ≤ ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left hwle hu
      _ = (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by rw [mul_comm]
  calc ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ))) := Finset.sum_le_sum hstep
    _ = (2 * Real.log X) * ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.log X) * (Cw * errorScale X ε (A + 1)) :=
        mul_le_mul_of_nonneg_left hw' (by linarith)
    _ = 2 * Cw * errorScale X ε A := by
        unfold errorScale
        have hkey : Real.log X * Real.log X ^ (-(A + 1)) = Real.log X ^ (-A) := by
          rw [show (-A : ℝ) = 1 + -(A + 1) by ring, Real.rpow_add hL, Real.rpow_one]
        calc (2 * Real.log X) * (Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + 1))))
            = 2 * Cw * (Real.log X * Real.log X ^ (-(A + 1))) * Y X ε ^ (1 / 2 : ℝ) := by
              ring
          _ = 2 * Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
              rw [hkey]; ring

end LeanLab.KumchevLiu2007.Task506b

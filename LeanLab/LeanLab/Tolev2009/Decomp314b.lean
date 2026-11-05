/-
AI wrote this Lean code. Codex task314.
Binary Goldbach is open.
Sources: Halupczok 2008 pages 11 to 12 and 18 to 19.
The geometric integral is proved. The arithmetic coefficient inputs remain OPEN.
-/
import LeanLab.Tolev2009.Integral314
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset Real MeasureTheory Filter
namespace LeanLab.Tolev2009.Decomp314b
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a

/-- Halupczok pages 11 to 12, the product of the three totients. -/
noncomputable def phiProduct (k : Fin 3 → ℕ) : ℝ :=
  ∏ i : Fin 3, ((k i).totient : ℝ)

/-- Halupczok page 18, q times the absolute normalised singular coefficient. -/
noncomputable def weightedCoeff (k l : Fin 3 → ℕ) (N q : ℕ) : ℝ :=
  (q : ℝ) * ‖ssTerm k l N q‖ / phiProduct k

/-- Halupczok pages 18 to 19, the common first absolute moment for e1 and e2. -/
noncomputable def coefficientMass (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  ∑' q : ℕ, weightedCoeff k l N q

/-- Positivity of the arithmetic denominator, including the zero modulus convention. -/
theorem phiProduct_nonneg (k : Fin 3 → ℕ) : 0 ≤ phiProduct k := by
  exact prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- Every term in the absolute first moment is nonnegative. -/
theorem weightedCoeff_nonneg (k l : Fin 3 → ℕ) (N q : ℕ) :
    0 ≤ weightedCoeff k l N q := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (phiProduct_nonneg k)

/-- The total first moment is nonnegative even before its summability is supplied. -/
theorem coefficientMass_nonneg (k l : Fin 3 → ℕ) (N : ℕ) :
    0 ≤ coefficientMass k l N :=
  tsum_nonneg fun q => weightedCoeff_nonneg k l N q

/-- Taking absolute values removes the bounded third weight.
This is the finite averaging step used for e1 and e2 on Halupczok page 12. -/
theorem EF_dominate (F G : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ)
    (lam : ℕ → ℝ) (l₃ : ℕ) (B c : ℝ) (N : ℕ)
    (hlam : ∀ k, |lam k| ≤ 1) (hc : 0 ≤ c)
    (hG : ∀ k l, 0 ≤ G k l)
    (hFG : ∀ k l, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      |F k l| ≤ c * G k l) :
    EF F lam l₃ B N ≤ c * EF G (fun _ => 1) l₃ B N := by
  unfold EF
  simp only [mul_sum]
  apply sum_le_sum
  intro k₁ hk₁
  apply sum_le_sum
  intro k₂ hk₂
  have h0 := mul_nonneg hc (innerF_nonneg G (fun _ => 1) l₃
    ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊ k₁ k₂)
  unfold innerF
  refine Real.iSup_le (fun l₁ => Real.iSup_le (fun h₁ => Real.iSup_le
    (fun l₂ => Real.iSup_le (fun h₂ => ?_) h0) h0) h0) h0
  have hs : |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
      (fun k₃ => Nat.Coprime k₃ l₃), lam k₃ * F ![k₁, k₂, k₃] ![l₁, l₂, l₃]| ≤
      c * |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
      (fun k₃ => Nat.Coprime k₃ l₃), (1 : ℝ) * G ![k₁, k₂, k₃] ![l₁, l₂, l₃]| := by
    rw [abs_of_nonneg (sum_nonneg fun _ _ => mul_nonneg (by norm_num) (hG _ _)), mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k₃ hk₃
    rw [abs_mul, one_mul]
    have h1 := (mem_Icc.mp hk₁).1
    have h2 := (mem_Icc.mp hk₂).1
    have h3 := (mem_Icc.mp (mem_filter.mp hk₃).1).1
    have hc1 := (mem_filter.mp h₁).2
    have hc2 := (mem_filter.mp h₂).2
    have hc3 := (mem_filter.mp hk₃).2.symm
    exact (mul_le_of_le_one_left (abs_nonneg _) (hlam k₃)).trans
      (hFG _ _ (by intro i; fin_cases i <;> assumption)
        (by intro i; fin_cases i <;> assumption))
  refine hs.trans (mul_le_mul_of_nonneg_left ?_ hc)
  exact le_iSup2 _ _ (fun l₁ l₂ => |∑ k₃ ∈
    (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
      (fun k₃ => Nat.Coprime k₃ l₃), (1 : ℝ) * G ![k₁, k₂, k₃] ![l₁, l₂, l₃]|)
    (fun _ _ => abs_nonneg _) h₁ h₂

/-- LEAF. Halupczok page 18, absolute convergence of the q weighted series.
The prime power and local factor analysis precedes averaging. OPEN. -/
theorem weighted_coeff_summable (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) (hN : Odd N) :
    Summable (fun q : ℕ => weightedCoeff k l N q) := by
  sorry

/-- LEAF. Halupczok pages 18 to 19, the gcd and divisor moment average.
No major arc integral or progression polynomial occurs in this arithmetic input.
Exponent 5000 exceeds 4924 from the seven reciprocal divisor sums and log losses.
OPEN with the fixed 2009 residue and cutoffs. -/
theorem coefficient_mass_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => coefficientMass k l N) (fun _ => 1) l₃ (10 ^ 4 * A) N ≤
          C * Real.log N ^ (5000 : ℝ) := by
  sorry

/-- Halupczok page 11 and Tolev 1999 page 78 after display 35.
Only the finite geometric integral is estimated. No arithmetic coefficient occurs.
The condition N at most tau squared absorbs the lattice endpoint error. -/
theorem geometric_integral_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N q : ℕ) (τ : ℝ), 1 ≤ q → 2 ≤ τ → (N : ℝ) ≤ τ ^ 2 →
      ‖arcIntegral τ N q - ((N : ℂ) ^ 2 / 2)‖ ≤ C * (q : ℝ) ^ 2 * τ ^ 2 := by
  exact ⟨4, by norm_num, fun N q τ hq hτ hN =>
    Integral314.geometric_integral_estimate N q τ hq hτ hN⟩

/-- Halupczok page 12, the finite main term in the complex normalisation of model. -/
theorem truncatedMain_as_re (Q : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    truncatedMain Q k l N =
      (∑ q ∈ Icc 1 ⌊Q⌋₊, ssTerm k l N q /
        (∏ i : Fin 3, ((k i).totient : ℂ)) * ((N : ℂ) ^ 2 / 2)).re := by
  simp only [← sum_mul, ← sum_div]
  have hd : (∏ i : Fin 3, ((k i).totient : ℂ)) = (phiProduct k : ℂ) := by
    simp [phiProduct]
  have hn : ((N : ℂ) ^ 2 / 2) = (((N : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hd, hn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.div_ofReal_re]
  simp only [truncatedMain, phiProduct, Fin.prod_univ_three]
  ring

/-- Halupczok pages 11 to 12, subtract only the finite integral main term. -/
theorem finite_integral_difference (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    model Q τ k l N - truncatedMain Q k l N =
      (∑ q ∈ Icc 1 ⌊Q⌋₊, ssTerm k l N q /
        (∏ i : Fin 3, ((k i).totient : ℂ)) *
          (arcIntegral τ N q - ((N : ℂ) ^ 2 / 2))).re := by
  rw [truncatedMain_as_re]
  simp [model, mul_sub, sum_sub_distrib]

/-- Halupczok page 19, the finite q squared moment is bounded by Q times the first moment. -/
theorem finite_second_moment (Q : ℝ) (k l : Fin 3 → ℕ) (N : ℕ)
    (hQ : 0 ≤ Q) (hs : Summable (fun q : ℕ => weightedCoeff k l N q)) :
    ∑ q ∈ Icc 1 ⌊Q⌋₊, (q : ℝ) ^ 2 * ‖ssTerm k l N q‖ / phiProduct k ≤
      Q * coefficientMass k l N := by
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, Q * weightedCoeff k l N q := by
      apply sum_le_sum
      intro q hq
      have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hQ)
      have hn := weightedCoeff_nonneg k l N q
      calc
        _ = (q : ℝ) * weightedCoeff k l N q := by unfold weightedCoeff; ring
        _ ≤ Q * weightedCoeff k l N q := mul_le_mul_of_nonneg_right hqQ hn
    _ = Q * ∑ q ∈ Icc 1 ⌊Q⌋₊, weightedCoeff k l N q := by rw [mul_sum]
    _ ≤ Q * coefficientMass k l N :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun q _ => weightedCoeff_nonneg k l N q)) hQ

/-- Halupczok page 12, pass the geometric integral error through the finite coefficient sum.
CONDITIONAL ON the explicit pointwise integral estimate and summability premise. -/
theorem finite_integral_contraction (Q τ c : ℝ) (k l : Fin 3 → ℕ) (N : ℕ)
    (hQ : 0 ≤ Q) (hc : 0 ≤ c)
    (hs : Summable (fun q : ℕ => weightedCoeff k l N q))
    (he : ∀ q ∈ Icc 1 ⌊Q⌋₊,
      ‖arcIntegral τ N q - ((N : ℂ) ^ 2 / 2)‖ ≤ c * (q : ℝ) ^ 2 * τ ^ 2) :
    |model Q τ k l N - truncatedMain Q k l N| ≤
      (c * τ ^ 2 * Q) * coefficientMass k l N := by
  rw [finite_integral_difference]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊,
        c * τ ^ 2 * ((q : ℝ) ^ 2 * ‖ssTerm k l N q‖ / phiProduct k) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, norm_div]
      have hd : ‖∏ i : Fin 3, ((k i).totient : ℂ)‖ = phiProduct k := by
        simp [norm_prod, phiProduct, Complex.norm_natCast]
      rw [hd]
      calc
        _ ≤ (‖ssTerm k l N q‖ / phiProduct k) * (c * (q : ℝ) ^ 2 * τ ^ 2) :=
          mul_le_mul_of_nonneg_left (he q hq) (div_nonneg (norm_nonneg _) (phiProduct_nonneg k))
        _ = _ := by ring
    _ = c * τ ^ 2 * (∑ q ∈ Icc 1 ⌊Q⌋₊,
        (q : ℝ) ^ 2 * ‖ssTerm k l N q‖ / phiProduct k) := by rw [mul_sum]
    _ ≤ c * τ ^ 2 * (Q * coefficientMass k l N) :=
      mul_le_mul_of_nonneg_left (finite_second_moment Q k l N hQ hs) (by positivity)
    _ = _ := by ring

/-- Halupczok page 19, the first moment loses only one power of the major arc cutoff. -/
theorem logarithmic_absorption (A L : ℝ) (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ L) :
    L ^ (5000 : ℝ) / L ^ (20 * A) ≤ L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.rpow_sub hL0]
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-- Halupczok page 12, transfer a pointwise first moment bound through the weighted mean. -/
theorem mean_of_mass_bound
    (F : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℝ)
    (A D C : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ)
    (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ Real.log N) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hlam : ∀ k, |lam k| ≤ 1)
    (hm : EF (fun k l => coefficientMass k l N) (fun _ => 1) l₃ (10 ^ 4 * A) N ≤
      C * Real.log N ^ (5000 : ℝ))
    (he : ∀ k l, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      |F k l| ≤ (D * (N : ℝ) ^ 2 / Qof A N) * coefficientMass k l N) :
    EF F lam l₃ (10 ^ 4 * A) N ≤ D * C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos (by linarith) _
  have hd : 0 ≤ D * (N : ℝ) ^ 2 / Qof A N := by positivity
  calc
    _ ≤ (D * (N : ℝ) ^ 2 / Qof A N) *
        EF (fun k l => coefficientMass k l N) (fun _ => 1) l₃ (10 ^ 4 * A) N :=
      EF_dominate _ _ lam l₃ _ _ N hlam hd (fun k l => coefficientMass_nonneg k l N) he
    _ ≤ (D * (N : ℝ) ^ 2 / Qof A N) * (C * Real.log N ^ (5000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hd
    _ = (D * C * (N : ℝ) ^ 2) *
        (Real.log N ^ (5000 : ℝ) / Real.log N ^ (20 * A)) := by unfold Qof; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (logarithmic_absorption A (Real.log N) hA hL) (by positivity)

/-- The major arc parameters eventually satisfy the finite integral size regime.
This is the elementary cutoff condition implicit on Halupczok page 11. -/
theorem integral_cutoff_regime (A : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ Real.log N ∧ 2 ≤ τof A N ∧ (N : ℝ) ≤ (τof A N) ^ 2 := by
  have he := (isLittleO_log_rpow_rpow_atTop (40 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (he.and (hl.and (eventually_ge_atTop (4 : ℝ))))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨heN, hL, h4⟩ := hN₀ N hN
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos hL0 _
  have hsq : (Qof A N) ^ 2 ≤ (N : ℝ) := by
    have hr : (Qof A N) ^ 2 = Real.log N ^ (40 * A) := by
      unfold Qof
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    rw [hr]
    simpa only [Real.rpow_one, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _),
      abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] using heN
  have hτ : 0 ≤ τof A N := div_nonneg (Nat.cast_nonneg N) hQ.le
  have hprod : τof A N * Qof A N = N := by unfold τof; exact div_mul_cancel₀ _ hQ.ne'
  have hQt : Qof A N ≤ τof A N := by
    by_contra hn
    have hx := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hQ
    nlinarith [hsq, hprod]
  have hsqτ : (N : ℝ) ≤ (τof A N) ^ 2 := by
    calc
      _ = τof A N * Qof A N := hprod.symm
      _ ≤ τof A N * τof A N := mul_le_mul_of_nonneg_left hQt hτ
      _ = _ := by ring
  refine ⟨hL, ?_, hsqτ⟩
  nlinarith

/-- Exact sealed finite singular integral error statement.
CONDITIONAL ON the two arithmetic first moment leaves. -/
theorem singular_integral_error :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => model (Qof A N) (τof A N) k l N -
            truncatedMain (Qof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨c, hc, he⟩ := geometric_integral_error
  obtain ⟨C, Nm, hC, hm⟩ := coefficient_mass_mean A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := integral_cutoff_regime A
  refine ⟨c * C, max Nm Ng, ?_⟩
  intro lam hlam N hodd hN
  have hNm := (le_max_left _ _).trans hN
  have hNg := (le_max_right _ _).trans hN
  obtain ⟨hL, hτ, hNτ⟩ := hg N hNg
  apply mean_of_mass_bound _ A c C lam l₃ N hA hL hc hC hlam (hm N hodd hNm)
  intro k l hk hl
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos (by linarith) _
  have ht := finite_integral_contraction (Qof A N) (τof A N) c k l N hQ.le hc
    (weighted_coeff_summable k l N hk hl hodd)
    (fun q hq => he N q (τof A N) (mem_Icc.mp hq).1 hτ hNτ)
  have hid : c * (τof A N) ^ 2 * Qof A N = c * (N : ℝ) ^ 2 / Qof A N := by
    unfold τof
    field_simp
  simpa only [hid] using ht

end LeanLab.Tolev2009.Decomp314b

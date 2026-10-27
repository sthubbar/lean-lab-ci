/-
P0045 Languasco, Pintz, Zaccagnini 2007, Section 3, and idea I-0091: the minor arc L² bound
from a minor arc sup bound, by Bessel's inequality on the interval `(P/X, P/X + 1]`.

Unit U-1220, T2 FRONTIER, PC run 20261020T1203Z-6833.

Source: P0045 preprint p.4, Section 3. The paper: by Lemma 6.3, `S(α) ≪ X^{4/5} L⁴` on `𝔪`;
then `Σ_{N ∈ J(X)} |R''_𝔪(N)|² ≤ ∫_𝔪 |S|⁴ |G|^{2k} ≪ X^{8/5} L^{8+2k} ∫₀¹ |S|² ≪ X^{13/5} L^{2k+9}`,
by Bessel, `|G| ≤ L` and `∫₀¹ |S|² = Σ_{m ≤ X} Λ(m)² ≪ X log X`.

What is here, all PROVED unconditional unless said:
* `bessel_interval`: Bessel's inequality for the system `e(nx)` on any interval `(a, a + 1]`,
  for every `f ∈ L²`, from Mathlib's Parseval on `ℝ/ℤ` through `AddCircle.liftIoc`.
* `Rmpp_eq`: `R''_𝔪(N)` is the `N`-th Fourier coefficient on `(P/X, P/X + 1]` of
  `1_𝔪 S² G^k`; needs `𝔪` measurable, `measurableSet_majorArcs`.
* `integral_norm_sq_Sx`: `∫_a^{a+1} |S|² = Σ_{m ≤ X} Λ(m)²`, Parseval for `S`.
* `sum_vonMangoldt_sq_le`: `Σ_{m ≤ X} Λ(m)² ≤ (log 4 + 4) X log X`, from Mathlib's Chebyshev bound.
* `MinorBoundσ σ`: `S(α) ≤ B X^σ L⁴` on `𝔪`; `minorBound_iff`: at `σ = 4/5` it is the cited
  `MinorBound` exactly.
* `minorL2σ_of_bound`: `MinorBoundσ σ → MinorL2σ σ`, for every `σ`.
* `minorL2_of_minorBound`: the paper's Section 3 L² bound from its sup bound, `MinorBound → MinorL2`.
* `exceptional_of_sup`: `MinorBoundσ σ → Eq7σ σ`, exceptions `≪ X^{2σ−1} L^{10}`; with
  `eq7_of_minorBound`, the paper's (7) follows from its sup bound alone, so of the three cited
  Section 3 statements only `minorBound`, the paper's use of Lemma 6.3, remains an input.
* `exceptional_19_24`: I-0091, a minor arc sup `X^{19/24} L⁴` gives exceptions `≪ X^{7/12} L^{10}`,
  CONDITIONAL ON `MinorBoundσ (19/24)`, which the MPR 2026 bound `N^{19/24+ε}` does NOT give as
  stated: it carries `N^ε` and needs major arcs to `N^{5/12}`, outside P0045's `P ≤ X^{0.41}`.

KNOWN mathematics, the paper's own Section 3. AI wrote this Lean code. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.ExceptionalOfSup
import LeanLab.ExceptionalSet.PintzAlthofer2026Sup

namespace LeanLab.LPZ2007.MinorBessel

open Finset Real MeasureTheory AddCircle LeanLab.LPZ2007 LeanLab.LPZ2007.ExceptionalOfSup
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Bessel on an interval of length one -/

theorem fourierCoeff_liftIoc_one (a : ℝ) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (liftIoc 1 a f) n = ∫ x in a..a + 1, e (-(n * x)) * f x := by
  rw [fourierCoeff_eq_intervalIntegral _ _ a]
  rw [div_one, one_smul]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
  rw [Set.uIoc_of_le (by linarith)] at hx
  rw [liftIoc_coe_apply hx, fourier_coe_apply, smul_eq_mul]
  unfold e
  congr 2
  push_cast
  ring

theorem haar_eq_volume : (haarAddCircle : Measure 𝕋) = volume := by
  rw [volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

theorem memLp_liftIoc_one {a : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 1)))) :
    MemLp (liftIoc 1 a f) 2 haarAddCircle := by
  rw [haar_eq_volume]
  exact hf.memLp_liftIoc

theorem integral_norm_sq_liftIoc (a : ℝ) (f : ℝ → ℂ) :
    ∫ t, ‖liftIoc 1 a f t‖ ^ 2 ∂haarAddCircle = ∫ x in a..a + 1, ‖f x‖ ^ 2 := by
  rw [integral_haarAddCircle, inv_one, one_smul]
  have : (fun t => ‖liftIoc 1 a f t‖ ^ 2) = liftIoc 1 a (fun x => ‖f x‖ ^ 2) := rfl
  rw [this, integral_liftIoc_eq_intervalIntegral]

/-- **Bessel's inequality on `(a, a + 1]`**: `Σ_{n∈T} |∫ f(x) e(−nx) dx|² ≤ ∫ |f|²`. -/
theorem bessel_interval (a : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 1))))
    (T : Finset ℕ) :
    ∑ n ∈ T, ‖∫ x in a..a + 1, e (-(n * x)) * f x‖ ^ 2 ≤ ∫ x in a..a + 1, ‖f x‖ ^ 2 := by
  have h := bessel_finset (memLp_liftIoc_one hf) (T.map ⟨((↑) : ℕ → ℤ), Nat.cast_injective⟩)
  rw [Finset.sum_map, integral_norm_sq_liftIoc] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Function.Embedding.coeFn_mk, fourierCoeff_liftIoc_one]
  push_cast
  rfl

/-! ### The minor arcs and `R''_𝔪(N)` -/

theorem measurableSet_majorArcs (X P : ℝ) : MeasurableSet (majorArcs X P) := by
  have : majorArcs X P = ⋃ q : ℕ, ⋃ a : ℕ,
      {_α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q} ∩
        Set.Icc ((a : ℝ) / q - 1 / (q * (X / P))) ((a : ℝ) / q + 1 / (q * (X / P))) := by
    ext α
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨q, a, ⟨h1, h2, h3, h4, h5⟩, h6, h7⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4, h5⟩, h6, h7⟩; exact ⟨q, a, h1, h2, h3, h4, h5, h6, h7⟩
  rw [this]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a =>
    (MeasurableSet.const _).inter measurableSet_Icc

theorem measurableSet_minorArcs (X P : ℝ) : MeasurableSet (minorArcs X P) :=
  measurableSet_Icc.diff (measurableSet_majorArcs X P)

theorem minorArcs_subset (X P : ℝ) : minorArcs X P ⊆ Set.Icc (P / X) (P / X + 1) := by
  intro x hx
  have := hx.1
  rw [Set.mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- `S(α)² G(α)^k`. -/
def Fk (k : ℕ) (X : ℝ) (α : ℝ) : ℂ := Sx X α ^ 2 * Gx X α ^ k

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

theorem continuous_e : Continuous e := by
  unfold e; fun_prop

theorem continuous_Sx (X : ℝ) : Continuous (Sx X) := by
  unfold Sx
  exact continuous_finsetSum _ fun m _ =>
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

theorem continuous_Gx (X : ℝ) : Continuous (Gx X) := by
  unfold Gx
  exact continuous_finsetSum _ fun m _ => continuous_e.comp (continuous_const.mul continuous_id)

theorem norm_Sx_le (X α : ℝ) : ‖Sx X α‖ ≤ ∑ m ∈ Icc 1 ⌊X⌋₊, Λ m := by
  unfold Sx
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_))
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem norm_Gx_le (X α : ℝ) : ‖Gx X α‖ ≤ ⌊Lp X⌋₊ := by
  unfold Gx
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_e, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

theorem continuous_Fk (k : ℕ) (X : ℝ) : Continuous (Fk k X) := by
  unfold Fk
  exact ((continuous_Sx X).pow 2).mul ((continuous_Gx X).pow k)

theorem memLp_indicator_Fk (k : ℕ) (X P a : ℝ) :
    MemLp ((minorArcs X P).indicator (Fk k X)) 2 (volume.restrict (Set.Ioc a (a + 1))) := by
  have hb : ∀ x, ‖Fk k X x‖ ≤ (∑ m ∈ Icc 1 ⌊X⌋₊, Λ m) ^ 2 * (⌊Lp X⌋₊ : ℝ) ^ k := by
    intro x
    unfold Fk
    rw [norm_mul, norm_pow, norm_pow]
    gcongr
    · exact norm_Sx_le X x
    · exact norm_Gx_le X x
  have hm : MemLp (Fk k X) 2 (volume.restrict (Set.Ioc a (a + 1))) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc a (a + 1))) := by
      rw [isFiniteMeasure_restrict]; simp
    exact MemLp.of_bound (continuous_Fk k X).aestronglyMeasurable _ (ae_of_all _ hb)
  exact hm.indicator (measurableSet_minorArcs X P).nullMeasurableSet

/-- `R''_𝔪(N)` is the `N`-th Fourier coefficient of `1_𝔪 S² G^k` on `(P/X, P/X + 1]`. -/
theorem Rmpp_eq (k : ℕ) (X P : ℝ) (N : ℕ) :
    Rmpp k X P N =
      ∫ x in P / X..P / X + 1, e (-(N * x)) * (minorArcs X P).indicator (Fk k X) x := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hm := measurableSet_minorArcs X P
  have : (fun x => e (-(N * x)) * (minorArcs X P).indicator (Fk k X) x) =
      (minorArcs X P).indicator (fun x => Fk k X x * e (-(N * x))) := by
    ext x
    by_cases hx : x ∈ minorArcs X P
    · simp [hx, mul_comm]
    · simp [hx]
  rw [this, setIntegral_indicator hm]
  have h1 : (Set.Ioc (P / X) (P / X + 1) ∩ minorArcs X P : Set ℝ) =ᵐ[volume]
      (Set.Icc (P / X) (P / X + 1) ∩ minorArcs X P : Set ℝ) :=
    (Ioc_ae_eq_Icc).inter (ae_eq_refl _)
  rw [Set.inter_eq_right.mpr (minorArcs_subset X P)] at h1
  unfold Rmpp
  exact setIntegral_congr_set h1.symm

/-! ### Parseval for `S` and the mean value `Σ Λ(m)² ≪ X log X` -/

theorem sum_range_succ_eq_Icc {β : Type*} [AddCommMonoid β] (f : ℕ → β) (h0 : f 0 = 0) (n : ℕ) :
    ∑ m ∈ range (n + 1), f m = ∑ m ∈ Icc 1 n, f m := by
  rw [Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_eq_sum_Ico_succ_bot (by omega), h0, zero_add]

theorem liftIoc_Sx (X a : ℝ) :
    liftIoc 1 a (Sx X) = trig (fun m => (Λ m : ℂ)) ⌊X⌋₊ := by
  funext t
  set y : ℝ := (equivIoc 1 a t : ℝ) with hy
  have ht : ((y : ℝ) : 𝕋) = t := coe_equivIoc
  have hl : liftIoc 1 a (Sx X) t = Sx X y := rfl
  rw [hl, ← ht]
  unfold Sx trig
  rw [sum_range_succ_eq_Icc _ (by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fourier_coe_apply]
  unfold e
  congr 2
  push_cast
  ring

theorem integral_norm_sq_Sx (X a : ℝ) :
    ∫ x in a..a + 1, ‖Sx X x‖ ^ 2 = ∑ m ∈ range (⌊X⌋₊ + 1), Λ m ^ 2 := by
  rw [← integral_norm_sq_liftIoc, liftIoc_Sx, LeanLab.ExceptionalSet.PintzAlthofer2026Sup.parseval_trig]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem sum_vonMangoldt_eq_psi (X : ℝ) :
    ∑ m ∈ range (⌊X⌋₊ + 1), Λ m = Chebyshev.psi X := by
  rw [sum_range_succ_eq_Icc _ (by simp)]
  unfold Chebyshev.psi
  rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]

theorem sum_vonMangoldt_sq_le {X : ℝ} (hX : 1 ≤ X) :
    ∑ m ∈ range (⌊X⌋₊ + 1), Λ m ^ 2 ≤ (Real.log 4 + 4) * X * Real.log X := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have h1 : ∑ m ∈ range (⌊X⌋₊ + 1), Λ m ^ 2 ≤ ∑ m ∈ range (⌊X⌋₊ + 1), Real.log X * Λ m := by
    refine Finset.sum_le_sum fun m hm => ?_
    rw [sq]
    refine mul_le_mul_of_nonneg_right ?_ ArithmeticFunction.vonMangoldt_nonneg
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, ArithmeticFunction.map_zero]; exact hlogX
    · refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hpos) ?_)
      have : m ≤ ⌊X⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
  rw [← Finset.mul_sum, sum_vonMangoldt_eq_psi] at h1
  have h2 := Chebyshev.psi_le_const_mul_self (x := X) (by linarith)
  calc _ ≤ Real.log X * Chebyshev.psi X := h1
    _ ≤ Real.log X * ((Real.log 4 + 4) * X) := mul_le_mul_of_nonneg_left h2 hlogX
    _ = (Real.log 4 + 4) * X * Real.log X := by ring

/-! ### Section 3 with a general exponent -/

/-- The minor arc sup bound with a general exponent: `|S(α)| ≤ B X^σ L⁴` on `𝔪`. -/
def MinorBoundσ (σ : ℝ) : Prop :=
  ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P → ∀ α ∈ minorArcs X P,
    ‖Sx X α‖ ≤ B * X ^ σ * Lg X ^ 4

/-- At `σ = 4/5` it is the cited `MinorBound`. -/
theorem minorBound_iff : MinorBound ↔ MinorBoundσ (4 / 5) := Iff.rfl

theorem log_eq_Lg {X : ℝ} : Real.log X = Real.log 2 * Lg X := by
  unfold Lg Real.logb
  field_simp

/-- **The Section 3 L² bound from the sup bound, every `σ`, PROVED unconditional.** -/
theorem minorL2σ_of_bound {σ : ℝ} (h : MinorBoundσ σ) : MinorL2σ σ := by
  intro k _hk
  obtain ⟨B, X0, hB⟩ := h
  refine ⟨B ^ 2 * ((Real.log 4 + 4) * Real.log 2), max X0 2, fun X hX P hP => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Lg X := one_le_Lg hX2
  have hL0 : 0 < Lg X := by linarith
  set L := Lg X with hLdef
  set a : ℝ := P / X with ha
  set M : ℝ := B * X ^ σ * L ^ 4 with hM
  set G0 : ℝ := (⌊Lp X⌋₊ : ℝ) with hG0
  have hG0L : G0 ≤ L := by
    have hLp : Lp X ≤ L := by
      unfold Lp; rw [← hLdef]; linarith [Real.sqrt_nonneg L]
    rw [hG0]
    rcases le_or_gt 0 (Lp X) with h | h
    · exact (Nat.floor_le h).trans hLp
    · rw [Nat.floor_eq_zero.2 (by linarith)]; simp; linarith
  have hG00 : 0 ≤ G0 := Nat.cast_nonneg _
  set f : ℝ → ℂ := (minorArcs X P).indicator (Fk k X) with hf
  -- Bessel
  have hbes0 := bessel_interval a (memLp_indicator_Fk k X P a)
    ((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)))
  have hbes : ∑ N ∈ (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)), ‖Rmpp k X P N‖ ^ 2
      ≤ ∫ x in a..a + 1, ‖f x‖ ^ 2 :=
    le_trans (le_of_eq (Finset.sum_congr rfl fun N _ => by rw [Rmpp_eq])) hbes0
  -- pointwise bound
  have hpt : ∀ x, ‖f x‖ ^ 2 ≤ (M ^ 2 * G0 ^ (2 * k)) * ‖Sx X x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ minorArcs X P
    · rw [hf, Set.indicator_of_mem hx]
      have hS := hB X (le_trans (le_max_left _ _) hX) P hP x hx
      have hS0 : 0 ≤ ‖Sx X x‖ := norm_nonneg _
      have hSM : ‖Sx X x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hS0 hS 2
      have hG : ‖Gx X x‖ ^ (2 * k) ≤ G0 ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg _) (norm_Gx_le X x) _
      unfold Fk
      rw [norm_mul, norm_pow, norm_pow]
      calc (‖Sx X x‖ ^ 2 * ‖Gx X x‖ ^ k) ^ 2 = ‖Sx X x‖ ^ 2 * ‖Gx X x‖ ^ (2 * k) * ‖Sx X x‖ ^ 2 := by ring
        _ ≤ M ^ 2 * G0 ^ (2 * k) * ‖Sx X x‖ ^ 2 := by gcongr
    · rw [hf, Set.indicator_of_notMem hx, norm_zero, zero_pow two_ne_zero]
      positivity
  have hint : ∫ x in a..a + 1, ‖f x‖ ^ 2 ≤ ∫ x in a..a + 1, (M ^ 2 * G0 ^ (2 * k)) * ‖Sx X x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) ?_ (ae_of_all _ hpt)
    exact (Continuous.integrableOn_Ioc (by
      exact continuous_const.mul ((continuous_Sx X).norm.pow 2)))
  rw [intervalIntegral.integral_const_mul, integral_norm_sq_Sx] at hint
  have hsq := sum_vonMangoldt_sq_le (X := X) (by linarith)
  have hC : 0 ≤ M ^ 2 * G0 ^ (2 * k) := by positivity
  have hfin : M ^ 2 * G0 ^ (2 * k) * ((Real.log 4 + 4) * X * Real.log X) ≤
      B ^ 2 * ((Real.log 4 + 4) * Real.log 2) * X ^ (2 * σ + 1) * L ^ (2 * k + 9) := by
    have hG : G0 ^ (2 * k) ≤ L ^ (2 * k) := pow_le_pow_left₀ hG00 hG0L _
    have hX : X ^ (2 * σ + 1) = (X ^ σ) ^ 2 * X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add_one hX0.ne']
      congr 1; push_cast; ring
    have hlog4 : 0 ≤ Real.log 4 + 4 := by positivity
    rw [log_eq_Lg (X := X), ← hLdef, hX, hM]
    calc (B * X ^ σ * L ^ 4) ^ 2 * G0 ^ (2 * k) * ((Real.log 4 + 4) * X * (Real.log 2 * L))
        ≤ (B * X ^ σ * L ^ 4) ^ 2 * L ^ (2 * k) * ((Real.log 4 + 4) * X * (Real.log 2 * L)) := by
          gcongr
      _ = B ^ 2 * ((Real.log 4 + 4) * Real.log 2) * ((X ^ σ) ^ 2 * X) * L ^ (2 * k + 9) := by ring
  calc _ ≤ _ := hbes
    _ ≤ _ := hint
    _ ≤ M ^ 2 * G0 ^ (2 * k) * ((Real.log 4 + 4) * X * Real.log X) := mul_le_mul_of_nonneg_left hsq hC
    _ ≤ _ := hfin

/-- **The paper's Section 3 L² bound from its sup bound**: `MinorBound → MinorL2`. -/
theorem minorL2_of_minorBound (h : MinorBound) : MinorL2 :=
  minorL2_iff.mpr (minorL2σ_of_bound (minorBound_iff.mp h))

/-- **`exceptional_of_sup`**: a minor arc sup `≪ X^σ L⁴` gives at most `≪ X^{2σ−1} L^{10}` even
`N ∈ J(X)` with `|R''_𝔪(N)| ≥ N L^{k−1/2}`. PROVED unconditional as an implication. -/
theorem exceptional_of_sup {σ : ℝ} (h : MinorBoundσ σ) : Eq7σ σ :=
  eq7σ_of_minorL2σ (minorL2σ_of_bound h)

/-- **The paper's (7) from its sup bound alone**: `MinorBound → Eq7`. -/
theorem eq7_of_minorBound (h : MinorBound) : Eq7 :=
  eq7_iff.mpr (exceptional_of_sup (minorBound_iff.mp h))

/-- (7) and the L² bound CONDITIONAL ON the cited `minorBound` only. -/
theorem eq7_from_cited : Eq7 := eq7_of_minorBound minorBound
theorem minorL2_from_cited : MinorL2 := minorL2_of_minorBound minorBound

/-- I-0091 at `σ = 19/24`: exceptions `≪ X^{7/12} L^{10}`, CONDITIONAL ON `MinorBoundσ (19/24)`. -/
theorem exceptional_19_24 (h : MinorBoundσ (19 / 24)) :
    ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
      ((Exc7 k X P).card : ℝ) ≤ B * X ^ (7 / 12 : ℝ) * Lg X ^ 10 :=
  eq7_19_24 (minorL2σ_of_bound h)


/-- **Vacuity test**: `MinorBoundσ 1` holds outright, by `|S| ≤ ψ(X) ≤ (log 4 + 4) X`, so the
hypothesis of `exceptional_of_sup` can hold; it then gives the trivial `X^1 L^{10}`. -/
theorem minorBoundσ_one : MinorBoundσ 1 := by
  refine ⟨Real.log 4 + 4, 2, fun X hX P _ α _ => ?_⟩
  have hL1 : 1 ≤ Lg X := one_le_Lg hX
  have hS : ‖Sx X α‖ ≤ Chebyshev.psi X := by
    refine (norm_Sx_le X α).trans (le_of_eq ?_)
    rw [← sum_vonMangoldt_eq_psi, sum_range_succ_eq_Icc _ (by simp)]
  have hpsi := Chebyshev.psi_le_const_mul_self (x := X) (by linarith)
  have hL4 : 1 ≤ Lg X ^ 4 := one_le_pow₀ hL1
  rw [Real.rpow_one]
  have h0 : 0 ≤ (Real.log 4 + 4) * X := by positivity
  calc ‖Sx X α‖ ≤ (Real.log 4 + 4) * X := hS.trans hpsi
    _ ≤ (Real.log 4 + 4) * X * Lg X ^ 4 := le_mul_of_one_le_right h0 hL4

theorem exceptional_one : Eq7σ 1 := exceptional_of_sup minorBoundσ_one

end

end LeanLab.LPZ2007.MinorBessel

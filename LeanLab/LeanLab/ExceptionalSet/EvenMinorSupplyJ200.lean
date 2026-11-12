import Mathlib
import LeanLab.ExceptionalSet.OddSupplyJ200
import LeanLab.ExceptionalSet.OddKernel467
import LeanLab.ExceptionalSet.MajorSupplyJ200
import LeanLab.ExceptionalSet.BrudernPerelliExplicit
import LeanLab.ExceptionalSet.State1539Data264

/-!
Upstream supply of displays (32) and (33) of P0082 for
`OddMinorMoments.leaf_even_minor_moment`, display (29).
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621, pages 367 and 368.

Page 367: with `w_e(α) = w(2α + 1)`, display (31), and its inverse transform `K_e`, Lemma 1
with `h = S² 1_𝔫` gives `∫_𝔫 S² K_e e(-αF(n)) dα = w_e({F(n)} - 1) R₂(ν_n + 1)`.
Page 368: `w_e({F(n)} - 1) = 1` unless `{F(n)} < Δ/2` or `{F(n)} > 1 - Δ/2`; the trivial bound
`|R₂(m)| ≤ ∫_0^1 |S|² ≪ X log X` and Lemma 4 for the boundary count give display (33).

The kernel `K_e` is `OddKernel467.evenKernel`, whose transform is proved there to be `w_e`.
The Parseval bound, the coefficient identity and the window inclusion are copies of the proved
`PrimeEnergy385.prime_energy`, `OddCoefficient467.weighted_minor_identity`,
`Decomp483a.minorCoefficient_norm_le`, `Decomp483a.odd_upper_moment_transfer`, the window
lemmas of `Decomp371a` and `Decomp404e.log_F_sq_le_calE_quarter`, restated for `R2` of
`OddSupplyJ200`. Those files import `DecompJ200`, which imports the leaf file this supplies,
so they cannot be imported here. The proofs are unchanged up to names.

Only `boundary_count_of_lemma4` and `boundary_moment_of_lemma4` take an input: Lemma 4 of
the paper, as an explicit hypothesis. They are CONDITIONAL ON Lemma 4.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.EvenMinorSupplyJ200

open Real Finset MeasureTheory Filter Topology ComplexConjugate
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp eC majorArcs hcheck ftR nu calE Lemma4)
open LeanLab.ExceptionalSet.OddSupplyJ200 (R2)

/-- Parseval for the finite prime sum of P0082 page 357. Copy of
`PrimeEnergy385.prime_energy`. -/
theorem prime_energy (P X : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) =
      ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (α : ℝ) : Sp P X α = ∑ n ∈ s, (Real.log n : ℂ) * BG2026.eC (n * α) := by
    unfold Sp
    apply sum_congr rfl
    intro n hn
    unfold U1539.eC BG2026.eC
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he2 (α : ℝ) : ((‖Sp P X α‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, ((Real.log n : ℂ) * Real.log m) *
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', he, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [map_mul, Complex.conj_ofReal, BG2026.conj_eC]
    have hx : BG2026.eC (n * α) * BG2026.eC (-(m * α)) =
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
      unfold BG2026.eC
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hx]
    ring
  simp_rw [he2]
  rw [BG2026.integral_double_sum]
  push_cast
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp
    ring
  · intro m hm hmn
    rw [ite_eq_right (by omega)]
    simp
  · intro h
    exact absurd hn h

/-- The trivial mass bound `∫_0^1 |S|² ≤ log 4 · X log X` of P0082 page 368 before (33),
from Mathlib's Chebyshev bound. Copy of `PrimeEnergy385.prime_energy_le` at `a = 0`. -/
theorem prime_energy_le (P X : ℝ) (hX : 2 ≤ X) :
    (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) ≤ Real.log 4 * X * Real.log X := by
  classical
  rw [prime_energy]
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have hX0 : 0 ≤ X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsum : (∑ p ∈ s, Real.log p) ≤ Chebyshev.theta X := by
    unfold Chebyshev.theta
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases mem_filter.mp hp with ⟨hI, hprime⟩
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hI).1,
        (mem_Ioc.mp hI).2⟩, hprime⟩
    · intro p hp _
      have hp1 := (mem_filter.mp hp).2.one_lt.le
      exact Real.log_nonneg (by exact_mod_cast hp1)
  have hterm (p : ℕ) (hp : p ∈ s) : Real.log p ^ 2 ≤ Real.log X * Real.log p := by
    have hprime := (mem_filter.mp hp).2
    have hLp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hpfloor : (p : ℝ) ≤ ⌊X⌋₊ := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hpX : (p : ℝ) ≤ X := hpfloor.trans (Nat.floor_le hX0)
    have hL := Real.log_le_log (by exact_mod_cast hprime.pos) hpX
    nlinarith [mul_nonneg hLp (sub_nonneg.mpr hL)]
  calc ∑ p ∈ s, Real.log p ^ 2 ≤ ∑ p ∈ s, Real.log X * Real.log p := sum_le_sum hterm
    _ = Real.log X * ∑ p ∈ s, Real.log p := (mul_sum _ _ _).symm
    _ ≤ Real.log X * Chebyshev.theta X := mul_le_mul_of_nonneg_left hsum hLX
    _ ≤ Real.log X * (Real.log 4 * X) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hX0) hLX
    _ = _ := by ring

/-- `h(α) = S(α)²` on the minor arcs `𝔫` and `0` on the major arcs, the function `h` of
Lemma 1 on P0082 page 367 below (31). -/
noncomputable def minorSq (P X : ℝ) : ℝ → ℂ :=
  (majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2)

/-- `h = S² 1_𝔫` is integrable on one period. Copy of
`OddCoefficient467.minor_intervalIntegrable`. -/
theorem minorSq_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable (minorSq P X) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by unfold Sp eC; fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (PrimeKernel264.measurableSet_majorArcs P X).compl, by simp⟩

/-- `h = S² 1_𝔫` has period one, since `S` and the major arcs do. -/
theorem minorSq_periodic (P X : ℝ) : Function.Periodic (minorSq P X) 1 := by
  intro α
  have hm : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X :=
    Iff.of_eq (MajorSupplyJ200.majorArcs_periodic P X α)
  classical
  show minorSq P X (α + 1) = minorSq P X α
  unfold minorSq
  rw [Set.indicator_apply, Set.indicator_apply, MajorSupplyJ200.Sp_periodic P X α]
  simp only [Set.mem_compl_iff, hm]

/-- `R₂(m)` is the Fourier coefficient `ȟ(m)` of `h = S² 1_𝔫`, P0082 page 366 display (28)
and page 367 below (31). The closed and half open unit intervals differ by a null set. -/
theorem R2_eq_hcheck (P X : ℝ) (m : ℤ) : R2 P X m = hcheck (minorSq P X) m := by
  classical
  have hmeas := (PrimeKernel264.measurableSet_majorArcs P X).compl
  unfold R2 hcheck
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hf : (fun α => minorSq P X α * eC (-(α * m))) =
      (majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2 * eC (-(α * m))) := by
    funext α
    by_cases ha : α ∈ majorArcs P X <;> simp [minorSq, ha]
  rw [hf, integral_indicator hmeas, Measure.restrict_restrict hmeas]
  apply setIntegral_congr_set
  exact ae_eq_set_inter (ae_eq_refl _) Ioc_ae_eq_Icc.symm

/-- The trivial bound `|R₂(m)| ≤ ∫_0^1 |S(α)|² dα ≪ X log X`, P0082 page 368 before (33).
Copy of `Decomp483a.minorCoefficient_norm_le`. -/
theorem R2_norm_le (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖R2 P X m‖ ≤ Real.log 4 * X * Real.log X := by
  classical
  rw [R2_eq_hcheck]
  unfold hcheck
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun α _ => ?_))
    (show IntervalIntegrable (fun α => ‖Sp P X α‖ ^ 2) volume 0 1 from
      (by unfold Sp eC; fun_prop : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2)).intervalIntegrable _ _)).trans ?_
  · by_cases ha : α ∈ majorArcs P X
    · simp [minorSq, ha]
    · simp [minorSq, ha, norm_pow, U1539.norm_eC]
  · exact prime_energy_le P X hX

/-- P0082 page 367, the display after (31), from Lemma 1 with `h = S² 1_𝔫` and kernel `K_e`:
`∫_𝔫 S² K_e e(-αv) dα = w_e({v} - 1) R₂([v] + 1)`, where `w_e({v} - 1) = w(2{v} - 1)`.
Copy of `OddCoefficient467.weighted_minor_identity` for `R2`. -/
theorem minor_weighted_identity (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
        (KernelTransform264.weight Δ (2 * Int.fract v - 1) : ℂ) * R2 P X (⌊v⌋ + 1) := by
  classical
  have hh := OddKernel467.weighted_adjacent_identity (minorSq P X) (minorSq_periodic P X)
    (minorSq_intervalIntegrable P X) Δ v hΔ hΔ1
  have he : (fun α : ℝ => minorSq P X α * OddKernel467.evenKernel Δ α * eC (-(α * v))) =
      (majorArcs P X)ᶜ.indicator (fun α =>
        Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) := by
    ext α
    by_cases ha : α ∈ majorArcs P X <;> simp [minorSq, ha]
  rw [he, integral_indicator (PrimeKernel264.measurableSet_majorArcs P X).compl] at hh
  rw [hh, R2_eq_hcheck]

/-- P0082 page 368 before (32): when `Δ/2 ≤ {v} ≤ 1 - Δ/2` the weight is one and the kernel
integral is `R₂([v] + 1)` itself. -/
theorem minor_plateau_identity (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hleft : Δ / 2 ≤ Int.fract v) (hright : Int.fract v ≤ 1 - Δ / 2) :
    (∫ α in (majorArcs P X)ᶜ,
      Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v))) = R2 P X (⌊v⌋ + 1) := by
  rw [minor_weighted_identity P X Δ v hΔ hΔ1]
  have hp : |2 * Int.fract v - 1| ≤ 1 - Δ := by rw [abs_le]; constructor <;> linarith
  rw [KernelTransform264.weight_one hΔ hΔ1 hp]
  simp

/-- P0082 page 368 display (32) with the remainder `R` of (33) made explicit: for any finite
index set, the second moment of `R₂([v_n] + 1)` is at most the second moment of the kernel
integrals plus the number of boundary indices times `(X log X)²`, up to `log 4`.
Copy of `Decomp483a.odd_upper_moment_transfer` for `R2`. -/
theorem moment_transfer (P X Δ : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖R2 P X (⌊v n⌋ + 1)‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v n))‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  classical
  let bad := fun n => Int.fract (v n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (v n)
  let f := fun n => ‖R2 P X (⌊v n⌋ + 1)‖ ^ 2
  let g := fun n => ‖∫ α in (majorArcs P X)ᶜ,
    Sp P X α ^ 2 * OddKernel467.evenKernel Δ α * eC (-(α * v n))‖ ^ 2
  have hsplit := (Finset.sum_filter_add_sum_filter_not s bad f).symm
  have hgood : (∑ n ∈ s.filter (fun n => ¬ bad n), f n) ≤ ∑ n ∈ s, g n := by
    calc _ = ∑ n ∈ s.filter (fun n => ¬ bad n), g n := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnb := (Finset.mem_filter.mp hn).2
          simp only [bad, not_or, not_lt] at hnb
          simp only [f, g, minor_plateau_identity P X Δ (v n) hΔ hΔ1 hnb.1 hnb.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  have hbad : (∑ n ∈ s.filter bad, f n) ≤
      ((s.filter bad).card : ℝ) * (Real.log 4 * X * Real.log X) ^ 2 := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro n _
    exact pow_le_pow_left₀ (norm_nonneg _) (R2_norm_le P X hX _) 2
  change (∑ n ∈ s, f n) ≤ (∑ n ∈ s, g n) + ((s.filter bad).card : ℝ) * _
  linarith

/-! ### The cognate (30): the kernel `K_o(α) = K_e(-α)` with transform `w_e(-α)` -/

/-- P0082 page 369 after (39): for (30) replace `w_e(α)` by `w_o(α) = w_e(-α)`. Its inverse
transform is `K_o(α) = K_e(-α)`. -/
noncomputable def oddKernel (Δ α : ℝ) : ℂ := OddKernel467.evenKernel Δ (-α)

/-- `K_o` is integrable, as `K_e` is. -/
theorem oddKernel_integrable (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (oddKernel Δ) :=
  (OddKernel467.evenKernel_integrable Δ hΔ hΔ1).comp_neg

/-- `K_o` is continuous, as `K_e` is. -/
theorem oddKernel_continuous (Δ : ℝ) : Continuous (oddKernel Δ) :=
  (OddKernel467.evenKernel_continuous Δ).comp continuous_neg

/-- `K̂_o(y) = w_e(-y) = w(1 - 2y)`, P0082 page 369 after (39). -/
theorem ftR_oddKernel (Δ y : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ftR (oddKernel Δ) y = (KernelTransform264.weight Δ (1 - 2 * y) : ℂ) := by
  have h := integral_neg_eq_self
    (fun β => OddKernel467.evenKernel Δ β * eC (-((-y) * β))) volume
  have he : (fun β : ℝ => oddKernel Δ β * eC (-(y * β))) =
      fun β => OddKernel467.evenKernel Δ (-β) * eC (-((-y) * (-β))) := by
    funext β
    rw [show -((-y) * (-β)) = -(y * β) by ring]
    rfl
  have h2 := OddKernel467.ftR_evenKernel Δ (-y) hΔ hΔ1
  unfold ftR at h2 ⊢
  rw [he, h, h2]
  congr 2
  ring

/-- The transform of `K_o` vanishes outside `[-1, 1]`, as Lemma 1 needs. -/
theorem oddKernel_transform_support (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ y : ℝ, 1 < |y| → ftR (oddKernel Δ) y = 0 := by
  intro y hy
  rw [ftR_oddKernel Δ y hΔ hΔ1]
  have hh : 1 ≤ |1 - 2 * y| := by
    rw [le_abs]
    rcases lt_abs.mp hy with hy | hy
    · right; linarith
    · left; linarith
  rw [KernelTransform264.weight_zero hΔ hΔ1 hh]
  simp

/-- Lemma 1 with kernel `K_o` selects the lower coefficient:
`∫ h K_o e(-αv) = w(1 - 2{v}) ȟ([v])`, the cognate of the display after (31). -/
theorem odd_adjacent_identity (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α : ℝ, h α * oddKernel Δ α * eC (-(α * v))) =
      (KernelTransform264.weight Δ (1 - 2 * Int.fract v) : ℂ) * hcheck h ⌊v⌋ := by
  have hmain := Decomp464j.lemma1_supplied h (oddKernel Δ) hper hh
    (oddKernel_integrable Δ hΔ hΔ1) (oddKernel_continuous Δ)
    (oddKernel_transform_support Δ hΔ hΔ1) v
  rw [ftR_oddKernel Δ (Int.fract v) hΔ hΔ1,
    ftR_oddKernel Δ (Int.fract v - 1) hΔ hΔ1] at hmain
  have hz : KernelTransform264.weight Δ (1 - 2 * (Int.fract v - 1)) = 0 := by
    apply KernelTransform264.weight_zero hΔ hΔ1
    have := Int.fract_lt_one v
    rw [abs_of_nonneg (by linarith)]
    linarith
  simpa only [hz, Complex.ofReal_zero, zero_mul, add_zero] using hmain

/-- The cognate of `minor_weighted_identity`:
`∫_𝔫 S² K_o e(-αv) dα = w(1 - 2{v}) R₂([v])`. -/
theorem minor_weighted_identity_odd (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in (majorArcs P X)ᶜ, Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v))) =
        (KernelTransform264.weight Δ (1 - 2 * Int.fract v) : ℂ) * R2 P X ⌊v⌋ := by
  classical
  have hh := odd_adjacent_identity (minorSq P X) (minorSq_periodic P X)
    (minorSq_intervalIntegrable P X) Δ v hΔ hΔ1
  have he : (fun α : ℝ => minorSq P X α * oddKernel Δ α * eC (-(α * v))) =
      (majorArcs P X)ᶜ.indicator (fun α => Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v))) := by
    ext α
    by_cases ha : α ∈ majorArcs P X <;> simp [minorSq, ha]
  rw [he, integral_indicator (PrimeKernel264.measurableSet_majorArcs P X).compl] at hh
  rw [hh, R2_eq_hcheck]

/-- The cognate plateau: when `Δ/2 ≤ {v} ≤ 1 - Δ/2`, `∫_𝔫 S² K_o e(-αv) dα = R₂([v])`. -/
theorem minor_plateau_identity_odd (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hleft : Δ / 2 ≤ Int.fract v) (hright : Int.fract v ≤ 1 - Δ / 2) :
    (∫ α in (majorArcs P X)ᶜ, Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v))) =
      R2 P X ⌊v⌋ := by
  rw [minor_weighted_identity_odd P X Δ v hΔ hΔ1]
  have hp : |1 - 2 * Int.fract v| ≤ 1 - Δ := by rw [abs_le]; constructor <;> linarith
  rw [KernelTransform264.weight_one hΔ hΔ1 hp]
  simp

/-- The cognate of `moment_transfer` for (30), with the same boundary set. -/
theorem moment_transfer_odd (P X Δ : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖R2 P X ⌊v n⌋‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v n))‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  classical
  let bad := fun n => Int.fract (v n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (v n)
  let f := fun n => ‖R2 P X ⌊v n⌋‖ ^ 2
  let g := fun n => ‖∫ α in (majorArcs P X)ᶜ,
    Sp P X α ^ 2 * oddKernel Δ α * eC (-(α * v n))‖ ^ 2
  have hsplit := (Finset.sum_filter_add_sum_filter_not s bad f).symm
  have hgood : (∑ n ∈ s.filter (fun n => ¬ bad n), f n) ≤ ∑ n ∈ s, g n := by
    calc _ = ∑ n ∈ s.filter (fun n => ¬ bad n), g n := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnb := (Finset.mem_filter.mp hn).2
          simp only [bad, not_or, not_lt] at hnb
          simp only [f, g, minor_plateau_identity_odd P X Δ (v n) hΔ hΔ1 hnb.1 hnb.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  have hbad : (∑ n ∈ s.filter bad, f n) ≤
      ((s.filter bad).card : ℝ) * (Real.log 4 * X * Real.log X) ^ 2 := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro n _
    exact pow_le_pow_left₀ (norm_nonneg _) (R2_norm_le P X hX _) 2
  change (∑ n ∈ s, f n) ≤ (∑ n ∈ s, g n) + ((s.filter bad).card : ℝ) * _
  linarith

/-! ### The summation window, copies of the window lemmas of `Decomp371a` -/

/-- The lab window `n ≤ 2N`, `X/2 < ν_n ≤ X`, `X = F(N)`, written as in the leaf
`OddMinorMoments.leaf_even_minor_moment`; definitionally `DecompJ200.window`. -/
noncomputable def win (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

/-- P0082 page 372 display 47: `F' ≥ γ` on `x ≥ 8`, as growth. Copy of `Decomp371a.F_growth`. -/
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

/-- The window lies below `N`. Copy of `Decomp371a.window_upper`. -/
theorem win_upper (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 8 ≤ N)
    (n : ℕ) (hn : n ∈ win γ N) : n ≤ N := by
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

/-- `F(x)/x` is nondecreasing on `x ≥ 8`. Copy of `Decomp371a.F_ratio_mono`. -/
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

/-- The window lies above `N/2` for `N ≥ 16`. Copy of `Decomp371a.window_lower`. -/
theorem win_lower (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N)
    (n : ℕ) (hn : n ∈ win γ N) : N / 2 < n := by
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

/-- The lab window lies in the paper's range `N/2 < n ≤ N` for `N ≥ 16`.
Copy of `Decomp371a.window_subset_Ioc`. -/
theorem win_subset_Ioc (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N) :
    win γ N ⊆ Finset.Ioc (N / 2) N := fun n hn =>
  Finset.mem_Ioc.mpr ⟨win_lower γ hγ N hN n hn, win_upper γ hγ N (by omega) n hn⟩

/-! ### Display (33): the boundary count by Lemma 4 -/

/-- P0082 page 368 before (33): the `n` with `0 < w_e({F(n)} - 1) < 1` have
`{F(n)} < Δ/2` or `{F(n)} > 1 - Δ/2`, and by Lemma 4 with `α = 1` their number is
`≤ ΔN/2 + 2BN exp(-κ (log N)^{3-2γ})`, which is `O(NΔ + Nℰ^{-1})`.
CONDITIONAL ON Lemma 4. -/
theorem boundary_count_of_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₄ B : ℝ, 0 < κ₄ ∧ ∀ N : ℕ, 16 ≤ N → ∀ (s : Finset ℕ), s ⊆ win γ N →
      ∀ Δ : ℝ, 0 < Δ → Δ < 1 →
        ((s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
          1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
            Δ * N / 2 + 2 * (B * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ))) := by
  classical
  obtain ⟨κ, B, hκ, hB⟩ := h4 γ h1 h2
  refine ⟨κ, B, hκ, fun N hN s hs Δ hΔ hΔ1 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hF1 : 1 < F γ N := by
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    rw [abs_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num)
  let I := Finset.Ioc (N / 2) N
  let A := I.filter (fun n : ℕ =>
    (0 : ℝ) ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < Δ / 2)
  let C := I.filter (fun n : ℕ =>
    1 - Δ / 2 ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < 1)
  have hA := hB N hN1 1 hα (by simp) (Δ / 2) 0 (le_refl _) (by linarith) (by linarith)
  have hC := hB N hN1 1 hα (by simp) 1 (1 - Δ / 2) (by linarith) (by linarith) (le_refl _)
  have hsub : s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n)) ⊆ A ∪ C := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hb⟩
    have hnI : n ∈ I := win_subset_Ioc γ h1 N hN (hs hns)
    rcases hb with hb | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hnI, by simp only [one_mul]; exact ⟨Int.fract_nonneg _, hb⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hnI, by simp only [one_mul]; exact ⟨hb.le, Int.fract_lt_one _⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le A C)
  have hcardR : ((s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤ (A.card : ℝ) + C.card := by
    exact_mod_cast hcard
  have hA' := (abs_le.mp hA).2
  have hC' := (abs_le.mp hC).2
  change (A.card : ℝ) - (Δ / 2 - 0) * N / 2 ≤ _ at hA'
  change (C.card : ℝ) - (1 - (1 - Δ / 2)) * N / 2 ≤ _ at hC'
  nlinarith

/-! ### Absorption of the logarithms, display (34) at `ℰ' = ℰ²` -/

/-- A quarter power of `ℰ` absorbs `(log X)²`. Copy of `Decomp404e.log_F_sq_le_calE_quarter`. -/
theorem log_F_sq_le_calE_quarter (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 2 ≤ calE γ κ N ^ (1 / 4 : ℝ) := by
  let a := 3 - 2 * γ
  have ha : 0 < a := by dsimp [a]; linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop ha).comp hlog
  have hs := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * γ / a) (κ / 4) (by positivity)).comp ht
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN hsN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpow : (Real.log N ^ a) ^ (2 * γ / a) = (Real.log N ^ γ) ^ 2 := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul_natCast hL.le]
    congr 1
    field_simp
    norm_num
  change (Real.log N ^ a) ^ (2 * γ / a) * Real.exp (-(κ / 4) * Real.log N ^ a) < 1 at hsN
  rw [hpow, show -(κ / 4) * Real.log N ^ a = -(κ * Real.log N ^ a * (1 / 4)) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)] at hsN
  simpa only [F, Real.log_exp, calE, ← Real.exp_mul, one_mul] using hsN.le

/-- `ℰ(2κ)^{-1/3} = ℰ(κ)^{-2/3}`: display (34) at the inner scale `ℰ' = ℰ(2κ) = ℰ²`. -/
theorem calE_two_mul (γ κ : ℝ) (N : ℕ) :
    calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  simp only [calE, ← Real.exp_mul]
  congr 1
  ring

/-- P0082 page 368 displays (33) and (34), with `Δ = ℰ'^{-1/3}` at `ℰ' = ℰ(2κ)`: for `κ` at
most the Lemma 4 constant the remainder `R` of (32) is `≪ N X² ℰ^{-1/3}`.
This is where the `(log X)²` of (33), which the printed `Δ = ℰ^{-1/3}` does not absorb, is
paid for by the doubled `κ`. CONDITIONAL ON Lemma 4. -/
theorem boundary_moment_of_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₄ : ℝ, 0 < κ₄ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₄ →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (s : Finset ℕ), s ⊆ win γ N →
        ((s.filter (fun n : ℕ => Int.fract (F γ n) < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) / 2 ∨
          1 - calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) *
            (Real.log 4 * F γ N * Real.log (F γ N)) ^ 2 ≤
          C * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨κ₄, B, hκ₄, hB⟩ := boundary_count_of_lemma4 h4 γ h1 h2
  refine ⟨κ₄, hκ₄, fun κ hκ hκ₄le => ?_⟩
  obtain ⟨Nl, hl⟩ := log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨Real.log 4 ^ 2 * (1 / 2 + 2 * |B|) + 1, by positivity, max (max Nl 16) 2,
    fun N hN s hs => ?_⟩
  have hNl : Nl ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  set E := calE γ κ N with hEdef
  set X := F γ N with hXdef
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hκ.le
    (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _))
  have hE0 : 0 < E := by linarith
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = E ^ (-(2 / 3 : ℝ)) := calE_two_mul γ κ N
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) with hΔdef
  have hΔ0 : 0 < Δ := by rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hEgt : 1 < calE γ (2 * κ) N := by
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hEgt (by norm_num)
  have hcount := hB N hN16 s hs Δ hΔ0 hΔ1
  have hexp : Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) ≤ E ^ (-1 : ℝ) := by
    rw [hEdef, calE, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log N ^ (3 - 2 * γ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _
    nlinarith
  have hlog := hl N hNl
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- `(log X)² Δ ≤ ℰ^{1/4 - 2/3} ≤ ℰ^{-1/3}` and `(log X)² ℰ^{-1} ≤ ℰ^{-1/3}`.
  have hq1 : Real.log X ^ 2 * Δ ≤ E ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]
    calc _ ≤ E ^ (1 / 4 : ℝ) * E ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_pos_of_pos hE0 _).le
      _ = E ^ ((1 / 4 : ℝ) + -(2 / 3)) := (Real.rpow_add hE0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hq2 : Real.log X ^ 2 * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) ≤
      E ^ (-(1 / 3 : ℝ)) := by
    calc _ ≤ E ^ (1 / 4 : ℝ) * E ^ (-1 : ℝ) :=
          mul_le_mul hlog hexp (Real.exp_pos _).le (Real.rpow_pos_of_pos hE0 _).le
      _ = E ^ ((1 / 4 : ℝ) + -1) := (Real.rpow_add hE0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hE3 : 0 ≤ E ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hE0 _).le
  have hLsq : 0 ≤ Real.log X ^ 2 := sq_nonneg _
  have hcnt0 : (0 : ℝ) ≤ ((s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) := Nat.cast_nonneg _
  have hcount' : ((s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
      Δ * N / 2 + 2 * (|B| * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ))) := by
    refine hcount.trans ?_
    have := le_abs_self B
    have he0 := (Real.exp_pos (-κ₄ * Real.log N ^ (3 - 2 * γ))).le
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hN0 he0)]
  set c := ((s.filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) with hc
  set ex := Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) with hex
  have hkey : c * Real.log X ^ 2 ≤ (1 / 2 + 2 * |B|) * N * E ^ (-(1 / 3 : ℝ)) := by
    calc c * Real.log X ^ 2 ≤ (Δ * N / 2 + 2 * (|B| * N * ex)) * Real.log X ^ 2 :=
          mul_le_mul_of_nonneg_right hcount' hLsq
      _ = N / 2 * (Real.log X ^ 2 * Δ) + 2 * |B| * N * (Real.log X ^ 2 * ex) := by ring
      _ ≤ N / 2 * E ^ (-(1 / 3 : ℝ)) + 2 * |B| * N * E ^ (-(1 / 3 : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc c * (Real.log 4 * X * Real.log X) ^ 2
        = Real.log 4 ^ 2 * X ^ 2 * (c * Real.log X ^ 2) := by ring
    _ ≤ Real.log 4 ^ 2 * X ^ 2 * ((1 / 2 + 2 * |B|) * N * E ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ (Real.log 4 ^ 2 * (1 / 2 + 2 * |B|) + 1) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
        have : 0 ≤ N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by positivity
        nlinarith

end LeanLab.ExceptionalSet.EvenMinorSupplyJ200

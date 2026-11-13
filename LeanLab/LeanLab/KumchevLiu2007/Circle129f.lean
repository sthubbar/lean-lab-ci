/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 8, p3, 2026-11-12.
Page 7 display 29 and page 4 display 17: the reduction of the minor arc mean square
display 32 to a single minor arc integral of S2 against the kernel of the sum over
X less than n at most X plus H of e of gamma n, together with the Parseval identity
display 17 for S1. Builds on `Circle129d` and `Circle129e`; the minor arc leaves
statements of display 32 on the two ranges are proved here from the narrower kernel
leaves below. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Circle129e

namespace LeanLab.KumchevLiu2007.Task129f

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task129d
open scoped BigOperators ComplexConjugate

/-- The kernel of page 7 display 29: the sum over n in N of e of gamma n. -/
noncomputable def kern (N : Finset ℕ) (γ : ℝ) : ℂ := ∑ n ∈ N, U1534.ee (γ * n)

theorem ee_conj (x : ℝ) : conj (U1534.ee x) = U1534.ee (-x) := by
  unfold U1534.ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

theorem ee_add (x y : ℝ) : U1534.ee (x + y) = U1534.ee x * U1534.ee y := by
  unfold U1534.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

theorem kern_neg (N : Finset ℕ) (γ : ℝ) : kern N (-γ) = conj (kern N γ) := by
  unfold kern
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [ee_conj, neg_mul]

theorem norm_kern_neg (N : Finset ℕ) (γ : ℝ) : ‖kern N (-γ)‖ = ‖kern N γ‖ := by
  rw [kern_neg, Complex.norm_conj]

theorem kern_continuous (N : Finset ℕ) : Continuous (kern N) := by
  unfold kern U1534.ee; fun_prop

theorem expSum1_continuous (lam : ℕ → ℝ) (X Y : ℝ) : Continuous (expSum1 lam X Y) := by
  unfold expSum1 U1534.ee; fun_prop

theorem expSum2_continuous (lam : ℕ → ℝ) (Y : ℝ) : Continuous (expSum2 lam Y) := by
  unfold expSum2 U1534.ee; fun_prop

/-- Integrability of continuous functions on the square of a bounded measurable set. -/
theorem integrable_prod_of_continuous {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} {a b : ℝ}
    (hs : s ⊆ Set.Icc a b) {f : ℝ × ℝ → E} (hf : Continuous f) :
    Integrable f ((volume.restrict s).prod (volume.restrict s)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono hs hs)

/-- Integrability of continuous functions on a bounded measurable set. -/
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} {a b : ℝ}
    (hs : s ⊆ Set.Icc a b) {f : ℝ → E} (hf : Continuous f) :
    Integrable f (volume.restrict s) :=
  (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hs

/-- Page 4 display 17, PROVED: the integral of the square of S1 over an interval of
length 1 is the sum of the squared weights. -/
theorem parseval1 (lam : ℕ → ℝ) (X Y a : ℝ) :
    ∫ α in a..a + 1, ‖expSum1 lam X Y α‖ ^ 2 = ∑ m ∈ win1 X Y, lam m ^ 2 := by
  have hC : ∀ α : ℝ, ((‖expSum1 lam X Y α‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ win1 X Y, ∑ m' ∈ win1 X Y, ((lam m * lam m' : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - (m' : ℤ) : ℤ) : ℂ) * (α : ℂ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold expSum1
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [map_mul, Complex.conj_ofReal, ee_conj]
    unfold U1534.ee
    have : Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - (m' : ℤ) : ℤ) : ℂ) * (α : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((α * m : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((-(α * m') : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  have hR : ((∫ α in a..a + 1, ‖expSum1 lam X Y α‖ ^ 2 : ℝ) : ℂ) =
      ((∑ m ∈ win1 X Y, lam m ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hC]
    rw [intervalIntegral.integral_finsetSum (fun m _ => by
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ (fun m' _ => by fun_prop))]
    simp only [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [intervalIntegral.integral_finsetSum (fun m' _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp_rw [intervalIntegral.integral_const_mul, integral_ee_int]
    rw [Finset.sum_eq_single m]
    · simp [sq]
    · intro m' _ hne
      have : ((m : ℤ) - (m' : ℤ)) ≠ 0 := by intro h; apply hne; omega
      simp [this]
    · intro h; exact absurd ‹m ∈ win1 X Y› h
  exact_mod_cast hR

/-- Bookkeeping for display 17: the window I1 has at most Y plus 1 integers. -/
theorem card_win1_le (X Y : ℝ) (hY : 0 ≤ Y) : ((win1 X Y).card : ℝ) ≤ Y + 1 := by
  rcases le_or_gt X 0 with hX | hX
  · have : win1 X Y = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro m hm
      simp only [win1, Finset.mem_filter] at hm
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hm.2.2]
    rw [this]; simp; linarith
  have hsub : win1 X Y ⊆ Finset.Icc ⌈X - Y⌉₊ ⌊X⌋₊ := by
    intro m hm
    simp only [win1, Finset.mem_filter, Finset.mem_range] at hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hm.2.1, Nat.lt_succ_iff.mp hm.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : ((⌊X⌋₊ + 1 - ⌈X - Y⌉₊ : ℕ) : ℝ) ≤ Y + 1 := by
    rcases le_or_gt ⌈X - Y⌉₊ (⌊X⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      have := Nat.floor_le hX.le
      have := Nat.le_ceil (X - Y)
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
  calc ((win1 X Y).card : ℝ) ≤ ((⌊X⌋₊ + 1 - ⌈X - Y⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ Y + 1 := h2

/-- The minor arcs m of page 4 display 15 inside the unit interval. -/
def minorSet (P Q : ℝ) : Set ℝ := unitArc Q \ majorArcs P Q

theorem minorSet_subset (P Q : ℝ) : minorSet P Q ⊆ Set.Icc (1 / Q) (1 / Q + 1) :=
  fun _ hx => Set.Ioc_subset_Icc_self hx.1

theorem minorSet_meas (P Q : ℝ) : MeasurableSet (minorSet P Q) :=
  measurableSet_Ioc.diff (majorArcs_isOpen P Q).measurableSet

/-- Page 7 display 29, PROVED. For any finite set N of integers n, the sum over n
in N of the square of the minor arc integral of S1 S2 e of minus alpha n is at
most D times the sum of the squared weights of S1, which is I1 of display 17,
whenever for every beta on the minor arcs the integral over the minor arcs of
the square of S2 of alpha times the norm of the kernel at beta minus alpha is at
most D. The paper expands the square, bounds the product of S1 S2 at alpha and
at beta by the arithmetic geometric mean inequality, uses symmetry and then
display 17. -/
theorem display29 (X Y P Q D : ℝ) (N : Finset ℕ) (hD : 0 ≤ D)
    (h : ∀ β ∈ minorSet P Q, ∫ α in minorSet P Q,
      ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * ‖kern N (β - α)‖ ≤ D) :
    ∑ n ∈ N, ‖minorInt X Y P Q n‖ ^ 2 ≤ D * ∑ m ∈ win1 X Y, lam1 m ^ 2 := by
  have hsub := minorSet_subset P Q
  set μ : Measure ℝ := volume.restrict (minorSet P Q) with hμ
  set F : ℝ → ℂ := fun α => expSum1 lam1 X Y α * expSum2 (lam2 Y P) Y α with hF_def
  have hF : Continuous F := (expSum1_continuous _ _ _).mul (expSum2_continuous _ _)
  have hee : Continuous (fun x : ℝ => U1534.ee x) := by unfold U1534.ee; fun_prop
  have hcont : ∀ n : ℕ, Continuous (fun z : ℝ × ℝ =>
      F z.1 * conj (F z.2) * U1534.ee ((z.2 - z.1) * n)) := by
    intro n
    exact ((hF.comp continuous_fst).mul (Complex.continuous_conj.comp (hF.comp continuous_snd))).mul
      (hee.comp (by fun_prop))
  -- step A: each square as a double integral
  have hA : ∀ n : ℕ, ((‖minorInt X Y P Q n‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, F z.1 * conj (F z.2) * U1534.ee ((z.2 - z.1) * n) ∂(μ.prod μ) := by
    intro n
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    have hm : minorInt X Y P Q n = ∫ α, F α * U1534.ee (-(α * n)) ∂μ := rfl
    rw [hm, ← integral_conj, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [map_mul, ee_conj]
    rw [show (z.2 - z.1) * (n : ℝ) = -(z.1 * n) + -(-(z.2 * n)) by ring, ee_add]
    ring
  -- step B: sum over n inside
  have hB : ((∑ n ∈ N, ‖minorInt X Y P Q n‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, F z.1 * conj (F z.2) * kern N (z.2 - z.1) ∂(μ.prod μ) := by
    rw [Complex.ofReal_sum]
    simp_rw [hA]
    rw [← integral_finsetSum _ (fun n _ => integrable_prod_of_continuous hsub (hcont n))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [kern, Finset.mul_sum]
  -- step C
  have hkc := kern_continuous N
  have hC : ∑ n ∈ N, ‖minorInt X Y P Q n‖ ^ 2 ≤
      ∫ z, ‖F z.1 * conj (F z.2) * kern N (z.2 - z.1)‖ ∂(μ.prod μ) := by
    have := norm_integral_le_integral_norm (μ := μ.prod μ)
      (fun z => F z.1 * conj (F z.2) * kern N (z.2 - z.1))
    rw [← hB, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at this
    exact this
  set u : ℝ × ℝ → ℝ := fun z => ‖expSum1 lam1 X Y z.1‖ ^ 2 *
    ‖expSum2 (lam2 Y P) Y z.2‖ ^ 2 * ‖kern N (z.1 - z.2)‖ with hu_def
  have h1c := expSum1_continuous lam1 X Y
  have h2c := expSum2_continuous (lam2 Y P) Y
  have hucont : Continuous u := by
    simp only [hu_def]
    exact (((h1c.comp continuous_fst).norm.pow 2).mul ((h2c.comp continuous_snd).norm.pow 2)).mul
      (hkc.comp (continuous_fst.sub continuous_snd)).norm
  have hu : Integrable u (μ.prod μ) := integrable_prod_of_continuous hsub hucont
  have hpt : ∀ z : ℝ × ℝ, ‖F z.1 * conj (F z.2) * kern N (z.2 - z.1)‖ ≤ (u z.swap + u z) / 2 := by
    intro z
    have hk : ‖kern N (z.1 - z.2)‖ = ‖kern N (z.2 - z.1)‖ := by rw [← norm_kern_neg, neg_sub]
    simp only [hF_def, hu_def, norm_mul, Complex.norm_conj, Prod.fst_swap, Prod.snd_swap, hk]
    have ha1 := norm_nonneg (expSum1 lam1 X Y z.1)
    have ha2 := norm_nonneg (expSum1 lam1 X Y z.2)
    have hb1 := norm_nonneg (expSum2 (lam2 Y P) Y z.1)
    have hb2 := norm_nonneg (expSum2 (lam2 Y P) Y z.2)
    have hk0 := norm_nonneg (kern N (z.2 - z.1))
    nlinarith [mul_nonneg (sq_nonneg (‖expSum1 lam1 X Y z.2‖ * ‖expSum2 (lam2 Y P) Y z.1‖ -
      ‖expSum1 lam1 X Y z.1‖ * ‖expSum2 (lam2 Y P) Y z.2‖)) hk0]
  have hD1 : ∫ z, ‖F z.1 * conj (F z.2) * kern N (z.2 - z.1)‖ ∂(μ.prod μ) ≤
      ∫ z, u z ∂(μ.prod μ) := by
    have hrhs : Integrable (fun z : ℝ × ℝ => (u z.swap + u z) / 2) (μ.prod μ) :=
      integrable_prod_of_continuous hsub
        (((hucont.comp continuous_swap).add hucont).div_const 2)
    have hlhs : Integrable (fun z : ℝ × ℝ => ‖F z.1 * conj (F z.2) * kern N (z.2 - z.1)‖)
        (μ.prod μ) :=
      integrable_prod_of_continuous hsub
        (((hF.comp continuous_fst).mul (Complex.continuous_conj.comp
          (hF.comp continuous_snd))).mul (hkc.comp (continuous_snd.sub continuous_fst))).norm
    refine (integral_mono hlhs hrhs hpt).trans (le_of_eq ?_)
    have hus : Integrable (fun z : ℝ × ℝ => u z.swap) (μ.prod μ) := hu.swap
    rw [integral_div, integral_add hus hu, integral_prod_swap u]
    ring
  -- step E
  have hE : ∫ z, u z ∂(μ.prod μ) = ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 *
      (∫ α, ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * ‖kern N (β - α)‖ ∂μ) ∂μ := by
    rw [integral_prod u hu]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
    simp only [hu_def]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
    simp only; ring
  have hint1 : Integrable (fun β => ‖expSum1 lam1 X Y β‖ ^ 2 *
      (∫ α, ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * ‖kern N (β - α)‖ ∂μ)) μ := by
    have := hu.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall (fun β => ?_))
    simp only [hu_def]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
    simp only; ring
  have hint2 : Integrable (fun β => ‖expSum1 lam1 X Y β‖ ^ 2 * D) μ :=
    integrable_of_continuous hsub ((h1c.norm.pow 2).mul continuous_const)
  have hle : ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 *
      (∫ α, ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * ‖kern N (β - α)‖ ∂μ) ∂μ ≤
      ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 * D ∂μ := by
    apply integral_mono_ae hint1 hint2
    rw [hμ, Filter.EventuallyLE, ae_restrict_iff' (minorSet_meas P Q)]
    exact Filter.Eventually.of_forall (fun β hβ =>
      mul_le_mul_of_nonneg_left (h β hβ) (sq_nonneg _))
  have hJ : ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 ∂μ ≤ ∫ β in unitArc Q, ‖expSum1 lam1 X Y β‖ ^ 2 := by
    apply setIntegral_mono_set
    · exact integrable_of_continuous Set.Ioc_subset_Icc_self (h1c.norm.pow 2)
    · exact Filter.Eventually.of_forall (fun β => sq_nonneg _)
    · exact (Set.diff_subset : minorSet P Q ⊆ unitArc Q).eventuallyLE
  have hParseval : ∫ β in unitArc Q, ‖expSum1 lam1 X Y β‖ ^ 2 = ∑ m ∈ win1 X Y, lam1 m ^ 2 := by
    unfold unitArc
    rw [← intervalIntegral.integral_of_le (by linarith)]
    exact parseval1 lam1 X Y (1 / Q)
  calc ∑ n ∈ N, ‖minorInt X Y P Q n‖ ^ 2
      ≤ ∫ z, u z ∂(μ.prod μ) := hC.trans hD1
    _ ≤ ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 * D ∂μ := hE ▸ hle
    _ = D * ∫ β, ‖expSum1 lam1 X Y β‖ ^ 2 ∂μ := by rw [integral_mul_const]; ring
    _ ≤ D * ∑ m ∈ win1 X Y, lam1 m ^ 2 := by
        rw [← hParseval]; exact mul_le_mul_of_nonneg_left hJ hD

/-- The distance of gamma to the nearest integer, written as the smaller of the
fractional part and 1 minus it. -/
noncomputable def nint (γ : ℝ) : ℝ := min (Int.fract γ) (1 - Int.fract γ)

/-- The distance to the nearest integer is nonnegative. -/
theorem nint_nonneg (γ : ℝ) : 0 ≤ nint γ :=
  le_min (Int.fract_nonneg γ) (by linarith [Int.fract_lt_one γ])

/-- e of x has norm 1. -/
theorem norm_ee (x : ℝ) : ‖U1534.ee x‖ = 1 := by
  unfold U1534.ee
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The trivial bound for the kernel of display 29. -/
theorem kern_le_card (N : Finset ℕ) (γ : ℝ) : ‖kern N γ‖ ≤ N.card := by
  unfold kern
  refine (norm_sum_le _ _).trans ?_
  simp [norm_ee]

/-- Jordan's inequality form used for the bound of page 7: the absolute value of
sin of pi gamma is at least 2 times the distance of t to the nearest integer. -/
theorem two_nint_le_abs_sin (γ : ℝ) : 2 * nint γ ≤ |Real.sin (Real.pi * γ)| := by
  set t := Int.fract γ with ht
  have h0 : 0 ≤ t := Int.fract_nonneg γ
  have h1 : t < 1 := Int.fract_lt_one γ
  have hs : |Real.sin (Real.pi * γ)| = Real.sin (Real.pi * t) := by
    have : Real.pi * γ = Real.pi * t + (⌊γ⌋ : ℤ) * Real.pi := by
      rw [ht, Int.fract]; ring
    have hz : |(-1 : ℝ) ^ ⌊γ⌋| = 1 := by rw [abs_zpow, abs_neg, abs_one, one_zpow]
    rw [this, Real.sin_add_int_mul_pi, abs_mul, hz, one_mul]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]))
  rw [hs]
  rcases le_or_gt t (1 / 2) with h | h
  · have := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rw [e] at this
    exact le_trans (by unfold nint; rw [← ht]; nlinarith [min_le_left t (1 - t)]) this
  · have hsym : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
    have := Real.mul_le_sin (x := Real.pi * (1 - t)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * (1 - t)) = 2 * (1 - t) := by field_simp
    rw [e] at this
    rw [hsym]
    exact le_trans (by unfold nint; rw [← ht]; nlinarith [min_le_right t (1 - t)]) this

/-- The norm of e of gamma minus 1 is 2 times the absolute value of sin of pi gamma. -/
theorem norm_ee_sub_one (γ : ℝ) : ‖U1534.ee γ - 1‖ = 2 * |Real.sin (Real.pi * γ)| := by
  unfold U1534.ee
  rw [show (2 * Real.pi * Complex.I * (γ : ℂ)) = Complex.I * ((2 * Real.pi * γ : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  congr 2; ring

/-- The well known bound of page 7 before display 29: the sum of e of gamma n over
an interval of integers has norm at most 1 over 2 times the distance of gamma to the
nearest integer. -/
theorem kern_Ioc_le (a b : ℕ) (γ : ℝ) (hγ : 0 < nint γ) :
    ‖kern (Finset.Ioc a b) γ‖ ≤ 1 / (2 * nint γ) := by
  set x := U1534.ee γ with hx
  have hpow : ∀ n : ℕ, U1534.ee (γ * n) = x ^ n := by
    intro n; rw [hx]; unfold U1534.ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hx1 : ‖x - 1‖ ≥ 4 * nint γ := by
    rw [hx, norm_ee_sub_one]; linarith [two_nint_le_abs_sin γ]
  have hxne : x - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hx1; linarith
  have hxn : ‖x‖ = 1 := norm_ee γ
  unfold kern
  simp_rw [hpow]
  rcases le_or_gt b a with hab | hab
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  have hsplit : ∑ n ∈ Finset.Ioc a b, x ^ n =
      x ^ (a + 1) * ∑ i ∈ Finset.range (b - a), x ^ i := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show b + 1 - (a + 1) = b - a by omega]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add]
  have hxne1 : x ≠ 1 := fun h => hxne (by rw [h, sub_self])
  rw [hsplit, norm_mul, norm_pow, hxn, one_pow, one_mul, geom_sum_eq hxne1, norm_div]
  have hnum : ‖x ^ (b - a) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hxn, one_pow, norm_one]; norm_num
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr hxne
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- The majorant min of H plus 1 and 1 over 2 times the distance of gamma to the
nearest integer of page 7 display 29, with the value H plus 1 at integers. -/
noncomputable def kmaj (H γ : ℝ) : ℝ :=
  if nint γ = 0 then H + 1 else min (H + 1) (1 / (2 * nint γ))

theorem nint_measurable : Measurable nint := by
  unfold nint
  exact measurable_fract.min (measurable_const.sub measurable_fract)

theorem kmaj_measurable (H : ℝ) : Measurable (kmaj H) := by
  unfold kmaj
  exact Measurable.ite (measurableSet_eq_fun nint_measurable measurable_const) measurable_const
    (measurable_const.min (measurable_const.div (nint_measurable.const_mul 2)))

theorem kmaj_nonneg {H : ℝ} (hH : 0 ≤ H) (γ : ℝ) : 0 ≤ kmaj H γ := by
  unfold kmaj
  split_ifs with h
  · linarith
  · exact le_min (by linarith) (by have := nint_nonneg γ; positivity)

theorem kmaj_le (H γ : ℝ) : kmaj H γ ≤ H + 1 := by
  unfold kmaj; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The summation range X less than n at most X plus H of display 32 is the
interval of integers from the floor of X exclusive to the floor of X plus H. -/
theorem iocFilter_eq {X H : ℝ} (hX : 0 ≤ X) :
    (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)) =
      Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  rw [← Nat.floor_lt hX]
  omega

/-- The well known bound of page 7 before display 29 for the kernel of the range
X less than n at most X plus H: at most the majorant `kmaj`. -/
theorem kern_le_kmaj {X H : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) (γ : ℝ) :
    ‖kern ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))) γ‖ ≤ kmaj H γ := by
  rw [iocFilter_eq hX]
  have hcard : ((Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊).card : ℝ) ≤ H + 1 := by
    rw [Nat.card_Ioc]
    have hmono : ⌊X⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_le_floor (by linarith)
    rw [Nat.cast_sub hmono]
    have h3 : (⌊X + H⌋₊ : ℝ) ≤ X + H := Nat.floor_le (by linarith)
    have h4 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    linarith
  have htriv := (kern_le_card (Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊) γ).trans hcard
  unfold kmaj
  split_ifs with h
  · exact htriv
  · exact le_min htriv (kern_Ioc_le _ _ γ (lt_of_le_of_ne (nint_nonneg γ) (Ne.symm h)))

/-- The trivial bound for S2. -/
theorem norm_expSum2_le (lam : ℕ → ℝ) (Y α : ℝ) :
    ‖expSum2 lam Y α‖ ≤ ∑ m ∈ win2 Y, |lam m| := by
  unfold expSum2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- From the paper's majorant to the kernel: if the minor arc integral of the
square of S2 against the majorant of display 29 is at most D, then so is the
integral against the norm of the kernel. -/
theorem kern_integral_le {X H P Q Y β D : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H)
    (h : ∫ α in minorSet P Q, ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * kmaj H (β - α) ≤ D) :
    ∫ α in minorSet P Q, ‖expSum2 (lam2 Y P) Y α‖ ^ 2 *
      ‖kern ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))) (β - α)‖ ≤ D := by
  refine le_trans ?_ h
  have h2c := expSum2_continuous (lam2 Y P) Y
  have hsub := minorSet_subset P Q
  apply integral_mono
  · exact integrable_of_continuous hsub ((h2c.norm.pow 2).mul
      ((kern_continuous _).comp (continuous_const.sub continuous_id)).norm)
  · have hfin : volume (minorSet P Q) < ⊤ :=
      lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top
    refine IntegrableOn.of_bound hfin
      ((h2c.norm.pow 2).measurable.mul
        ((kmaj_measurable H).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      ((∑ m ∈ win2 Y, |lam2 Y P m|) ^ 2 * (H + 1)) (Filter.Eventually.of_forall (fun α => ?_))
    have hk0 := kmaj_nonneg hH (β - α)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_expSum2_le _ _ _) 2)
      (kmaj_le H _) hk0 (by positivity)
  · intro α
    exact mul_le_mul_of_nonneg_left (kern_le_kmaj hX hH _) (sq_nonneg _)

/-- Bookkeeping for display 17 with lambda1 equal to varpi: the sum of the squared
weights is at most Y plus 1. -/
theorem sum_lam1_sq_le (X Y : ℝ) (hY : 0 ≤ Y) : ∑ m ∈ win1 X Y, lam1 m ^ 2 ≤ Y + 1 := by
  refine le_trans ?_ (card_win1_le X Y hY)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum (fun m _ => ?_)
  unfold lam1; split_ifs <;> norm_num

/-- LEAF, route burst session 8 p3. Displays 30 and 31 of page 7. LEAF, route burst session 8 p3. Page 7, the last line of display 29 and the
claim after display 31, for lambda2 equal to lambda0 on the written range, with H
at most Y P to the minus 2 as in `minor_arc_display32`: for every beta on the
minor arcs, the minor arc integral of the square of S2 of alpha times the majorant
min of H plus 1 and 1 over 2 times the distance of beta minus alpha to the nearest
integer is at most a constant times H L to the minus A. The paper proves it by the
subdivision display 30, display 31, Gallagher's lemma, reference 5 Lemma 1, and
hypothesis A2.3, verified on page 15 by Lemma 3.4, which cites Liu and Zhan Lemma
5.1 and Mikawa and Peneva Lemma 2. CITED. -/
theorem minor_dist_display30 : (
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 →
      ∀ β ∈ minorSet (Real.log X ^ B) (H / Real.log X ^ B),
        ∫ α in minorSet (Real.log X ^ B) (H / Real.log X ^ B),
          ‖expSum2 (lam2 (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B)) (X ^ (7 / 12 + ε / 2)) α‖ ^ 2 *
          kmaj H (β - α) ≤ C * H * Real.log X ^ (-A)
  ) := by
  sorry

/-- LEAF, route burst session 8 p3, UNWRITTEN RANGE. The same kernel bound on the unwritten range. LEAF, route burst session 8 p3, UNWRITTEN RANGE. The statement of
`minor_dist_display30` on the range of display 32 with epsilon in 5/18 to 11/18 and
H above X to the 1 minus epsilon. -/
theorem minor_dist_display30_large : (
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → 5 / 18 < ε → ε ≤ 11 / 18 →
      min (X ^ (7 / 18 + ε)) (X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2) ≤ H → X ^ (1 - ε) < H →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 →
      ∀ β ∈ minorSet (Real.log X ^ B) (H / Real.log X ^ B),
        ∫ α in minorSet (Real.log X ^ B) (H / Real.log X ^ B),
          ‖expSum2 (lam2 (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B)) (X ^ (7 / 12 + ε / 2)) α‖ ^ 2 *
          kmaj H (β - α) ≤ C * H * Real.log X ^ (-A)
  ) := by
  sorry

/-- The final step of display 32 from display 29: with D equal to C H L to the
minus A and I1 at most 2 Y. -/
theorem minor_from_kernel {X Y P Q C H LA : ℝ} (N : Finset ℕ) (hY : 1 ≤ Y) (hC : 0 < C)
    (hH : 0 ≤ H) (hLA : 0 ≤ LA)
    (h : ∀ β ∈ minorSet P Q, ∫ α in minorSet P Q,
      ‖expSum2 (lam2 Y P) Y α‖ ^ 2 * ‖kern N (β - α)‖ ≤ C * H * LA) :
    ∑ n ∈ N, ‖minorInt X Y P Q n‖ ^ 2 ≤ (2 * C) * H * Y * LA := by
  have hD : 0 ≤ C * H * LA := by positivity
  refine (display29 X Y P Q (C * H * LA) N hD h).trans ?_
  have := sum_lam1_sq_le X Y (by linarith)
  calc C * H * LA * ∑ m ∈ win1 X Y, lam1 m ^ 2 ≤ C * H * LA * (Y + 1) :=
        mul_le_mul_of_nonneg_left this hD
    _ ≤ C * H * LA * (2 * Y) := mul_le_mul_of_nonneg_left (by linarith) hD
    _ = (2 * C) * H * Y * LA := by ring

theorem one_le_Y {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) : 1 ≤ X ^ (7 / 12 + ε / 2) :=
  Real.one_le_rpow hX (by linarith)

/-- Page 7 display 32, PROVED from display 29, the kernel bound of page 7 and the
leaf `minor_dist_display30`. For lambda1 equal to varpi and lambda2 equal to
lambda0, given A there is B0 such that for B at least B0 the sum over X less than n
at most X plus H of the square of the minor arc integral is at most a constant times
H Y L to the minus A. The paper proves it by displays 29 to 31, Gallagher's lemma
and hypothesis A2.3, which page 15 verifies through Lemma 3.4, Liu and Zhan Lemma
5.1 and Mikawa and Peneva Lemma 2. The proof on page 7 uses the interval of n only
through the bound for the sum of e of alpha n over it, so the statement is taken for
any interval N0 less than n at most N0 plus H with N0 nonnegative; H is at most
Y P to the minus 2 as in `major_arc_display28`. -/
theorem minor_arc_display32 : (
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 → ∀ N0 : ℝ, 0 ≤ N0 →
        ∑ n ∈ (Finset.range (⌊N0 + H⌋₊ + 1)).filter (fun n : ℕ => N0 < (n : ℝ)),
          ‖minorInt X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) (H / Real.log X ^ B) n‖ ^ 2 ≤
          C * H * X ^ (7 / 12 + ε / 2) * Real.log X ^ (-A)
  ) := by
  intro A hA
  obtain ⟨B0, hB0, hk⟩ := minor_dist_display30 A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, hk'⟩ := hk B hB ε hε
  refine ⟨2 * C, X0, by positivity, hX0, fun X H hX hH1 hH2 hH3 N0 hN0 => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have hH : 0 ≤ H := le_trans (Real.rpow_nonneg (by linarith) _) hH1
  have hL : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hX1) _
  exact minor_from_kernel _ (one_le_Y hX1 hε) hC hH hL
    (fun β hβ => kern_integral_le hN0 hH (hk' X H hX hH1 hH2 hH3 β hβ))

/-- Page 7 display 32 on the unwritten range, PROVED from display 29, the kernel
bound of page 7 and the leaf `minor_dist_display30_large`. The same mean square
bound as `minor_arc_display32`, for epsilon in 5/18 to 11/18 and H above X to the
1 minus epsilon, where page 15 verifies hypothesis A2.3 by Lemma 3.4 only on the
written range. -/
theorem minor_arc_display32_large : (
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → 5 / 18 < ε → ε ≤ 11 / 18 →
      min (X ^ (7 / 18 + ε)) (X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2) ≤ H → X ^ (1 - ε) < H →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 → ∀ N0 : ℝ, 0 ≤ N0 →
        ∑ n ∈ (Finset.range (⌊N0 + H⌋₊ + 1)).filter (fun n : ℕ => N0 < (n : ℝ)),
          ‖minorInt X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) (H / Real.log X ^ B) n‖ ^ 2 ≤
          C * H * X ^ (7 / 12 + ε / 2) * Real.log X ^ (-A)
  ) := by
  intro A hA
  obtain ⟨B0, hB0, hk⟩ := minor_dist_display30_large A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, hk'⟩ := hk B hB ε hε
  refine ⟨2 * C, X0, by positivity, hX0, fun X H hX he1 he2 hH0 hH1 hH2 N0 hN0 => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have hH : 0 ≤ H := le_trans (Real.rpow_nonneg (by linarith) _) hH1.le
  have hL : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hX1) _
  exact minor_from_kernel _ (one_le_Y hX1 hε) hC hH hL
    (fun β hβ => kern_integral_le hN0 hH (hk' X H hX he1 he2 hH0 hH1 hH2 β hβ))

end LeanLab.KumchevLiu2007.Task129f

#print axioms LeanLab.KumchevLiu2007.Task129f.parseval1
#print axioms LeanLab.KumchevLiu2007.Task129f.card_win1_le
#print axioms LeanLab.KumchevLiu2007.Task129f.display29
#print axioms LeanLab.KumchevLiu2007.Task129f.minor_from_kernel
#print axioms LeanLab.KumchevLiu2007.Task129f.kern_Ioc_le
#print axioms LeanLab.KumchevLiu2007.Task129f.kern_le_kmaj
#print axioms LeanLab.KumchevLiu2007.Task129f.kern_integral_le
#print axioms LeanLab.KumchevLiu2007.Task129f.minor_arc_display32
#print axioms LeanLab.KumchevLiu2007.Task129f.minor_arc_display32_large

import LeanLab.ExceptionalSet.UpJ200.Decomp509a
import LeanLab.ExceptionalSet.Decomp371a
import LeanLab.ExceptionalSet.Decomp404b

/-!
P0082 page 357 display 8, specialized on page 364 display 23.
Source: https://doi.org/10.5802/aif.1621
The explicit kernel satisfies Poisson summation through its quadratic decay.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp404a

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.DecompJ200

/-- P0082 page 357 display 8. The major arc indicator times S squared
has period one. -/
theorem major_periodic (P X : ℝ) :
    Function.Periodic ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) 1 := by
  classical
  intro α
  have hmem : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X := by
    exact Iff.of_eq (Decomp371a.majorArcs_periodic P X α)
  simp only [Set.indicator_apply, hmem, Decomp371a.Sp_periodic P X α]



/-- P0082 page 357 display 8. The weighted major integral is the sum
of its two adjacent integer coefficients times the explicit trapezoid weights. -/
theorem major_integral_formula (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in majorArcs P X, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) =
      (KernelTransform264.weight Δ (Int.fract v) : ℂ) * R1 P X ⌊v⌋ +
        (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) * R1 P X (⌊v⌋ + 1) := by
  classical
  let h : ℝ → ℂ := (majorArcs P X).indicator (fun α => Sp P X α ^ 2)
  let K : ℝ → ℂ := fun α => (Kfun Δ α : ℂ)
  have hmeas := PrimeKernel264.measurableSet_majorArcs P X
  have he : (fun α : ℝ => h α * K α * eC (-(α * v))) =
      (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [h, K, hα]
  have hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
    rw [he]
    exact (PrimeKernel264.total_integrable hΔ hΔ1 P X v).indicator hmeas
  have hfold := Decomp404b.fold_of_integrable h K (major_periodic P X) v hg
  rw [he, integral_indicator hmeas] at hfold
  rw [hfold]
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  calc
    _ = ∫ α in (0 : ℝ)..1,
        (h α * eC (-(α * (⌊v⌋ : ℝ)))) * (KernelTransform264.weight Δ (Int.fract v) : ℂ) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) *
            (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only [K]
      rw [Decomp404b.poisson_kernel Δ v α hΔ hΔ1]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (KernelTransform264.weight Δ (Int.fract v) : ℂ))
        (hg1.mul_const (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ)),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      change hcheck h ⌊v⌋ * _ + hcheck h (⌊v⌋ + 1) * _ = _
      rw [major_hcheck, major_hcheck]
      ring

/-- P0082 pages 357 and 364 displays 8 and 23. This is the exact
existing major identity statement, now from the explicit kernel alone. -/
theorem major_identity (γ δ κ : ℝ) (N n : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hleft : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ Int.fract (F γ n))
    (hright : Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ))) :
    majorInt γ δ κ N n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) := by
  unfold majorInt
  rw [major_integral_formula _ _ _ _ hΔ hΔ1]
  have hw0 : KernelTransform264.weight (calE γ κ N ^ (-(1 / 8 : ℝ))) (Int.fract (F γ n)) = 1 := by
    apply KernelTransform264.weight_one hΔ hΔ1
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact hright
  have hw1 : KernelTransform264.weight (calE γ κ N ^ (-(1 / 8 : ℝ))) (Int.fract (F γ n) - 1) = 1 := by
    apply KernelTransform264.weight_one hΔ hΔ1
    rw [abs_of_nonpos (by linarith [Int.fract_lt_one (F γ n)] : Int.fract (F γ n) - 1 ≤ 0)]
    linarith
  rw [hw0, hw1]
  simp only [Complex.ofReal_one, one_mul, nu]

/-- P0082 page 364 after display 23. The fractional boundary count
follows from the existing Lemma4 discrepancy input on the full index interval. -/
theorem boundary_of_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := h4 γ h1 h2
  refine ⟨8 * κa, by positivity, fun κ hκ hκsmall => ?_⟩
  let B := 2 * |A| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hE.eventually_ge_atTop 2)
  refine ⟨B, hB, max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE1 : 1 < calE γ κ N := lt_of_lt_of_le (by norm_num) (hNE N ((le_max_right _ _).trans hN))
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE1 (by norm_num)
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num : -(1 / 2 : ℝ) < 0)
  have hlo := hdisc N hN1 1 hα (by norm_num) Δ 0 (by norm_num) hΔ hΔ1.le
  have hhi := hdisc N hN1 1 hα (by norm_num) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul, sub_zero, sub_sub_cancel] at hlo hhi
  have herr : Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ Δ := by
    dsimp [Δ, calE]
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log N ^ (3 - 2 * γ) := (Real.rpow_pos_of_pos hL _).le
    nlinarith [mul_le_mul_of_nonneg_right hκsmall hp]
  let L := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let R := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)
  have hsubset : (window γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ⊆ L ∪ R := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hn⟩
    have hnI := Decomp371a.window_subset_Ioc γ h1 N hN16 hnW
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, Int.fract_nonneg _, hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hn.le, Int.fract_lt_one _⟩)
  have hcard : (((window γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤ L.card + R.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)
  have hl : (L.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hlo).2
    change (L.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  have hr : (R.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hhi).2
    change (R.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  calc
    _ ≤ (L.card : ℝ) + R.card := hcard
    _ ≤ (Δ * N / 2 + |A| * N * Δ) + (Δ * N / 2 + |A| * N * Δ) := add_le_add hl hr
    _ = _ := by dsimp [B]; ring


/-- Assembly. P0082 page 365 Lemma 8 with the exact existing major
bound statement. Only the coefficient lower bound and the existing Lemma4 input remain
conditional. The Fourier identity is supplied by the explicit kernel proof. -/
theorem major_bound_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := Decomp371a.leaf_coefficient_lower γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := boundary_of_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
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
      have hid := major_identity γ δ κ N n hΔ hΔ1
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


end LeanLab.ExceptionalSet.Decomp404a

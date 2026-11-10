/-
P0069, Sections 2 to 5. CODEX task165.
The paper hypotheses and weight constructions are separate OPEN leaves.
The exact sieve_data assembly is CONDITIONAL on those leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.DecompC165a
import LeanLab.BHP1997.DecompC165c
import LeanLab.BHP1997.Decomp414a
import LeanLab.BHP1997.DecompC165d
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.Thm2Sing
import LeanLab.BHP1997.Characters132
import LeanLab.BHP1997.SieveMarginsC165
import LeanLab.ChenDoubleSieve.BuchstabBounds

namespace LeanLab.BHP1997.DecompC165b
open Classical Complex Decomp132

/-- Page 2, the positive scale Y times the singular series divided by
log x times log Y. Positivity is proved separately for x greater than 1. -/
noncomputable def correlationScale (ε x : ℝ) (N : ℕ) : ℝ :=
  x ^ (11 / 20 + ε) / (Real.log x * Real.log (x ^ (11 / 20 + ε))) * Thm2.sing (N / 2)

/-- Page 3, the exceptional set in 1.6 for one pair of real weights. -/
noncomputable def badSet (ε u v K : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
    (fun N => Even N ∧ K * |u * v| * correlationScale ε x N / Real.log x <
      |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N -
        u * v * correlationScale ε x N|)

/-- Page 3, Theorem 2 applied to one pair of real weights satisfying
conditions i to iv. CONDITIONAL on Theorem 2 at epsilon and B. -/
theorem pair_correlation {ε B u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (h2 : Thm2.Theorem2 ε B) (ha : LeftConditions ε B u a)
    (hb : RightConditions ε B v b) :
    ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
      ((badSet ε u v K a b x).card : ℝ) <
        x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ A := by
  obtain ⟨hai, ⟨Ca, hCa⟩, harough⟩ := ha
  obtain ⟨⟨Cb, hCb⟩, hbiii, E, hbiv⟩ := hb
  have hdiv : ∃ C : ℝ, ∀ x k,
      ‖(a x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖(b x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
    refine ⟨max Ca Cb, ?_⟩
    intro x k
    have hpow : 0 ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg (by positivity) _
    constructor
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCa x k).trans (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) hpow)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCb x k).trans (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) hpow)
  have hrough : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 → (a x k : ℂ) = 0 := by
    intro A hA
    obtain ⟨C, hC⟩ := harough A hA
    exact ⟨C, fun x hx k hk => by simp [hC x hx k hk]⟩
  have hout := h2 (fun x k => (a x k : ℂ)) (fun x k => (b x k : ℂ)) u v E
    hai hdiv hrough hbiii (by simpa only [sieveQ, rightInterval] using hbiv)
  intro A hA
  obtain ⟨K, C, hC⟩ := hout A hA
  refine ⟨K, C, fun x hx => ?_⟩
  have hc := hC x hx
  convert hc using 1
  congr 2
  apply Finset.filter_congr
  intro N hN
  have hconv : (∑ k ∈ leftInterval ε x, ∑ m ∈ rightInterval ε x,
      if k + m = N then (a x k : ℂ) * (b x m : ℂ) else 0) =
      (convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N : ℂ) := by
    simp only [convolution, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp
  simp only [correlationScale, leftInterval, rightInterval] at *
  rw [hconv]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  ring_nf

/-- LEAF. Section 2, pages 5 to 11, proof of Theorem 2 from conditions
 i to iv on page 3 and the circle estimates 2.1 onward. OPEN. -/
theorem section2_circle_method : Thm2.Theorem2Paper := by
  sorry

/-- LEAF. Section 3, pages 11 to 21, Theorem 4 and its mean value lemmas.
Reuse the proved exponent lemmas. The finer analytic leaves are in DecompC165c. CONDITIONAL. -/
theorem section3_mean_values : Thm4.Theorem4Paper := by
  exact Decomp414a.dyadic_mean_value DecompC165c.hybrid_mean_square
    DecompC165c.hybrid_large_values DecompC165c.energy_log_bound

section Task217Numerics
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Real

/-- Page 42 auxiliary rational box grid in five gap coordinates. The sixth natural coordinate is slack. -/
def upperFiveGrid : Finset (Fin 6 → ℕ) := Finset.Nat.antidiagonalTuple 6 12

/-- Page 42 auxiliary grid count. Checked by kernel reduction. -/
theorem upper_five_grid_card : upperFiveGrid.card = 6188 := by
  decide +kernel

/-- Page 42 auxiliary upper Darboux sum. The Jacobian is 1/720 and the product lower bound is 0.1 times 0.18 to the fifth power. -/
noncomputable def upperFiveGridBound : ℝ :=
  ∑ _ ∈ upperFiveGrid, (0.08 / 12 : ℝ) ^ 5 / (720 * (0.1 * 0.18 ^ 5))

/-- Page 42 auxiliary rational certificate. This is a bound for the explicit box sum, not yet the integral. -/
theorem upper_five_grid_bound : upperFiveGridBound < 0.000006 := by
  norm_num [upperFiveGridBound, Finset.sum_const, upper_five_grid_card]

/-- Page 42 auxiliary product estimate for the denominator. Local exact? search found no matching lemma. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hp := Finset.prod_le_one₀ h0s h1s
    have hpa := mul_nonneg (sub_nonneg.mpr (h1 a (Finset.mem_insert_self _ _))) (sub_nonneg.mpr hp)
    have hi := ih h0s h1s
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith

/-- Page 42 denominator bound for six nonnegative exponents summing to 1 and at most 0.18. -/
theorem upper_five_product_bound (a : Fin 6 → ℝ)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 0.18) (hs : ∑ i, a i = 1) :
    0.1 * 0.18 ^ 5 ≤ ∏ i, a i := by
  have h := one_sub_sum_le_prod Finset.univ (fun i => a i / 0.18)
    (fun i _ => div_nonneg (h0 i) (by norm_num)) (fun i _ => (div_le_one (by norm_num)).mpr (h1 i))
  have hsum : (∑ i : Fin 6, (1 - a i / 0.18)) = 6 - 1 / 0.18 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    norm_num
  rw [hsum, Finset.prod_div_distrib] at h
  norm_num at h
  linarith

/-- Page 42 auxiliary closed rational box in weighted gap coordinates. -/
noncomputable def upperFiveBox (q : Fin 6 → ℕ) : Set (Fin 5 → ℝ) :=
 Icc (fun i => (q i.castSucc : ℝ) * (0.08 / 12))
     (fun i => ((q i.castSucc : ℝ) + 1) * (0.08 / 12))

/-- Page 42 simplex cover by rational boxes. Natural floors choose the box and the last coordinate records the unused mesh budget. -/
theorem upper_five_grid_cover (g : Fin 5 → ℝ)
    (h0 : ∀ i, 0 ≤ g i) (hs : ∑ i, g i ≤ 0.08) :
    ∃ q ∈ upperFiveGrid, g ∈ upperFiveBox q := by
  let k : Fin 5 → ℕ := fun i => ⌊g i / (0.08 / 12)⌋₊
  have hk : (∑ i, k i) ≤ 12 := by
    have hr : (∑ i, (k i : ℝ)) ≤ 12 := by
      calc
        (∑ i, (k i : ℝ)) ≤ ∑ i, g i / (0.08 / 12) :=
          Finset.sum_le_sum (fun i _ => Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
        _ ≤ 12 := by rw [← Finset.sum_div]; norm_num; linarith
    exact_mod_cast hr
  let q : Fin 6 → ℕ := Fin.snoc (α := fun _ => ℕ) k (12 - ∑ i, k i)
  refine ⟨q, ?_, ?_⟩
  · rw [upperFiveGrid, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc]
    simpa only [q, Fin.snoc_castSucc, Fin.snoc_last] using Nat.add_sub_of_le hk
  · constructor
    · intro i
      dsimp only [upperFiveBox] at *
      simp only [q, Fin.snoc_castSucc]
      change (k i : ℝ) * (0.08 / 12) ≤ g i
      exact (le_div_iff₀ (by norm_num)).mp (Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
    · intro i
      dsimp only [upperFiveBox] at *
      simp only [q, Fin.snoc_castSucc]
      change g i ≤ ((k i : ℝ) + 1) * (0.08 / 12)
      exact ((div_lt_iff₀ (by norm_num)).mp (Nat.lt_floor_add_one (g i / (0.08 / 12)))).le

/-- Page 42 auxiliary rational box volume. Reuses Real.volume_Icc_pi. -/
theorem upper_five_box_volume (q : Fin 6 → ℕ) :
    volume (upperFiveBox q) = ENNReal.ofReal ((0.08 / 12 : ℝ) ^ 5) := by
  rw [upperFiveBox, Real.volume_Icc_pi]
  have hh : ∀ i : Fin 5,
    ((q i.castSucc : ℝ) + 1) * (0.08 / 12) - (q i.castSucc : ℝ) * (0.08 / 12) = 0.08 / 12 := by
    intro i; ring
  simp_rw [hh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Page 42 simplex enclosure. Reuses finite subadditivity of measure. -/
theorem upper_five_simplex_volume :
    volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08} ≤
      ENNReal.ofReal ((6188 : ℝ) * (0.08 / 12) ^ 5) := by
  calc
    _ ≤ volume (⋃ q ∈ upperFiveGrid, upperFiveBox q) := by
      apply measure_mono
      intro g hg
      obtain ⟨q,hq,hgq⟩ := upper_five_grid_cover g hg.1 hg.2
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq,hgq⟩⟩
    _ ≤ ∑ q ∈ upperFiveGrid, volume (upperFiveBox q) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [upper_five_box_volume, Finset.sum_const, upper_five_grid_card, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Page 42 displayed five dimensional integration region, transcribed from the page image. -/
noncomputable def upperFiveRegion : Set (Fin 5 → ℝ) :=
 {a | a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧ a 3 ≤ a 4 ∧
   a 4 ≤ 1 - ∑ i, a i ∧ 1 - ∑ i, a i < 0.18 ∧
   0.46 ≤ a 0 + a 1 + a 2 ∧ a 0 + a 1 + a 2 ≤ 0.5}

/-- Page 42 displayed five dimensional discarded integral. This definition asserts no estimate. -/
noncomputable def upperFiveIntegral : ℝ :=
 ∫ a in upperFiveRegion, (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹

/-- Page 42 auxiliary weighted gaps of the six ordered exponents. -/
noncomputable def upperFiveGaps (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
 ![6 * ((∑ i, a i) - 0.82),
   5 * (1 - (∑ i, a i) - a 4),
   4 * (a 4 - a 3), 3 * (a 3 - a 2), 2 * (a 2 - a 1)]

/-- Page 42 auxiliary matrix of the affine weighted gap map. -/
noncomputable def upperFiveGapMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
 !![6, 6, 6, 6, 6; -5, -5, -5, -5, -10; 0, 0, 0, -4, 4;
    0, 0, -3, 3, 0; 0, -2, 2, 0, 0]

/-- Page 42 auxiliary Jacobian computation by exact rational arithmetic. -/
theorem upper_five_gap_det : upperFiveGapMatrix.det = 720 := by
 norm_num [upperFiveGapMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- Page 42 auxiliary affine coordinate identity. -/
theorem upper_five_gap_affine (a : Fin 5 → ℝ) :
 upperFiveGaps a = upperFiveGapMatrix.mulVec a + ![-4.92, 5, 0, 0, 0] := by
 ext i
 fin_cases i <;> simp [upperFiveGaps, upperFiveGapMatrix, dotProduct,
  Fin.sum_univ_succ] <;> ring

/-- Page 42 region geometry, including the automatic lower exponent bound 0.1. -/
theorem upper_five_geometry {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
 (∀ i, 0 ≤ upperFiveGaps a i) ∧ (∑ i, upperFiveGaps a i) ≤ 0.08 ∧
 (∀ i, 0.1 ≤ a i ∧ a i ≤ 0.18) ∧ 0.1 ≤ 1 - ∑ i, a i := by
 rcases ha with ⟨h01,h12,h23,h34,h45,h5,h3,h3'⟩
 have hs : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 := by
  simp [Fin.sum_univ_succ]; ring
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i
   fin_cases i <;> simp [upperFiveGaps] <;> linarith
 · simp [upperFiveGaps, Fin.sum_univ_succ]
   linarith
 · intro i
   fin_cases i <;> dsimp <;> constructor <;> linarith
 · linarith

/-- Page 42 change of measure. Reuses the Mathlib determinant scaling theorem and translation invariance. -/
theorem upper_five_gap_map :
    Measure.map upperFiveGaps volume = ENNReal.ofReal (1 / 720 : ℝ) • volume := by
  have hm : Measurable (Matrix.toLin' upperFiveGapMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  have he : upperFiveGaps = (fun x : Fin 5 → ℝ => x + ![-4.92, 5, 0, 0, 0]) ∘
      Matrix.toLin' upperFiveGapMatrix := by
    ext a i
    exact congrFun (upper_five_gap_affine a) i
  rw [he, ← Measure.map_map (by fun_prop) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [upper_five_gap_det]; norm_num),
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]
  norm_num [upper_five_gap_det]

/-- Page 42 discarded region volume bounded through the rational box cover. -/
theorem upper_five_region_volume :
    volume upperFiveRegion ≤ ENNReal.ofReal ((6188 : ℝ) * (0.08 / 12) ^ 5 / 720) := by
  let S : Set (Fin 5 → ℝ) := {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
      (measurable_pi_apply i)).inter (measurableSet_le (show Measurable (fun g : Fin 5 → ℝ => ∑ i, g i) by fun_prop) measurable_const)
  have hm : Measurable upperFiveGaps := by
    unfold upperFiveGaps
    fun_prop
  calc
    volume upperFiveRegion ≤ volume (upperFiveGaps ⁻¹' S) := by
      apply measure_mono
      intro a ha
      exact ⟨(upper_five_geometry ha).1, (upper_five_geometry ha).2.1⟩
    _ = ENNReal.ofReal (1 / 720 : ℝ) * volume S := by
      rw [← Measure.map_apply hm hS, upper_five_gap_map, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / 720 : ℝ) *
        ENNReal.ofReal ((6188 : ℝ) * (0.08 / 12) ^ 5) :=
      by gcongr; exact upper_five_simplex_volume
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Page 42 pointwise denominator enclosure. -/
theorem upper_five_integrand_bound {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
    ‖(∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹‖ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ := by
  obtain ⟨_, _, harange, hr⟩ := upper_five_geometry ha
  let b : Fin 6 → ℝ := Fin.snoc (α := fun _ => ℝ) a (1 - ∑ i, a i)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (show (0 : ℝ) ≤ 1 - ∑ j, a j by linarith)
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (show (0 : ℝ) ≤ a j by linarith [(harange j).1])
  have hb1 : ∀ i, b i ≤ 0.18 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using le_of_lt ha.2.2.2.2.2.1
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (harange j).2
  have hsum : ∑ i, b i = 1 := by rw [Fin.sum_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hprod := upper_five_product_bound b hb hb1 hsum
  have he : (∏ i, b i) = (∏ i, a i) * (1 - ∑ i, a i) := by
    rw [Fin.prod_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
  rw [he] at hprod
  rw [← mul_inv, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hprod))]
  exact inv_anti₀ (by norm_num) hprod

/-- Page 42 integral enclosure by the explicit rational grid. No numerical integration oracle is used. -/
theorem upper_five_integral_le_grid : upperFiveIntegral ≤ upperFiveGridBound := by
  have hv := upper_five_region_volume
  have hfin : volume upperFiveRegion < ⊤ := lt_of_le_of_lt hv (by simp)
  have hi := norm_setIntegral_le_of_norm_le_const hfin (fun a ha => upper_five_integrand_bound ha)
  have hreal : volume.real upperFiveRegion ≤ (6188 : ℝ) * (0.08 / 12) ^ 5 / 720 := by
    have h := ENNReal.toReal_mono (by simp) hv
    rw [ENNReal.toReal_ofReal (show 0 ≤ (6188 : ℝ) * (0.08 / 12) ^ 5 / 720 by norm_num)] at h
    exact h
  calc
    upperFiveIntegral ≤ ‖upperFiveIntegral‖ := le_abs_self _
    _ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ * volume.real upperFiveRegion := hi
    _ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ * ((6188 : ℝ) * (0.08 / 12) ^ 5 / 720) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = upperFiveGridBound := by
      norm_num [upperFiveGridBound, Finset.sum_const, upper_five_grid_card]

/-- Page 42 certified conservative replacement for the printed 0.000001 bound. The seven dimensional losses and weight construction remain open. -/
theorem upper_five_integral_lt : upperFiveIntegral < 0.000006 :=
  upper_five_integral_le_grid.trans_lt upper_five_grid_bound

/-- Pages 34 and 39. Every point in the Gamma envelope has a two factor subproduct in the Lemma 17a range. -/
theorem gamma_subsum {a b c d e : ℝ} (hab : b ≤ a) (ha : a ≤ 0.36)
    (hs : 0.64 ≤ a + b) (hc : 0.1 ≤ c) (hd : 0.1 ≤ d) (he : 0.1 ≤ e)
    (ht : a + b + c + d + e = 1) :
    b + c ∈ Icc (0.4 : ℝ) 0.46 ∨ b + d ∈ Icc (0.4 : ℝ) 0.46 ∨
      b + e ∈ Icc (0.4 : ℝ) 0.46 := by
  by_contra h
  have hbc : b + c < 0.4 ∨ 0.46 < b + c := by
    by_cases hh : b + c < 0.4
    · exact Or.inl hh
    · exact Or.inr (lt_of_not_ge (fun hle => h (Or.inl ⟨le_of_not_gt hh, hle⟩)))
  have hbd : b + d < 0.4 ∨ 0.46 < b + d := by
    by_cases hh : b + d < 0.4
    · exact Or.inl hh
    · exact Or.inr (lt_of_not_ge (fun hle => h (Or.inr (Or.inl ⟨le_of_not_gt hh, hle⟩))))
  have hbe : b + e < 0.4 ∨ 0.46 < b + e := by
    by_cases hh : b + e < 0.4
    · exact Or.inl hh
    · exact Or.inr (lt_of_not_ge (fun hle => h (Or.inr (Or.inr ⟨le_of_not_gt hh, hle⟩))))
  rcases hbc with hbc | hbc <;> rcases hbd with hbd | hbd <;>
    rcases hbe with hbe | hbe <;> linarith

/-- Pages 34 and 39. An envelope for the discarded C4 region over Gamma. Only three of the Lemma 17a exclusions are needed. -/
noncomputable def gammaDiscardRegion : Set (Fin 4 → ℝ) :=
 {a | a 1 ≤ a 0 ∧ a 0 ≤ 0.36 ∧ 0.64 ≤ a 0 + a 1 ∧
   0.1 ≤ a 2 ∧ 0.1 ≤ a 3 ∧ 0.1 ≤ 1 - ∑ i, a i ∧
   a 1 + a 2 ∉ Icc (0.4 : ℝ) 0.46 ∧ a 1 + a 3 ∉ Icc (0.4 : ℝ) 0.46 ∧
   a 1 + (1 - ∑ i, a i) ∉ Icc (0.4 : ℝ) 0.46}

/-- Pages 34 and 39. The Gamma discarded envelope is empty by Lemma 17a subproducts. -/
theorem gamma_discard_region_empty : gammaDiscardRegion = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hab,ha,hs,hc,hd,he,hbc,hbd,hbe⟩ := ha
  have ht : a 0 + a 1 + a 2 + a 3 + (1 - ∑ i, a i) = 1 := by
    simp [Fin.sum_univ_succ]; ring
  rcases gamma_subsum hab ha hs hc hd he ht with h | h | h
  · exact hbc h
  · exact hbd h
  · exact hbe h

/-- Pages 39 and 41. Buchstab integral over the Gamma discarded envelope. -/
noncomputable def gammaDiscardIntegral (ω : ℝ → ℝ) : ℝ :=
 ∫ a in gammaDiscardRegion,
   ω ((1 - ∑ i, a i) / a 3) / (a 0 * a 1 * a 2 * a 3 ^ 2)

/-- Pages 39 and 41. Empty-region integral certificate. -/
theorem gamma_discard_integral_zero (ω : ℝ → ℝ) : gammaDiscardIntegral ω = 0 := by
  simp [gammaDiscardIntegral, gamma_discard_region_empty]

/-- Page 41. The Gamma envelope satisfies the printed 0.0003 discard budget. -/
theorem gamma_discard_integral_lt (ω : ℝ → ℝ) : gammaDiscardIntegral ω < 0.0003 := by
  rw [gamma_discard_integral_zero]
  norm_num

/-- Page 41 auxiliary four dimensional rational grid. The dependent finite sums enumerate each box once. -/
def delta4Grid : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
 (Finset.range 41).sigma fun a => (Finset.range 21).sigma fun b =>
 if 40 ≤ a + 2 * b + 3 then
   (Finset.range 81).sigma fun c =>
     if a + b + c ≤ 80 then Finset.range (min c ((80 - a - b - c) / 2) + 1) else ∅
 else ∅

/-- Page 41 explicit rational grid count, checked by kernel reduction. -/
theorem delta4_grid_card : delta4Grid.card = 166879 := by
  simp only [delta4Grid, Finset.card_sigma, apply_ite, Finset.card_range, Finset.card_empty]
  decide +kernel

/-- Page 41 explicit rational upper Darboux sum. -/
noncomputable def delta4GridBound : ℝ :=
 ∑ _ ∈ delta4Grid, (0.001 : ℝ) ^ 4 / 0.00008832

/-- Page 41 numerical certificate for the finite rational box sum. -/
theorem delta4_grid_bound : delta4GridBound < 0.002 := by
 norm_num [delta4GridBound, Finset.sum_const, delta4_grid_card]

/-- Pages 40 and 41. An enclosing region for discarded C4 terms over Delta4 with each sifted factor exponent at least 0.1. No availability exclusions are needed for this bound. -/
noncomputable def delta4Region : Set (Fin 4 → ℝ) :=
 {a | 0.46 ≤ a 0 ∧ a 0 ≤ 0.5 ∧ 0.16 ≤ a 1 ∧ a 1 ≤ 0.18 ∧
  0.1 ≤ a 2 ∧ 0.1 ≤ a 3 ∧ a 3 ≤ a 2 ∧ a 0 + 2 * a 1 ≥ 0.82 ∧
  a 3 ≤ 1 - ∑ i, a i}

/-- Page 41 rational integral over the Delta4 envelope. The Buchstab reduction is a separate implication. -/
noncomputable def delta4Integral : ℝ :=
 ∫ a in delta4Region, (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹

/-- Page 41 auxiliary closed rational box of mesh 0.001. -/
noncomputable def delta4Box (q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) : Set (Fin 4 → ℝ) :=
 let r : Fin 4 → ℝ := ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2.1 : ℝ), (q.2.2.2 : ℝ)]
 let v : Fin 4 → ℝ := ![0.46,0.16,0.1,0.1]
 Icc (fun i => v i + r i * 0.001) (fun i => v i + (r i + 1) * 0.001)

/-- Page 41 auxiliary rational box volume. Reuses Real.volume_Icc_pi. -/
theorem delta4_box_volume (q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :
 volume (delta4Box q) = ENNReal.ofReal ((0.001 : ℝ)^4) := by
 rw [delta4Box, Real.volume_Icc_pi]
 have hh : ∀ i : Fin 4,
  (![0.46,0.16,0.1,0.1] i +
    (![↑q.1, ↑q.2.1, ↑q.2.2.1, ↑q.2.2.2] i + 1) * (0.001 : ℝ)) -
  (![0.46,0.16,0.1,0.1] i +
    ![↑q.1, ↑q.2.1, ↑q.2.2.1, ↑q.2.2.2] i * (0.001 : ℝ)) = 0.001 := by
   intro i; ring
 simp_rw [hh]
 simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
 rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Page 41 exact grid coverage certificate. Natural floors locate the box. -/
theorem delta4_grid_cover {a : Fin 4 → ℝ} (ha : a ∈ delta4Region) :
    ∃ q ∈ delta4Grid, a ∈ delta4Box q := by
  obtain ⟨ha0,ha1,hb0,hb1,hc0,hd0,hdc,hplane,hr⟩ := ha
  have hsum : ∑ i, a i = a 0 + a 1 + a 2 + a 3 := by
    simp [Fin.sum_univ_succ]; ring
  let v : Fin 4 → ℝ := ![0.46,0.16,0.1,0.1]
  let k : Fin 4 → ℕ := fun i => ⌊1000 * (a i - v i)⌋₊
  have hnon : ∀ i, 0 ≤ 1000 * (a i - v i) := by
    intro i; fin_cases i <;> simp [v] <;> linarith
  have hlo : ∀ i, (k i : ℝ) ≤ 1000 * (a i - v i) := fun i => Nat.floor_le (hnon i)
  have hup : ∀ i, 1000 * (a i - v i) < (k i : ℝ) + 1 := fun i => Nat.lt_floor_add_one _
  have hka : k 0 ≤ 40 := by
    have h := hlo 0; dsimp [v] at h; exact_mod_cast (show (k 0 : ℝ) ≤ 40 by linarith)
  have hkb : k 1 ≤ 20 := by
    have h := hlo 1; dsimp [v] at h; exact_mod_cast (show (k 1 : ℝ) ≤ 20 by linarith)
  have hsumk : k 0 + k 1 + k 2 + 2 * k 3 ≤ 80 := by
    have h0 := hlo 0; have h1 := hlo 1; have h2 := hlo 2; have h3 := hlo 3
    dsimp [v] at h0 h1 h2 h3
    exact_mod_cast (show (k 0 : ℝ) + k 1 + k 2 + 2 * k 3 ≤ 80 by linarith)
  have hkc : k 2 ≤ 80 := by omega
  have hkd : k 3 ≤ k 2 := by
    exact Nat.floor_mono (by dsimp [v]; linarith)
  have hplane' : 40 ≤ k 0 + 2 * k 1 + 3 := by
    have h0 := hup 0; have h1 := hup 1
    dsimp [v] at h0 h1
    exact_mod_cast (show (40 : ℝ) ≤ k 0 + 2 * k 1 + 3 by linarith)
  let q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ := ⟨k 0,k 1,k 2,k 3⟩
  refine ⟨q, ?_, ?_⟩
  · simp only [delta4Grid, Finset.mem_sigma, Finset.mem_range, q, hplane', ite_true]
    refine ⟨by omega, by omega, by omega, ?_⟩
    have hh : k 0 + k 1 + k 2 ≤ 80 := by omega
    simp only [hh, ite_true, Finset.mem_range]
    have hdiv : k 3 ≤ (80 - k 0 - k 1 - k 2) / 2 := by omega
    omega
  · have hrk : (![↑(k 0), ↑(k 1), ↑(k 2), ↑(k 3)] : Fin 4 → ℝ) =
        fun i => (k i : ℝ) := by
      ext i; fin_cases i <;> rfl
    constructor
    · change (fun i => v i + ![↑(k 0), ↑(k 1), ↑(k 2), ↑(k 3)] i * (0.001 : ℝ)) ≤ a
      rw [hrk]
      intro i
      have h := hlo i
      linarith
    · change a ≤ (fun i => v i + (![↑(k 0), ↑(k 1), ↑(k 2), ↑(k 3)] i + 1) * (0.001 : ℝ))
      rw [hrk]
      intro i
      have h := hup i
      linarith

/-- Page 41 volume enclosure from the finite box cover. -/
theorem delta4_region_volume :
    volume delta4Region ≤ ENNReal.ofReal ((166879 : ℝ) * 0.001 ^ 4) := by
  calc
    volume delta4Region ≤ volume (⋃ q ∈ delta4Grid, delta4Box q) := by
      apply measure_mono
      intro a ha
      obtain ⟨q,hq,haq⟩ := delta4_grid_cover ha
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq,haq⟩⟩
    _ ≤ ∑ q ∈ delta4Grid, volume (delta4Box q) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [delta4_box_volume, Finset.sum_const, delta4_grid_card, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Page 41 pointwise rational enclosure. The product of the three tail factors is at least 0.0012. -/
theorem delta4_integrand_bound {a : Fin 4 → ℝ} (ha : a ∈ delta4Region) :
    ‖(∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹‖ ≤ (0.00008832 : ℝ)⁻¹ := by
  obtain ⟨ha0,ha1,hb0,hb1,hc0,hd0,hdc,hplane,hr⟩ := ha
  let e := 1 - ∑ i, a i
  have hs : a 0 + a 1 + a 2 + a 3 + e = 1 := by
    dsimp [e]; simp [Fin.sum_univ_succ]; ring
  have he : 0.1 ≤ e := hd0.trans hr
  have h1 := mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr hd0)
  have h2 := mul_nonneg (show 0 ≤ a 2 + a 3 - 0.2 by linarith) (show 0 ≤ e - 0.1 by linarith)
  have h3 := mul_nonneg (show 0 ≤ e by linarith) h1
  have ht : 0.0012 ≤ a 2 * a 3 * e := by nlinarith
  have hab : 0.0736 ≤ a 0 * a 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr hb0)]
  have hp : 0.00008832 ≤ (∏ i, a i) * e := by
    have hh : (0.0736 : ℝ) * 0.0012 ≤ (a 0 * a 1) * (a 2 * a 3 * e) := by gcongr
    have hprod : (∏ i, a i) = a 0 * a 1 * a 2 * a 3 := by
      simp [Fin.prod_univ_succ]; ring
    rw [hprod]
    nlinarith only [hh]
  rw [← mul_inv, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hp))]
  exact inv_anti₀ (by norm_num) hp

/-- Page 41 integral enclosure by the explicit rational grid. -/
theorem delta4_integral_le_grid : delta4Integral ≤ delta4GridBound := by
  have hv := delta4_region_volume
  have hfin : volume delta4Region < ⊤ := lt_of_le_of_lt hv ENNReal.ofReal_lt_top
  have hi := norm_setIntegral_le_of_norm_le_const hfin (fun a ha => delta4_integrand_bound ha)
  have hreal : volume.real delta4Region ≤ (166879 : ℝ) * 0.001 ^ 4 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    rw [ENNReal.toReal_ofReal (show 0 ≤ (166879 : ℝ) * 0.001 ^ 4 by norm_num)] at h
    exact h
  calc
    delta4Integral ≤ ‖delta4Integral‖ := le_abs_self _
    _ ≤ (0.00008832 : ℝ)⁻¹ * volume.real delta4Region := hi
    _ ≤ (0.00008832 : ℝ)⁻¹ * ((166879 : ℝ) * 0.001 ^ 4) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = delta4GridBound := by norm_num [delta4GridBound, Finset.sum_const, delta4_grid_card]

/-- Page 41 certified Delta4 envelope bound. -/
theorem delta4_integral_lt : delta4Integral < 0.002 :=
  delta4_integral_le_grid.trans_lt delta4_grid_bound

/-- Page 41 and the defining Buchstab formula. -/
theorem delta4_buchstab_argument {a : Fin 4 → ℝ} (ha : a ∈ delta4Region) :
    1 ≤ (1 - ∑ i, a i) / a 3 ∧ (1 - ∑ i, a i) / a 3 ≤ 2 := by
  obtain ⟨ha0,ha1,hb0,hb1,hc0,hd0,hdc,hplane,hr⟩ := ha
  have hs : ∑ i, a i = a 0 + a 1 + a 2 + a 3 := by
    simp [Fin.sum_univ_succ]; ring
  constructor
  · exact (le_div_iff₀ (by linarith)).mpr (by linarith)
  · exact (div_le_iff₀ (by linarith)).mpr (by linarith)

/-- Page 41 rationalization of the Buchstab integral. CONDITIONAL ON the defining formula omega u equal to 1 divided by u between 1 and 2. -/
theorem delta4_buchstab_integral_eq (ω : ℝ → ℝ)
    (hω : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → ω u = 1 / u) :
    (∫ a in delta4Region,
      ω ((1 - ∑ i, a i) / a 3) / (a 0 * a 1 * a 2 * a 3 ^ 2)) = delta4Integral := by
  have hm : MeasurableSet delta4Region := by
    unfold delta4Region
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals apply measurableSet_le <;> fun_prop
  apply setIntegral_congr_fun hm
  intro a ha
  dsimp only
  rw [hω _ (delta4_buchstab_argument ha).1 (delta4_buchstab_argument ha).2]
  have hp : (∏ i, a i) = a 0 * a 1 * a 2 * a 3 := by
    simp [Fin.prod_univ_succ]; ring
  change _ = (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹
  rw [hp]
  have hd : a 3 ≠ 0 := by linarith [ha.2.2.2.2.2.1]
  have he : 1 - ∑ i, a i ≠ 0 := by linarith [ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.2.2]
  field_simp

/-- Page 41 discarded integral budget. CONDITIONAL ON the defining Buchstab formula on the interval from 1 to 2. -/
theorem delta4_buchstab_integral_lt (ω : ℝ → ℝ)
    (hω : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → ω u = 1 / u) :
    (∫ a in delta4Region,
      ω ((1 - ∑ i, a i) / a 3) / (a 0 * a 1 * a 2 * a 3 ^ 2)) < 0.002 := by
  rw [delta4_buchstab_integral_eq ω hω]
  exact delta4_integral_lt

/-- Page 27, the smallest-prime partition in 4.14. -/
theorem sifted_quotient_at_prime {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    siftedWeight (n / p) p = if p = n.minFac then 1 else 0 := by
  by_cases heq : p = n.minFac
  · rw [ite_eq_left heq]
    apply (sifted_weight_support _ _).mpr
    intro q hq hqp hqn
    have hqn' : q ∣ n := hqn.trans (Nat.div_dvd_of_dvd hpn)
    have hm := Nat.minFac_le_of_dvd hq.two_le hqn'
    omega
  · rw [ite_eq_right heq]
    have hn1 : n ≠ 1 := by rintro rfl; exact hp.not_dvd_one hpn
    have hq : n.minFac.Prime := Nat.minFac_prime hn1
    have hq_lt : n.minFac < p := lt_of_le_of_ne (Nat.minFac_le_of_dvd hp.two_le hpn) (Ne.symm heq)
    have hnot : ¬n.minFac ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · exact hq.ne_one h
      · exact heq h.symm
    have hqn : n.minFac ∣ n / p := by
      have hm : n.minFac ∣ p * (n / p) := by
        rw [Nat.mul_div_cancel' hpn]
        exact Nat.minFac_dvd n
      exact (hq.dvd_mul.mp hm).resolve_left hnot
    have hfail : ¬ (n / p = 1 ∨ p ≤ (n / p).minFac) := by
      intro hh
      rcases hh with hh | hh
      · rw [hh] at hqn
        exact hq.not_dvd_one hqn
      · have hm := Nat.minFac_le_of_dvd hq.two_le hqn
        omega
    simp [siftedWeight, hfail]

/-- Page 27, identity 4.14 at natural cutoffs. -/
theorem buchstab_finite (n w z : ℕ) (hwz : w ≤ z) :
    siftedWeight n z = siftedWeight n w -
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n), siftedWeight (n / p) p := by
  have hsum : (∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n), siftedWeight (n / p) p) =
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n),
        if p = n.minFac then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    exact sifted_quotient_at_prime (Nat.mem_primesBelow.mp hpf.1).2 hpf.2.2
  rw [hsum, Finset.sum_ite_eq']
  by_cases hn : n = 1
  · subst n
    norm_num [siftedWeight, Nat.mem_primesBelow]
  · have hp := Nat.minFac_prime hn
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    simp only [hp, Nat.minFac_dvd, and_true]
    simp only [siftedWeight, hn, false_or]
    split_ifs <;> norm_num at * <;> omega

/-- Page 27, exact real-cutoff version of 4.14. -/
theorem buchstab_real_cutoffs (n : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    siftedWeight n ⌈z⌉₊ = siftedWeight n ⌈w⌉₊ -
      ∑ p ∈ (⌈z⌉₊.primesBelow).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ p ∣ n),
        siftedWeight (n / p) p := by
  simpa only [Nat.ceil_le] using buchstab_finite n ⌈w⌉₊ ⌈z⌉₊ (Nat.ceil_mono hwz)

/-- Page 27, monotonicity underlying the Buchstab step. -/
theorem sifted_weight_antitone (n w z : ℕ) (hwz : w ≤ z) :
    siftedWeight n z ≤ siftedWeight n w := by
  unfold siftedWeight
  split_ifs <;> norm_num at * <;> omega

/-- Page 27, finite weighted form of 4.14. -/
theorem buchstab_weighted_sum (S : Finset ℕ) (c : ℕ → ℝ) (w z : ℕ) (hwz : w ≤ z) :
    (∑ n ∈ S, c n * siftedWeight n z) = (∑ n ∈ S, c n * siftedWeight n w) -
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p),
        ∑ n ∈ S.filter (fun n => p ∣ n), c n * siftedWeight (n / p) p := by
  have hpoint (n : ℕ) : siftedWeight n z = siftedWeight n w -
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p),
        if p ∣ n then siftedWeight (n / p) p else 0 := by
    rw [buchstab_finite n w z hwz]
    congr 1
    simp only [Finset.sum_filter, ite_and]
  simp_rw [hpoint, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.sum_filter, mul_ite, mul_zero]

/-- Pages 25 to 27, elementary support consequence of w equal to exp of log x to the power 9/10. Reuses Mathlib isLittleO_log_rpow_atTop. -/
theorem sieve_threshold_dominates_logs (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ A ≤ Real.exp (Real.log x ^ (9 / 10 : ℝ)) := by
  have hsmall : ∀ᶠ t : ℝ in atTop, A * Real.log t ≤ t ^ (9 / 10 : ℝ) := by
    filter_upwards [((isLittleO_log_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).const_mul_left A).bound
      (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop 0] with t ht ht0
    have hh : |A * Real.log t| ≤ t ^ (9 / 10 : ℝ) := by
      simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)] using ht
    exact (le_abs_self _).trans hh
  filter_upwards [Real.tendsto_log_atTop.eventually hsmall,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hx hx0
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Page 3 condition ii and pages 25 to 27 sieve threshold. -/
theorem sifted_weight_log_rough_support (A : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 →
        siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ = 0 := by
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp (sieve_threshold_dominates_logs A)
  refine ⟨C, fun x hx k hk => ?_⟩
  have hm := sifted_weight_antitone k ⌈Real.log x ^ A⌉₊
    ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ (Nat.ceil_mono (hC x hx))
  rw [sifted_weight_primorial k (Real.log x ^ A), ite_eq_right hk] at hm
  apply le_antisymm hm
  unfold siftedWeight
  split_ifs <;> norm_num

/-- Page 3 condition ii and pages 25 to 27. This proves the rough-support clause for arbitrary coefficients multiplied by the sifted indicator. -/
theorem sifted_family_rough_support (c : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 →
        c x k * siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ = 0 := by
  intro A _
  obtain ⟨C,hC⟩ := sifted_weight_log_rough_support A
  exact ⟨C, fun x hx k hk => by rw [hC x hx k hk, mul_zero]⟩

/-- Page 41, density budget using the certified Gamma and Delta4 envelopes. CONDITIONAL ON the remaining Delta2, Delta3 and six dimensional losses and the density relation. -/
theorem lower_density_of_remaining_losses (ω : ℝ → ℝ) {d2 d3 s u : ℝ}
    (h2 : d2 < 0.0003) (h3 : d3 < 0.002) (hs : s < 0.0001)
    (hu : 1 - (d2 + d3 + delta4Integral + gammaDiscardIntegral ω + s) ≤ u) :
    0.9953 < u :=
  SieveMarginsC165.lower_discard_budget h2 h3 delta4_integral_lt
    (gamma_discard_integral_lt ω) hs hu

/-- Page 42, sufficient upper density budget. CONDITIONAL ON the explicit seven dimensional loss and the density relation. The bound 0.000028 is a sufficient auxiliary budget, not a printed paper assertion. -/
theorem upper_density_of_remaining_loss (n : ℕ) (hn : n ≤ 12) {s u : ℝ}
    (hs : s < 0.000028) (hu : u ≤ 1 + (n : ℝ) * upperFiveIntegral + s) :
    u < 1.0001 := by
  have hmul := mul_le_mul_of_nonneg_left upper_five_integral_lt.le (Nat.cast_nonneg (α := ℝ) n)
  have hn' : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  linarith

/-- Pages 41 and 42, concrete consistency certificates for the numerical integration domains. -/
theorem numeric_regions_nonempty : upperFiveRegion.Nonempty ∧ delta4Region.Nonempty := by
  constructor
  · refine ⟨fun _ => (1 / 6 : ℝ), ?_⟩
    norm_num [upperFiveRegion, Fin.sum_univ_succ]
  · refine ⟨![(0.48 : ℝ),0.17,0.11,0.1], ?_⟩
    norm_num [delta4Region, Fin.sum_univ_succ]

/-- LEAF. Section 4, pages 24 to 41. Construct the lower sifted coefficients,
prove the character distribution and divisor bound, and link the discarded
region integrals to the stated density. The remaining analytic inputs include
Lemma 11, Lemma 12 with Hildebrand and Siegel Walfisz, and the region classification
of Lemmas 13 to 27. The Delta2, Delta3 and six dimensional certificates remain OPEN.
The Gamma and Delta4 envelope certificates above do not prove that classification.
The rough support clause is omitted here because it is proved separately. OPEN. -/
theorem section4_lower_sifted_data (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u0 : ℝ) (c0 : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ t : ℝ, t ≤ x →
            ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
              ((section4SiftedFamily c0 x k : ℂ) * χ (k : ZMod q) -
                Thm2.delta χ * u0 / Real.log x)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ primeWeight k := by
  sorry

/-- LEAF. Section 4, pages 41 and 42. Construct the upper sifted coefficients,
prove the character distribution and divisor bound, and link the five and seven
dimensional losses with their actual multiplicities to the upper density.
Lemma 28 supplies the decomposition ranges. The five dimensional integral has
a certified conservative envelope above. The seven dimensional certificate and
the analytic distribution estimates remain OPEN.
The rough support clause is omitted here because it is proved separately. OPEN. -/
theorem section4_upper_sifted_data (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ t : ℝ, t ≤ x →
            ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
              ((section4SiftedFamily c1 x k : ℂ) * χ (k : ZMod q) -
                Thm2.delta χ * u1 / Real.log x)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  sorry

/-- Page 27, nonempty consistency certificate for 4.14. -/
theorem buchstab_nonempty_instance :
    (((5 : ℕ).primesBelow).filter (fun p => 2 ≤ p ∧ p ∣ 30)).Nonempty ∧
    siftedWeight 30 2 = 1 ∧ siftedWeight 30 5 = 0 ∧
    (∑ p ∈ ((5 : ℕ).primesBelow).filter (fun p => 2 ≤ p ∧ p ∣ 30),
      siftedWeight (30 / p) p) = 1 := by
  have h2 : siftedWeight 30 2 = 1 := by norm_num [siftedWeight, Nat.minFac_eq]
  have h5 : siftedWeight 30 5 = 0 := by norm_num [siftedWeight, Nat.minFac_eq]
  have h := buchstab_finite 30 2 5 (by norm_num)
  rw [h2,h5] at h
  refine ⟨?_,h2,h5,by linarith⟩
  exact ⟨2, by decide⟩

/-- Pages 25 to 27, nonzero consistency certificate for the rough-support family. -/
theorem sifted_family_nonzero_instance (x : ℝ) :
    section4SiftedFamily (fun _ _ => 1) x 1 = 1 := by
  simp [section4SiftedFamily, siftedWeight]

/-- Page 42, integrability of the actual displayed rational integrand. Reuses the proved finite-volume enclosure, pointwise bound and Mathlib integrable domination. -/
theorem upper_five_integrable :
    IntegrableOn (fun a : Fin 5 → ℝ => (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹) upperFiveRegion := by
  have hf : volume upperFiveRegion ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt upper_five_region_volume ENNReal.ofReal_lt_top)
  have hm : MeasurableSet upperFiveRegion := by
    unfold upperFiveRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals first | apply measurableSet_le | apply measurableSet_lt
    all_goals fun_prop
  have hc : IntegrableOn (fun _ : Fin 5 → ℝ => (0.1 * 0.18 ^ 5 : ℝ)⁻¹) upperFiveRegion :=
    integrableOn_const hf
  apply hc.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem hm] with a ha
  exact upper_five_integrand_bound ha

/-- Page 41, integrability of the rational Delta4 envelope. Reuses the proved finite-volume enclosure and pointwise bound. -/
theorem delta4_integrable :
    IntegrableOn (fun a : Fin 4 → ℝ => (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹) delta4Region := by
  have hf : volume delta4Region ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt delta4_region_volume ENNReal.ofReal_lt_top)
  have hm : MeasurableSet delta4Region := by
    unfold delta4Region
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals apply measurableSet_le <;> fun_prop
  have hc : IntegrableOn (fun _ : Fin 4 → ℝ => (0.00008832 : ℝ)⁻¹) delta4Region :=
    integrableOn_const hf
  apply hc.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem hm] with a ha
  exact delta4_integrand_bound ha

/-- Pages 25 and 32, finite product rule for the sifted indicator. Reuses Mathlib Nat.coprime_prod_left_iff and Finset.prod_boole. -/
theorem sifted_weight_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (z : ℕ) :
    siftedWeight (∏ i ∈ s, n i) z = ∏ i ∈ s, siftedWeight (n i) z := by
  classical
  have hi (m : ℕ) : siftedWeight m z =
      if m.Coprime (Thm2.primorialBelow (z : ℝ)) then (1 : ℝ) else 0 := by
    simpa only [Nat.ceil_natCast, Nat.coprime_iff_gcd_eq_one] using sifted_weight_primorial m (z : ℝ)
  simp_rw [hi, Nat.coprime_prod_left_iff, Finset.prod_boole]

/-- Pages 25 and 32, rough support of one product term in 4.25. -/
theorem sifted_product_support {ι : Type*} (s : Finset ι) (n z : ι → ℕ) (w : ℕ)
    (hw : ∀ i ∈ s, w ≤ z i) :
    (∏ i ∈ s, siftedWeight (n i) (z i)) * siftedWeight (∏ i ∈ s, n i) w =
      ∏ i ∈ s, siftedWeight (n i) (z i) := by
  rw [sifted_weight_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hh := hw i hi
  unfold siftedWeight
  split_ifs <;> norm_num at * <;> omega

/-- Page 32, rough support of a finite linear combination of product terms in 4.25. Coefficients include the alternating signs. -/
theorem sifted_sum_support {ι κ : Type*} (s : Finset ι) (t : ι → Finset κ)
    (n z : ι → κ → ℕ) (c : ι → ℝ) (k w : ℕ)
    (hk : ∀ j ∈ s, ∏ i ∈ t j, n j i = k)
    (hw : ∀ j ∈ s, ∀ i ∈ t j, w ≤ z j i) :
    (∑ j ∈ s, c j * ∏ i ∈ t j, siftedWeight (n j i) (z j i)) * siftedWeight k w =
      ∑ j ∈ s, c j * ∏ i ∈ t j, siftedWeight (n j i) (z j i) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ← hk j hj, sifted_product_support _ _ _ _ (hw j hj)]

/-- Pages 41 and 42, auxiliary rational-grid counting identity. Reuses the Mathlib tuple antidiagonal and Nat.sum_range_add_choose. -/
theorem antidiagonal_tuple_card (d n : ℕ) :
    (Finset.Nat.antidiagonalTuple (d + 1) n).card = (n + d).choose d := by
  have aux : ∀ d n : ℕ, (List.Nat.antidiagonalTuple (d + 1) n).length = (n + d).choose d := by
    intro d
    induction d with
    | zero => intro n; simp
    | succ d ih =>
      intro n
      rw [List.Nat.antidiagonalTuple, List.length_flatMap]
      simp_rw [List.length_map, ih]
      rw [List.Nat.antidiagonal, List.map_map]
      change (∑ i ∈ Finset.range (n + 1), (n - i + d).choose d) = (n + (d + 1)).choose (d + 1)
      calc
        _ = ∑ i ∈ Finset.range (n + 1), (i + d).choose d := by
          simpa using Finset.sum_range_reflect (fun i => (i + d).choose d) (n + 1)
        _ = _ := by simpa [Nat.add_assoc] using Nat.sum_range_add_choose n d
  exact aux d n

/-- Pages 41 and 42, auxiliary lower product bound for nonnegative deficits above a fixed base. -/
theorem one_add_sum_le_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs := Finset.sum_nonneg hfs
    have hh := mul_le_mul_of_nonneg_left (ih hfs) (show 0 ≤ 1 + f a by linarith)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hfa hs]

/-- Page 42 seven dimensional envelope, auxiliary denominator estimate. -/
theorem ordered_seven_product_bound (a : Fin 8 → ℝ)
    (ha : ∀ i, 0.1 ≤ a i) (hs : ∑ i, a i = 1) :
    0.3 * 0.1 ^ 7 ≤ ∏ i, a i := by
  have h := one_add_sum_le_prod_nonneg Finset.univ (fun i => a i / 0.1 - 1)
    (fun i _ => sub_nonneg.mpr ((le_div_iff₀ (by norm_num)).mpr (by simpa using ha i)))
  have hsum : (∑ i : Fin 8, (a i / 0.1 - 1)) = 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    norm_num
  have he : (fun i : Fin 8 => 1 + (a i / 0.1 - 1)) = fun i => a i / 0.1 := by
    ext i; ring
  rw [hsum, he, Finset.prod_div_distrib] at h
  norm_num at h
  linarith

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
def orderedSevenGrid : Finset (Fin 8 → ℕ) := Finset.Nat.antidiagonalTuple 8 12

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_grid_card : orderedSevenGrid.card = 50388 := by
  norm_num [orderedSevenGrid, antidiagonal_tuple_card, Nat.choose]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
noncomputable def orderedSevenGridBound : ℝ :=
 ∑ _ ∈ orderedSevenGrid, (0.2 / 12 : ℝ) ^ 7 / (40320 * (0.3 * 0.1 ^ 7))

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_rational_grid_bound : orderedSevenGridBound < 0.000015 := by
 norm_num [orderedSevenGridBound, Finset.sum_const, ordered_seven_grid_card]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_buchstab_grid_bound :
 (3 * (567144 / 1000000 : ℝ)) * orderedSevenGridBound < 0.000026 := by
 norm_num [orderedSevenGridBound, Finset.sum_const, ordered_seven_grid_card]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
noncomputable def orderedSevenBox (q : Fin 8 → ℕ) : Set (Fin 7 → ℝ) :=
 Icc (fun i => (q i.castSucc : ℝ) * (0.2 / 12))
     (fun i => ((q i.castSucc : ℝ) + 1) * (0.2 / 12))

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_grid_cover (g : Fin 7 → ℝ)
    (h0 : ∀ i, 0 ≤ g i) (hs : ∑ i, g i ≤ 0.2) :
    ∃ q ∈ orderedSevenGrid, g ∈ orderedSevenBox q := by
  let k : Fin 7 → ℕ := fun i => ⌊g i / (0.2 / 12)⌋₊
  have hk : (∑ i, k i) ≤ 12 := by
    have hr : (∑ i, (k i : ℝ)) ≤ 12 := by
      calc
        (∑ i, (k i : ℝ)) ≤ ∑ i, g i / (0.2 / 12) :=
          Finset.sum_le_sum (fun i _ => Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
        _ ≤ 12 := by rw [← Finset.sum_div]; norm_num; linarith
    exact_mod_cast hr
  let q : Fin 8 → ℕ := Fin.snoc (α := fun _ => ℕ) k (12 - ∑ i, k i)
  refine ⟨q, ?_, ?_⟩
  · rw [orderedSevenGrid, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc]
    simpa only [q, Fin.snoc_castSucc, Fin.snoc_last] using Nat.add_sub_of_le hk
  · constructor
    · intro i
      dsimp only [orderedSevenBox] at *
      simp only [q, Fin.snoc_castSucc]
      change (k i : ℝ) * (0.2 / 12) ≤ g i
      exact (le_div_iff₀ (by norm_num)).mp (Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
    · intro i
      dsimp only [orderedSevenBox] at *
      simp only [q, Fin.snoc_castSucc]
      change g i ≤ ((k i : ℝ) + 1) * (0.2 / 12)
      exact ((div_lt_iff₀ (by norm_num)).mp (Nat.lt_floor_add_one (g i / (0.2 / 12)))).le

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_box_volume (q : Fin 8 → ℕ) :
    volume (orderedSevenBox q) = ENNReal.ofReal ((0.2 / 12 : ℝ) ^ 7) := by
  rw [orderedSevenBox, Real.volume_Icc_pi]
  have hh : ∀ i : Fin 7,
    ((q i.castSucc : ℝ) + 1) * (0.2 / 12) - (q i.castSucc : ℝ) * (0.2 / 12) = 0.2 / 12 := by
    intro i; ring
  simp_rw [hh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_simplex_volume :
    volume {g : Fin 7 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.2} ≤
      ENNReal.ofReal ((50388 : ℝ) * (0.2 / 12) ^ 7) := by
  calc
    _ ≤ volume (⋃ q ∈ orderedSevenGrid, orderedSevenBox q) := by
      apply measure_mono
      intro g hg
      obtain ⟨q,hq,hgq⟩ := ordered_seven_grid_cover g hg.1 hg.2
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq,hgq⟩⟩
    _ ≤ ∑ q ∈ orderedSevenGrid, volume (orderedSevenBox q) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [ordered_seven_box_volume, Finset.sum_const, ordered_seven_grid_card, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
noncomputable def orderedSevenRegion : Set (Fin 7 → ℝ) :=
 {a | 0.1 ≤ a 0 ∧ a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧
    a 3 ≤ a 4 ∧ a 4 ≤ a 5 ∧ a 5 ≤ a 6 ∧ a 6 ≤ 1 - ∑ i, a i}

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
noncomputable def orderedSevenGaps (a : Fin 7 → ℝ) : Fin 7 → ℝ :=
 ![8 * (a 0 - 0.1), 7 * (a 1 - a 0), 6 * (a 2 - a 1),
   5 * (a 3 - a 2), 4 * (a 4 - a 3), 3 * (a 5 - a 4), 2 * (a 6 - a 5)]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
noncomputable def orderedSevenGapMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
 !![8,0,0,0,0,0,0; -7,7,0,0,0,0,0; 0,-6,6,0,0,0,0;
    0,0,-5,5,0,0,0; 0,0,0,-4,4,0,0; 0,0,0,0,-3,3,0; 0,0,0,0,0,-2,2]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_gap_det : orderedSevenGapMatrix.det = 40320 := by
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    have hlt : i < j := hij
    fin_cases i <;> fin_cases j <;> norm_num [orderedSevenGapMatrix] at * )]
  norm_num [orderedSevenGapMatrix, Fin.prod_univ_succ]

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_gap_affine (a : Fin 7 → ℝ) :
    orderedSevenGaps a = orderedSevenGapMatrix.mulVec a + ![-0.8,0,0,0,0,0,0] := by
  ext i
  fin_cases i <;> simp [orderedSevenGaps,orderedSevenGapMatrix,dotProduct,Fin.sum_univ_succ] <;> ring

/-- Page 42, auxiliary enclosure for one ordered seven dimensional region. No discarded-region multiplicity is asserted. -/
theorem ordered_seven_geometry {a : Fin 7 → ℝ} (ha : a ∈ orderedSevenRegion) :
    (∀ i, 0 ≤ orderedSevenGaps a i) ∧ (∑ i, orderedSevenGaps a i) ≤ 0.2 ∧
    (∀ i, 0.1 ≤ a i) ∧ 0.1 ≤ 1 - ∑ i, a i ∧
    1 - ∑ i, a i ≤ 0.3 ∧
    1 ≤ (1 - ∑ i, a i) / a 6 ∧ (1 - ∑ i, a i) / a 6 ≤ 3 := by
  obtain ⟨h0,h01,h12,h23,h34,h45,h56,h6⟩ := ha
  have hs : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 := by
    simp [Fin.sum_univ_succ]; ring
  have hr : 0.1 ≤ 1 - ∑ i, a i := by linarith
  have h6pos : 0 < a 6 := by linarith
  refine ⟨?_, ?_, ?_, hr, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [orderedSevenGaps] <;> linarith
  · simp [orderedSevenGaps,Fin.sum_univ_succ]
    linarith
  · intro i; fin_cases i <;> dsimp <;> linarith
  · linarith
  · exact (le_div_iff₀ h6pos).mpr (by linarith)
  · exact (div_le_iff₀ h6pos).mpr (by linarith)

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_gap_map :
    Measure.map orderedSevenGaps volume = ENNReal.ofReal (1 / 40320 : ℝ) • volume := by
  have hm : Measurable (Matrix.toLin' orderedSevenGapMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  have he : orderedSevenGaps = (fun x : Fin 7 → ℝ => x + ![-0.8,0,0,0,0,0,0]) ∘
      Matrix.toLin' orderedSevenGapMatrix := by
    ext a i
    exact congrFun (ordered_seven_gap_affine a) i
  rw [he, ← Measure.map_map (by fun_prop) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [ordered_seven_gap_det]; norm_num),
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]
  norm_num [ordered_seven_gap_det]

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_region_volume :
    volume orderedSevenRegion ≤ ENNReal.ofReal ((50388 : ℝ) * (0.2 / 12) ^ 7 / 40320) := by
  let S : Set (Fin 7 → ℝ) := {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.2}
  have hS : MeasurableSet S := by
    simp only [S, ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
      (measurable_pi_apply i)).inter (measurableSet_le (show Measurable (fun g : Fin 7 → ℝ => ∑ i, g i) by fun_prop) measurable_const)
  have hm : Measurable orderedSevenGaps := by
    unfold orderedSevenGaps
    fun_prop
  calc
    volume orderedSevenRegion ≤ volume (orderedSevenGaps ⁻¹' S) := by
      apply measure_mono
      intro a ha
      exact ⟨(ordered_seven_geometry ha).1, (ordered_seven_geometry ha).2.1⟩
    _ = ENNReal.ofReal (1 / 40320 : ℝ) * volume S := by
      rw [← Measure.map_apply hm hS, ordered_seven_gap_map, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / 40320 : ℝ) *
        ENNReal.ofReal ((50388 : ℝ) * (0.2 / 12) ^ 7) :=
      by gcongr; exact ordered_seven_simplex_volume
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
noncomputable def orderedSevenRationalIntegral : ℝ :=
 ∫ a in orderedSevenRegion, (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_integrand_bound {a : Fin 7 → ℝ} (ha : a ∈ orderedSevenRegion) :
    ‖(∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹‖ ≤ (0.3 * 0.1 ^ 7 : ℝ)⁻¹ := by
  have hg := ordered_seven_geometry ha
  let b : Fin 8 → ℝ := Fin.snoc (α := fun _ => ℝ) a (1 - ∑ i, a i)
  have hb : ∀ i, 0.1 ≤ b i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using hg.2.2.2.1
    · simpa only [b, Fin.snoc_castSucc] using hg.2.2.1 j
  have hsum : ∑ i, b i = 1 := by
    rw [Fin.sum_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hp := ordered_seven_product_bound b hb hsum
  have he : (∏ i, b i) = (∏ i, a i) * (1 - ∑ i, a i) := by
    rw [Fin.prod_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
  rw [he] at hp
  rw [← mul_inv, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hp))]
  exact inv_anti₀ (by norm_num) hp

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_rational_integral_le_grid :
    orderedSevenRationalIntegral ≤ orderedSevenGridBound := by
  have hv := ordered_seven_region_volume
  have hfin : volume orderedSevenRegion < ⊤ := lt_of_le_of_lt hv (by simp)
  have hi := norm_setIntegral_le_of_norm_le_const hfin (fun a ha => ordered_seven_integrand_bound ha)
  have hreal : volume.real orderedSevenRegion ≤ (50388 : ℝ) * (0.2 / 12) ^ 7 / 40320 := by
    have h := ENNReal.toReal_mono (by simp) hv
    rw [ENNReal.toReal_ofReal (show 0 ≤ (50388 : ℝ) * (0.2 / 12) ^ 7 / 40320 by norm_num)] at h
    exact h
  calc
    orderedSevenRationalIntegral ≤ ‖orderedSevenRationalIntegral‖ := le_abs_self _
    _ ≤ (0.3 * 0.1 ^ 7 : ℝ)⁻¹ * volume.real orderedSevenRegion := hi
    _ ≤ (0.3 * 0.1 ^ 7 : ℝ)⁻¹ * ((50388 : ℝ) * (0.2 / 12) ^ 7 / 40320) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = orderedSevenGridBound := by
      norm_num [orderedSevenGridBound, Finset.sum_const, ordered_seven_grid_card]

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_rational_integrable :
    IntegrableOn (fun a : Fin 7 → ℝ => (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹) orderedSevenRegion := by
  have hf : volume orderedSevenRegion ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt ordered_seven_region_volume ENNReal.ofReal_lt_top)
  have hm : MeasurableSet orderedSevenRegion := by
    unfold orderedSevenRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals apply measurableSet_le <;> fun_prop
  have hc : IntegrableOn (fun _ : Fin 7 → ℝ => (0.3 * 0.1 ^ 7 : ℝ)⁻¹) orderedSevenRegion :=
    integrableOn_const hf
  apply hc.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem hm] with a ha
  exact ordered_seven_integrand_bound ha

/-- CONDITIONAL ON the explicit Buchstab defining equations. Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem buchstab_ratio_norm {ω : ℝ → ℝ} (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc 1 3) :
    ‖u * ω u‖ ≤ 3 * (567144 / 1000000 : ℝ) := by
  by_cases h2 : u ≤ 2
  · rw [hω.2.1 u hu.1 h2]
    have hu0 : u ≠ 0 := by linarith [hu.1]
    rw [mul_one_div_cancel hu0]
    norm_num
  · have h2' : 2 ≤ u := le_of_lt (lt_of_not_ge h2)
    have hb := LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω h2'
    have hn : 0 ≤ ω u := by
      rw [LeanLab.ChenDoubleSieve.Wu04Buchstab.formula_two_three hω ⟨h2', hu.2⟩]
      exact div_nonneg (by linarith [Real.log_nonneg (show 1 ≤ u - 1 by linarith)]) (by linarith [hu.1])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hu.1]) hn)]
    calc
      u * ω u ≤ u * (567144 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left hb (by linarith [hu.1])
      _ ≤ _ := mul_le_mul_of_nonneg_right hu.2 (by norm_num)

/-- Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
noncomputable def orderedSevenBuchstabIntegral (ω : ℝ → ℝ) : ℝ :=
 ∫ a in orderedSevenRegion, ω ((1 - ∑ i, a i) / a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹

/-- CONDITIONAL ON the explicit Buchstab defining equations. Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_buchstab_integrand_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) {a : Fin 7 → ℝ} (ha : a ∈ orderedSevenRegion) :
    ‖ω ((1 - ∑ i, a i) / a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹‖ ≤
      (3 * (567144 / 1000000 : ℝ)) * (0.3 * 0.1 ^ 7 : ℝ)⁻¹ := by
  have hg := ordered_seven_geometry ha
  have ha6 : a 6 ≠ 0 := by linarith [hg.2.2.1 6]
  have he : 1 - ∑ i, a i ≠ 0 := by linarith [hg.2.2.2.1]
  have hid : ω ((1 - ∑ i, a i) / a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹ =
      (((1 - ∑ i, a i) / a 6) * ω ((1 - ∑ i, a i) / a 6)) *
        ((∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹) := by
    field_simp
  rw [hid, norm_mul]
  exact mul_le_mul (buchstab_ratio_norm hω ⟨hg.2.2.2.2.2.1,hg.2.2.2.2.2.2⟩)
    (ordered_seven_integrand_bound ha) (norm_nonneg _) (by norm_num)

/-- CONDITIONAL ON the explicit Buchstab defining equations. Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_buchstab_integral_le_grid {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) :
    orderedSevenBuchstabIntegral ω ≤ (3 * (567144 / 1000000 : ℝ)) * orderedSevenGridBound := by
  have hv := ordered_seven_region_volume
  have hfin : volume orderedSevenRegion < ⊤ := lt_of_le_of_lt hv (by simp)
  have hi := norm_setIntegral_le_of_norm_le_const hfin
    (fun a ha => ordered_seven_buchstab_integrand_bound hω ha)
  have hreal : volume.real orderedSevenRegion ≤ (50388 : ℝ) * (0.2 / 12) ^ 7 / 40320 := by
    have h := ENNReal.toReal_mono (by simp) hv
    rw [ENNReal.toReal_ofReal (show 0 ≤ (50388 : ℝ) * (0.2 / 12) ^ 7 / 40320 by norm_num)] at h
    exact h
  calc
    orderedSevenBuchstabIntegral ω ≤ ‖orderedSevenBuchstabIntegral ω‖ := le_abs_self _
    _ ≤ ((3 * (567144 / 1000000 : ℝ)) * (0.3 * 0.1 ^ 7 : ℝ)⁻¹) * volume.real orderedSevenRegion := hi
    _ ≤ ((3 * (567144 / 1000000 : ℝ)) * (0.3 * 0.1 ^ 7 : ℝ)⁻¹) *
      ((50388 : ℝ) * (0.2 / 12) ^ 7 / 40320) := mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = _ := by norm_num [orderedSevenGridBound, Finset.sum_const, ordered_seven_grid_card]

/-- CONDITIONAL ON the explicit Buchstab defining equations. Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_buchstab_integral_lt {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) : orderedSevenBuchstabIntegral ω < 0.000026 :=
  (ordered_seven_buchstab_integral_le_grid hω).trans_lt ordered_seven_buchstab_grid_bound

/-- CONDITIONAL ON the explicit Buchstab defining equations. Page 42, one ordered envelope only. No total discarded-region loss is asserted. -/
theorem ordered_seven_buchstab_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) :
    IntegrableOn (fun a : Fin 7 → ℝ =>
      ω ((1 - ∑ i, a i) / a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹) orderedSevenRegion := by
  have h6 (a : Fin 7 → ℝ) (ha : a ∈ orderedSevenRegion) : a 6 ≠ 0 := by
    linarith [(ordered_seven_geometry ha).2.2.1 6]
  have hp (a : Fin 7 → ℝ) (ha : a ∈ orderedSevenRegion) : (∏ i, a i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    linarith [(ordered_seven_geometry ha).2.2.1 i]
  have harg : ContinuousOn (fun a : Fin 7 → ℝ => (1 - ∑ i, a i) / a 6) orderedSevenRegion :=
    (show Continuous (fun a : Fin 7 → ℝ => 1 - ∑ i, a i) by fun_prop).continuousOn.div
      (continuous_apply 6).continuousOn h6
  have hw : ContinuousOn (fun a : Fin 7 → ℝ => ω ((1 - ∑ i, a i) / a 6)) orderedSevenRegion :=
    hω.1.comp harg (fun a ha => (ordered_seven_geometry ha).2.2.2.2.2.1)
  have hcont : ContinuousOn (fun a : Fin 7 → ℝ =>
      ω ((1 - ∑ i, a i) / a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹) orderedSevenRegion :=
    (hw.mul ((show Continuous (fun a : Fin 7 → ℝ => ∏ i, a i) by fun_prop).continuousOn.inv₀ hp)).mul
      ((continuous_apply 6).continuousOn.inv₀ h6)
  have hm : MeasurableSet orderedSevenRegion := by
    unfold orderedSevenRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals apply measurableSet_le <;> fun_prop
  have hf : volume orderedSevenRegion ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt ordered_seven_region_volume ENNReal.ofReal_lt_top)
  have hc : IntegrableOn (fun _ : Fin 7 → ℝ =>
      (3 * (567144 / 1000000 : ℝ)) * (0.3 * 0.1 ^ 7 : ℝ)⁻¹) orderedSevenRegion :=
    integrableOn_const hf
  apply hc.mono' (hcont.aestronglyMeasurable hm)
  filter_upwards [ae_restrict_mem hm] with a ha
  exact ordered_seven_buchstab_integrand_bound hω ha


/-- CONDITIONAL ON a Buchstab solution and the explicit density relation with at most twelve five dimensional copies and one ordered seven dimensional envelope. Page 42. This is a sufficient auxiliary budget, not a proved decomposition count. -/
theorem upper_density_of_ordered_losses {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (n : ℕ) (hn : n ≤ 12) (u : ℝ)
    (hu : u ≤ 1 + (n : ℝ) * upperFiveIntegral + orderedSevenBuchstabIntegral ω) :
    u < 1.0001 := by
  apply upper_density_of_remaining_loss n hn (s := orderedSevenBuchstabIntegral ω) (u := u)
  · exact (ordered_seven_buchstab_integral_lt hω).trans (by norm_num)
  · exact hu

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_geometry_converse (a : Fin 5 → ℝ)
    (h0 : ∀ i, 0 ≤ upperFiveGaps a i) (hs : ∑ i, upperFiveGaps a i ≤ 0.08)
    (hp : 0 < upperFiveGaps a 0) : a ∈ upperFiveRegion := by
  have h1 := h0 1
  have h2 := h0 2
  have h3 := h0 3
  have h4 := h0 4
  have hsum : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 := by
    simp [Fin.sum_univ_succ]; ring
  simp [upperFiveGaps, Fin.sum_univ_succ] at hs hp h1 h2 h3 h4
  change a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧ a 3 ≤ a 4 ∧
    a 4 ≤ 1 - ∑ i, a i ∧ 1 - ∑ i, a i < 0.18 ∧
    0.46 ≤ a 0 + a 1 + a 2 ∧ a 0 + a 1 + a 2 ≤ 0.5
  repeat' constructor
  all_goals linarith

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
def upperFiveInnerGrid : Finset (Fin 6 → ℕ) := Finset.Nat.antidiagonalTuple 6 194

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_inner_grid_card : upperFiveInnerGrid.card = 2472258789 := by
  norm_num [upperFiveInnerGrid, antidiagonal_tuple_card, Nat.choose]

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
noncomputable def upperFiveInnerBox (q : Fin 6 → ℕ) : Set (Fin 5 → ℝ) :=
 Set.pi Set.univ (fun i => Ico
   (((q i.castSucc : ℝ) + if i = 0 then 1 else 0) * 0.0004)
   (((q i.castSucc : ℝ) + (if i = 0 then 1 else 0) + 1) * 0.0004))

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_inner_box_geometry {q : Fin 6 → ℕ} (hq : q ∈ upperFiveInnerGrid)
    {g : Fin 5 → ℝ} (hg : g ∈ upperFiveInnerBox q) :
    (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08 ∧ 0 < g 0 := by
  have hl (i : Fin 5) := (hg i (Set.mem_univ i)).1
  have hu (i : Fin 5) := (hg i (Set.mem_univ i)).2
  have hsum : ∑ i, q i = 194 := Finset.Nat.mem_antidiagonalTuple.mp hq
  have hqsum : (∑ i : Fin 5, (q i.castSucc : ℝ)) ≤ 194 := by
    have hn : ∑ i : Fin 5, q i.castSucc ≤ 194 := by
      rw [Fin.sum_univ_castSucc] at hsum
      omega
    exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hn : 0 ≤ (q i.castSucc : ℝ) := Nat.cast_nonneg _
    have := hl i
    split_ifs at this <;> linarith
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => (hu i).le)
    have he : (∑ i : Fin 5, ((q i.castSucc : ℝ) + (if i = 0 then 1 else 0) + 1) * 0.0004) =
        ((∑ i : Fin 5, (q i.castSucc : ℝ)) + 6) * 0.0004 := by
      simp [Fin.sum_univ_succ]; ring
    rw [he] at hh
    linarith
  · have := hl 0
    norm_num at this
    have : 0 ≤ (q 0 : ℝ) := Nat.cast_nonneg _
    linarith

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_inner_box_disjoint :
    Set.PairwiseDisjoint (↑upperFiveInnerGrid) upperFiveInnerBox := by
  intro q hq r hr hqr
  have hcoord : ∃ i : Fin 5, q i.castSucc ≠ r i.castSucc := by
    by_contra hn
    push Not at hn
    apply hqr
    have hqs : ∑ i, q i = 194 := Finset.Nat.mem_antidiagonalTuple.mp hq
    have hrs : ∑ i, r i = 194 := Finset.Nat.mem_antidiagonalTuple.mp hr
    have hs : ∑ i : Fin 5, q i.castSucc = ∑ i : Fin 5, r i.castSucc :=
      Finset.sum_congr rfl (fun i _ => hn i)
    ext i
    refine Fin.lastCases ?_ (fun j => hn j) i
    rw [Fin.sum_univ_castSucc] at hqs hrs
    omega
  obtain ⟨i,hi⟩ := hcoord
  apply Set.disjoint_left.mpr
  intro g hgq hgr
  have hqg := hgq i (Set.mem_univ i)
  have hrg := hgr i (Set.mem_univ i)
  change ((q i.castSucc : ℝ) + (if i = 0 then 1 else 0)) * 0.0004 ≤ g i ∧
    g i < ((q i.castSucc : ℝ) + (if i = 0 then 1 else 0) + 1) * 0.0004 at hqg
  change ((r i.castSucc : ℝ) + (if i = 0 then 1 else 0)) * 0.0004 ≤ g i ∧
    g i < ((r i.castSucc : ℝ) + (if i = 0 then 1 else 0) + 1) * 0.0004 at hrg
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hcast : (q i.castSucc : ℝ) + 1 ≤ r i.castSucc := by exact_mod_cast hlt
    linarith
  · have hcast : (r i.castSucc : ℝ) + 1 ≤ q i.castSucc := by exact_mod_cast hgt
    linarith

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_inner_box_volume (q : Fin 6 → ℕ) :
    volume (upperFiveInnerBox q) = ENNReal.ofReal ((0.0004 : ℝ) ^ 5) := by
  rw [upperFiveInnerBox, Real.volume_pi_Ico]
  have hh : ∀ i : Fin 5,
      ((q i.castSucc : ℝ) + (if i = 0 then 1 else 0) + 1) * 0.0004 -
      ((q i.castSucc : ℝ) + (if i = 0 then 1 else 0)) * 0.0004 = 0.0004 := by
    intro i; ring
  simp_rw [hh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_inner_union_volume :
    volume (⋃ q ∈ upperFiveInnerGrid, upperFiveInnerBox q) =
      ENNReal.ofReal ((2472258789 : ℝ) * 0.0004 ^ 5) := by
  rw [measure_biUnion_finset upper_five_inner_box_disjoint
    (fun q _ => MeasurableSet.univ_pi (fun i => measurableSet_Ico))]
  simp only [upper_five_inner_box_volume, Finset.sum_const, upper_five_inner_grid_card, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_region_volume_lower :
    ENNReal.ofReal ((2472258789 : ℝ) * 0.0004 ^ 5 / 720) ≤ volume upperFiveRegion := by
  let S := ⋃ q ∈ upperFiveInnerGrid, upperFiveInnerBox q
  have hS : MeasurableSet S := by
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro hq
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)
  have hm : Measurable upperFiveGaps := by unfold upperFiveGaps; fun_prop
  calc
    _ = ENNReal.ofReal (1 / 720 : ℝ) * volume S := by
      rw [show volume S = ENNReal.ofReal ((2472258789 : ℝ) * 0.0004 ^ 5) from upper_five_inner_union_volume,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    _ = volume (upperFiveGaps ⁻¹' S) := by
      rw [← Measure.map_apply hm hS, upper_five_gap_map, Measure.smul_apply, smul_eq_mul]
    _ ≤ volume upperFiveRegion := by
      apply measure_mono
      intro a ha
      change upperFiveGaps a ∈ ⋃ q ∈ upperFiveInnerGrid, upperFiveInnerBox q at ha
      obtain ⟨q,hg⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hqm,hga⟩ := Set.mem_iUnion.mp hg
      obtain ⟨h0,hs,hp⟩ := upper_five_inner_box_geometry hqm hga
      exact upper_five_geometry_converse a h0 hs hp

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_integrand_lower {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
    (0.18 ^ 6 : ℝ)⁻¹ ≤ (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹ := by
  obtain ⟨_,_,har,her⟩ := upper_five_geometry ha
  have hp : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => by linarith [(har i).1])
  have he : 0 < 1 - ∑ i, a i := by linarith
  have hprod : (∏ i, a i) ≤ 0.18 ^ 5 := by
    have ht := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      (show 0 ≤ a i by linarith [(har i).1])) (fun i _ => (har i).2)
    simpa using ht
  have hE : 1 - ∑ i, a i ≤ 0.18 := ha.2.2.2.2.2.1.le
  rw [← mul_inv]
  apply inv_anti₀ (mul_pos hp he)
  calc
    (∏ i, a i) * (1 - ∑ i, a i) ≤ (0.18 ^ 5 : ℝ) * 0.18 :=
      mul_le_mul hprod hE he.le (by norm_num)
    _ = _ := by norm_num

/-- Page 42, auxiliary rational inner-grid certificate for the literal displayed domain. The discrepancy with the printed bound is recorded as a QUESTION. -/
theorem upper_five_integral_gt_printed : (0.000001 : ℝ) < upperFiveIntegral := by
  have hv := upper_five_region_volume_lower
  have hvfin : volume upperFiveRegion ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt upper_five_region_volume ENNReal.ofReal_lt_top)
  have hreal : (2472258789 : ℝ) * 0.0004 ^ 5 / 720 ≤ volume.real upperFiveRegion := by
    have hh := ENNReal.toReal_mono hvfin hv
    rw [ENNReal.toReal_ofReal (by norm_num)] at hh
    exact hh
  have hl : (0.18 ^ 6 : ℝ)⁻¹ * volume.real upperFiveRegion ≤ upperFiveIntegral := by
    have hc : IntegrableOn (fun _ : Fin 5 → ℝ => (0.18 ^ 6 : ℝ)⁻¹) upperFiveRegion :=
      integrableOn_const hvfin
    have hm : MeasurableSet upperFiveRegion := by
      unfold upperFiveRegion
      simp only [Set.ofPred_and]
      repeat' apply MeasurableSet.inter
      all_goals first | apply measurableSet_le | apply measurableSet_lt
      all_goals fun_prop
    have hi := setIntegral_mono_on hc upper_five_integrable hm (fun a ha => upper_five_integrand_lower ha)
    simpa [upperFiveIntegral, integral_const, smul_eq_mul, mul_comm] using hi
  have hn : (0.000001 : ℝ) < (0.18 ^ 6 : ℝ)⁻¹ * ((2472258789 : ℝ) * 0.0004 ^ 5 / 720) := by norm_num
  exact hn.trans_le ((mul_le_mul_of_nonneg_left hreal (by norm_num)).trans hl)

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
def filteredSevenLoopGrid :=
 (Finset.range 21).sigma fun a =>
 (Finset.range (21-a)).sigma fun b =>
 (Finset.range (21-a-b)).sigma fun c =>
 (Finset.range (21-a-b-c)).sigma fun d =>
 ((Finset.range (21-a-b-c-d)).filter fun e =>
   105*(a+1)+90*(b+1)+70*(c+1)+42*(d+1) ≥ 1260 ∧
   175*(a+1)+160*(b+1)+140*(c+1)+112*(d+1)+70*(e+1) ≥ 2800).sigma
    fun e => Finset.Nat.antidiagonalTuple 3 (20-a-b-c-d-e)

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_loop_card : filteredSevenLoopGrid.card = 164366 := by
  simp only [filteredSevenLoopGrid, Finset.card_sigma]
  have hc : ∀ n : ℕ, (Finset.Nat.antidiagonalTuple 3 n).card = (n+2).choose 2 := by
    intro n
    exact antidiagonal_tuple_card 2 n
  simp_rw [hc]
  decide +kernel

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
noncomputable def filteredSevenRegion : Set (Fin 7 → ℝ) :=
 {a | a ∈ orderedSevenRegion ∧ 0.46 ≤ a 0 + a 1 + a 2 + a 3 ∧
   0.6 ≤ a 0 + a 1 + a 2 + a 3 + a 4}

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
noncomputable def filteredSevenGapRegion : Set (Fin 7 → ℝ) :=
 {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.2 ∧
   12.6 ≤ 105*g 0+90*g 1+70*g 2+42*g 3 ∧
   28 ≤ 175*g 0+160*g 1+140*g 2+112*g 3+70*g 4}

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_geometry {a : Fin 7 → ℝ} (ha : a ∈ filteredSevenRegion) :
    orderedSevenGaps a ∈ filteredSevenGapRegion := by
  obtain ⟨hp,hfour,hfive⟩ := ha
  have hg := ordered_seven_geometry hp
  refine ⟨hg.1,hg.2.1,?_,?_⟩
  · simp only [orderedSevenGaps, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    norm_num
    linarith
  · simp [orderedSevenGaps]
    linarith

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
noncomputable def filteredSevenBox
    (q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Fin 3 → ℕ) : Set (Fin 7 → ℝ) :=
 let r : Fin 7 → ℝ := ![↑q.1,↑q.2.1,↑q.2.2.1,↑q.2.2.2.1,↑q.2.2.2.2.1,
   ↑(q.2.2.2.2.2 0),↑(q.2.2.2.2.2 1)]
 Icc (fun i => r i * 0.01) (fun i => (r i+1)*0.01)

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_box_volume
    (q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Fin 3 → ℕ) :
    volume (filteredSevenBox q) = ENNReal.ofReal ((0.01 : ℝ)^7) := by
  rw [filteredSevenBox, Real.volume_Icc_pi]
  have hh : ∀ x : ℝ, (x+1)*0.01-x*0.01=0.01 := by intro x; ring
  simp_rw [hh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_grid_cover {g : Fin 7 → ℝ} (hg : g ∈ filteredSevenGapRegion) :
    ∃ q ∈ filteredSevenLoopGrid, g ∈ filteredSevenBox q := by
  obtain ⟨hg0,hgs,hfirst,hsecond⟩ := hg
  let k : Fin 7 → ℕ := fun i => ⌊100*g i⌋₊
  have hlo : ∀ i, (k i : ℝ) ≤ 100*g i := fun i => Nat.floor_le (mul_nonneg (by norm_num) (hg0 i))
  have hup : ∀ i, 100*g i < (k i : ℝ)+1 := fun i => Nat.lt_floor_add_one _
  have hsumk : k 0+k 1+k 2+k 3+k 4+k 5+k 6 ≤ 20 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hlo i)
    rw [← Finset.mul_sum] at hh
    have hs : (∑ i, (k i : ℝ)) ≤ 20 := by linarith
    have hr : (k 0:ℝ)+k 1+k 2+k 3+k 4+k 5+k 6 ≤ 20 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    exact_mod_cast hr
  have hP1 : 1260 ≤ 105*(k 0+1)+90*(k 1+1)+70*(k 2+1)+42*(k 3+1) := by
    have h0:=hup 0; have h1:=hup 1; have h2:=hup 2; have h3:=hup 3
    exact_mod_cast (show (1260:ℝ) ≤ 105*((k 0:ℝ)+1)+90*((k 1:ℝ)+1)+70*((k 2:ℝ)+1)+42*((k 3:ℝ)+1) by linarith)
  have hP2 : 2800 ≤ 175*(k 0+1)+160*(k 1+1)+140*(k 2+1)+112*(k 3+1)+70*(k 4+1) := by
    have h0:=hup 0; have h1:=hup 1; have h2:=hup 2; have h3:=hup 3; have h4:=hup 4
    exact_mod_cast (show (2800:ℝ) ≤ 175*((k 0:ℝ)+1)+160*((k 1:ℝ)+1)+140*((k 2:ℝ)+1)+112*((k 3:ℝ)+1)+70*((k 4:ℝ)+1) by linarith)
  let q : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Fin 3 → ℕ :=
    ⟨k 0,k 1,k 2,k 3,k 4,![k 5,k 6,20-(k 0+k 1+k 2+k 3+k 4+k 5+k 6)]⟩
  refine ⟨q,?_,?_⟩
  · simp only [filteredSevenLoopGrid, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_filter, q, hP1, hP2, and_true]
    refine ⟨by omega,by omega,by omega,by omega,by omega,?_⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp [Fin.sum_univ_succ]
    omega
  · have hrk : (![↑(k 0),↑(k 1),↑(k 2),↑(k 3),↑(k 4),↑(k 5),↑(k 6)] : Fin 7 → ℝ) =
        fun i => (k i : ℝ) := by ext i; fin_cases i <;> rfl
    constructor
    · change (fun i => ![↑(k 0),↑(k 1),↑(k 2),↑(k 3),↑(k 4),↑(k 5),↑(k 6)] i * (0.01:ℝ)) ≤ g
      rw [hrk]
      intro i
      have h:=hlo i
      linarith
    · change g ≤ (fun i => (![↑(k 0),↑(k 1),↑(k 2),↑(k 3),↑(k 4),↑(k 5),↑(k 6)] i+1) * (0.01:ℝ))
      rw [hrk]
      intro i
      have h:=hup i
      linarith

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_of_no_subproduct {a : Fin 7 → ℝ} (ha : a ∈ orderedSevenRegion)
    (hno : ∀ s : Finset (Fin 8), ¬ ((0.4 : ℝ) ≤
      ∑ i ∈ s, (![a 0,a 1,a 2,a 3,a 4,a 5,a 6,1-∑ j, a j] : Fin 8 → ℝ) i ∧
      (∑ i ∈ s, (![a 0,a 1,a 2,a 3,a 4,a 5,a 6,1-∑ j, a j] : Fin 8 → ℝ) i) ≤ 0.46)) :
    a ∈ filteredSevenRegion := by
  have hg := ordered_seven_geometry ha
  have hfour := hno {0,1,2,3}
  have hthree := hno {5,6,7}
  norm_num [Finset.sum_insert, Finset.sum_singleton] at hfour hthree
  have h0:=hg.2.2.1 0; have h1:=hg.2.2.1 1
  have h2:=hg.2.2.1 2; have h3:=hg.2.2.1 3; have h4:=hg.2.2.1 4
  have hf : 0.46 < a 0+a 1+a 2+a 3 := by
    by_contra hn
    have hh := hfour (by linarith)
    linarith
  have hs : (∑ j, a j) = a 0+a 1+a 2+a 3+a 4+a 5+a 6 := by
    simp [Fin.sum_univ_succ]; ring
  have ht : a 5+a 6+(1-∑ j, a j) < 0.4 := by
    by_contra hn
    have hh := hthree (by linarith)
    linarith
  exact ⟨ha,hf.le,by linarith⟩

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
noncomputable def filteredSevenGridBound : ℝ :=
 ∑ _ ∈ filteredSevenLoopGrid, (3*(567144/1000000:ℝ)) * 0.01^7 / (40320*(0.3*0.1^7))

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_grid_bound : filteredSevenGridBound < 0.00000232 := by
 norm_num [filteredSevenGridBound, Finset.sum_const, filtered_seven_loop_card]

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_gap_region_volume : volume filteredSevenGapRegion ≤
    ENNReal.ofReal ((164366:ℝ)*0.01^7) := by
  calc
    _ ≤ volume (⋃ q ∈ filteredSevenLoopGrid, filteredSevenBox q) := by
      apply measure_mono
      intro g hg
      obtain ⟨q,hq,hgq⟩ := filtered_seven_grid_cover hg
      exact Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨hq,hgq⟩⟩
    _ ≤ ∑ q ∈ filteredSevenLoopGrid, volume (filteredSevenBox q) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [filtered_seven_box_volume, Finset.sum_const, filtered_seven_loop_card, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_region_volume : volume filteredSevenRegion ≤
    ENNReal.ofReal ((164366:ℝ)*0.01^7/40320) := by
  have hS : MeasurableSet filteredSevenGapRegion := by
    unfold filteredSevenGapRegion
    simp only [Set.ofPred_and, Set.ofPred_forall]
    repeat' apply MeasurableSet.inter
    · exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    all_goals apply measurableSet_le <;> fun_prop
  have hm : Measurable orderedSevenGaps := by unfold orderedSevenGaps; fun_prop
  calc
    _ ≤ volume (orderedSevenGaps ⁻¹' filteredSevenGapRegion) :=
      measure_mono (fun a ha => filtered_seven_geometry ha)
    _ = ENNReal.ofReal (1/40320:ℝ) * volume filteredSevenGapRegion := by
      rw [← Measure.map_apply hm hS, ordered_seven_gap_map, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (1/40320:ℝ) * ENNReal.ofReal ((164366:ℝ)*0.01^7) := by
      gcongr; exact filtered_seven_gap_region_volume
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
noncomputable def filteredSevenBuchstabIntegral (ω : ℝ → ℝ) : ℝ :=
 ∫ a in filteredSevenRegion, ω ((1-∑ i, a i)/a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹

/-- CONDITIONAL ON the stated Buchstab solution and any stated density relation. Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_buchstab_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) :
    IntegrableOn (fun a : Fin 7 → ℝ =>
      ω ((1-∑ i, a i)/a 6) * (∏ i, a i)⁻¹ * (a 6)⁻¹) filteredSevenRegion :=
  (ordered_seven_buchstab_integrable hω).mono_set (fun _ ha => ha.1)

/-- CONDITIONAL ON the stated Buchstab solution and any stated density relation. Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_buchstab_integral_le_grid {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) :
    filteredSevenBuchstabIntegral ω ≤ filteredSevenGridBound := by
  have hv := filtered_seven_region_volume
  have hfin : volume filteredSevenRegion < ⊤ := lt_of_le_of_lt hv (by simp)
  have hi := norm_setIntegral_le_of_norm_le_const hfin
    (fun a ha => ordered_seven_buchstab_integrand_bound hω ha.1)
  have hreal : volume.real filteredSevenRegion ≤ (164366:ℝ)*0.01^7/40320 := by
    have h := ENNReal.toReal_mono (by simp) hv
    rw [ENNReal.toReal_ofReal (by norm_num)] at h
    exact h
  calc
    filteredSevenBuchstabIntegral ω ≤ ‖filteredSevenBuchstabIntegral ω‖ := le_abs_self _
    _ ≤ ((3*(567144/1000000:ℝ))*(0.3*0.1^7:ℝ)⁻¹)*volume.real filteredSevenRegion := hi
    _ ≤ ((3*(567144/1000000:ℝ))*(0.3*0.1^7:ℝ)⁻¹)*((164366:ℝ)*0.01^7/40320) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = filteredSevenGridBound := by
      norm_num [filteredSevenGridBound, Finset.sum_const, filtered_seven_loop_card]

/-- CONDITIONAL ON the stated Buchstab solution and any stated density relation. Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_buchstab_integral_lt {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) :
    filteredSevenBuchstabIntegral ω < 0.00000232 :=
  (filtered_seven_buchstab_integral_le_grid hω).trans_lt filtered_seven_grid_bound

/-- CONDITIONAL ON the stated Buchstab solution and any stated density relation. Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem upper_density_of_filtered_losses {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (n m : ℕ) (hn : n ≤ 12) (hm : m ≤ 12) (u : ℝ)
    (hu : u ≤ 1+(n:ℝ)*upperFiveIntegral+(m:ℝ)*filteredSevenBuchstabIntegral ω) :
    u < 1.0001 := by
  have hnR : (n:ℝ) ≤ 12 := by exact_mod_cast hn
  have hmR : (m:ℝ) ≤ 12 := by exact_mod_cast hm
  have hf := mul_le_mul_of_nonneg_left upper_five_integral_lt.le (Nat.cast_nonneg (α:=ℝ) n)
  have hs := mul_le_mul_of_nonneg_left (filtered_seven_buchstab_integral_lt hω).le (Nat.cast_nonneg (α:=ℝ) m)
  nlinarith

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem filtered_seven_nonempty_instance :
    (fun _ : Fin 7 => (1/8:ℝ)) ∈ filteredSevenRegion := by
  norm_num [filteredSevenRegion, orderedSevenRegion, Fin.sum_univ_succ]

/-- Pages 34 and 42, auxiliary filtered ordered envelope from necessary Lemma 17a exclusions. No actual sieve multiplicities are asserted. -/
theorem equal_eighths_no_subproduct (s : Finset (Fin 8)) :
    ¬ ((0.4:ℝ) ≤ ∑ i ∈ s, (1/8:ℝ) ∧ (∑ i ∈ s, (1/8:ℝ)) ≤ 0.46) := by
  simp only [Finset.sum_const, nsmul_eq_mul]
  intro ⟨hl,hu⟩
  have hn0 : (3:ℝ) < s.card := by linarith
  have hn1 : (s.card:ℝ) < 4 := by linarith
  have h0 : 3 < s.card := by exact_mod_cast hn0
  have h1 : s.card < 4 := by exact_mod_cast hn1
  omega

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
def refinedFiveGrid : Finset (Fin 6 → ℕ) := Finset.Nat.antidiagonalTuple 6 100

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_grid_card : refinedFiveGrid.card = 96560646 := by
  norm_num [refinedFiveGrid, antidiagonal_tuple_card, Nat.choose]

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
noncomputable def refinedFiveGridBound : ℝ :=
 ∑ _ ∈ refinedFiveGrid, (0.08 / 100 : ℝ) ^ 5 / (720 * (0.1 * 0.18 ^ 5))

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_grid_bound : refinedFiveGridBound < 0.0000024 := by
 norm_num [refinedFiveGridBound, Finset.sum_const, refined_five_grid_card]

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
noncomputable def refinedFiveBox (q : Fin 6 → ℕ) : Set (Fin 5 → ℝ) :=
 Icc (fun i => (q i.castSucc : ℝ) * (0.08 / 100))
     (fun i => ((q i.castSucc : ℝ) + 1) * (0.08 / 100))

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_grid_cover (g : Fin 5 → ℝ)
    (h0 : ∀ i, 0 ≤ g i) (hs : ∑ i, g i ≤ 0.08) :
    ∃ q ∈ refinedFiveGrid, g ∈ refinedFiveBox q := by
  let k : Fin 5 → ℕ := fun i => ⌊g i / (0.08 / 100)⌋₊
  have hk : (∑ i, k i) ≤ 100 := by
    have hr : (∑ i, (k i : ℝ)) ≤ 100 := by
      calc
        (∑ i, (k i : ℝ)) ≤ ∑ i, g i / (0.08 / 100) :=
          Finset.sum_le_sum (fun i _ => Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
        _ ≤ 100 := by rw [← Finset.sum_div]; norm_num; linarith
    exact_mod_cast hr
  let q : Fin 6 → ℕ := Fin.snoc (α := fun _ => ℕ) k (100 - ∑ i, k i)
  refine ⟨q, ?_, ?_⟩
  · rw [refinedFiveGrid, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc]
    simpa only [q, Fin.snoc_castSucc, Fin.snoc_last] using Nat.add_sub_of_le hk
  · constructor
    · intro i
      dsimp only [refinedFiveBox] at *
      simp only [q, Fin.snoc_castSucc]
      change (k i : ℝ) * (0.08 / 100) ≤ g i
      exact (le_div_iff₀ (by norm_num)).mp (Nat.floor_le (div_nonneg (h0 i) (by norm_num)))
    · intro i
      dsimp only [refinedFiveBox] at *
      simp only [q, Fin.snoc_castSucc]
      change g i ≤ ((k i : ℝ) + 1) * (0.08 / 100)
      exact ((div_lt_iff₀ (by norm_num)).mp (Nat.lt_floor_add_one (g i / (0.08 / 100)))).le

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_box_volume (q : Fin 6 → ℕ) :
    volume (refinedFiveBox q) = ENNReal.ofReal ((0.08 / 100 : ℝ) ^ 5) := by
  rw [refinedFiveBox, Real.volume_Icc_pi]
  have hh : ∀ i : Fin 5,
    ((q i.castSucc : ℝ) + 1) * (0.08 / 100) - (q i.castSucc : ℝ) * (0.08 / 100) = 0.08 / 100 := by
    intro i; ring
  simp_rw [hh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_simplex_volume :
    volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08} ≤
      ENNReal.ofReal ((96560646 : ℝ) * (0.08 / 100) ^ 5) := by
  calc
    _ ≤ volume (⋃ q ∈ refinedFiveGrid, refinedFiveBox q) := by
      apply measure_mono
      intro g hg
      obtain ⟨q,hq,hgq⟩ := refined_five_grid_cover g hg.1 hg.2
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq,hgq⟩⟩
    _ ≤ ∑ q ∈ refinedFiveGrid, volume (refinedFiveBox q) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [refined_five_box_volume, Finset.sum_const, refined_five_grid_card, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_region_volume :
    volume upperFiveRegion ≤ ENNReal.ofReal ((96560646 : ℝ) * (0.08 / 100) ^ 5 / 720) := by
  let S : Set (Fin 5 → ℝ) := {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08}
  have hS : MeasurableSet S := by
    simp only [S, ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
      (measurable_pi_apply i)).inter (measurableSet_le (show Measurable (fun g : Fin 5 → ℝ => ∑ i, g i) by fun_prop) measurable_const)
  have hm : Measurable upperFiveGaps := by
    unfold upperFiveGaps
    fun_prop
  calc
    volume upperFiveRegion ≤ volume (upperFiveGaps ⁻¹' S) := by
      apply measure_mono
      intro a ha
      exact ⟨(upper_five_geometry ha).1, (upper_five_geometry ha).2.1⟩
    _ = ENNReal.ofReal (1 / 720 : ℝ) * volume S := by
      rw [← Measure.map_apply hm hS, upper_five_gap_map, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / 720 : ℝ) *
        ENNReal.ofReal ((96560646 : ℝ) * (0.08 / 100) ^ 5) :=
      by gcongr; exact refined_five_simplex_volume
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_integral_le_grid : upperFiveIntegral ≤ refinedFiveGridBound := by
  have hv := refined_five_region_volume
  have hfin : volume upperFiveRegion < ⊤ := lt_of_le_of_lt hv (by simp)
  have hi := norm_setIntegral_le_of_norm_le_const hfin (fun a ha => upper_five_integrand_bound ha)
  have hreal : volume.real upperFiveRegion ≤ (96560646 : ℝ) * (0.08 / 100) ^ 5 / 720 := by
    have h := ENNReal.toReal_mono (by simp) hv
    rw [ENNReal.toReal_ofReal (show 0 ≤ (96560646 : ℝ) * (0.08 / 100) ^ 5 / 720 by norm_num)] at h
    exact h
  calc
    upperFiveIntegral ≤ ‖upperFiveIntegral‖ := le_abs_self _
    _ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ * volume.real upperFiveRegion := hi
    _ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ * ((96560646 : ℝ) * (0.08 / 100) ^ 5 / 720) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = refinedFiveGridBound := by
      norm_num [refinedFiveGridBound, Finset.sum_const, refined_five_grid_card]

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem refined_five_integral_lt : upperFiveIntegral < 0.0000024 :=
  refined_five_integral_le_grid.trans_lt refined_five_grid_bound

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem six_product_le_sixth (b : Fin 6 → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, b i = 1) :
    (∏ i, b i) ≤ (1/6:ℝ)^6 := by
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin 6 => (1:ℝ)) b
    (fun _ _ => by norm_num) (by norm_num) (fun i _ => hb i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hs] at h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hb i)) _) h 6
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hb i)) (by norm_num : (6:ℕ) ≠ 0)] at hh
  exact hh

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem upper_five_integrand_lower_amgm {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
    (46656:ℝ) ≤ (∏ i, a i)⁻¹ * (1-∑ i, a i)⁻¹ := by
  have hg := upper_five_geometry ha
  let b : Fin 6 → ℝ := Fin.snoc (α:=fun _ => ℝ) a (1-∑ i, a i)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using (show (0:ℝ) ≤ 1-∑ i, a i by linarith [hg.2.2.2])
    · simpa only [b, Fin.snoc_castSucc] using (show (0:ℝ) ≤ a j by linarith [(hg.2.2.1 j).1])
  have hs : ∑ i, b i = 1 := by
    rw [Fin.sum_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hp := six_product_le_sixth b hb hs
  have he : (∏ i, b i) = (∏ i, a i)*(1-∑ i, a i) := by
    rw [Fin.prod_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
  rw [he] at hp
  have hpos : 0 < (∏ i, a i)*(1-∑ i, a i) := by
    apply mul_pos
    · exact Finset.prod_pos (fun i _ => by linarith [(hg.2.2.1 i).1])
    · linarith [hg.2.2.2]
  have hi := inv_anti₀ hpos hp
  norm_num at hi
  simpa [mul_inv, mul_comm] using hi

/-- Page 42, auxiliary rational enclosure for the literal displayed integral. The printed numerical discrepancy remains a QUESTION. -/
theorem upper_five_integral_gt_amgm : (0.0000016:ℝ) < upperFiveIntegral := by
  have hv := upper_five_region_volume_lower
  have hvfin : volume upperFiveRegion ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt upper_five_region_volume ENNReal.ofReal_lt_top)
  have hreal : (2472258789:ℝ)*0.0004^5/720 ≤ volume.real upperFiveRegion := by
    have hh := ENNReal.toReal_mono hvfin hv
    rw [ENNReal.toReal_ofReal (by norm_num)] at hh
    exact hh
  have hm : MeasurableSet upperFiveRegion := by
    unfold upperFiveRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals first | apply measurableSet_le | apply measurableSet_lt
    all_goals fun_prop
  have hc : IntegrableOn (fun _ : Fin 5 → ℝ => (46656:ℝ)) upperFiveRegion := integrableOn_const hvfin
  have hi := setIntegral_mono_on hc upper_five_integrable hm (fun a ha => upper_five_integrand_lower_amgm ha)
  have hl : (46656:ℝ)*volume.real upperFiveRegion ≤ upperFiveIntegral := by
    simpa [upperFiveIntegral, integral_const, smul_eq_mul, mul_comm] using hi
  have hn : (0.0000016:ℝ) < 46656*((2472258789:ℝ)*0.0004^5/720) := by norm_num
  exact hn.trans_le ((mul_le_mul_of_nonneg_left hreal (by norm_num)).trans hl)

/-- Page 3 conditions i and ii, auxiliary finite linear assembly for the Section 4 identity on page 32. No analytic character estimate is asserted for a new summand. -/
theorem left_conditions_zero (ε B : ℝ) : LeftConditions ε B 0 (fun _ _ => 0) := by
  refine ⟨?_,⟨0,?_⟩,?_⟩
  · intro A hA
    exact ⟨0, by intros; simp⟩
  · intros; simp
  · intro A hA
    exact ⟨0,by intros; rfl⟩

/-- Page 3 conditions i and ii, auxiliary finite linear assembly for the Section 4 identity on page 32. No analytic character estimate is asserted for a new summand. -/
theorem left_conditions_add {ε B u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : LeftConditions ε B u a) (hb : LeftConditions ε B v b) :
    LeftConditions ε B (u+v) (fun x k => a x k+b x k) := by
  obtain ⟨hai,⟨Da,hDa⟩,har⟩ := ha
  obtain ⟨hbi,⟨Db,hDb⟩,hbr⟩ := hb
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨Ca,hCa⟩ := hai A hA
    obtain ⟨Cb,hCb⟩ := hbi A hA
    let C := max (max Ca Cb) (max 1 (Ca+Cb))
    refine ⟨C,fun x hx q hq hqx χ t ht => ?_⟩
    have hxa : Ca ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
    have hxb : Cb ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
    have hx1 : 1 ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
    have hsum : Ca+Cb ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have he : (∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        (((a x k+b x k:ℝ):ℂ)*χ (k:ZMod q)-Thm2.delta χ*((u+v:ℝ):ℂ)/Real.log x)) =
      (∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log x)) +
      ∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        ((b x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*v/Real.log x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    dsimp only
    rw [he]
    calc
      _ ≤ ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
          ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log x)‖ +
        ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
          ((b x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*v/Real.log x)‖ := norm_add_le _ _
      _ ≤ Ca*x^(11/20+ε)*Real.log x^(-A)+Cb*x^(11/20+ε)*Real.log x^(-A) :=
        add_le_add (hCa x hxa q hq hqx χ t ht) (hCb x hxb q hq hqx χ t ht)
      _ = (Ca+Cb)*x^(11/20+ε)*Real.log x^(-A) := by ring
      _ ≤ C*x^(11/20+ε)*Real.log x^(-A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (by linarith) _))
          (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  · refine ⟨Da+Db,fun x k => ?_⟩
    calc
      |a x k+b x k| ≤ |a x k|+|b x k| := abs_add_le _ _
      _ ≤ Da*((k.divisors.card:ℕ):ℝ)^B+Db*((k.divisors.card:ℕ):ℝ)^B := add_le_add (hDa x k) (hDb x k)
      _ = _ := by ring
  · intro A hA
    obtain ⟨Ca,hCa⟩ := har A hA
    obtain ⟨Cb,hCb⟩ := hbr A hA
    refine ⟨max Ca Cb,fun x hx k hk => ?_⟩
    change a x k+b x k=0
    rw [hCa x ((le_max_left _ _).trans hx) k hk,hCb x ((le_max_right _ _).trans hx) k hk]
    norm_num

/-- Page 3 conditions i and ii, auxiliary finite linear assembly for the Section 4 identity on page 32. No analytic character estimate is asserted for a new summand. -/
theorem left_conditions_neg {ε B u : ℝ} {a : ℝ → ℕ → ℝ}
    (ha : LeftConditions ε B u a) : LeftConditions ε B (-u) (fun x k => -a x k) := by
  obtain ⟨hai,had,har⟩ := ha
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨C,hC⟩ := hai A hA
    refine ⟨C,fun x hx q hq hqx χ t ht => ?_⟩
    have he : (∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        (((-a x k:ℝ):ℂ)*χ (k:ZMod q)-Thm2.delta χ*((-u:ℝ):ℂ)/Real.log x)) =
      -(∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k:ℝ) ≤ t),
        ((a x k:ℂ)*χ (k:ZMod q)-Thm2.delta χ*u/Real.log x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    dsimp only
    rw [he,norm_neg]
    exact hC x hx q hq hqx χ t ht
  · simpa only [abs_neg] using had
  · intro A hA
    obtain ⟨C,hC⟩ := har A hA
    exact ⟨C,fun x hx k hk => by change -a x k=0; rw [hC x hx k hk,neg_zero]⟩

/-- Page 3 conditions i and ii, auxiliary finite linear assembly for the Section 4 identity on page 32. No analytic character estimate is asserted for a new summand. -/
theorem left_conditions_sub {ε B u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : LeftConditions ε B u a) (hb : LeftConditions ε B v b) :
    LeftConditions ε B (u-v) (fun x k => a x k-b x k) := by
  simpa only [sub_eq_add_neg] using left_conditions_add ha (left_conditions_neg hb)

/-- Page 3 conditions i and ii, auxiliary finite linear assembly for the Section 4 identity on page 32. No analytic character estimate is asserted for a new summand. -/
theorem left_conditions_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (a : ι → ℝ → ℕ → ℝ) (ε B : ℝ) (ha : ∀ i ∈ s, LeftConditions ε B (u i) (a i)) :
    LeftConditions ε B (∑ i ∈ s, u i) (fun x k => ∑ i ∈ s, a i x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using left_conditions_zero ε B
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using left_conditions_add (ha i (Finset.mem_insert_self _ _)) hsum

/-- Pages 25 and 32, elementary comparison of the paper sieve threshold with fixed positive power cutoffs. Reuses Mathlib tendsto_rpow_neg_atTop. -/
theorem sieve_threshold_le_fixed_power {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x ^ (9/10:ℝ)) ≤ x^α := by
  have hs : ∀ᶠ t : ℝ in atTop, t^(-(1/10:ℝ)) < α :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/10)).eventually (eventually_lt_nhds hα)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hp : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (9/10:ℝ) = Real.log x * Real.log x ^ (-(1/10:ℝ)) := by
    calc
      _ = Real.log x ^ ((1:ℝ)+(-(1/10:ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hp,Real.rpow_one]
  rw [Real.rpow_def_of_pos (by linarith : 0<x)]
  apply Real.exp_le_exp.mpr
  rw [he]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hx.le hp.le

end Task217Numerics

/-- LEAF. Section 4, pages 24 to 41, the lower weight a0.
The discarded region integrals on page 41 give u0 greater than 0.9953.
Use the Section 3 mean values for condition i and the sifted construction
for condition ii. The lower weight has density at most 1. OPEN. -/
theorem section4_lower (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u0 : ℝ) (a0 : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧ LeftConditions ε B u0 a0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, a0 x k ≤ primeWeight k := by
  obtain ⟨B0, η, hη, hdata⟩ := section4_lower_sifted_data h4
  refine ⟨B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨u0, c0, hu0, hu01, hdist, hdiv, X, hsand⟩ := hdata B ε hB hε hεη
  refine ⟨u0, section4SiftedFamily c0, hu0, hu01, ?_, X, hsand⟩
  exact ⟨hdist, hdiv, sifted_family_rough_support c0⟩


/-- LEAF. Section 4, pages 41 and 42, Lemma 28 and the upper weight a1.
The five and seven dimensional discarded integrals give u1 below 1.0001.
The upper density is at least 1. The bound is on page 42. OPEN. -/
theorem section4_upper (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u1 : ℝ) (a1 : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧ LeftConditions ε B u1 a1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ a1 x k := by
  obtain ⟨B0, η, hη, hdata⟩ := section4_upper_sifted_data h4
  refine ⟨B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨u1, c1, hu11, hu1, hdist, hdiv, X, hsand⟩ := hdata B ε hB hε hεη
  refine ⟨u1, section4SiftedFamily c1, hu11, hu1, ?_, X, hsand⟩
  exact ⟨hdist, hdiv, sifted_family_rough_support c1⟩


/-- LEAF. Section 5, pages 43 to 53, Lemmas 29 to 35 and the two short
weights. Condition iv is 5.1 to 5.3 followed by Lemma 29. The final
Buchstab integrals yield v0 greater than 0.05 and v1 below 2.2.
The page 22 Lemma 9 and Section 3 mean values are explicit inputs.
The finer construction leaves are in DecompC165d. CONDITIONAL. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  exact DecompC165d.section5_weights h4 h9

/-- LEAF. Pages 2 to 4, applying Theorem 2 three times gives the
correlations before 1.5 outside the union of three exceptional sets.
Spend one extra log power on their cardinalities. Positivity of sing,
proved in Thm2Sing, gives r. The fixed positive margin absorbs the
relative errors for large x. This is the remaining elementary transfer.
PROVED as an implication from Theorem 2 and the four weight conditions. -/
theorem correlation_transfer
    {ε B u0 u1 v0 v1 : ℝ} {a0 a1 b0 b1 : ℝ → ℕ → ℝ}
    (h2 : Thm2.Theorem2 ε B)
    (hε : 0 < ε) (hε1 : ε < 8.8 / 10 ^ 5)
    (hu0 : 0.99 < u0) (hu : u0 ≤ u1) (hu1 : u1 < 1.01)
    (hv0 : 0.05 < v0) (hv : v0 ≤ v1) (hv1 : v1 < 2.2)
    (ha0 : LeftConditions ε B u0 a0) (ha1 : LeftConditions ε B u1 a1)
    (hb0 : RightConditions ε B v0 b0) (hb1 : RightConditions ε B v1 b1)
    (hsand : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (∀ k ∈ leftInterval ε x, a0 x k ≤ primeWeight k ∧ primeWeight k ≤ a1 x k) ∧
      (∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  intro A hA
  obtain ⟨K01, C01, h01⟩ := pair_correlation h2 ha0 hb1 (A + 1) (by linarith)
  obtain ⟨K10, C10, h10⟩ := pair_correlation h2 ha1 hb0 (A + 1) (by linarith)
  obtain ⟨K11, C11, h11⟩ := pair_correlation h2 ha1 hb1 (A + 1) (by linarith)
  obtain ⟨Xs, hs⟩ := hsand
  let m := u0 * v1 + u1 * v0 - u1 * v1
  have hm : 0 < m := constants15 hu0 hu hu1 hv0 hv hv1
  let D := max 1 (max (max (K01 * |u0 * v1|) (K10 * |u1 * v0|)) (K11 * |u1 * v1|))
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD01 : K01 * |u0 * v1| ≤ D :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD10 : K10 * |u1 * v0| ≤ D :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD11 : K11 * |u1 * v1| ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  let R := 4 + 6 * D / m
  let X := max (max Xs C01) (max (max C10 C11) (Real.exp (R + 1)))
  refine ⟨X, fun x hx => ?_⟩
  have hxS : Xs ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx01 : C01 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx10 : C10 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx11 : C11 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hxexp : Real.exp (R + 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hR : 4 < R := by
    have hp : 0 < 6 * D / m := by positivity
    dsimp [R]
    linarith
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by linarith)) hxexp
  have hx0 : 0 < x := by linarith
  have hlogR : R + 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlog3 : 3 < Real.log x := by linarith
  have hDlog : 6 * D ≤ m * Real.log x := by
    have ht : 6 * D / m ≤ Real.log x := by dsimp [R] at hlogR; linarith
    have hh := (div_le_iff₀ hm).mp ht
    nlinarith
  let E01 := badSet ε u0 v1 K01 a0 b1 x
  let E10 := badSet ε u1 v0 K10 a1 b0 x
  let E11 := badSet ε u1 v1 K11 a1 b1 x
  let E := (E01 ∪ E10) ∪ E11
  refine ⟨leftInterval ε x, rightInterval ε x, a0 x, a1 x, b0 x, b1 x, E,
    (hs x hxS).1, (hs x hxS).2, ?_, ?_⟩
  · have hcard : E.card ≤ E01.card + E10.card + E11.card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcast : (E.card : ℝ) ≤ (E01.card : ℝ) + (E10.card : ℝ) + (E11.card : ℝ) := by
      exact_mod_cast hcard
    have hc01 := h01 x hx01
    have hc10 := h10 x hx10
    have hc11 := h11 x hx11
    have hsmall : (E.card : ℝ) <
        3 * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ (A + 1)) := by
      dsimp only [E01, E10, E11] at hcast
      linarith
    apply lt_trans hsmall
    rw [← mul_div_assoc, Real.rpow_add hlog, Real.rpow_one,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ A := by
      positivity
    nlinarith [mul_lt_mul_of_pos_left hlog3 hp]
  · intro N hN hEven hNE
    let r := correlationScale ε x N
    have hr : 0 < r := by
      dsimp [r, correlationScale]
      have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := by
        rw [Real.log_rpow hx0]
        positivity
      exact mul_pos (div_pos (Real.rpow_pos_of_pos hx0 _) (mul_pos hlog hlogY)) (Thm2.sing_pos _)
    refine ⟨r, hr, ?_, ?_, ?_⟩
    all_goals
      have hnot01 : N ∉ E01 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hn)
      have hnot10 : N ∉ E10 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hn)
      have hnot11 : N ∉ E11 := by
        intro hn
        apply hNE
        exact Finset.mem_union_right _ hn
      have hbound (u v K : ℝ) (a b : ℝ → ℕ → ℝ)
          (hn : N ∉ badSet ε u v K a b x) (hK : K * |u * v| ≤ D) :
          |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤ m * r / 6 := by
        have he : |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤
            K * |u * v| * r / Real.log x := by
          apply le_of_not_gt
          intro hbad
          exact hn (Finset.mem_filter.mpr ⟨hN, hEven, hbad⟩)
        apply he.trans
        apply (div_le_iff₀ hlog).mpr
        have h1 := mul_le_mul_of_nonneg_right hK hr.le
        have h2 := mul_le_mul_of_nonneg_right hDlog hr.le
        nlinarith
    · exact hbound u0 v1 K01 a0 b1 hnot01 hD01
    · exact hbound u1 v0 K10 a1 b0 hnot10 hD10
    · exact hbound u1 v1 K11 a1 b1 hnot11 hD11

/-- Pages 1 to 4 and Sections 2 to 5. The exact existing sieve_data
statement follows from three local OPEN leaves, the Sections 3 and 5 decompositions
and the proved correlation transfer.
No direct sorry.
CONDITIONAL on all named analytic inputs. -/
theorem sieve_data :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  have h4 := section3_mean_values
  obtain ⟨Bl, ηl, hηl, hl⟩ := section4_lower h4
  obtain ⟨Bu, ηu, hηu, hu⟩ := section4_upper h4
  obtain ⟨Br, ηr, hηr, hr⟩ := section5_weights h4 DecompC165a.lemma9
  obtain ⟨η2, hη2, h2⟩ := section2_circle_method (max Bl (max Bu Br))
  let η := min η2 (min ηl (min ηu (min ηr (8.8 / 10 ^ 5))))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε < η := by dsimp [ε]; linarith
  have hε2 : ε < η2 := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεl : ε < ηl := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεu : ε < ηu := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεr : ε < ηr := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε1 : ε < 8.8 / 10 ^ 5 := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  let B := max Bl (max Bu Br)
  obtain ⟨u0, a0, hu0, hu01, ha0, X0, hs0⟩ := hl B ε (le_max_left _ _) hε hεl
  obtain ⟨u1, a1, hu11, hu1, ha1, X1, hs1⟩ := hu B ε
    (le_trans (le_max_left _ _) (le_max_right _ _)) hε hεu
  obtain ⟨v0, v1, b0, b1, hv0, hv, hv1, hb0, hb1, Xb, hsb⟩ := hr B ε
    (le_trans (le_max_right _ _) (le_max_right _ _)) hε hεr
  have hu0' : 0.99 < u0 := by linarith
  have hu' : u0 ≤ u1 := le_trans hu01 hu11
  have hu1' : u1 < 1.01 := by linarith
  refine ⟨ε, u0, u1, v0, v1, hε, hε1, hu0', hu', hu1', hv0, hv, hv1, ?_⟩
  exact correlation_transfer (h2 ε hε hε2) hε hε1 hu0' hu' hu1' hv0 hv hv1
    ha0 ha1 hb0 hb1 ⟨max X0 (max X1 Xb), fun x hx =>
      ⟨fun k hk => ⟨hs0 x (le_trans (le_max_left _ _) hx) k hk,
        hs1 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) k hk⟩,
       hsb x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)⟩⟩


/-- Pages 25 to 27. Sifting a prime indicator removes exactly the primes
below the cutoff. This is an indicator identity and asserts no distribution estimate. -/
theorem sifted_prime_indicator (k z : ℕ) :
    primeWeight k * siftedWeight k z = if z ≤ k then primeWeight k else 0 := by
  by_cases hk : k.Prime
  · simp [primeWeight, siftedWeight, hk, hk.ne_one]
  · simp [primeWeight, hk]

/-- Pages 1 and 25 to 27. On the long interval the prime coefficient family
survives the sieve cutoff for all sufficiently large x. The condition epsilon
less than 9 over 20 ensures that the long interval stays away from zero. -/
theorem prime_sifted_eventually_on_left {ε : ℝ} (hε : ε < 9 / 20) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k ∈ leftInterval ε x,
      section4SiftedFamily (fun _ k => primeWeight k) x k = primeWeight k := by
  have hδ : 0 < 1 - (11 / 20 + ε) := by linarith
  have hy : ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (-(1 - (11 / 20 + ε))) < (1 / 4 : ℝ) :=
    (tendsto_rpow_neg_atTop hδ).eventually (eventually_lt_nhds (by norm_num))
  have hs : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(1 / 2 : ℝ)) < (1 / 4 : ℝ) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_lt_nhds (by norm_num))
  filter_upwards [hy, hs, sieve_threshold_le_fixed_power (by norm_num : (0 : ℝ) < 1 / 2),
    Filter.eventually_gt_atTop (0 : ℝ)] with x hy hs hc hx
  have hey : x ^ (-(1 - (11 / 20 + ε))) = x ^ (11 / 20 + ε) / x := by
    rw [show -(1 - (11 / 20 + ε)) = (11 / 20 + ε) - 1 by ring,
      Real.rpow_sub_one hx.ne']
  have hes : x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) / x := by
    rw [show -(1 / 2 : ℝ) = (1 / 2 : ℝ) - 1 by norm_num, Real.rpow_sub_one hx.ne']
  rw [hey, div_lt_iff₀ hx] at hy
  rw [hes, div_lt_iff₀ hx] at hs
  intro k hk
  have hkx : x - 2 * x ^ (11 / 20 + ε) < (k : ℝ) :=
    Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hk).1
  have hcut : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (k : ℝ) := by linarith
  have hceil : ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ ≤ k := Nat.ceil_le.mpr hcut
  change primeWeight k * siftedWeight k _ = primeWeight k
  rw [sifted_prime_indicator, ite_eq_left hceil]


/-- Page 3, display 1.9. Diagnostic for the prefix triangle method.
Its cubic Y scale cannot fit the required scale even with Q replaced by
the larger value Y to one sixteenth and any fixed logarithmic allowance.
This refutes that bound comparison, not the exceptional moment statement. -/
theorem prefix_triangle_scale_not_log_absorbable (A : ℝ) :
    ¬ ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
      Y ^ (3 : ℕ) ≤ C * (Y ^ (1 / 16 : ℝ)) ^ 2 * Y * Real.log Y ^ A := by
  rintro ⟨C, hC⟩
  apply DecompC165c.positive_power_not_log_bounded (by norm_num : (0 : ℝ) < 15 / 8) A
  refine ⟨C, fun Y hY => ?_⟩
  have hy : 0 < Y := by linarith
  have hs : (Y ^ (1 / 16 : ℝ)) ^ 2 = Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul_natCast hy.le]
    norm_num
  have he : Y ^ (15 / 8 : ℝ) * ((Y ^ (1 / 16 : ℝ)) ^ 2 * Y) = Y ^ (3 : ℕ) := by
    rw [hs]
    calc
      _ = Y ^ (15 / 8 : ℝ) * (Y ^ (1 / 8 : ℝ) * Y ^ (1 : ℝ)) := by rw [Real.rpow_one]
      _ = Y ^ ((15 / 8 : ℝ) + (1 / 8 + 1)) := by rw [Real.rpow_add hy, Real.rpow_add hy]
      _ = _ := by norm_num
  have hh := hC Y hY
  rw [← he] at hh
  have hp : 0 < (Y ^ (1 / 16 : ℝ)) ^ 2 * Y := by positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  convert hh using 1 <;> ring


/-- Page 3, the definition of Q. The integer cutoff is no greater than
Y to one sixteenth whenever Y is at least one. This is the conservative
comparison used in the prefix triangle scale diagnostic. -/
theorem sieveQ_le_sixteenth_power {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  unfold sieveQ
  calc
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by norm_num)
    _ = (x ^ (11 / 20 + ε)) ^ ((1 / 16 : ℝ) - 1 / 10 ^ 5) := by
      rw [← Real.rpow_mul hY0]
      congr 1
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

end LeanLab.BHP1997.DecompC165b

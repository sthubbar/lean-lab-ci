/-
The separate dimension estimate and Rosser main sum estimate.
The original upper_weights file is not imported or edited.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp558a
import LeanLab.KumchevLiu2007.Decomp558c
import LeanLab.KumchevLiu2007.Decomp506f

namespace LeanLab.KumchevLiu2007.Task558b

open Real Task506b Task506d Task506e Task558a
open scoped BigOperators Topology

/-- Page 13 display 44, the inverse local product on a half open prime band. -/
noncomputable def densityIntervalProduct (n : ℕ) (w v : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v), (1 - density n p)⁻¹

/-- Page 17 before display 58, the product with a strict upper prime cutoff. -/
noncomputable def strictProduct (X δ : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ ((Finset.range (⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ + 1)).filter Nat.Prime).filter
      (fun (p : ℕ) => (p : ℝ) < Real.exp (Real.log X ^ (1 - δ / 2))), (1 - density n p)

/-- Page 17 definition of g, all prime local factors are at least one half. -/
theorem density_prime_le_half (n p : ℕ) (hn : InH2 n) (hp : p.Prime) :
    density n p ≤ 1 / 2 := by
  by_cases h2 : p = 2
  · subst p; rw [density_two_of_InH2 n hn]; norm_num
  by_cases h3 : p = 3
  · subst p; rw [density_three_of_InH2 n hn]; norm_num
  have hp5 : 5 ≤ p := by
    have hp2 := hp.two_le
    have hp4 : p ≠ 4 := by intro h; subst p; norm_num at hp
    omega
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  exact (density_prime_le n p hp).trans ((div_le_iff₀ (by linarith)).mpr (by linarith))

/-- Page 13 strict and closed prime cutoffs differ by at most one prime. -/
theorem cutoff_complement_subset (z : ℝ) (hz : 0 ≤ z) :
    (((Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime).filter (fun (p : ℕ) => ¬ (p : ℝ) < z)) ⊆
      {⌊z⌋₊} := by
  intro p hp
  obtain ⟨hpT, hpn⟩ := Finset.mem_filter.mp hp
  have hple : p ≤ ⌊z⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hpT).1)
  have hfloor := Nat.floor_le hz
  have hpg : z ≤ (p : ℝ) := le_of_not_gt hpn
  have hpeq : p = ⌊z⌋₊ := by
    apply le_antisymm hple
    exact_mod_cast hfloor.trans hpg
  simpa using hpeq

/-- Page 13 Lemma 3.7, a strict prime product is at most twice the closed product. -/
theorem strict_product_le_twice_closed (z : ℝ) (hz : 0 ≤ z) (n : ℕ) (hn : InH2 n) :
    (∏ p ∈ ((Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime).filter (fun (p : ℕ) => (p : ℝ) < z),
      (1 - density n p)) ≤
      2 * ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - density n p) := by
  classical
  let T := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime
  let A := T.filter (fun (p : ℕ) => (p : ℝ) < z)
  let E := T.filter (fun (p : ℕ) => ¬ (p : ℝ) < z)
  have hprod : (∏ p ∈ A, (1 - density n p)) * (∏ p ∈ E, (1 - density n p)) =
      ∏ p ∈ T, (1 - density n p) := Finset.prod_filter_mul_prod_filter_not _ _ _
  have hA : 0 ≤ ∏ p ∈ A, (1 - density n p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpp := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact (sub_pos.mpr (density_prime_lt_one n p hn hpp)).le
  have hE : (1 / 2 : ℝ) ≤ ∏ p ∈ E, (1 - density n p) := by
    have hsub : E ⊆ {⌊z⌋₊} := cutoff_complement_subset z hz
    by_cases he : E = ∅
    · norm_num [he]
    · have hEq : E = {⌊z⌋₊} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hpEq := Finset.mem_singleton.mp (hsub hp)
        exact ⟨hpEq ▸ hp, fun q hq => Finset.mem_singleton.mp (hsub hq)⟩
      have hm : ⌊z⌋₊ ∈ E := by rw [hEq]; simp
      have hprime := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      simpa [hEq] using (show (1 / 2 : ℝ) ≤ 1 - density n ⌊z⌋₊ by
        linarith [density_prime_le_half n ⌊z⌋₊ hn hprime])
  change (∏ p ∈ A, (1 - density n p)) ≤ 2 * ∏ p ∈ T, (1 - density n p)
  nlinarith [mul_nonneg hA (sub_nonneg.mpr hE)]
/-- Page 17 before display 58, any fixed sieve ratio is eventually below log D over log z. -/
theorem weight_level_parameters (δ ε s : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hs : 0 < s) :
    ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧
      2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) ∧
      (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ Y X ε ^ (1 / 9 : ℝ) := by
  let θ : ℝ := 7 / 12 + ε / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have ha : 0 < δ / 2 := by linarith
  have hq : 0 < 1 - δ / 2 := by linarith
  have ht := ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop).eventually
    (Filter.eventually_ge_atTop (9 * s / θ))
  have hz := (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop hq).comp Real.tendsto_log_atTop)).eventually
      (Filter.eventually_ge_atTop (2 : ℝ))
  filter_upwards [ht, hz, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ)] with X ht hz hL hX
  have hXp : 0 < X := by linarith
  have hLp : 0 < Real.log X := by linarith
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hY1 : 1 ≤ Y X ε := Real.one_le_rpow hX hθ.le
  have hD1 : 1 ≤ Y X ε ^ (1 / 9 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  refine ⟨hD1, hz, ?_⟩
  have hm : Real.log X ^ (1 - δ / 2) * Real.log X ^ (δ / 2) = Real.log X := by
    rw [← Real.rpow_add hLp]
    ring_nf
    rw [Real.rpow_one]
  have hb : 9 * s ≤ θ * Real.log X ^ (δ / 2) :=
    by simpa [Function.comp_def, mul_comm] using (div_le_iff₀ hθ).mp ht
  have hmul := mul_le_mul_of_nonneg_left hb
    (Real.rpow_nonneg hLp.le (1 - δ / 2))
  have hexp : Real.log X ^ (1 - δ / 2) * s ≤ Real.log X * θ * (1 / 9 : ℝ) := by
    nlinarith [hm]
  rw [← Real.exp_mul, Real.rpow_def_of_pos hY, Y, Real.log_rpow hXp]
  apply Real.exp_le_exp.mpr
  dsimp [θ] at hexp
  nlinarith [hexp]

/-- Page 13 display 44, admissible local factors make the band product positive. -/
theorem densityIntervalProduct_pos (n : ℕ) (hn : InH2 n) (w v : ℝ) :
    0 < densityIntervalProduct n w v := by
  unfold densityIntervalProduct
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (density_prime_lt_one n p hn (Finset.mem_filter.mp hp).2.1))

/-- Page 13 display 44, each admissible inverse local factor is at least one. -/
theorem density_inverse_factor_one_le (n p : ℕ) (hn : InH2 n) (hp : p.Prime) :
    1 ≤ (1 - density n p)⁻¹ := by
  have hpos : 0 < 1 - density n p := sub_pos.mpr (density_prime_lt_one n p hn hp)
  simpa only [div_one, one_div] using one_div_le_one_div_of_le hpos
    (show 1 - density n p ≤ (1 : ℝ) by linarith [density_nonneg n p])

/-- Page 13 display 44, the inverse density product on every band is at least one. -/
theorem densityIntervalProduct_one_le (n : ℕ) (hn : InH2 n) (w v : ℝ) :
    1 ≤ densityIntervalProduct n w v := by
  unfold densityIntervalProduct
  apply Finset.one_le_prod₀
  intro p hp
  exact density_inverse_factor_one_le n p hn (Finset.mem_filter.mp hp).2.1

/-- Page 13 display 44 and Iwaniec page 198 Lemma 21, enlarging a prime
band increases its inverse density product. This supplies the elementary
monotonicity used in partial summation of weighted chain estimates. -/
theorem densityIntervalProduct_mono (n : ℕ) (hn : InH2 n) (w v w' v' : ℝ)
    (hw : w' ≤ w) (hv : v ≤ v') :
    densityIntervalProduct n w v ≤ densityIntervalProduct n w' v' := by
  classical
  unfold densityIntervalProduct
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hprange, hprime, hpw, hpv⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hprime, hw.trans hpw, hpv.trans_le hv⟩
    exact (Finset.mem_range.mp hprange).trans_le (Nat.succ_le_succ (Nat.floor_mono hv))
  · intro p hp
    exact (density_inverse_factor_one_le n p hn (Finset.mem_filter.mp hp).2.1).trans' (by norm_num)
  · intro p hp hnot
    exact density_inverse_factor_one_le n p hn (Finset.mem_filter.mp hp).2.1

/-- Page 17 display 58, the strict product has at most a factor two endpoint cost. -/
theorem strictProduct_le (X δ : ℝ) (n : ℕ) (hn : InH2 n) :
    strictProduct X δ n ≤ 2 * sieveProduct X δ n := by
  have h := strict_product_le_twice_closed (Real.exp (Real.log X ^ (1 - δ / 2)))
    (Real.exp_pos _).le n hn
  unfold strictProduct sieveProduct
  convert h using 1
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [← density_prime_eq n p (Finset.mem_filter.mp hp).2]

/-- Page 17 density comparison, the uniform dimension two majorant omits
primes two and three and uses the maximal root count at all other primes. -/
noncomputable def dimensionTwoProduct (w v : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
      (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v),
    if 5 ≤ p then (1 - 2 / ((p : ℝ) - 1))⁻¹ else 1

/-- Page 17 before display 58, local root counts reduce every admissible
density band product to the same numerical prime product. -/
theorem densityIntervalProduct_le (n : ℕ) (hn : InH2 n) (w v : ℝ) :
    densityIntervalProduct n w v ≤ dimensionTwoProduct w v := by
  classical
  unfold densityIntervalProduct dimensionTwoProduct
  apply Finset.prod_le_prod₀
  · intro p hp
    exact (inv_pos.mpr (sub_pos.mpr (density_prime_lt_one n p hn (Finset.mem_filter.mp hp).2.1))).le
  · intro p hp
    have hprime := (Finset.mem_filter.mp hp).2.1
    by_cases hp5 : 5 ≤ p
    · rw [ite_eq_left hp5]
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hmajor : 0 < 1 - 2 / ((p : ℝ) - 1) := by
        have hh : 2 / ((p : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
        linarith
      simpa only [one_div] using one_div_le_one_div_of_le hmajor
        (show 1 - 2 / ((p : ℝ) - 1) ≤ 1 - density n p by
          linarith [density_prime_le n p hprime])
    · rw [ite_eq_right hp5]
      have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hprime
      have hp2 := hprime.two_le
      have hcases : p = 2 ∨ p = 3 := by omega
      rcases hcases with rfl | rfl
      · simp [density_two_of_InH2 n hn]
      · simp [density_three_of_InH2 n hn]

/-- LEAF: Kumchev and Liu page 17 before display 58 and page 13 display 44.
The numerical dimension two prime majorant has a uniform relative logarithmic
product estimate, proved by the relative Mertens bands. It mentions no
sequence, residue class, model or sieve coefficients. -/
theorem numerical_dimension_two :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ w v : ℝ, 2 ≤ w → w < v →
      dimensionTwoProduct w v ≤ (Real.log v / Real.log w) ^ 2 *
        (1 + K / Real.log w) := by
  classical
  let K : ℝ := 128 * Real.exp (128 / Real.log 2)
  have hK : 2 ≤ K := by
    have he : 1 ≤ Real.exp (128 / Real.log 2) := Real.one_le_exp (by positivity)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro w v hw hwv
  let S := (Finset.range (⌊v⌋₊ + 1)).filter
    (fun (p : ℕ) => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < v)
  let f : ℕ → ℝ := fun p => if 5 ≤ p then (1 - 2 / ((p : ℝ) - 1))⁻¹ else 1
  have hf : ∀ p ∈ S, 0 < f p := by
    intro p hp
    dsimp [f]
    split_ifs with hp5
    · have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      apply inv_pos.mpr
      have hh : 2 / ((p : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      linarith
    · norm_num
  have hprod : 0 < dimensionTwoProduct w v := Finset.prod_pos hf
  have hlog : Real.log (dimensionTwoProduct w v) ≤
      2 * (Real.log (Real.log v) - Real.log (Real.log w)) + 128 / Real.log w := by
    change Real.log (∏ p ∈ S, f p) ≤ _
    rw [Real.log_prod (fun p hp => (hf p hp).ne')]
    have hterm : ∀ p ∈ S, Real.log (f p) ≤ 2 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹ := by
      intro p hp
      dsimp [f]
      split_ifs with hp5
      · simpa only [div_eq_mul_inv] using Task558c.log_majorant_factor p hp5
      · simp only [Real.log_one]
        positivity
    have hs := Finset.sum_le_sum hterm
    have he : (∑ p ∈ S, (2 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹)) =
        2 * Task558c.primeReciprocalBand w v + 16 * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
      unfold Task558c.primeReciprocalBand
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [he] at hs
    have hb := Task558c.primeReciprocalBand_bound w v hw hwv
    have hsq := Task558c.prime_square_band_bound w v hw hwv
    change (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤ 4 / Real.log w at hsq
    simp only [div_eq_mul_inv] at *
    linarith
  have hLw : 0 < Real.log w := Real.log_pos (by linarith)
  have hLv : 0 < Real.log v := Real.log_pos (by linarith)
  have hp : Real.exp (2 * (Real.log (Real.log v) - Real.log (Real.log w))) =
      (Real.log v / Real.log w) ^ 2 := by
    rw [← Real.log_div hLv.ne' hLw.ne', mul_comm, Real.exp_mul,
      Real.exp_log (div_pos hLv hLw), Real.rpow_two]
  have hv : dimensionTwoProduct w v ≤
      (Real.log v / Real.log w) ^ 2 * Real.exp (128 / Real.log w) := by
    calc
      _ = Real.exp (Real.log (dimensionTwoProduct w v)) := (Real.exp_log hprod).symm
      _ ≤ Real.exp (2 * (Real.log (Real.log v) - Real.log (Real.log w)) + 128 / Real.log w) :=
        Real.exp_le_exp.mpr hlog
      _ = _ := by rw [Real.exp_add, hp]
  exact hv.trans (mul_le_mul_of_nonneg_left
    (Task558c.exp_inverse_log_bound 128 w (by norm_num) hw) (sq_nonneg _))

/-- Page 17 before display 58 and page 13 display 44, the admissible local
density has dimension two. This follows from the proved numerical prime product bound. -/
theorem uniform_dimension_two :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ n : ℕ, InH2 n → ∀ w v : ℝ, 2 ≤ w → w < v →
      densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
        (1 + K / Real.log w) := by
  obtain ⟨K, hK, hprod⟩ := numerical_dimension_two
  exact ⟨K, hK, fun n hn w v hw hwv =>
    (densityIntervalProduct_le n hn w v).trans (hprod w v hw hwv)⟩

/-- LEAF: Iwaniec page 172 Theorem 1 and page 179 formulas 3.4 and 3.6.
For a fixed dimension constant choose a real prefix exponent and a fixed
sieve ratio. The main sum of the explicit coefficients is bounded by the strict
sieve product when the supplied dimension estimate holds. No upper divisor
inequality, coefficient bound, support assertion or large X limit is assumed.
The quantitative source step is Lemma 20 on pages 197 to 201 and the
conclusion formulas 9.1 and 9.2 on pages 201 and 202. -/
theorem rosser_main_of_dimension (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X B δ ε : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ Y X ε ^ (1 / 9 : ℝ) →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β) ≤
          C * strictProduct X δ n := by
  sorry

/-- Page 17 before display 58, the exact sealed upper_weights statement from
one strictly smaller analytic leaf. CONDITIONAL ON
rosser_main_of_dimension. The coefficient and
support bounds, endpoint factor and parameter reduction are proved. -/
theorem upper_weights_from_leaves (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, ∀ hn : InH2 n,
      ∃ μ : ℕ → ℝ, BoundingSieve.IsUpperMoebius μ ∧
        (∀ d ∈ (primeProduct X δ n).divisors, Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0) ∧
        (∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1) ∧
        (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n := by
  obtain ⟨K, hK, hdim⟩ := uniform_dimension_two
  obtain ⟨β, C, s, hβ, hC, hs, hmain⟩ := rosser_main_of_dimension K hK
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (weight_level_parameters δ ε s hδ hδ1 hε hs)
  refine ⟨2 * C, X0, by positivity, ?_⟩
  intro X hX n hn
  obtain ⟨hD, hz, hratio⟩ := hX0 X hX
  refine ⟨rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β, rosserWeight_upper _ _, ?_, ?_, ?_⟩
  · intro d hd hlarge
    exact rosserWeight_support _ β hβ hD d hlarge
  · intro d hd
    exact rosserWeight_abs_le_one _ β d
  · calc
      _ ≤ C * strictProduct X δ n := hmain X B δ ε n hn hz hratio
        (fun w v hw hwv hv => hdim n hn w v hw hwv)
      _ ≤ C * (2 * sieveProduct X δ n) := mul_le_mul_of_nonneg_left (strictProduct_le X δ n hn) hC.le
      _ = (2 * C) * sieveProduct X δ n := by ring

end LeanLab.KumchevLiu2007.Task558b

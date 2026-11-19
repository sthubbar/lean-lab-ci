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

/- ===== private helpers (WIP pass 2026-11-17) ===== -/

/-- The local factor product over the sieve support.  The split's leaf one
ranges over `(primeProduct X δ n).primeFactorsList.dedup.toFinset`, which is
that support; a support prime carries positive density and every strict-cutoff
prime outside it carries density zero, so the two products agree. -/
private theorem strictProduct_eq_prod_primeSupport (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n = ∏ p ∈ primeSupport X δ n, (1 - density n p) := by
  classical
  unfold strictProduct primeSupport
  symm
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    obtain ⟨hmem, hprime, hpz, hpos⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hprime⟩, hpz⟩
  · intro p hp hnot
    obtain ⟨hpT, hpz⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := (Finset.mem_filter.mp hpT).2
    have hzero : density n p = 0 := by
      have hnp : ¬ (0 < density n p) := fun hpos =>
        hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, hprime, hpz, hpos⟩)
      linarith [density_nonneg n p]
    rw [hzero, sub_zero]

/-- The prime factor set of the sifting product is the sieve support. -/
private theorem primeFactors_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactors = primeSupport X δ n := by
  classical
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    exact prime_mem_of_dvd_product X δ n p hp hdvd
  · intro hp
    refine ⟨(Finset.mem_filter.mp hp).2.1, Finset.dvd_prod_of_mem _ hp, ?_⟩
    exact (primeProduct_squarefree X δ n).ne_zero

/-- The distinct prime factors of the sifting product, as a finset, are the
sieve support: `primeFactors` is `primeFactorsList.toFinset`, so `dedup` is
harmless.  This is the index set of the split's leaf one. -/
private theorem primeFactorsList_dedup_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactorsList.dedup.toFinset = primeSupport X δ n := by
  rw [List.toFinset_dedup, Nat.toFinset_factors, primeFactors_primeProduct]

/-- Iwaniec page 179 formula 3.4 with the density weight: the Rosser main sum of
a `BoundingSieve` is the alternating sum over the distinct descending prime
sublists of its sifting product, each term carrying the product of the local
densities over the sublist. -/
private theorem mainSum_eq_sublists (s : BoundingSieve) (D β : ℝ) :
    s.mainSum (rosserWeight D β) =
      ((s.prodPrimes.primeFactorsList.dedup.reverse).sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t *
          ∏ p ∈ t.toFinset, s.nu p)).sum := by
  classical
  have hn : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  let L := s.prodPrimes.primeFactorsList.dedup.reverse
  have hLnodup : L.Nodup := List.nodup_reverse.mpr (List.nodup_dedup _)
  have hLsort : L.Pairwise (· ≥ ·) := List.pairwise_reverse.mpr
    ((Nat.isChain_primeFactorsList s.prodPrimes).pairwise.sublist (List.dedup_sublist _))
  have hLprime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp (List.mem_reverse.mp hp))
  have hLdvd : L.prod ∣ s.prodPrimes := by
    have hd := (List.dedup_sublist s.prodPrimes.primeFactorsList).prod_dvd_prod
    rw [Nat.prod_primeFactorsList hn] at hd
    simpa only [L, List.prod_reverse] using hd
  have hprops : ∀ t ∈ L.sublists.toFinset,
      (∀ p ∈ t, Nat.Prime p) ∧ t.Pairwise (· ≥ ·) ∧ t.Nodup := by
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    exact ⟨fun p hp => hLprime p (hsub.subset hp), hLsort.sublist hsub, hLnodup.sublist hsub⟩
  have hbij : (∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod) =
      ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d := by
    apply Finset.sum_bij (fun t _ => t.prod)
    · intro t ht
      obtain ⟨hp, hs, hnd⟩ := hprops t ht
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hsub.prod_dvd_prod.trans hLdvd, hn⟩,
          descending_prime_product_squarefree t hp hs hnd⟩
    · intro t ht u hu he
      obtain ⟨htp, hts, htnd⟩ := hprops t ht
      obtain ⟨hup, hus, hund⟩ := hprops u hu
      have htF := descending_prime_factorization t htp hts
      have huF := descending_prime_factorization u hup hus
      rw [he] at htF
      exact htF.symm.trans huF
    · intro d hd
      obtain ⟨hdiv, hdSq⟩ := Finset.mem_filter.mp hd
      have hdn : d ≠ 0 := (Nat.pos_of_mem_divisors hdiv).ne'
      have htnd : d.primeFactorsList.reverse.Nodup :=
        List.nodup_reverse.mpr ((Nat.squarefree_iff_nodup_primeFactorsList hdn).mp hdSq)
      have hts : d.primeFactorsList.reverse.Pairwise (· ≥ ·) :=
        List.pairwise_reverse.mpr (Nat.isChain_primeFactorsList d).pairwise
      have hsubset : d.primeFactorsList.reverse ⊆ L := by
        intro p hp
        apply List.mem_reverse.mpr
        apply List.mem_dedup.mpr
        exact (Nat.primeFactorsList_sublist_of_dvd (Nat.dvd_of_mem_divisors hdiv) hn).subset
          (List.mem_reverse.mp hp)
      have htL : List.Sublist d.primeFactorsList.reverse L :=
        List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htnd hsubset) hts hLsort
      refine ⟨d.primeFactorsList.reverse, List.mem_toFinset.mpr (List.mem_sublists.mpr htL), ?_⟩
      rw [List.prod_reverse, Nat.prod_primeFactorsList hdn]
    · intro t ht
      rfl
  have hfilter : (∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d) =
      ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnsq : ¬ Squarefree d := by simpa only [Finset.mem_filter, hd, true_and] using hnot
    rw [rosserWeight_not_squarefree D β d hnsq, zero_mul]
  have hterm : ∀ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod =
      (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p := by
    intro t ht
    obtain ⟨htp, hts, htnd⟩ := hprops t ht
    rw [rosserWeight_prod D β t htp hts htnd]
    have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
      have h := List.prod_toFinset (f := id) htnd
      simpa using h
    have hndid : ∏ p ∈ t.toFinset, s.nu p = s.nu (∏ p ∈ t.toFinset, p) :=
      (ArithmeticFunction.IsMultiplicative.map_prod_of_prime s.nu_mult t.toFinset
        (fun p hp => htp p (List.mem_toFinset.mp hp))).symm
    rw [hndid, hprod]
  calc s.mainSum (rosserWeight D β)
      = ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := rfl
    _ = ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d :=
        hfilter.symm
    _ = ∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod := hbij.symm
    _ = ∑ t ∈ L.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p :=
        Finset.sum_congr rfl hterm
    _ = _ := List.sum_toFinset _ (List.nodup_sublists.mpr hLnodup)

/-- LEAF: step one of the proof, the local product identity.  The strict
product below the close cutoff equals the product of the one minus local
factors taken over the distinct prime factors of the squarefree sieve product.
A prime outside the sieve support carries density zero, so its factor is one
on both sides and the two products agree.  This is an identity in the
definitions alone: it names no main sum, no level and no dimension estimate. -/
theorem strictProduct_eq_primeFactors_prod (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n =
      ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset, (1 - density n p) := by
  rw [strictProduct_eq_prod_primeSupport, primeFactorsList_dedup_primeProduct]

/-- LEAF: step two of the proof, the weighted divisor to chain identity.  The
main sum of the explicit weights over the divisors of the sieve product equals
the alternating sum of prefix products over the distinct prime sublists, each
sublist carrying its own local factor at the product of the sublist.  This is
the weighted form of the squarefree divisor change of variables, so it is an
identity and it mentions no inequality, no constant and no level condition. -/
theorem mainSum_eq_chain_sum (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β)
      = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod := by
  classical
  have h := mainSum_eq_sublists (sieveModel X B δ ε n hn) D β
  rw [show (sieveModel X B δ ε n hn).prodPrimes = primeProduct X δ n from rfl] at h
  rw [h]
  rw [← List.sum_toFinset _
    (List.nodup_sublists.mpr (List.nodup_reverse.mpr (List.nodup_dedup _)))]
  apply Finset.sum_congr rfl
  intro t ht
  have hnu : ∀ p : ℕ, (sieveModel X B δ ε n hn).nu p = density n p := fun p => rfl
  simp only [hnu]
  have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
  have hnd : t.Nodup :=
    (List.nodup_reverse.mpr (List.nodup_dedup _)).sublist hsub
  have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactorsList
      (List.mem_dedup.mp (List.mem_reverse.mp (hsub.subset hp)))
  have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
    have hh := List.prod_toFinset (f := id) hnd
    simpa using hh
  have hndid : ∏ p ∈ t.toFinset, density n p = density n t.prod := by
    rw [← hprod]
    exact (ArithmeticFunction.IsMultiplicative.map_prod_of_prime (density_isMultiplicative n)
      (f := densityFunction n) t.toFinset
      (fun p hp => hprime p (List.mem_toFinset.mp hp))).symm
  rw [hndid]

/- ===== fundamental lemma helpers for the chain main estimate (burst 20261117) ===== -/

private theorem nil_or_append (u : List ℕ) : u = [] ∨ ∃ l p, u = l ++ [p] := by
  rcases List.eq_nil_or_concat u with h | ⟨l, p, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l, p, by rw [h, List.concat_eq_append]⟩

private theorem sublists_sum_prod_map (h : ℕ → ℝ) (L : List ℕ) :
    (L.sublists.map (fun u => (u.map h).prod)).sum = (L.map (fun p => 1 + h p)).prod := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.sublists_concat, List.map_append, List.sum_append, List.map_map]
    have h2 : (List.map ((fun u => (u.map h).prod) ∘ fun x => x ++ [a]) l.sublists).sum
        = (l.sublists.map (fun u => (u.map h).prod)).sum * h a := by
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro u _
      simp
    rw [h2, ih, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring

private theorem prefixStop_binary (D β : ℝ) (l : List ℕ) :
    prefixStop D β l = 0 ∨ prefixStop D β l = 1 := by
  unfold prefixStop
  split_ifs
  · left; rfl
  · rcases prefixGate_binary D β l with h | h <;>
      rcases prefixRho_binary D β l.dropLast with h' | h' <;> rw [h, h'] <;> norm_num

/-- LEAF. Iwaniec page 179 formula 3.6, a coarse finite recurrence for
surviving even prefixes at beta nineteen. Each pair retains at least nine
tenths of the unused logarithmic level. This is a derived weak bound. -/
private theorem rho_even_log_bound (D : ℝ) (_hD : 0 < D) : ∀ (k : ℕ) (l : List ℕ),
    (∀ p ∈ l, 2 ≤ p) → l.Pairwise (· > ·) → l.length = 2 * k → prefixRho D 19 l = 1 →
    (9 / 10 : ℝ) ^ k * Real.log D ≤ Real.log D - Real.log (l.prod : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro l _ _ hlen _
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp
  | succ k ih =>
    intro l h2 hs hlen hrho
    rcases nil_or_append l with rfl | ⟨m, b, rfl⟩
    · rw [List.length_nil] at hlen; omega
    rcases nil_or_append m with rfl | ⟨l', a, rfl⟩
    · rw [List.length_append, List.length_nil, List.length_singleton] at hlen; omega
    have hlen' : l'.length = 2 * k := by
      simp only [List.length_append, List.length_singleton] at hlen; omega
    rw [prefixRho_append, prefixRho_append] at hrho
    have hr1 : prefixRho D 19 l' = 1 := by
      rcases prefixRho_binary D 19 l' with h | h
      · rw [h] at hrho; simp at hrho
      · exact h
    have hg1 : prefixGate D 19 (l' ++ [a]) = 1 := by
      rcases prefixGate_binary D 19 (l' ++ [a]) with h | h
      · rw [h] at hrho; simp at hrho
      · exact h
    have hP0 : 0 < (l'.prod : ℝ) := by
      have : 0 < l'.prod := List.prod_pos (fun x hx => by
        have := h2 x (by simp [hx]); omega)
      exact_mod_cast this
    have ha2 : 2 ≤ a := h2 a (by simp)
    have hb2 : 2 ≤ b := h2 b (by simp)
    have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hba : b < a := (List.pairwise_append.mp hs).2.2 a (by simp) b (by simp)
    have hlogba : Real.log (b:ℝ) ≤ Real.log (a:ℝ) :=
      Real.log_le_log hb0 (by exact_mod_cast hba.le)
    have hloga : 0 ≤ Real.log (a:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a))
    have hgate : Real.log (l'.prod:ℝ) + 20 * Real.log (a:ℝ) < Real.log D := by
      unfold prefixGate at hg1
      split_ifs at hg1 with hc
      · norm_num at hg1
      · have hodd : Odd (l' ++ [a]).length := by
          rw [List.length_append, List.length_singleton, hlen']; exact ⟨k, rfl⟩
        have hlt : ((l' ++ [a]).prod : ℝ) * (((l' ++ [a]).getLastD 1 : ℕ) : ℝ) ^ (19:ℝ) < D := by
          by_contra hcon
          exact hc ⟨hodd, not_lt.mp hcon⟩
        rw [List.getLastD_concat, List.prod_append, List.prod_singleton, Nat.cast_mul] at hlt
        have := Real.log_lt_log (mul_pos (mul_pos hP0 ha0) (Real.rpow_pos_of_pos ha0 _)) hlt
        rw [Real.log_mul (mul_pos hP0 ha0).ne' (Real.rpow_pos_of_pos ha0 _).ne',
          Real.log_mul hP0.ne' ha0.ne', Real.log_rpow ha0] at this
        linarith
    have ih' := ih l' (fun x hx => h2 x (by simp [hx]))
      ((List.pairwise_append.mp (List.pairwise_append.mp hs).1).1) hlen' hr1
    have hprod : Real.log (((l' ++ [a] ++ [b]).prod : ℕ) : ℝ)
        = Real.log (l'.prod:ℝ) + Real.log (a:ℝ) + Real.log (b:ℝ) := by
      rw [List.prod_append, List.prod_append, List.prod_singleton, List.prod_singleton,
        Nat.cast_mul, Nat.cast_mul, Real.log_mul (mul_pos hP0 ha0).ne' hb0.ne',
        Real.log_mul hP0.ne' ha0.ne']
    rw [hprod, pow_succ]
    linarith

private theorem stop_last_log_bound (D : ℝ) (hD : 0 < D) (u : List ℕ)
    (hu2 : ∀ p ∈ u, 2 ≤ p) (hsort : u.Pairwise (· > ·)) (hstop : prefixStop D 19 u ≠ 0) :
    ∃ k : ℕ, u.length = 2 * k + 1 ∧
      (9 / 10 : ℝ) ^ k * Real.log D ≤ 20 * Real.log ((u.getLastD 0 : ℕ) : ℝ) := by
  rcases nil_or_append u with rfl | ⟨l, p, rfl⟩
  · exact absurd (by simp [prefixStop]) hstop
  rw [prefixStop_append] at hstop
  have hg0 : prefixGate D 19 (l ++ [p]) = 0 := by
    rcases prefixGate_binary D 19 (l ++ [p]) with h | h
    · exact h
    · rw [h] at hstop; simp at hstop
  have hr1 : prefixRho D 19 l = 1 := by
    rcases prefixRho_binary D 19 l with h | h
    · rw [h] at hstop; simp at hstop
    · exact h
  unfold prefixGate at hg0
  split_ifs at hg0 with hc
  · obtain ⟨hodd, hle⟩ := hc
    obtain ⟨k, hk⟩ := hodd
    rw [List.length_append, List.length_singleton] at hk
    have hlen : l.length = 2 * k := by omega
    refine ⟨k, by rw [List.length_append, List.length_singleton, hlen], ?_⟩
    rw [List.getLastD_concat]
    rw [List.getLastD_concat, List.prod_append, List.prod_singleton, Nat.cast_mul] at hle
    have hP0 : 0 < (l.prod : ℝ) := by
      have : 0 < l.prod := List.prod_pos (fun x hx => by
        have := hu2 x (by simp [hx]); omega)
      exact_mod_cast this
    have hp2 : 2 ≤ p := hu2 p (by simp)
    have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have h1 := Real.log_le_log hD hle
    rw [Real.log_mul (mul_pos hP0 hp0).ne' (Real.rpow_pos_of_pos hp0 _).ne',
      Real.log_mul hP0.ne' hp0.ne', Real.log_rpow hp0] at h1
    have h2 := rho_even_log_bound D hD k l (fun x hx => hu2 x (by simp [hx]))
      (List.pairwise_append.mp hsort).1 hlen hr1
    linarith
  · norm_num at hg0

private theorem prod_map_const_mul (c : ℝ) (g : ℕ → ℝ) (u : List ℕ) :
    (u.map (fun q => c * g q)).prod = c ^ u.length * (u.map g).prod := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, List.map_cons, List.prod_cons,
      pow_succ]
    ring

private theorem one_add_four_le (x : ℝ) (_h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    1 + 4 * x ≤ ((1 - x)⁻¹) ^ 4 := by
  have ht : 0 < 1 - x := by linarith
  have key : (1 + 4 * x) * (1 - x) ^ 4 ≤ 1 := by
    have h3 : 0 ≤ 4 * (1 - x) ^ 3 + 3 * (1 - x) ^ 2 + 2 * (1 - x) + 1 := by
      have := pow_pos ht 3
      have := pow_pos ht 2
      linarith
    nlinarith [mul_nonneg (sq_nonneg x) h3]
  rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos ht 4)]
  exact key

private theorem sublists_sum_le_of_ge (g : ℕ → ℝ) (L : List ℕ) (hnd : L.Nodup)
    (hg0 : ∀ p ∈ L, 0 ≤ g p) (hg1 : ∀ p ∈ L, g p ≤ 1 / 2) (w n : ℕ)
    (U : Finset (List ℕ)) (hU : ∀ u ∈ U, u.Sublist L ∧ u.length = n ∧ ∀ q ∈ u, w ≤ q) :
    (4:ℝ) ^ n * ∑ u ∈ U, (u.map g).prod
      ≤ (∏ q ∈ L.toFinset.filter (fun q => w ≤ q), (1 - g q)⁻¹) ^ 4 := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, ∀ q, h q = if w ≤ q then 4 * g q else 0 :=
    ⟨_, fun _ => rfl⟩
  have hh0 : ∀ q ∈ L, 0 ≤ h q := by
    intro q hq
    rw [hh]
    split_ifs
    · have := hg0 q hq; linarith
    · exact le_rfl
  have e1 : (4:ℝ) ^ n * ∑ u ∈ U, (u.map g).prod = ∑ u ∈ U, (u.map h).prod := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    obtain ⟨_, hlen, hw⟩ := hU u hu
    have : u.map h = u.map (fun q => 4 * g q) := by
      apply List.map_congr_left
      intro q hq
      rw [hh, ite_eq_left (hw q hq)]
    rw [this, prod_map_const_mul, hlen]
  have e2 : ∑ u ∈ U, (u.map h).prod ≤ ∑ u ∈ L.sublists.toFinset, (u.map h).prod := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      exact List.mem_toFinset.mpr (List.mem_sublists.mpr (hU u hu).1)
    · intro u hu _
      apply List.prod_nonneg
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hh0 q ((List.mem_sublists.mp (List.mem_toFinset.mp hu)).subset hq)
  have e3 : ∑ u ∈ L.sublists.toFinset, (u.map h).prod = ∏ q ∈ L.toFinset, (1 + h q) := by
    rw [List.sum_toFinset _ (List.nodup_sublists.mpr hnd), sublists_sum_prod_map,
      List.prod_toFinset _ hnd]
  have e4 : ∏ q ∈ L.toFinset, (1 + h q)
      ≤ ∏ q ∈ L.toFinset, (if w ≤ q then ((1 - g q)⁻¹) ^ 4 else 1) := by
    apply Finset.prod_le_prod₀
    · intro q hq
      have := hh0 q (List.mem_toFinset.mp hq); linarith
    · intro q hq
      have hqL := List.mem_toFinset.mp hq
      rw [hh]
      split_ifs
      · exact one_add_four_le _ (hg0 q hqL) (hg1 q hqL)
      · simp
  have e5 : ∏ q ∈ L.toFinset, (if w ≤ q then ((1 - g q)⁻¹) ^ 4 else 1)
      = (∏ q ∈ L.toFinset.filter (fun q => w ≤ q), (1 - g q)⁻¹) ^ 4 := by
    rw [← Finset.prod_filter, Finset.prod_pow]
  rw [e1]
  exact (e2.trans (e3.le.trans e4)).trans e5.le

private theorem getLastD_mem_of_ne_nil (u : List ℕ) (h : u ≠ []) : u.getLastD 0 ∈ u := by
  rcases nil_or_append u with rfl | ⟨l, p, rfl⟩
  · exact absurd rfl h
  · rw [List.getLastD_concat]; simp

private theorem getLastD_le_of_pairwise (u : List ℕ) (h : u.Pairwise (· > ·)) :
    ∀ q ∈ u, u.getLastD 0 ≤ q := by
  rcases nil_or_append u with rfl | ⟨l, p, rfl⟩
  · intro q hq; simp at hq
  · intro q hq
    rw [List.getLastD_concat]
    rcases List.mem_append.mp hq with hq | hq
    · exact le_of_lt ((List.pairwise_append.mp h).2.2 q hq p (by simp))
    · rw [List.mem_singleton.mp hq]

/-- LEAF. Iwaniec pages 201 and 202, the bounded tail normalization used
for the weak constant conclusion. This is the exact finite geometric series
in the derived proof, not an evaluation of the paper's delay functions. -/
private theorem geom_quarter (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 / 4 : ℝ) * (1 / 2) ^ k = 1 / 2 - (1 / 2) * (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- LEAF. Iwaniec page 179 formula 4.1 and pages 197 to 201 Lemma 20.
A derived finite substitute for the bounded tail needed here. A dimension
two band majorant and a level logarithm at least T bound the normalized
stopped tail by one at beta nineteen. This does not assert the stronger
asymptotic functions of formulas 9.1 and 9.2. -/
private theorem stop_tail_le_one (D T : ℝ) (g : ℕ → ℝ) (L : List ℕ)
    (hL : L.Pairwise (· > ·)) (hL2 : ∀ p ∈ L, 2 ≤ p)
    (hg0 : ∀ p ∈ L, 0 ≤ g p) (hg1 : ∀ p ∈ L, g p ≤ 1 / 2)
    (hT : 0 < T) (hTD : T ≤ Real.log D) (hD : 0 < D)
    (hband : ∀ w ∈ L, ∏ q ∈ L.toFinset.filter (fun q => w ≤ q), (1 - g q)⁻¹
        ≤ (T / (20 * Real.log (w : ℝ))) ^ 2) :
    (L.sublists.map (fun u => prefixStop D 19 u * (u.map g).prod *
        ∏ q ∈ L.toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹)).sum ≤ 1 := by
  classical
  have hnd : L.Nodup := hL.imp (fun {a b} h => by omega)
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ,
      ∀ w, R w = ∏ q ∈ L.toFinset.filter (fun q => w ≤ q), (1 - g q)⁻¹ :=
    ⟨fun w => ∏ q ∈ L.toFinset.filter (fun q => w ≤ q), (1 - g q)⁻¹, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : List ℕ → ℝ,
      ∀ u, F u = prefixStop D 19 u * (u.map g).prod * R (u.getLastD 0) :=
    ⟨fun u => prefixStop D 19 u * (u.map g).prod * R (u.getLastD 0), fun _ => rfl⟩
  have hgoal : (L.sublists.map (fun u => prefixStop D 19 u * (u.map g).prod *
        ∏ q ∈ L.toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹)).sum
      = ∑ u ∈ L.sublists.toFinset, F u := by
    rw [List.sum_toFinset _ (List.nodup_sublists.mpr hnd)]
    congr 1
    apply List.map_congr_left
    intro u _
    rw [hF, hR]
  rw [hgoal]
  have hR0 : ∀ w, 0 ≤ R w := by
    intro w
    rw [hR]
    apply Finset.prod_nonneg
    intro q hq
    have hqL := List.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    have := hg1 q hqL
    exact inv_nonneg.mpr (by linarith)
  have hbandR : ∀ w ∈ L, R w ≤ (T / (20 * Real.log (w : ℝ))) ^ 2 := by
    intro w hw
    rw [hR]
    exact hband w hw
  have hS : ∀ u ∈ L.sublists.toFinset, u.Sublist L :=
    fun u hu => List.mem_sublists.mp (List.mem_toFinset.mp hu)
  have hfact : ∀ u : List ℕ, u.Sublist L → prefixStop D 19 u ≠ 0 →
      prefixStop D 19 u = 1 ∧ u.getLastD 0 ∈ u ∧
        ∃ k : ℕ, u.length = 2 * k + 1 ∧ R (u.getLastD 0) ≤ ((10 / 9 : ℝ) ^ k) ^ 2 := by
    intro u hsub hstop
    have hu2 : ∀ p ∈ u, 2 ≤ p := fun p hp => hL2 p (hsub.subset hp)
    obtain ⟨k, hk, hlog⟩ := stop_last_log_bound D hD u hu2 (hL.sublist hsub) hstop
    have hne : u ≠ [] := by
      intro h
      have h' := hk
      rw [h, List.length_nil] at h'
      omega
    have hmem : u.getLastD 0 ∈ u := getLastD_mem_of_ne_nil u hne
    have hpL := hsub.subset hmem
    have hp2 : (2:ℝ) ≤ ((u.getLastD 0 : ℕ) : ℝ) := by exact_mod_cast hL2 _ hpL
    have hlogp : 0 < Real.log ((u.getLastD 0 : ℕ) : ℝ) := Real.log_pos (by linarith)
    refine ⟨(prefixStop_binary D 19 u).resolve_left hstop, hmem, k, hk,
      (hbandR _ hpL).trans ?_⟩
    have hpow : (10 / 9 : ℝ) ^ k * (9 / 10) ^ k = 1 := by rw [← mul_pow]; norm_num
    have h9 : 0 ≤ (9 / 10 : ℝ) ^ k := by positivity
    have h10 : 0 ≤ (10 / 9 : ℝ) ^ k := by positivity
    have hT' : (9 / 10 : ℝ) ^ k * T ≤ 20 * Real.log ((u.getLastD 0 : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_left hTD h9).trans hlog
    have hT2 : T ≤ (10 / 9 : ℝ) ^ k * (20 * Real.log ((u.getLastD 0 : ℕ) : ℝ)) := by
      calc T = (10 / 9 : ℝ) ^ k * ((9 / 10) ^ k * T) := by rw [← mul_assoc, hpow, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hT' h10
    have h20 : 0 < 20 * Real.log ((u.getLastD 0 : ℕ) : ℝ) := by linarith
    apply pow_le_pow_left₀ (div_nonneg hT.le h20.le)
    rw [div_le_iff₀ h20]
    exact hT2
  have h1 : ∑ u ∈ L.sublists.toFinset, F u
      = ∑ u ∈ L.sublists.toFinset.filter (fun u => prefixStop D 19 u ≠ 0), F u := by
    symm
    apply Finset.sum_filter_of_ne
    intro u _ hne hz
    apply hne
    rw [hF, hz]
    ring
  have h2 : ∑ u ∈ L.sublists.toFinset.filter (fun u => prefixStop D 19 u ≠ 0), F u
      = ∑ k ∈ Finset.range (L.length + 1),
          ∑ u ∈ (L.sublists.toFinset.filter (fun u => prefixStop D 19 u ≠ 0)).filter
            (fun u => (u.length - 1) / 2 = k), F u := by
    symm
    refine Finset.sum_fiberwise_of_maps_to (g := fun u : List ℕ => (u.length - 1) / 2) ?_ F
    intro u hu
    have hsub := hS u (Finset.mem_filter.mp hu).1
    have hle := hsub.length_le
    show (u.length - 1) / 2 ∈ Finset.range (L.length + 1)
    rw [Finset.mem_range]
    omega
  have hkb : ∀ k ∈ Finset.range (L.length + 1),
      ∑ u ∈ (L.sublists.toFinset.filter (fun u => prefixStop D 19 u ≠ 0)).filter
            (fun u => (u.length - 1) / 2 = k), F u ≤ (1 / 4 : ℝ) * (1 / 2) ^ k := by
    intro k _
    obtain ⟨U, hUdef⟩ : ∃ U : Finset (List ℕ),
        U = (L.sublists.toFinset.filter (fun u => prefixStop D 19 u ≠ 0)).filter
            (fun u => (u.length - 1) / 2 = k) := ⟨_, rfl⟩
    rw [← hUdef]
    have hUprop : ∀ u ∈ U, u.Sublist L ∧ prefixStop D 19 u = 1 ∧ u.getLastD 0 ∈ u ∧
        u.length = 2 * k + 1 ∧ R (u.getLastD 0) ≤ ((10 / 9 : ℝ) ^ k) ^ 2 := by
      intro u hu
      simp only [hUdef, Finset.mem_filter] at hu
      obtain ⟨⟨huS, hstop⟩, hK⟩ := hu
      have hsub := hS u huS
      obtain ⟨h1', hmem, k', hk', hRk⟩ := hfact u hsub hstop
      have hkk : k' = k := by rw [hk'] at hK; omega
      rw [hkk] at hk' hRk
      exact ⟨hsub, h1', hmem, hk', hRk⟩
    rcases U.eq_empty_or_nonempty with hUe | hUne
    · rw [hUe, Finset.sum_empty]; positivity
    obtain ⟨us, hus, hmin⟩ := Finset.exists_min_image U (fun u => u.getLastD 0) hUne
    obtain ⟨w, hw⟩ : ∃ w : ℕ, w = us.getLastD 0 := ⟨_, rfl⟩
    have hRw : R w ≤ ((10 / 9 : ℝ) ^ k) ^ 2 := by
      rw [hw]; exact (hUprop us hus).2.2.2.2
    have hA := sublists_sum_le_of_ge g L hnd hg0 hg1 w (2 * k + 1) U (by
      intro u hu
      obtain ⟨hsub, _, _, hlen, _⟩ := hUprop u hu
      refine ⟨hsub, hlen, fun q hq => ?_⟩
      rw [hw]
      exact (hmin u hu).trans (getLastD_le_of_pairwise u (hL.sublist hsub) q hq))
    have hA' : (4:ℝ) ^ (2 * k + 1) * ∑ u ∈ U, (u.map g).prod ≤ (R w) ^ 4 := by
      rw [hR]; exact hA
    have hGnn : ∀ u ∈ U, 0 ≤ (u.map g).prod := by
      intro u hu
      apply List.prod_nonneg
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hg0 q ((hUprop u hu).1.subset hq)
    have hX0 : 0 ≤ ∑ u ∈ U, (u.map g).prod := Finset.sum_nonneg hGnn
    have hsumle : ∑ u ∈ U, F u ≤ ((10 / 9 : ℝ) ^ k) ^ 2 * ∑ u ∈ U, (u.map g).prod := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨hsub, h1', _, _, hRk⟩ := hUprop u hu
      rw [hF, h1', one_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hRk (hGnn u hu)
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (10 / 9 : ℝ) ^ k := ⟨_, rfl⟩
    rw [← ha] at hsumle hRw
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ u ∈ U, (u.map g).prod := ⟨_, rfl⟩
    rw [← hX] at hsumle hA' hX0
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have ha10 : a ^ 10 ≤ 8 ^ k := by
      rw [ha, ← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by norm_num) k
    have h42 : (4:ℝ) ^ 2 = 16 := by norm_num
    have h4 : (4:ℝ) ^ (2 * k + 1) = 4 * 16 ^ k := by
      rw [pow_succ, pow_mul, h42, mul_comm]
    have h16 : (1 / 2 : ℝ) ^ k * 16 ^ k = 8 ^ k := by rw [← mul_pow]; norm_num
    have hA4 : (R w) ^ 4 ≤ (a ^ 2) ^ 4 := pow_le_pow_left₀ (hR0 w) hRw 4
    have hmain : a ^ 2 * X * (4 * 16 ^ k) ≤ (1 / 4 : ℝ) * (1 / 2) ^ k * (4 * 16 ^ k) := by
      have e1 : (1 / 4 : ℝ) * (1 / 2) ^ k * (4 * 16 ^ k) = 8 ^ k := by rw [← h16]; ring
      have e2 : a ^ 2 * X * (4 * 16 ^ k) = a ^ 2 * (4 ^ (2 * k + 1) * X) := by rw [h4]; ring
      rw [e1, e2]
      calc a ^ 2 * (4 ^ (2 * k + 1) * X) ≤ a ^ 2 * (a ^ 2) ^ 4 :=
            mul_le_mul_of_nonneg_left (hA'.trans hA4) (by positivity)
        _ = a ^ 10 := by ring
        _ ≤ 8 ^ k := ha10
    exact hsumle.trans (le_of_mul_le_mul_right hmain (by positivity))
  rw [h1, h2]
  calc _ ≤ ∑ k ∈ Finset.range (L.length + 1), (1 / 4 : ℝ) * (1 / 2) ^ k :=
        Finset.sum_le_sum hkb
    _ = 1 / 2 - (1 / 2) * (1 / 2) ^ (L.length + 1) := geom_quarter _
    _ ≤ 1 := by
        have : (0:ℝ) ≤ (1 / 2) ^ (L.length + 1) := by positivity
        linarith

private theorem chain_term_step (D β : ℝ) (g : ℕ → ℝ) (t : List ℕ) (p : ℕ) :
    (-1 : ℝ) ^ (t ++ [p]).length * prefixRho D β (t ++ [p]) * ((t ++ [p]).map g).prod =
      -(g p) * ((-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod) +
        prefixStop D β (t ++ [p]) * ((t ++ [p]).map g).prod := by
  rw [prefixRho_append, prefixStop_append]
  have hG : ((t ++ [p]).map g).prod = (t.map g).prod * g p := by simp
  have hlen : (t ++ [p]).length = t.length + 1 := by simp
  rw [hG]
  rcases prefixGate_binary D β (t ++ [p]) with h | h
  · have ho : Odd (t ++ [p]).length := by
      unfold prefixGate at h
      split_ifs at h with h'
      · exact h'.1
      · norm_num at h
    have he : Even t.length := by
      simp only [List.length_append, List.length_singleton, Nat.odd_iff] at ho
      rw [Nat.even_iff]
      omega
    rw [h, hlen, pow_succ, he.neg_one_pow]
    ring
  · rw [h, hlen, pow_succ]
    ring

private theorem chain_alg (a P0 S0 S : ℝ) (h : a * P0 ≠ 0) :
    a * (P0 * (1 + S0)) + S = a * P0 * (1 + (S0 + (a * P0)⁻¹ * S)) := by
  have h1 := mul_inv_cancel₀ h
  linear_combination (-S) * h1

/-- LEAF. Iwaniec pages 178 and 179 formulas 3.1 and 4.1.
The exact weighted Buchstab identity for all stopped descending prefixes.
The inverse band product normalizes each stop by the full sieve product. -/
private theorem chain_buchstab (D β : ℝ) (g : ℕ → ℝ) (L : List ℕ)
    (hL : L.Pairwise (· > ·)) (hg : ∀ p ∈ L, g p ≠ 1) :
    (L.sublists.map (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod)).sum =
      (∏ p ∈ L.toFinset, (1 - g p)) *
        (1 + (L.sublists.map (fun u => prefixStop D β u * (u.map g).prod *
          ∏ q ∈ L.toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹)).sum) := by
  induction L using List.reverseRecOn with
  | nil => simp [prefixRho_nil, prefixStop]
  | append_singleton L0 p ih =>
    obtain ⟨hL0, -, hlt⟩ := List.pairwise_append.mp hL
    have hp : ∀ a ∈ L0, p < a := fun a ha => hlt a ha p (by simp)
    have hpn : p ∉ L0.toFinset := by
      intro h
      exact lt_irrefl p (hp p (List.mem_toFinset.mp h))
    have hfin : (L0 ++ [p]).toFinset = insert p L0.toFinset := by
      ext x
      simp
    have ih' := ih hL0 (fun q hq => hg q (by simp [hq]))
    have hP : (∏ q ∈ (L0 ++ [p]).toFinset, (1 - g q)) =
        (1 - g p) * ∏ q ∈ L0.toFinset, (1 - g q) := by
      rw [hfin, Finset.prod_insert hpn]
    have hPne : (∏ q ∈ (L0 ++ [p]).toFinset, (1 - g q)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      exact sub_ne_zero.mpr (Ne.symm (hg q (List.mem_toFinset.mp hq)))
    have hLHS : ((L0 ++ [p]).sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod)).sum =
        (1 - g p) * (L0.sublists.map
          (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod)).sum +
        (L0.sublists.map
          (fun t => prefixStop D β (t ++ [p]) * ((t ++ [p]).map g).prod)).sum := by
      rw [List.sublists_concat, List.map_append, List.sum_append, List.map_map]
      have hc : List.map ((fun t : List ℕ =>
            (-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod) ∘ fun x => x ++ [p])
            L0.sublists =
          L0.sublists.map (fun t =>
            -(g p) * ((-1 : ℝ) ^ t.length * prefixRho D β t * (t.map g).prod) +
              prefixStop D β (t ++ [p]) * ((t ++ [p]).map g).prod) :=
        List.map_congr_left (fun t _ => chain_term_step D β g t p)
      rw [hc, List.sum_map_add, List.sum_map_mul_left]
      ring
    have hR1 : L0.sublists.map (fun u => prefixStop D β u * (u.map g).prod *
          ∏ q ∈ (L0 ++ [p]).toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹) =
        L0.sublists.map (fun u => prefixStop D β u * (u.map g).prod *
          ∏ q ∈ L0.toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹) := by
      apply List.map_congr_left
      intro u hu
      by_cases hu0 : u = []
      · subst hu0
        simp [prefixStop]
      · have hmem : u.getLastD 0 ∈ L0 := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hu0]
          exact (List.mem_sublists.mp hu).subset (List.getLast_mem hu0)
        have hf : (L0 ++ [p]).toFinset.filter (fun q => u.getLastD 0 ≤ q) =
            L0.toFinset.filter (fun q => u.getLastD 0 ≤ q) := by
          rw [hfin, Finset.filter_insert, ite_eq_right_of_eq_false (h := eq_false (not_le.mpr (hp _ hmem)))]
        rw [hf]
    have hR2 : ∀ t : List ℕ,
        (∏ q ∈ (L0 ++ [p]).toFinset.filter (fun q => (t ++ [p]).getLastD 0 ≤ q), (1 - g q)⁻¹) =
          (∏ q ∈ (L0 ++ [p]).toFinset, (1 - g q))⁻¹ := by
      intro t
      rw [List.getLastD_concat, Finset.filter_true_of_mem, Finset.prod_inv_distrib]
      intro q hq
      rcases List.mem_append.mp (List.mem_toFinset.mp hq) with h | h
      · exact (hp q h).le
      · exact (List.mem_singleton.mp h).ge
    have hRsum : ((L0 ++ [p]).sublists.map (fun u => prefixStop D β u * (u.map g).prod *
          ∏ q ∈ (L0 ++ [p]).toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹)).sum =
        (L0.sublists.map (fun u => prefixStop D β u * (u.map g).prod *
          ∏ q ∈ L0.toFinset.filter (fun q => u.getLastD 0 ≤ q), (1 - g q)⁻¹)).sum +
        (∏ q ∈ (L0 ++ [p]).toFinset, (1 - g q))⁻¹ * (L0.sublists.map
          (fun t => prefixStop D β (t ++ [p]) * ((t ++ [p]).map g).prod)).sum := by
      rw [List.sublists_concat, List.map_append, List.sum_append, List.map_map, hR1,
        ← List.sum_map_mul_left]
      congr 2
      apply List.map_congr_left
      intro t _
      rw [Function.comp_apply, hR2 t]
      ring
    rw [hLHS, hRsum, ih', hP]
    exact chain_alg _ _ _ _ (hP ▸ hPne)

/-- LEAF: step three of the proof, the chain main estimate.  For the dimension
constant it chooses a real exponent at least one, a positive constant and a
positive level exponent, and then the alternating chain sum of prefix products
over the distinct prime sublists is at most the constant times the product of
one minus the local factors, uniformly in the level, whenever the level
exponent dominates the cutoff, the cutoff is at least two, and the band
estimate for the inverse local product holds below the cutoff.  This is one
inequality about the chain sum: it carries no sieve model, no sequence, no B
and no upper divisor input. -/
theorem chain_sum_le_support_prod (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X δ D : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ D →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
            (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod) ≤
          C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
            (1 - density n p) := by
  classical
  refine ⟨19, 2, 20 * (1 + 2 * K), by norm_num, by norm_num, by positivity, ?_⟩
  intro X δ D n hn hz hlev hband
  have hzpos : (0 : ℝ) < Real.exp (Real.log X ^ (1 - δ / 2)) := Real.exp_pos _
  have hlogz : 0 < Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) :=
    Real.log_pos (by linarith)
  have hLnodup : ((primeProduct X δ n).primeFactorsList.dedup.reverse).Nodup :=
    List.nodup_reverse.mpr (List.nodup_dedup _)
  have hLsort : ((primeProduct X δ n).primeFactorsList.dedup.reverse).Pairwise (· ≥ ·) :=
    List.pairwise_reverse.mpr
      ((Nat.isChain_primeFactorsList (primeProduct X δ n)).pairwise.sublist
        (List.dedup_sublist _))
  have hLgt : ((primeProduct X δ n).primeFactorsList.dedup.reverse).Pairwise (· > ·) :=
    (hLsort.and hLnodup).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)
  have hmem : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse,
      p ∈ primeSupport X δ n := by
    intro p hp
    rw [← primeFactorsList_dedup_primeProduct X δ n, List.mem_toFinset]
    exact List.mem_reverse.mp hp
  have hprime : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse, Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp (hmem p hp)).2.1
  have hlt : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse,
      (p : ℝ) < Real.exp (Real.log X ^ (1 - δ / 2)) :=
    fun p hp => (Finset.mem_filter.mp (hmem p hp)).2.2.1
  have hL2 : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse, 2 ≤ p :=
    fun p hp => (hprime p hp).two_le
  have hg0 : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse, 0 ≤ density n p :=
    fun p _ => density_nonneg n p
  have hg1 : ∀ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse,
      density n p ≤ 1 / 2 :=
    fun p hp => density_prime_le_half n p hn (hprime p hp)
  have hK0 : (0 : ℝ) < 1 + 2 * K := by linarith
  have hT : 0 < 20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) := by
    positivity
  have hpowpos : 0 < Real.exp (Real.log X ^ (1 - δ / 2)) ^ (20 * (1 + 2 * K)) :=
    Real.rpow_pos_of_pos hzpos _
  have hD : 0 < D := lt_of_lt_of_le hpowpos hlev
  have hTD : 20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) ≤
      Real.log D := by
    rw [← Real.log_rpow hzpos]
    exact Real.log_le_log hpowpos hlev
  have hbandL : ∀ w ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse,
      ∏ q ∈ ((primeProduct X δ n).primeFactorsList.dedup.reverse).toFinset.filter
          (fun q => w ≤ q), (1 - density n q)⁻¹ ≤
        (20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) /
          (20 * Real.log (w : ℝ))) ^ 2 := by
    intro w hw
    have hw2 : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hL2 w hw
    have hlogw : 1 / 2 ≤ Real.log (w : ℝ) := by
      have h2 : Real.log 2 ≤ Real.log (w : ℝ) := Real.log_le_log (by norm_num) hw2
      have := Real.log_two_gt_d9
      linarith
    have hlogwpos : 0 < Real.log (w : ℝ) := by linarith
    have h1 : ∏ q ∈ ((primeProduct X δ n).primeFactorsList.dedup.reverse).toFinset.filter
          (fun q => w ≤ q), (1 - density n q)⁻¹ ≤
        densityIntervalProduct n (w : ℝ) (Real.exp (Real.log X ^ (1 - δ / 2))) := by
      unfold densityIntervalProduct
      apply Finset.prod_le_prod_of_subset_of_one_le₀
      · intro q hq
        obtain ⟨hqL, hwq⟩ := Finset.mem_filter.mp hq
        have hqL' := List.mem_toFinset.mp hqL
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hprime q hqL', ?_, hlt q hqL'⟩
        · exact Nat.lt_succ_of_le (Nat.le_floor (hlt q hqL').le)
        · exact_mod_cast hwq
      · intro q hq
        obtain ⟨hqL, -⟩ := Finset.mem_filter.mp hq
        exact (density_inverse_factor_one_le n q hn
          (hprime q (List.mem_toFinset.mp hqL))).trans' (by norm_num)
      · intro q hq _
        exact density_inverse_factor_one_le n q hn (Finset.mem_filter.mp hq).2.1
    have h2 := hband (w : ℝ) (Real.exp (Real.log X ^ (1 - δ / 2))) hw2 (hlt w hw) le_rfl
    have hKw : K / Real.log (w : ℝ) ≤ 2 * K := by
      rw [div_le_iff₀ hlogwpos]
      nlinarith
    have hratio : 0 ≤ Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) / Real.log (w : ℝ) :=
      div_nonneg hlogz.le hlogwpos.le
    have h3 : (Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) / Real.log (w : ℝ)) ^ 2 *
          (1 + K / Real.log (w : ℝ)) ≤
        (20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) /
          (20 * Real.log (w : ℝ))) ^ 2 := by
      have he : 20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) /
          (20 * Real.log (w : ℝ)) =
          (1 + 2 * K) * (Real.log (Real.exp (Real.log X ^ (1 - δ / 2))) / Real.log (w : ℝ)) := by
        field_simp
      rw [he, mul_pow, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    exact h1.trans (h2.trans h3)
  have hid := chain_buchstab D 19 (density n)
    ((primeProduct X δ n).primeFactorsList.dedup.reverse) hLgt
    (fun p hp => by have := hg1 p hp; linarith)
  have htail := stop_tail_le_one D
    (20 * (1 + 2 * K) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2)))) (density n)
    ((primeProduct X δ n).primeFactorsList.dedup.reverse) hLgt hL2 hg0 hg1 hT hTD hD hbandL
  have hsum : (∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
        (-1 : ℝ) ^ t.length * prefixRho D 19 t * density n t.prod) =
      (((primeProduct X δ n).primeFactorsList.dedup.reverse).sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D 19 t * (t.map (density n)).prod)).sum := by
    rw [← List.sum_toFinset _ (List.nodup_sublists.mpr hLnodup)]
    apply Finset.sum_congr rfl
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    have hnd : t.Nodup := hLnodup.sublist hsub
    have htprime : ∀ p ∈ t, Nat.Prime p := fun p hp => hprime p (hsub.subset hp)
    have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
      have hh := List.prod_toFinset (f := id) hnd
      simpa using hh
    have hndid : ∏ p ∈ t.toFinset, density n p = density n t.prod := by
      rw [← hprod]
      exact (ArithmeticFunction.IsMultiplicative.map_prod_of_prime (density_isMultiplicative n)
        (f := densityFunction n) t.toFinset
        (fun p hp => htprime p (List.mem_toFinset.mp hp))).symm
    rw [← hndid, List.prod_toFinset _ hnd]
  have hfin : (primeProduct X δ n).primeFactorsList.dedup.toFinset =
      ((primeProduct X δ n).primeFactorsList.dedup.reverse).toFinset :=
    List.toFinset_reverse.symm
  have hW : 0 ≤ ∏ p ∈ ((primeProduct X δ n).primeFactorsList.dedup.reverse).toFinset,
      (1 - density n p) := by
    apply Finset.prod_nonneg
    intro p hp
    have := hg1 p (List.mem_toFinset.mp hp)
    linarith
  rw [hsum, hid, hfin, mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith) hW

/-- LEAF: Iwaniec page 172 Theorem 1 and page 179 formulas 3.4 and 3.6.
For a fixed dimension constant choose a real prefix exponent and a fixed
sieve ratio. The main sum of the explicit coefficients is bounded by the strict
sieve product when the supplied dimension estimate holds. No upper divisor
inequality, coefficient bound, support assertion or large X limit is assumed.
The quantitative source step is Lemma 20 on pages 197 to 201 and the
conclusion formulas 9.1 and 9.2 on pages 201 and 202.
The proof below uses the coarser finite fundamental lemma already proved in
the lab. It gives beta nineteen and constant two from the exact Buchstab
identity and a geometric stopped tail bound, without assuming the stronger
asymptotic estimates or their delay functions. -/
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
  obtain ⟨β, C, s, hβ, hC, hs, hcore⟩ := chain_sum_le_support_prod K hK
  refine ⟨β, C, s, hβ, hC, hs, ?_⟩
  intro X B δ ε n hn hz hlev hband
  calc
    (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β)
        = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
              (-1 : ℝ) ^ t.length * prefixRho (Y X ε ^ (1 / 9 : ℝ)) β t *
                density n t.prod :=
          mainSum_eq_chain_sum X B δ ε (Y X ε ^ (1 / 9 : ℝ)) β n hn
    _ ≤ C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
          (1 - density n p) :=
          hcore X δ (Y X ε ^ (1 / 9 : ℝ)) n hn hz hlev hband
    _ = C * strictProduct X δ n := by rw [strictProduct_eq_primeFactors_prod]

/-- Page 17 before display 58, the exact sealed upper_weights statement from
the proved explicit Rosser main estimate. The coefficient and
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

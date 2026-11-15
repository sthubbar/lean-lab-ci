/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, pages 194 to 196.
Independent supply for the exceptional arc leaf.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570a

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a

namespace LeanLab.Hathi2021.Decomp570b

/-- Pages 194 and 195. The absolute product before the factor G. -/
noncomputable def baseNorm (n₁ n₂ : ℕ) (α : ℝ × ℝ) : ℝ :=
  ‖S n₁ n₁ α.1‖ * ‖T n₁ n₁ α.1‖ ^ 2 *
    ‖S n₁ n₂ α.2‖ * ‖T n₁ n₂ α.2‖ ^ 2

/-- Page 194. One of the two minor coordinate strips inside the unit square
and the exceptional set. The Boolean true selects the first coordinate. -/
noncomputable def minorStrip (n₁ n₂ : ℕ) (first : Bool) : Set (ℝ × ℝ) :=
  (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ exceptional n₁ ∩
    {α | if first then α.1 ∉ majorOne n₁ n₁ else α.2 ∉ majorOne n₁ n₂}

/-- Pages 194 to 196. The absolute mass of one minor coordinate strip,
without the power 82 factor of G. -/
noncomputable def stripMass (n₁ n₂ : ℕ) (first : Bool) : ℝ :=
  ∫ α in minorStrip n₁ n₂ first, baseNorm n₁ n₂ α

/-- Page 195. The prime linear second moment. -/
noncomputable def primeSecondMoment (n₁ n : ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, ‖S n₁ n x‖ ^ 2

/-- Page 195. The prime square fourth moment. -/
noncomputable def primeSquareFourthMoment (n₁ n : ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, ‖T n₁ n x‖ ^ 4

/-- Page 195. A translated one dimensional large G slice. -/
noncomputable def exceptionalSlice (n₁ : ℕ) (t : ℝ) : Set ℝ :=
  Set.Icc 0 1 ∩ {x | (PairLinnik.lam : ℝ) * L n₁ ≤ ‖G n₁ (x + t)‖}

/-- LEAF. Hu page 195, Hu and Liu reference 2 Lemma 2.5.
This is the pointwise prime square estimate on a minor arc.
The common logarithmic cutoff is retained. -/
theorem minor_prime_square_sup (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → (n₁ : ℝ) ≤ C * n → ∀ x : ℝ,
      x ∉ majorOne n₁ n → ‖T n₁ n x‖ ≤ K * (n : ℝ) ^ (7 / 16 + ε : ℝ) := by
  sorry

/-- Private helper: conjugation inverts the additive character. -/
private lemma e_conj (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- Private helper: the squared modulus of `S` as a double sum of characters. -/
private lemma S_mul_conj (n₁ n : ℕ) (x : ℝ) :
    S n₁ n x * (starRingEnd ℂ) (S n₁ n x) =
      ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)),
        ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧ cutoff n₁ n < (q : ℝ)),
          ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
  unfold S
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  have hconj : (starRingEnd ℂ) ((Real.log q : ℂ) * e (↑q * x)) =
      (Real.log q : ℂ) * e (-(↑q * x)) := by
    rw [map_mul, e_conj, Complex.conj_ofReal]
  rw [hconj]
  have harg : (↑p * x) + -(↑q * x) = (↑((p : ℤ) - (q : ℤ)) : ℝ) * x := by
    push_cast
    ring
  calc (Real.log p : ℂ) * e (↑p * x) * ((Real.log q : ℂ) * e (-(↑q * x)))
      = ((Real.log p * Real.log q : ℝ) : ℂ) * (e (↑p * x) * e (-(↑q * x))) := by
        push_cast
        ring
    _ = ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑p * x) + -(↑q * x)) := by rw [← e_add]
    _ = ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
        rw [harg]

/-- Private helper: a finite character sum integrates to its zero mode. -/
private lemma integral_e_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℤ) :
    (∫ x in Set.Icc (0 : ℝ) 1, ∑ i ∈ s, w i * e ((m i : ℝ) * x)) =
      ∑ i ∈ s, if m i = 0 then w i else 0 := by
  classical
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, setIntegral_e_int]
    split_ifs <;> simp
  · intro i _
    have hc : Continuous (fun x : ℝ => w i * e ((m i : ℝ) * x)) := by
      unfold e
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc

/-- Private helper: the restricted prime weight sum is bounded by the Chebyshev theta. -/
private lemma sum_log_le_theta (n₁ n : ℕ) :
    (∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)),
      Real.log p) ≤ Chebyshev.theta (n : ℝ) := by
  classical
  have hsub : (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)) ⊆
      (range (n + 1)).filter (fun p : ℕ => p.Prime) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hnn : ∀ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime), 0 ≤ Real.log p := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    exact Real.log_nonneg (by linarith)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)).trans ?_
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range]

/-- LEAF. Hu page 195, the well known prime linear mean square estimate.
This input involves neither G nor either two dimensional arc. -/
theorem prime_second_moment_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSecondMoment n₁ n ≤ K * (n : ℝ) * Real.log n := by
  classical
  refine ⟨Real.log 4, Real.log_nonneg (by norm_num), 4, ?_⟩
  intro n₁ n hn hn1
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  set P := (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)) with hP
  have hval : primeSecondMoment n₁ n = ∑ p ∈ P, (Real.log p) ^ 2 := by
    unfold primeSecondMoment
    have hS : Continuous fun x : ℝ => S n₁ n x := by
      unfold S e
      fun_prop
    have hcont : Continuous fun x : ℝ => S n₁ n x * (starRingEnd ℂ) (S n₁ n x) :=
      hS.mul (continuous_star.comp hS)
    have hint : IntegrableOn (fun x : ℝ => S n₁ n x * (starRingEnd ℂ) (S n₁ n x))
        (Set.Icc (0 : ℝ) 1) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    have hre2 : (∫ x in Set.Icc (0 : ℝ) 1,
          (S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re) =
        (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re := by
      simpa using integral_re hint
    have hre : (∫ x in Set.Icc (0 : ℝ) 1, ‖S n₁ n x‖ ^ 2) =
        (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re := by
      rw [← hre2]
      refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hcomplex : (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)) =
        ∑ p ∈ P, (((Real.log p) ^ 2 : ℝ) : ℂ) := by
      simp_rw [S_mul_conj]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun p hp => ?_
        rw [integral_e_finset_sum, Finset.sum_eq_single p]
        · rw [if_pos (by simp)]
          push_cast
          ring
        · intro q hq hne
          refine if_neg ?_
          intro h
          exact hne (by omega)
        · intro hp'
          exact absurd hp hp'
      · intro p _
        have hc : Continuous fun x : ℝ =>
            ∑ q ∈ P, ((Real.log p * Real.log q : ℝ) : ℂ) *
              e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
          refine continuous_finsetSum _ fun q _ => ?_
          unfold e
          fun_prop
        exact hc.continuousOn.integrableOn_compact isCompact_Icc
    rw [hre, hcomplex]
    have hfin : (∑ p ∈ P, (((Real.log p) ^ 2 : ℝ) : ℂ)).re = ∑ p ∈ P, (Real.log p) ^ 2 := by
      rw [← Complex.ofReal_sum (s := P) (f := fun p : ℕ => (Real.log p) ^ 2)]
      exact Complex.ofReal_re _
    exact hfin
  rw [hval]
  have hPsub : P ⊆ (range (n + 1)).filter (fun p : ℕ => p.Prime) := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hmem : ∀ p ∈ P, p ≤ n := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    omega
  have hlogpos : ∀ p ∈ P, 0 ≤ Real.log p := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
    exact Real.log_nonneg (by linarith)
  have hlogle : ∀ p ∈ P, Real.log p ≤ Real.log n := by
    intro p hp
    have hle : p ≤ n := hmem p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
    exact Real.log_le_log (by linarith) (by exact_mod_cast hle)
  calc ∑ p ∈ P, (Real.log p) ^ 2 = ∑ p ∈ P, Real.log p * Real.log p :=
        Finset.sum_congr rfl fun p _ => pow_two _
    _ ≤ ∑ p ∈ P, Real.log n * Real.log p :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hlogle p hp) (hlogpos p hp)
    _ = Real.log n * ∑ p ∈ P, Real.log p := by rw [Finset.mul_sum]
    _ ≤ Real.log n * Chebyshev.theta (n : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hlogn.le
        rw [hP]
        exact sum_log_le_theta n₁ n
    _ ≤ Real.log n * (Real.log 4 * (n : ℝ)) := by
        have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity)
        nlinarith [hlogn.le]
    _ = Real.log 4 * (n : ℝ) * Real.log n := by ring

/-- LEAF. Hu page 195, Rieger reference 17.
This input involves only the fourth moment of the prime square sum. -/
theorem rieger_fourth_moment_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSquareFourthMoment n₁ n ≤ K * (n : ℝ) * Real.log n ^ 2 := by
  sorry

/-- LEAF. Hu page 194 Lemma 2.3, Platt and Trudgian reference 16.
The translated slice form is the periodic version used on page 195.
This input contains no prime exponential sum. -/
theorem platt_trudgian_slice_bound :
    ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ → ∀ t : ℝ,
        volume.real (exceptionalSlice n₁ t) ≤ K * (n₁ : ℝ) ^ (-E) := by
  sorry

/-- LEAF. Hu pages 195 and 196, the two I bounds before multiplying by G.
This smaller analytic task contains no G to power 82 and no arc integral.
It needs the sectional Cauchy estimate, the four inputs above, and
absorption of the logarithms into the strict exponent reserve. -/
theorem strip_power_saving (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      stripMass n₁ n₂ true + stripMass n₁ n₂ false ≤
        K * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε) := by
  sorry

/-- Page 194. The complement of the product major region is exactly the
union of the two minor coordinate strips after restricting to E. -/
theorem exceptional_minor_partition (n₁ n₂ : ℕ) :
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
      ((major n₁ n₂)ᶜ ∩ exceptional n₁) =
        minorStrip n₁ n₂ true ∪ minorStrip n₁ n₂ false := by
  ext α
  simp only [minorStrip, Bool.true_eq, ↓reduceIte, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, major, Set.mem_prod]
  tauto

/-- Pages 194 and 195. The base norm is continuous and nonnegative. -/
theorem continuous_baseNorm (n₁ n₂ : ℕ) : Continuous (baseNorm n₁ n₂) := by
  unfold baseNorm S T e
  fun_prop

/-- Pages 194 and 195. The strips are measurable. -/
theorem measurableSet_minorStrip (n₁ n₂ : ℕ) (first : Bool) :
    MeasurableSet (minorStrip n₁ n₂ first) := by
  cases first <;> exact
    ((measurableSet_Icc.prod measurableSet_Icc).inter (measurableSet_exceptional n₁)).inter
      (by simp only [Bool.false_eq_true, ↓reduceIte, minorStrip];
          first | exact (measurableSet_majorOne n₁ n₂).compl.preimage measurable_snd |
                  exact (measurableSet_majorOne n₁ n₁).compl.preimage measurable_fst)

/-- Page 194. The union estimate does not require disjoint strips. -/
theorem integral_union_le {s t : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfi : IntegrableOn f (s ∪ t)) (h0 : ∀ x, 0 ≤ f x) :
    (∫ x in s ∪ t, f x) ≤ (∫ x in s, f x) + ∫ x in t, f x := by
  have hid : s ∪ t = s ∪ (t \ s) := by ext x; simp
  rw [hid, setIntegral_union Set.disjoint_sdiff_right (ht.diff hs)
    (hfi.mono_set Set.subset_union_left)
    (hfi.mono_set (Set.Subset.trans Set.sdiff_subset Set.subset_union_right))]
  apply add_le_add le_rfl
  exact setIntegral_mono_set (hfi.mono_set Set.subset_union_right)
    (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall Set.sdiff_subset)

/-- Page 194. Taking out G to power 82 leaves the two strip masses. -/
theorem exceptional_arc_strip_bound (n₁ n₂ : ℕ) (hn₁ : 16 ≤ n₁) :
    |R2 n₁ n₂| ≤ L n₁ ^ 82 * (stripMass n₁ n₂ true + stripMass n₁ n₂ false) := by
  let U := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let A := U ∩ ((major n₁ n₂)ᶜ ∩ exceptional n₁)
  have hAU : A ⊆ U := Set.inter_subset_left
  have hA : MeasurableSet A :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_major n₁ n₂).compl.inter (measurableSet_exceptional n₁))
  have h0 : ∀ α, 0 ≤ baseNorm n₁ n₂ α := by intro α; unfold baseNorm; positivity
  have hfi : IntegrableOn (baseNorm n₁ n₂) U :=
    (continuous_baseNorm n₁ n₂).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hcf : IntegrableOn (fun α => L n₁ ^ 82 * baseNorm n₁ n₂ α) A :=
    (show IntegrableOn (fun α => L n₁ ^ 82 * baseNorm n₁ n₂ α) U volume from
      hfi.const_mul _).mono_set hAU
  have hpoint (α : ℝ × ℝ) : ‖integrand n₁ n₂ α‖ ≤ L n₁ ^ 82 * baseNorm n₁ n₂ α := by
    have hG := pow_le_pow_left₀ (norm_nonneg (G n₁ (α.1 + α.2)))
      (norm_G_le n₁ hn₁ (α.1 + α.2)) 82
    calc
      ‖integrand n₁ n₂ α‖ = ‖G n₁ (α.1 + α.2)‖ ^ 82 * baseNorm n₁ n₂ α := by
        simp only [integrand, norm_mul, norm_pow, norm_e, mul_one, baseNorm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hG (h0 α)
  calc
    |R2 n₁ n₂| ≤ ‖∫ α in A, integrand n₁ n₂ α‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ α in A, ‖integrand n₁ n₂ α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in A, L n₁ ^ 82 * baseNorm n₁ n₂ α :=
      setIntegral_mono_on ((integrableOn_integrand n₁ n₂).mono_set hAU).norm hcf hA
        (fun α _ => hpoint α)
    _ = L n₁ ^ 82 * ∫ α in A, baseNorm n₁ n₂ α := integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change (∫ α in A, baseNorm n₁ n₂ α) ≤ _
      rw [show A = minorStrip n₁ n₂ true ∪ minorStrip n₁ n₂ false from
        exceptional_minor_partition n₁ n₂]
      exact integral_union_le (measurableSet_minorStrip n₁ n₂ true)
        (measurableSet_minorStrip n₁ n₂ false)
        (hfi.mono_set (by
          intro α hα; rcases hα with hα | hα <;> exact hα.1.1)) h0


/-- Page 196. A positive power saving absorbs the one additional factor L. -/
theorem L_mul_rpow_neg_le_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → L n * (n : ℝ) ^ (-ε) ≤ 1 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hz.comp tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds htwo))
  refine ⟨max 16 N, ?_⟩
  intro n hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog1 : 1 ≤ Real.log n := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (show (16 : ℝ) ≤ n by exact_mod_cast hn16)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [h16] at hm
    linarith [Real.log_two_gt_d9]
  have hratio : (n : ℝ) / Real.log n ≤ n :=
    (div_le_iff₀ hlogpos).2 (by nlinarith)
  have hL : L n ≤ Real.log n / Real.log 2 := by
    unfold L Decomp115.logScale
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (div_pos hnpos hlogpos) hratio) htwo.le
  have hdecay : Real.log n / (n : ℝ) ^ ε ≤ Real.log 2 :=
    (hN n ((le_max_right _ _).trans hn)).le
  rw [Real.rpow_neg hnpos.le]
  calc
    L n * ((n : ℝ) ^ ε)⁻¹ ≤ (Real.log n / Real.log 2) * ((n : ℝ) ^ ε)⁻¹ :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = (Real.log n / (n : ℝ) ^ ε) / Real.log 2 := by ring
    _ ≤ 1 := (div_le_one htwo).2 hdecay

/-- Page 196. CONDITIONAL ON the smaller two strip power saving estimate.
This has the exact statement of the sealed exceptional arc leaf. -/
theorem exceptional_arc_order_bound (C : ℝ) (hC : 1 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) := by
  obtain ⟨ε, hε, K, hK, N, hN⟩ := strip_power_saving C hC
  obtain ⟨N', hN'⟩ := L_mul_rpow_neg_le_one ε hε
  refine ⟨K, hK, max 16 (max N N'), ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have hn16 : 16 ≤ n₁ := ((le_max_left _ _).trans hn).trans hlt.le
  have hnN : N ≤ n₂ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnN' : N' ≤ n₁ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hn).trans hlt.le
  have hm := hN n₁ n₂ ho₁ ho₂ hnN hlt hratio
  have hdecay := hN' n₁ hnN'
  have hL : 0 ≤ L n₁ := (Decomp115.logScale_pos n₁ hn16).le
  calc
    |R2 n₁ n₂| ≤ L n₁ ^ 82 * (stripMass n₁ n₂ true + stripMass n₁ n₂ false) :=
      exceptional_arc_strip_bound n₁ n₂ hn16
    _ ≤ L n₁ ^ 82 * (K * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (K * ((n₁ : ℝ) * n₂) * L n₁ ^ 81) * (L n₁ * (n₁ : ℝ) ^ (-ε)) := by ring
    _ ≤ (K * ((n₁ : ℝ) * n₂) * L n₁ ^ 81) * 1 :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

end LeanLab.Hathi2021.Decomp570b

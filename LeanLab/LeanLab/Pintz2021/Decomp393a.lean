import LeanLab.Pintz2021.DecompJ803
import LeanLab.Pintz2021.Truncation168

/-!
Finite cutoff audit for the sealed DecompJ803 truncation leaf.
Source: arXiv:1804.05561v1 page 9 display 2.12 and page 37 display 10.27.
These are derived bookkeeping facts, not printed analytic estimates.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Decomp393a

open Filter Topology Finset State1581 DecompJ281 Truncation168

attribute [local instance] Classical.propDecidable

/-- At large height and character cutoff, exactly the lcm restriction remains. -/
theorem retainedPairs_eventually_eq_lcm (E : Finset ExcPair) (P : ℝ) (m : ℕ) :
    ∀ᶠ U : ℝ in atTop, retainedPairs E P U m =
      (E ×ˢ E).filter (fun p => (Nat.lcm p.1.r p.2.r : ℝ) ≤ P) := by
  have he : ∀ᶠ U : ℝ in atTop, ∀ p ∈ E ×ˢ E,
      max (max |p.1.ρ.im| |p.2.ρ.im|) (UCutoff p.1 p.2 m) ≤ U :=
    (E ×ˢ E).eventually_all.mpr (fun p _ => eventually_ge_atTop _)
  filter_upwards [he] with U hU
  ext p
  simp only [retainedPairs, mem_filter, mem_product]
  constructor
  · rintro ⟨hp, _, _, hl, _⟩
    exact ⟨hp, hl⟩
  · rintro ⟨hp, hl⟩
    have hb := hU p (mem_product.mpr hp)
    exact ⟨hp, (le_max_left _ _).trans ((le_max_left _ _).trans hb),
      (le_max_right _ _).trans ((le_max_left _ _).trans hb), hl,
      (le_max_right _ _).trans hb⟩

/-- The exact truncated main term stabilizes to the lcm restricted finite sum. -/
theorem truncated_eventually_eq_lcm_sum (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ) :
    ∀ᶠ U : ℝ in atTop,
      mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m =
        ∑ p ∈ (E ×ˢ E).filter (fun p => (Nat.lcm p.1.r p.2.r : ℝ) ≤ P),
          pairTerm Sg ε X m p := by
  filter_upwards [retainedPairs_eventually_eq_lcm E P m] with U hU
  rw [DecompJ665.truncatedPrime_eq_finite, truncatedPrime, hU]

/-- The tail error stabilizes to the sum over pairs permanently excluded by the lcm. -/
theorem error_eventually_eq_discarded_lcm_sum (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ) :
    ∀ᶠ U : ℝ in atTop,
      mainTermPrime (E : Set ExcPair) Sg ε X m -
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m =
        ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
          pairTerm Sg ε X m p := by
  filter_upwards [retainedPairs_eventually_eq_lcm E P m] with U hU
  rw [DecompJ665.truncatedPrime_eq_finite, main_partition, add_sub_cancel_left, hU]
  congr 1
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨hp, lt_of_not_ge (fun hl => hn ⟨hp, hl⟩)⟩
  · rintro ⟨hp, hl⟩
    exact ⟨hp, fun hn => (not_le_of_gt hl) hn.2⟩

/-- The logarithmic error factor tends to zero for any fixed real coefficient. -/
theorem tendsto_log_div_sqrt_mul (A : ℝ) :
    Tendsto (fun U : ℝ => A * (Real.log U / Real.sqrt U)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [Real.sqrt_eq_rpow, mul_zero] using h.const_mul A

/-- A decaying eventual error bound forces exact cancellation of the lcm discarded sum. -/
theorem discarded_lcm_sum_eq_zero_of_eventual_bound (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P A : ℝ) (m : ℕ)
    (h : ∀ᶠ U : ℝ in atTop,
      ‖mainTermPrime (E : Set ExcPair) Sg ε X m -
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m‖ ≤
          A * (Real.log U / Real.sqrt U)) :
    ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply ge_of_tendsto (tendsto_log_div_sqrt_mul A)
  filter_upwards [h, error_eventually_eq_discarded_lcm_sum E Sg ε X P m] with U hb he
  rwa [he] at hb

/-- A nonzero lcm discarded sum rules out every eventual logarithmic tail bound. -/
theorem no_eventual_bound_of_discarded_lcm_sum_ne_zero (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ)
    (hne : ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p ≠ 0) :
    ∀ A : ℝ, ¬ (∀ᶠ U : ℝ in atTop,
      ‖mainTermPrime (E : Set ExcPair) Sg ε X m -
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m‖ ≤
          A * (Real.log U / Real.sqrt U)) := by
  intro A h
  exact hne (discarded_lcm_sum_eq_zero_of_eventual_bound E Sg ε X P A m h)

/-- Cancellation of permanently discarded pairs makes the error eventually zero. -/
theorem error_eventually_zero_of_discarded_lcm_sum_eq_zero (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ)
    (hzero : ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p = 0) :
    ∀ᶠ U : ℝ in atTop,
      mainTermPrime (E : Set ExcPair) Sg ε X m =
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m := by
  filter_upwards [error_eventually_eq_discarded_lcm_sum E Sg ε X P m] with U hU
  exact sub_eq_zero.mp (hU.trans hzero)

/-- At fixed finite data, a decaying eventual bound is equivalent to exact lcm cancellation. -/
theorem eventual_bound_iff_discarded_lcm_sum_eq_zero (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ) :
    (∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
      ‖mainTermPrime (E : Set ExcPair) Sg ε X m -
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m‖ ≤
          A * (Real.log U / Real.sqrt U)) ↔
    ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p = 0 := by
  constructor
  · rintro ⟨A, _, hA⟩
    exact discarded_lcm_sum_eq_zero_of_eventual_bound E Sg ε X P A m hA
  · intro hz
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [error_eventually_zero_of_discarded_lcm_sum_eq_zero E Sg ε X P m hz,
      eventually_ge_atTop (2 : ℝ)] with U he hU
    rw [he, sub_self, norm_zero]
    exact mul_nonneg zero_le_one (div_nonneg
      (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _))

end LeanLab.Pintz2021.Decomp393a

#print axioms LeanLab.Pintz2021.Decomp393a.retainedPairs_eventually_eq_lcm
#print axioms LeanLab.Pintz2021.Decomp393a.truncated_eventually_eq_lcm_sum
#print axioms LeanLab.Pintz2021.Decomp393a.error_eventually_eq_discarded_lcm_sum
#print axioms LeanLab.Pintz2021.Decomp393a.tendsto_log_div_sqrt_mul
#print axioms LeanLab.Pintz2021.Decomp393a.discarded_lcm_sum_eq_zero_of_eventual_bound

#print axioms LeanLab.Pintz2021.Decomp393a.no_eventual_bound_of_discarded_lcm_sum_ne_zero

#print axioms LeanLab.Pintz2021.Decomp393a.error_eventually_zero_of_discarded_lcm_sum_eq_zero

#print axioms LeanLab.Pintz2021.Decomp393a.eventual_bound_iff_discarded_lcm_sum_eq_zero

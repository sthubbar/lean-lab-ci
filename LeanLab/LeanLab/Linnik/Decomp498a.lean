/-
Gallagher 1975 pp.127 and 131. Support for the exceptional energy split.
The other character coefficients do not depend on the chosen exceptional zero.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp486c

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- Gallagher 1975 p.127 uniqueness of the exceptional character and p.131 replacement
of its main polynomial. A different primitive pair never receives the exceptional
correction, for any real parameter in the exceptional strip. -/
theorem correctedCoefficient_eq_unexceptional {T : ℝ} (hT : 2 ≤ T)
    (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1))
    (hx : x ∈ excSet exceptionalStrip T)
    (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)) (hp : χ.IsPrimitive)
    (hne : (⟨k, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ≠ x)
    (γ : ℝ) (hγ : 1 - exceptionalStrip / Real.log T ≤ γ) :
    correctedCoefficient χ (x.1 + 1) γ = correctedCoefficient χ 0 0 := by
  classical
  have hflag : ¬ (k + 1 = x.1 + 1 ∧ χ.LFunction (γ : ℂ) = 0) := by
    intro hf
    have hk : k = x.1 := Nat.add_right_cancel hf.1
    have hmem : (⟨k, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
        excSet exceptionalStrip T := by
      refine ⟨?_, hp, (γ : ℂ), hf.2, ?_, ?_⟩
      · simpa only [hk] using hx.1
      · simpa only [Complex.ofReal_re] using hγ
      · simp only [Complex.ofReal_im, abs_zero]; linarith
    let b := Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton
    have hb : exceptionalStrip ≤ b := (min_le_right _ _).trans (min_le_right _ _)
    exact hne ((Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton).2 T hT
      (LeanLab.Linnik.Decomp1532b.excSet_mono hb hT hmem)
      (LeanLab.Linnik.Decomp1532b.excSet_mono hb hT hx))
  funext m
  unfold correctedCoefficient
  rw [ite_eq_right hflag]
  simp

/-- Gallagher 1975 p.131 display 14 and the exceptional replacement, using the largest
real zero in the p.127 strip. The single exceptional summand is bounded by the proved
full corrected family mean. No uniqueness at the sealed strip width is assumed. -/
theorem exceptional_summand_decay_of_max :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          (∀ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' → γ' < 1 → γ' ≤ γ) →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hmean⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_exceptional_max
  refine ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hmean θ hθ hθle
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₁ N₂, fun N hN q χ γ hp hq hz hlo hlt hmax => ?_⟩
  have hP2 : (2 : ℝ) ≤ (N : ℝ) ^ θ := hN₂ N ((le_max_right _ _).trans hN)
  have hPT : (N : ℝ) ^ θ ≤ ((N : ℝ) ^ θ) ^ 5 :=
    le_self_pow₀ (by linarith) (by norm_num)
  have hx : (⟨q, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
      excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5) := by
    refine ⟨hq.trans hPT, hp, (γ : ℂ), hz, ?_, ?_⟩
    · simpa only [Complex.ofReal_re] using hlo
    · simp only [Complex.ofReal_im, abs_zero]; positivity
  have hqK : q < ⌊(N : ℝ) ^ θ⌋₊ := by
    have : q + 1 ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
      (Nat.le_floor_iff (show (0 : ℝ) ≤ (N : ℝ) ^ θ by positivity)).mpr (by exact_mod_cast hq)
    omega
  have htotal := hN₁ N ((le_max_left _ _).trans hN) ⟨q, χ⟩ hx
    (by exact_mod_cast hq) γ hz hlo hlt hmax
  change (∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
        Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ (q + 1) γ) (N + 1)
              (gallagherLength N θ) m‖ ^ 2)) ≤ _ at htotal
  apply le_trans ?_ htotal
  calc
    _ ≤ ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun ψ => ψ.IsPrimitive), Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ (q + 1) γ) (N + 1)
              (gallagherLength N θ) m‖ ^ 2) :=
      single_le_sum (fun ψ _ => by positivity) (mem_filter.mpr ⟨mem_univ χ, hp⟩)
    _ ≤ _ := by
      apply single_le_sum (f := fun k : ℕ =>
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
          Real.pi / (2 * gallagherLength N θ) *
            Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
              ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ (q + 1) γ) (N + 1)
                (gallagherLength N θ) m‖ ^ 2))
        (fun k _ => sum_nonneg fun ψ _ => by positivity) (mem_range.mpr hqK)

/-- Auxiliary budget obstruction for Gallagher 1975 p.131 exceptional replacement.
For positive rates a and c and every positive theta cutoff, the difference between one
and exp of minus a over theta exceeds C times exp of minus c over theta somewhere below
that cutoff.
This scalar fact asserts nothing about the existence of two L function zeros. -/
theorem distinct_main_coefficient_budget_obstruction (a c C θlim : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hθlim : 0 < θlim) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ θlim ∧ θ ≤ 1 / 2 ∧
      C * Real.exp (-c / θ) < 1 - Real.exp (-a / θ) := by
  have ht (d : ℝ) (hd : 0 < d) :
      Tendsto (fun t : ℝ => Real.exp (-(d * t))) atTop (nhds 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -d < 0))
    simpa only [Function.comp_def, id_eq, neg_mul] using h
  have ha' := (ht a ha).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hct : Tendsto (fun t : ℝ => C * Real.exp (-(c * t))) atTop (nhds 0) := by
    simpa only [mul_zero] using (ht c hc).const_mul C
  have hc' := hct.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨t, htb, hat, hct⟩ :=
    ((eventually_ge_atTop (max (2 : ℝ) θlim⁻¹)).and (ha'.and hc')).exists
  have ht2 : (2 : ℝ) ≤ t := (le_max_left _ _).trans htb
  have htl : θlim⁻¹ ≤ t := (le_max_right _ _).trans htb
  have ht0 : 0 < t := by linarith
  refine ⟨1 / t, by positivity, ?_, ?_, ?_⟩
  · simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hθlim) htl
  · exact one_div_le_one_div_of_le (by norm_num) ht2
  · have heq (d : ℝ) : -d / (1 / t) = -(d * t) := by field_simp
    rw [heq, heq]
    linarith

/-- Auxiliary full period bound for Gallagher 1975 p.131 exceptional main polynomials.
The difference of two such polynomials has mean square at most J of zero when both
real exponents are at most one. This is a bound at the ordinary scale, with no saving. -/
theorem exceptionalMain_sub_mean_square_le (N : ℕ) (γ γ' : ℝ) (hγ : γ ≤ 1) (hγ' : γ' ≤ 1) :
    (∫ β in Set.Icc (0 : ℝ) 1, ‖exceptionalMain N γ β - exceptionalMain N γ' β‖ ^ 2) ≤
      LeanLab.Linnik.Decomp1532b.Jn N 0 := by
  let a : ℕ → ℝ := fun m => ((m : ℝ) ^ (γ - 1) - (m : ℝ) ^ (γ' - 1)) / Real.log m
  have heq (β : ℝ) : exceptionalMain N γ β - exceptionalMain N γ' β =
      LeanLab.Linnik.LiLiuLemma43.SA (Ioc 1 N) (fun m => (a m : ℂ)) β := by
    unfold exceptionalMain LeanLab.Linnik.LiLiuLemma43.SA
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    dsimp only [a]
    push_cast
    ring
  simp_rw [heq]
  rw [LeanLab.Linnik.U1426ChainWire.parseval, LeanLab.Linnik.Decomp1532b.Jn_zero_eq_sum]
  apply sum_le_sum
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_of_lt (mem_Ioc.mp hm).1)
  have hp : (m : ℝ) ^ (γ - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)⟩
  have hp' : (m : ℝ) ^ (γ' - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)⟩
  dsimp only [a]
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (sq_le_one_iff_abs_le_one _).mpr
    (by simpa only [Real.dist_eq] using Real.dist_le_of_mem_Icc_01 hp hp')

/-- LEAF. Residual nonmaximal zero case of the sealed exceptional summand estimate.
Gallagher 1975 p.127 asserts uniqueness for a sufficiently small strip and p.131 display 14
removes that unique zero. Here another larger real zero is explicitly assumed in the sealed
strip. The source would exclude this case if that strip were known to lie inside the
uniqueness strip. That constant comparison is not supplied by the sealed definitions.
This is an open subcase of the assigned target, not a proved consequence of display 14. -/
theorem leaf_nonmaximal_exceptional_summand_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          (∃ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' ∧ γ' < 1 ∧ γ < γ') →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

end LeanLab.Linnik.Decomp486c

#print axioms LeanLab.Linnik.Decomp486c.correctedCoefficient_eq_unexceptional

#print axioms LeanLab.Linnik.Decomp486c.exceptional_summand_decay_of_max

#print axioms LeanLab.Linnik.Decomp486c.leaf_nonmaximal_exceptional_summand_decay

#print axioms LeanLab.Linnik.Decomp486c.distinct_main_coefficient_budget_obstruction

#print axioms LeanLab.Linnik.Decomp486c.exceptionalMain_sub_mean_square_le

/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 44, 47 and 48.
Prime supported sieve interface and radial transfer.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420e
import LeanLab.Ternary.Decomp580e
import LeanLab.Helfgott2013.Decomp1538b

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The open arcs of Helfgott page 10 equation 3.5 at real radius r.
Their intersection with the fundamental interval represents the circle arcs. -/
noncomputable def majorArcs (x δ r : ℝ) : Set ℝ :=
  ⋃ q : ℕ, ⋃ (_h : 1 ≤ q ∧ (q : ℝ) ≤ Nat.gcd q 2 * r),
    ⋃ a : ℤ, ⋃ (_h : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - (Nat.gcd q 2 * δ * r : ℝ) / (2 * q * x))
        ((a : ℝ) / q + (Nat.gcd q 2 * δ * r : ℝ) / (2 * q * x))

/-- The exact open circle arcs are open.
Helfgott page 10 equation 3.5, used in Proposition 6.2 page 47. -/
theorem majorArcs_isOpen (x δ r : ℝ) : IsOpen (majorArcs x δ r) := by
  unfold majorArcs
  exact isOpen_iUnion fun q => isOpen_iUnion fun hq =>
    isOpen_iUnion fun a => isOpen_iUnion fun ha => isOpen_Ioo

/-- Increasing the real radius enlarges the exact open arcs.
Helfgott page 48 the shell decomposition in Proposition 6.2. -/
theorem majorArcs_mono {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) :
    Monotone (majorArcs x δ) := by
  intro r s hrs α hα
  simp only [majorArcs, Set.mem_iUnion] at hα ⊢
  rcases hα with ⟨q, ⟨hq, hqr⟩, a, ha, hα⟩
  refine ⟨q, ⟨hq, hqr.trans ?_⟩, a, ha, ?_⟩
  · exact mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg _)
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hw : (Nat.gcd q 2 * δ * r : ℝ) / (2 * q * x) ≤
        (Nat.gcd q 2 * δ * s : ℝ) / (2 * q * x) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrs (mul_nonneg (Nat.cast_nonneg _) hδ)) (by positivity)
    exact ⟨by linarith [hα.1], by linarith [hα.2]⟩

/-- The exact sieve constant c E of Corollary 5.7 on page 44.
The decimal approximation in the paper is not used as an equality. -/
noncomputable def sieveConstant : ℝ :=
  Real.eulerMascheroniConstant + ∑' p : ℕ,
    if p.Prime then Real.log p / ((p : ℝ) * (p - 1 : ℝ)) else 0

/-- LEAF. The finite prime supported large sieve on the circle arcs.
Helfgott page 44 Corollary 5.7 second inequality for finitely supported coefficients.
This is strictly smaller than the absolutely summable sequence statement. -/
theorem prime_supported_large_sieve_finset (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ : 1e5 ≤ Q₀)
    (hsize : (20000 * Q₀) ^ 2 ≤ x / (2 * δ))
    (hpower : 2 * Q₀ ≤ (2 * Real.sqrt (x / (2 * δ))) ^ (0.6 : ℝ))
    (hsupport : ∀ n ∈ A, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) ≤
      ((Real.log (2 * Q₀) + 1.36) /
        (Real.log (2 * Real.sqrt (x / (2 * δ))) + sieveConstant)) *
          ∑ n ∈ A, ‖a n‖ ^ 2 := by
  sorry

/-- The prime supported large sieve on the circle arcs.
Helfgott page 44 Corollary 5.7 second bound, with Q equal to sqrt x over
2 delta. The coefficients vanish below sqrt x and off the primes.
The explicit square summability hypothesis is also assumed in the paper.
CONDITIONAL ON prime_supported_large_sieve_finset. -/
theorem prime_supported_large_sieve (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ : 1e5 ≤ Q₀)
    (hsize : (20000 * Q₀) ^ 2 ≤ x / (2 * δ))
    (hpower : 2 * Q₀ ≤ (2 * Real.sqrt (x / (2 * δ))) ^ (0.6 : ℝ))
    (ha : Summable fun n => ‖a n‖) (ha2 : Summable fun n => ‖a n‖ ^ 2)
    (hsupport : ∀ n : ℕ, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖Task420.charSeries a α‖ ^ 2) ≤
      ((Real.log (2 * Q₀) + 1.36) /
        (Real.log (2 * Real.sqrt (x / (2 * δ))) + sieveConstant)) *
          ∑' n, ‖a n‖ ^ 2 := by
  apply charSeries_l2_of_finset_bounds a ha ha2 Set.inter_subset_right
  intro A
  exact prime_supported_large_sieve_finset A a x δ Q₀ hx hδ hQ hsize hpower
    (fun n _ => hsupport n)

/-- The radial stage for the lab natural index character series.
Helfgott pages 47 and 48 Proposition 6.2 equations 6.4 to 6.7.
CONDITIONAL ON the cumulative arc bound and
minor arc envelope. The proved Parseval adapter supplies the full mass identity.
The cited radial theorem is reused without a new axiom. -/
theorem charSeries_radial (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖)
    (hW : 0 < ∑' n, ‖a n‖ ^ 2)
    (S₂ : ℝ → ℂ) (hS₂ : Continuous S₂) {M : ℝ → Set ℝ}
    (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M)
    {r₀ : ℕ} {R : ℝ} (hr : (r₀ : ℝ) ≤ R) {H H' g : ℝ → ℝ}
    (hH : LeanLab.Helfgott2013.U1538.NondecFTC H H' r₀ R) (hH1 : H R = 1)
    (hcumulative : ∀ r ∈ Set.Icc (r₀ : ℝ) R,
      (∫ α in M (r + 1), ‖Task420.charSeries a α‖ ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ (∑' n, ‖a n‖ ^ 2) * H r)
    (hg0 : ∀ r ∈ Set.Icc (r₀ : ℝ) R, 0 ≤ g r)
    (hganti : AntitoneOn g (Set.Icc (r₀ : ℝ) R))
    (henvelope : ∀ r ∈ Set.Icc (r₀ : ℝ) R, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      α ∉ M r → ‖S₂ α‖ ≤ g r) :
    (∫ α in (M r₀)ᶜ, ‖Task420.charSeries a α‖ ^ 2 * ‖S₂ α‖
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤
      g r₀ * ((∑' n, ‖a n‖ ^ 2) * H r₀ -
        ∫ α in M r₀, ‖Task420.charSeries a α‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) +
      (∑' n, ‖a n‖ ^ 2) * ∫ r in (r₀ : ℝ)..R, g r * H' r := by
  have hc := Task420.continuous_charSeries a ha
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hS₂.norm.continuousOn
  have hbdd : ∀ᵐ α ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖S₂ α‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
    exact hC (Set.mem_image_of_mem _ (Set.Ioc_subset_Icc_self hα))
  apply LeanLab.Helfgott2013.U1538.prop62_real_mass
    (fun α => sq_nonneg ‖Task420.charSeries a α‖)
    (hc.norm.pow 2).integrableOn_Ioc hW (charSeries_parseval a ha)
    hS₂.norm.aestronglyMeasurable.restrict (fun α => norm_nonneg (S₂ α))
    hbdd hM hmono hr hH hH1 hcumulative hg0 hganti
  intro r hr'
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
  exact henvelope r hr' α hα

end LeanLab.Ternary.Task580

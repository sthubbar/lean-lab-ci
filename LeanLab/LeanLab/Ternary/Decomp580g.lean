/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 48, 51 and 52.
Weighted shell transfer with an explicit terminal mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580d
import LeanLab.Helfgott2013.Decomp1538b

namespace LeanLab.Ternary.Task580
open MeasureTheory Finset
open LeanLab.Helfgott2013.U1538

/-- The finite shell radial estimate retains the terminal mass jump.
Helfgott page 48 equation 6.8, applied to the terminal jump on page 51
before equation 6.19 on page 52.
CONDITIONAL ON the explicit cumulative mass and envelope bounds. -/
theorem weighted_integral_with_terminal_mass {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) {M : ℕ → Set X}
    (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M) {a b : ℕ}
    (hab : a ≤ b) (F g : ℕ → ℝ)
    (hcumulative : ∀ n ∈ Icc a b,
      (∫ y in M (n + 1), w y ∂μ) - (∫ y in M a, w y ∂μ) ≤ F n)
    (hg : AntitoneOn g (Set.Icc a (b + 1)))
    (henvelope : ∀ r ∈ Icc a (b + 1), ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    (∫ y in (M a)ᶜ, w y * s y ∂μ) ≤
      g a * F a + (∑ n ∈ Ico a b, g (n + 1) * (F (n + 1) - F n)) +
        g (b + 1) * ((∫ y in (M a)ᶜ, w y ∂μ) - F b) := by
  let f : ℕ → ℝ := fun r => ∫ y in piece M (b + 1) r, w y ∂μ
  have hprefix : ∀ n ∈ Icc a b, ∑ m ∈ Icc a n, f m ≤ F n := by
    intro n hn
    change (∑ m ∈ Icc a n, ∫ y in piece M (b + 1) m, w y ∂μ) ≤ F n
    rw [sum_pieces_partial (r0 := a) (r1 := b + 1) hwi hM hmono n (mem_Icc.mp hn).1 (by
      have := (mem_Icc.mp hn).2
      omega)]
    exact hcumulative n hn
  have hmass := integral_compl_eq_sum_pieces (r0 := a) (r1 := b + 1) hwi hM hmono (show a ≤ b + 1 by omega)
  change (∫ y in (M a)ᶜ, w y ∂μ) = ∑ r ∈ Icc a (b + 1), f r at hmass
  rw [sum_Icc_succ_top (by omega)] at hmass
  have hfinite := radial_sum_with_terminal_mass f g F hab hprefix hg
    (f (b + 1)) (∫ y in (M a)ᶜ, w y ∂μ) hmass.symm
  have hpieces : (∫ y in (M a)ᶜ, w y * s y ∂μ) ≤
      ∑ r ∈ Icc a (b + 1), f r * g r := by
    rw [integral_compl_eq_sum_pieces (r0 := a) (r1 := b + 1) (integrable_mul_bdd hwi hsm hs0 hsC)
      hM hmono (show a ≤ b + 1 by omega)]
    apply sum_le_sum
    intro r hr
    calc
      _ ≤ g r * f r := piece_bound hw0 hwi hsm hs0 hsC hM (b + 1) r (henvelope r hr)
      _ = _ := mul_comm _ _
  rw [sum_Icc_succ_top (by omega)] at hpieces
  exact hpieces.trans hfinite

end LeanLab.Ternary.Task580

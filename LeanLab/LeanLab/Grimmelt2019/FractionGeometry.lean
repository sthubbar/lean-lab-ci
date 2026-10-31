/-
AI wrote this Lean code for CODEX task51.
P0074 page 8, rational separation for Lemma 3.1.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.FareyCoefficients
import LeanLab.PNTPort.Vinogradov.TernaryArcs

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- A coprime integer numerator has a reduced natural representative with the same phases. -/
theorem normalize_numerator {q : ℕ} (hq : 0 < q) (r : ℤ) (hr : Int.gcd r q = 1) :
    ∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧ ∀ n : ℤ,
      LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q) = LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * ((a : ℝ) / q)) := by
  let a : ℕ := (r % q).toNat
  have hnonneg : 0 ≤ r % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have ha : (a : ℤ) = r % q := Int.toNat_of_nonneg hnonneg
  refine ⟨a, ?_, ?_, ?_⟩
  · have hlt : (a : ℤ) < q := by
      rw [ha]
      exact Int.emod_lt_of_pos r (show (0 : ℤ) < q by omega)
    exact_mod_cast hlt
  · change Nat.gcd a q = 1
    have hg : Int.gcd (a : ℤ) q = 1 := by rw [ha, Int.gcd_emod, hr]
    simpa only [Int.gcd_natCast_natCast] using hg
  · intro n
    have he := e_emod hq n r
    have har : (a : ℝ) = (r % q : ℤ) := by exact_mod_cast ha
    rw [← har] at he
    convert he using 1 <;> congr 1 <;> ring

/-- There is a nearest reduced fraction whenever Q is positive. -/
theorem exists_nearest_farey {Q : ℕ} (hQ : 0 < Q) (α : ℝ) :
    ∃ p0 ∈ farey Q, ∀ p ∈ farey Q, dist0 (α - fareyPt p0) ≤ dist0 (α - fareyPt p) := by
  have hne : (farey Q).Nonempty := by
    refine ⟨(1, 0), mem_farey.mpr ?_⟩
    simp only [Nat.coprime_zero_left, and_true]
    omega
  exact Finset.exists_min_image (farey Q) (fun p => dist0 (α - fareyPt p)) hne

/-- All fractions other than a nearest one have geometric interval bound Q squared. -/
theorem interval_bound_off_nearest {Q : ℕ} (hQ : 0 < Q) (α t H : ℝ)
    {p0 : ℕ × ℕ} (hp0 : p0 ∈ farey Q)
    (hnear : ∀ p ∈ farey Q, dist0 (α - fareyPt p0) ≤ dist0 (α - fareyPt p))
    {p : ℕ × ℕ} (hp : p ∈ farey Q) (hne : p ≠ p0) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (α - fareyPt p))‖ ≤ (Q : ℝ) ^ 2 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsep := nearest_fraction_separated (farey Q) fareyPt α (1 / (Q : ℝ) ^ 2) p0
    hnear (fun p hp hne => farey_spaced Q p hp p0 hp0 hne) p hp hne
  have hdist : 0 < dist0 (α - fareyPt p) := lt_of_lt_of_le (by positivity) hsep
  apply (shortInterval_exp_sum_le t H _ hdist).trans
  apply (div_le_iff₀ (by positivity : 0 < 2 * dist0 (α - fareyPt p))).mpr
  have hscaled := (div_le_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) ^ 2)).mp
    (show 1 / (Q : ℝ) ^ 2 ≤ 2 * dist0 (α - fareyPt p) by linarith)
  nlinarith only [hscaled]

/-- Distinct reduced fractions have the denominator product separation. -/
theorem farey_product_separation {Q R : ℕ} {p p' : ℕ × ℕ}
    (hp : p ∈ farey Q) (hp' : p' ∈ farey R) (hne : p ≠ p') :
    1 / ((p.1 : ℝ) * p'.1) ≤ dist0 (fareyPt p - fareyPt p') := by
  have h1 : p ∈ LeanLab.PNTPort.Vinogradov.majIdx (max Q R) := by
    change p ∈ farey (max Q R)
    have h := mem_farey.mp hp
    exact mem_farey.mpr ⟨h.1, h.2.1.trans (le_max_left _ _), h.2.2⟩
  have h2 : p' ∈ LeanLab.PNTPort.Vinogradov.majIdx (max Q R) := by
    change p' ∈ farey (max Q R)
    have h := mem_farey.mp hp'
    exact mem_farey.mpr ⟨h.1, h.2.1.trans (le_max_right _ _), h.2.2⟩
  exact LeanLab.PNTPort.Vinogradov.frac_sep h1 h2 hne

#print axioms normalize_numerator
#print axioms exists_nearest_farey
#print axioms interval_bound_off_nearest
#print axioms farey_product_separation
end LeanLab.Grimmelt2019.MainTerm

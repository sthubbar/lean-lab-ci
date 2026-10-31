import LeanLab.Ternary78.BennettGrowth
import LeanLab.Ternary78.CountSummability

/-
AI wrote this Lean code. Binary Goldbach is open.
The indices are zero occurrences and retain multiplicity.
The data interface supplies finite integer height sublevels and identifies their cardinalities
with the parameter N. It is not a formalization of the analytic L-function zero set.
-/

namespace LeanLab.Ternary78.Bennett
open Real
open scoped Classical

/-- CONDITIONAL ON BennettThm1_1. The data interface and the derived polynomial
count bound prove real summability of the actual Gamma weights. -/
theorem summable_gamma_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} (γ : ι → ℝ)
    [∀ n : ℕ, Fintype {a // |γ a| ≤ (n + 1 : ℝ)}]
    (hcount : ∀ n : ℕ, N q χ (n + 1 : ℝ) = Fintype.card {a // |γ a| ≤ (n + 1 : ℝ)})
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun a => ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * Complex.I)‖) := by
  classical
  let incl (n : ℕ) (a : {a // ⌊|γ a|⌋₊ = n}) : {a // |γ a| ≤ (n + 1 : ℝ)} :=
    ⟨a.val, by
      have h := Nat.lt_floor_add_one |γ a.val|
      rw [a.property] at h
      exact h.le⟩
  have hinj (n : ℕ) : Function.Injective (incl n) := by
    intro a b h
    exact Subtype.ext (congrArg (fun (a : {a // |γ a| ≤ (n + 1 : ℝ)}) => a.val) h)
  let : ∀ n : ℕ, Fintype {a // ⌊|γ a|⌋₊ = n} :=
    fun n => Fintype.ofInjective (incl n) (hinj n)
  obtain ⟨C, _hC, hCbound⟩ := exists_quadratic_bound_of_bennett hB hq hq1 χ hχ
  apply summable_gamma_of_quadratic_bins γ (fun a => ⌊|γ a|⌋₊)
    (fun a => Nat.floor_le (abs_nonneg (γ a))) hσ
  intro n
  have hc := Fintype.card_le_of_injective (incl n) (hinj n)
  have hc' : (Fintype.card {a // ⌊|γ a|⌋₊ = n} : ℝ) ≤ (N q χ (n + 1 : ℝ) : ℝ) := by
    rw [hcount n]
    exact_mod_cast hc
  exact hc'.trans (hCbound n)

#print axioms summable_gamma_of_bennett

/-- CONDITIONAL ON BennettThm1_1 only as a cited analytic input.
The total is a convergent real sum. Convergence is proved from the same input. -/
theorem gamma_real_tsum_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (γ : ι → ℝ)
    [∀ n : ℕ, Fintype {a // |γ a| ≤ (n + 1 : ℝ)}]
    (hcountNat : ∀ n : ℕ, N q χ (n + 1 : ℝ) = Fintype.card {a // |γ a| ≤ (n + 1 : ℝ)})
    (z : Finset ι) {σ : ℝ} (hσ : 0 < σ)
    (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i) (k : ℕ)
    (hcount : ∀ i, 0 < i → i ≤ k → N q χ (t i) = (heightSet z γ t i).card) :
    weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * Complex.I)‖) k ≤
      ∑' a, ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * Complex.I)‖ := by
  have hs := summable_gamma_of_bennett hB hq hq1 χ hχ γ hcountNat hσ
  have he := gamma_tsum_lower_of_bennett hB hq hq1 χ hχ z γ hσ t ht ht0 k hcount
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs] at he
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun _ => norm_nonneg _))).mp he

#print axioms gamma_real_tsum_lower_of_bennett

end LeanLab.Ternary78.Bennett

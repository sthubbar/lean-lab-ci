import Mathlib
import LeanLab.Zhao2025.Zhao2025U6909Sub030

/-!
# Zhao 2025, the printed case `λ₁,₁ ∈ [0.40, 0.60]`, (4.10) to (4.20), wired

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6910, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

By Lemma 2.4 (5), `N(0.92) ≤ 2`, so at most `i₀ ≤ 2` sets have a zero below 0.92.  For `i > i₀`,
`Sᵢ = Rᵢ + Tᵢ` at `Λ = 1.467` with `max Rᵢ ≤ 0.157`, `Σ Rᵢ ≤ 0.457`, `max Tᵢ ≤ 0.0704`,
`Σ Tᵢ ≤ 6.33`, (4.12), (4.13); for `i ≤ i₀`, `Sᵢ ≤ Rᵢ + Tᵢ ≤ 0.374 + 0.0808` when `i₀ = 2` and
`≤ 0.556 + 0.0808` when `i₀ = 1`, (4.15), (4.16), (4.18).  Those nine inputs are certified in U-6904 and
U-6905 as `p412_ok`, `p412sum_ok`, `p413max_ok`, `p413sum_ok`, `p415_ok`, `p416_ok`, `p418N3_ok`
CONDITIONAL ON (3.15), (3.16), (3.26), (3.38), (3.42), (3.43), with `N* = 3` for (4.18).

* `layout411`, PROVED: `Σ (Rᵢ + Tᵢ)² ≤ r ΣR + t (2 ΣR + ΣT)` for `0 ≤ Rᵢ ≤ r`, `0 ≤ Tᵢ ≤ t`.
* `sub040_i02_closes`, `sub040_i01_closes`, PROVED from those inputs as hypotheses: `Σ Sᵢ² < 0.9955`.
-/

namespace LeanLab.Zhao2025.U6900

/-- PROVED: the (4.11) layout. -/
theorem layout411 (n : ℕ) (R T : ℕ → ℝ) (r t sR sT : ℝ)
    (hR : ∀ i, i < n → 0 ≤ R i ∧ R i ≤ r) (hT : ∀ i, i < n → 0 ≤ T i ∧ T i ≤ t)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ sR) (hsT : ∑ i ∈ Finset.range n, T i ≤ sT)
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 ≤ r * sR + t * (2 * sR + sT) := by
  have h1 : ∑ i ∈ Finset.range n, (R i + T i) ^ 2 ≤
      ∑ i ∈ Finset.range n, (r * R i + t * (2 * R i + T i)) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨a, b⟩ := hR i (Finset.mem_range.mp hi)
    obtain ⟨c, d⟩ := hT i (Finset.mem_range.mp hi)
    nlinarith
  have h2 : ∑ i ∈ Finset.range n, (r * R i + t * (2 * R i + T i)) =
      r * ∑ i ∈ Finset.range n, R i + t * (2 * ∑ i ∈ Finset.range n, R i +
        ∑ i ∈ Finset.range n, T i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  have h3 : 0 ≤ ∑ i ∈ Finset.range n, R i :=
    Finset.sum_nonneg (fun i hi => (hR i (Finset.mem_range.mp hi)).1)
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left hsR hr, mul_le_mul_of_nonneg_left hsR ht,
    mul_le_mul_of_nonneg_left hsT ht]

/-- PROVED: `i₀ = 2`, two head sets with `Sᵢ ≤ 0.374 + 0.0808`. -/
theorem sub040_i02_closes (n : ℕ) (R T : ℕ → ℝ) (s1 s2 : ℝ)
    (h1 : 0 ≤ s1 ∧ s1 ≤ 0.374 + 0.0808) (h2 : 0 ≤ s2 ∧ s2 ≤ 0.374 + 0.0808)
    (hR : ∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) (hT : ∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.457) (hsT : ∑ i ∈ Finset.range n, T i ≤ 6.33) :
    s1 ^ 2 + s2 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 0.9955 := by
  have := layout411 n R T 0.157 0.0704 0.457 6.33 hR hT hsR hsT (by norm_num) (by norm_num)
  nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- PROVED: `i₀ = 1`, one head set with `S₁ ≤ 0.556 + 0.0808`. -/
theorem sub040_i01_closes (n : ℕ) (R T : ℕ → ℝ) (s1 : ℝ)
    (h1 : 0 ≤ s1 ∧ s1 ≤ 0.556 + 0.0808)
    (hR : ∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) (hT : ∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.457) (hsT : ∑ i ∈ Finset.range n, T i ≤ 6.33) :
    s1 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 0.9955 := by
  have := layout411 n R T 0.157 0.0704 0.457 6.33 hR hT hsR hsT (by norm_num) (by norm_num)
  nlinarith [h1.1, h1.2]

end LeanLab.Zhao2025.U6900

#print axioms LeanLab.Zhao2025.U6900.layout411
#print axioms LeanLab.Zhao2025.U6900.sub040_i02_closes
#print axioms LeanLab.Zhao2025.U6900.sub040_i01_closes

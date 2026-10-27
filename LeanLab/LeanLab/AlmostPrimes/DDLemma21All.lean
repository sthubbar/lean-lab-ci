/-
AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1271.
P0048 A. Dudek, L. Dunn, arXiv 2602.22720, Section 2, Lemma 2.1 assembled from its four cases:
for integer `w ≥ 2` and real `z > w`, `∏_{w ≤ p < z} (1 - g(p))⁻¹ ≤ 3 (log z / log w)²`.

* Case 1, `w ≥ 286`: `DDLemma21.lemma2_1_case1`, K ≤ 1.24, needs Rosser-Schoenfeld.
* Case 2, `3 ≤ w ≤ 285`, `z ≥ 286`: a script in the paper, K ≤ 1.86, hypothesis `Case2Script`.
* Case 3, `w = 2`, `z ≥ 286`: PROVED here from Case 2 at `w = 3` and
  `DudekDunn2026.lemma2_1_case3`, K ≤ 1.49: `case3`.
* Case 4, `z < 286`: a script in the paper, K ≤ 3, hypothesis `Case4Script`.
CONDITIONAL ON `RSHyp` (Rosser-Schoenfeld Theorem 5 in the form of `hRS`), `Case2Script`
and `Case4Script`: `lemma2_1`. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDLemma21
import LeanLab.AlmostPrimes.DudekDunn2026

open Real Finset LeanLab.AlmostPrimes.DDLemma21

noncomputable section
namespace LeanLab.AlmostPrimes.DDLemma21All

/-- Rosser-Schoenfeld Theorem 5 in the form Case 1 uses, cited. -/
def RSHyp : Prop := ∀ w z : ℝ, 286 ≤ w → w < z →
  2 * ∑ p ∈ primesIn w z, (1 : ℝ) / p ≤ 2 * log (log z / log w) + 1 / (log z) ^ 2 + 1 / (log w) ^ 2

/-- Lemma 2.1 Case 2, the paper's script: `K ≤ 1.86` for `3 ≤ w ≤ 285`, `z ≥ 286`, cited. -/
def Case2Script (N : ℕ) : Prop := ∀ w : ℕ, 3 ≤ w → w ≤ 285 → ∀ z : ℝ, 286 ≤ z →
  ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 1.86 * (log z / log w) ^ 2

/-- Lemma 2.1 Case 4, the paper's computer verification: `K ≤ 3` for `z < 286`, cited. -/
def Case4Script (N : ℕ) : Prop := ∀ w : ℕ, 2 ≤ w → ∀ z : ℝ, (w : ℝ) < z → z < 286 →
  ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 3 * (log z / log w) ^ 2

lemma primesIn_two (z : ℝ) : primesIn 2 z = insert 2 (primesIn 3 z) ∨ z ≤ 2 := by
  by_cases hz : z ≤ 2
  · exact Or.inr hz
  left
  push Not at hz
  ext p
  simp only [primesIn, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hr, hp, h2, hz'⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · right
      have : 2 ≤ p := hp.two_le
      have : 3 ≤ p := by omega
      exact ⟨hr, hp, by exact_mod_cast this, hz'⟩
  · rintro (rfl | ⟨hr, hp, h3, hz'⟩)
    · refine ⟨?_, Nat.prime_two, by norm_num, by exact_mod_cast hz⟩
      have := Nat.le_ceil z
      have : (2 : ℝ) < ⌈z⌉₊ := lt_of_lt_of_le hz this
      exact_mod_cast this
    · exact ⟨hr, hp, by linarith, hz'⟩

/-- **Case 3**, `w = 2`, `z ≥ 286`: `K ≤ 1.49`, from Case 2 at `w = 3`. PROVED from `Case2Script`. -/
theorem case3 (N : ℕ) (h2 : Case2Script N) (z : ℝ) (hz : 286 ≤ z) :
    ∏ p ∈ primesIn 2 z, (1 - g N p)⁻¹ ≤ 1.49 * (log z / log 2) ^ 2 := by
  rcases primesIn_two z with he | hz2
  swap; · linarith
  have hn : (2 : ℕ) ∉ primesIn 3 z := by
    simp only [primesIn, Finset.mem_filter]; intro h; norm_num at h
  rw [he, Finset.prod_insert hn]
  have hg : (1 - g N 2)⁻¹ = 2 := by unfold g; norm_num
  rw [hg]
  have h3 := h2 3 (le_refl _) (by norm_num) z hz
  push_cast at h3
  have hc := DudekDunn2026.lemma2_1_case3
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have key : 2 * (1.86 * (log z / log 3) ^ 2) ≤ 1.49 * (log z / log 2) ^ 2 := by
    rw [div_pow, div_pow]
    have hz2 : 0 ≤ (log z) ^ 2 := sq_nonneg _
    rw [show 2 * (1.86 * ((log z) ^ 2 / (log 3) ^ 2)) = (log z) ^ 2 * (3.72 / (log 3) ^ 2) by ring,
      show 1.49 * ((log z) ^ 2 / (log 2) ^ 2) = (log z) ^ 2 * (1.49 / (log 2) ^ 2) by ring]
    apply mul_le_mul_of_nonneg_left _ hz2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith

/-- **Dudek-Dunn Lemma 2.1**, `K = 3`, for integer `w ≥ 2` and real `z > w`.
CONDITIONAL ON `RSHyp`, `Case2Script N` and `Case4Script N`. -/
theorem lemma2_1 (N : ℕ) (hRS : RSHyp) (h2 : Case2Script N) (h4 : Case4Script N)
    (w : ℕ) (hw : 2 ≤ w) (z : ℝ) (hwz : (w : ℝ) < z) :
    ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 3 * (log z / log w) ^ 2 := by
  have hsq : 0 ≤ (log z / log w) ^ 2 := sq_nonneg _
  by_cases hz : z < 286
  · exact h4 w hw z hwz hz
  push Not at hz
  by_cases h286 : 286 ≤ w
  · have := lemma2_1_case1 N w z (by exact_mod_cast h286) hwz (hRS w z (by exact_mod_cast h286) hwz)
    linarith
  push Not at h286
  by_cases hw2 : w = 2
  · subst hw2
    have := case3 N h2 z hz
    push_cast
    linarith
  · have := h2 w (by omega) (by omega) z hz
    linarith

#print axioms case3
#print axioms lemma2_1

end LeanLab.AlmostPrimes.DDLemma21All

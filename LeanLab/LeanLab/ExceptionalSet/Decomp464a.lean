import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_index
import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_endpoint
import LeanLab.ExceptionalSet.Decomp404b

/-!
P0082 page 356, elementary inputs for the two adjacent Fourier frequencies.
Exact clean companions preserve all original split files and their sealed statements.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464a

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_shift (v : ℝ) (m : ℤ) :
    v + (m : ℝ) = Int.fract v + ((m + ⌊v⌋ : ℤ) : ℝ) := by
  simp only [Int.fract, Int.cast_add]
  ring

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_ne_zero (v : ℝ) (m : ℤ) (hm : m ≠ -⌊v⌋) :
    m + ⌊v⌋ ≠ 0 := by
  omega

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_ne_neg_one (v : ℝ) (m : ℤ) (hm : m ≠ -(⌊v⌋ + 1)) :
    m + ⌊v⌋ ≠ -1 := by
  omega

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_dichotomy (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ -1) :
    1 ≤ k ∨ k ≤ -2 := by
  omega

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_upper (v : ℝ) (k : ℤ) (hk : 1 ≤ k) :
    1 ≤ |Int.fract v + (k : ℝ)| := by
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact (by linarith [Int.fract_nonneg v] : (1 : ℝ) ≤ Int.fract v + (k : ℝ)).trans
    (le_abs_self _)

/-- P0082 page 356, adjacent frequency reduction in the Poisson display.
Exact clean companion for the open index leaf. -/
theorem leaf_poisson_index_lower (v : ℝ) (k : ℤ) (hk : k ≤ -2) :
    1 ≤ |Int.fract v + (k : ℝ)| := by
  have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast hk
  have hneg : Int.fract v + (k : ℝ) ≤ -1 := by linarith [Int.fract_lt_one v]
  calc (1 : ℝ) ≤ -(Int.fract v + (k : ℝ)) := by linarith
    _ ≤ |Int.fract v + (k : ℝ)| := neg_le_abs _

/-- P0082 page 356, exact original split statement from the completed companions. -/
theorem leaf_poisson_index_split (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
  intro m hm hm'
  rw [leaf_poisson_index_shift v m]
  have h0 : m + ⌊v⌋ ≠ 0 := leaf_poisson_index_ne_zero v m hm
  have h1 : m + ⌊v⌋ ≠ -1 := leaf_poisson_index_ne_neg_one v m hm'
  rcases leaf_poisson_index_dichotomy (m + ⌊v⌋) h0 h1 with hk | hk
  · exact leaf_poisson_index_upper v (m + ⌊v⌋) hk
  · exact leaf_poisson_index_lower v (m + ⌊v⌋) hk

end LeanLab.ExceptionalSet.Decomp464a

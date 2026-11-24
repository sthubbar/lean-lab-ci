/-
Jia 1996 Lemma 27, pages 281 and 282, with Lemma 21 on page 262 and display 40 on page 261.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564c.rough12_to_integral into cited LEAF steps, burst-20261122.
The Buchstab leaves and the generic assembly are shared from Feed564bRough.
The parent statement is proved below from the leaves, CONDITIONAL ON the open leaves
and on nothing else.
-/
import LeanLab.Languasco2004.Feed564bRough

namespace LeanLab.Languasco2004.Feed564cRough
open Finset Real Decomp279a Decomp316c Model564 RemainderData564 Feed564bRough
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia pages 281 and 282 with Lemma 21 on page 262, applied to each cofactor count
S of B_pq and q over regions 53 and 66, then summed; the Lemma 21 error is absorbed by the
Mertens bound for the sum of t over log q over these two regions. HARD -/
theorem rough12_lemma21_sum (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      buchstabMain labels12 w Y - η * (Y / Real.log Y) ≤ roughModel labels12 Y := by sorry

/-- LEAF: Jia pages 281 and 282, the prime number theorem Riemann sum step: the double prime
sum of the Lemma 21 main term over regions 53 and 66 is at least the Buchstab integral over
the seven printed subdomains, rows eleven to seventeen, times Y over log Y. HARD -/
theorem buchstabMain12_riemann (w : ℝ → ℝ) (hw : IsBuchstab w) (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), fullRow w i) - η) *
        (Y / Real.log Y) ≤ buchstabMain labels12 w Y := by sorry

/-- Jia Lemma 27 pages 281 and 282: Decomp564c.rough12_to_integral from the leaves.
CONDITIONAL ON rough12_lemma21_sum and buchstabMain12_riemann. Same type as the parent. -/
theorem rough12_to_integral_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (integral12 - δ) * Y / Real.log Y ≤ roughModel labels12 Y := by
  obtain ⟨w, hw⟩ := isBuchstab_exists
  have hrow : integral12 ≤
      ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), fullRow w i :=
    sum_le_sum fun i _ => row_integral_lower' w hw.1
      (buchstab_initial_segment w hw) (buchstab_global_lower w hw) i
  exact family_from_buchstab labels12 _ _ w hrow (rough12_lemma21_sum w hw)
    (buchstabMain12_riemann w hw) δ hδ

#print axioms rough12_lemma21_sum
#print axioms buchstabMain12_riemann
#print axioms rough12_to_integral_from_leaves
end
end LeanLab.Languasco2004.Feed564cRough

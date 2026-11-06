import LeanLab.ExceptionalSet.BhowmikGrimmelt2026
import LeanLab.ExceptionalSet.MVConditional

/-!
The counting step after P0029 page 13 display 3.8.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real ArithmeticFunction

noncomputable section

/-- The paper error E2 on even indices, using the existing even Euler product.
Source: P0029 page 13 before display 3.8. The same formula extends to other indices. -/
def error (n : ℕ) : ℝ := r2 n - (n : ℝ) * Sing n

/-- The count bound E of X at most X gives every exponent at least one.
Source: P0029 page 9 Theorem 3.1, the trivial large exponent range. -/
theorem powerBound_of_one_le {θ : ℝ} (hθ : 1 ≤ θ) : PowerBound θ := by
  apply powerBound_mono hθ
  refine ⟨1, fun X _ => ?_⟩
  simpa only [Real.rpow_one, one_mul] using (show (E X : ℝ) ≤ X by exact_mod_cast E_le X)

/-- Finite Chebyshev counting on a specified subset, P0029 page 13. -/
theorem count_from_energy {s t : Finset ℕ} {f : ℕ → ℝ} {a B : ℝ}
    (ha : 0 < a) (hst : s ⊆ t)
    (hlarge : ∀ n ∈ s, a ≤ |f n|)
    (henergy : ∑ n ∈ t, (f n) ^ 2 ≤ B) :
    (s.card : ℝ) ≤ B / a ^ 2 := by
  have hlow : (s.card : ℝ) * a ^ 2 ≤ ∑ n ∈ s, (f n) ^ 2 := by
    simpa only [nsmul_eq_mul] using s.card_nsmul_le_sum (fun n => (f n) ^ 2) (a ^ 2)
      (fun n hn => by nlinarith [hlarge n hn, sq_abs (f n)])
  have hsum : ∑ n ∈ s, (f n) ^ 2 ≤ ∑ n ∈ t, (f n) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _)
  exact (le_div_iff₀ (sq_pos_of_pos ha)).mpr (hlow.trans (hsum.trans henergy))

/-- A window error lower bound and a mean square bound give the exceptional window count.
Source: P0029 page 13 display 3.8 and its following calculation. -/
theorem window_from_energy {X : ℕ} {θ C c : ℝ} (hX : 1 ≤ X) (hc : 0 < c)
    (hlarge : ∀ n ∈ Icc (X / 2 + 1) X, Even n → ¬ IsGoldbachSum n →
      c * (X : ℝ) ≤ |error n|)
    (henergy : ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
      C * (X : ℝ) ^ (θ + 2)) :
    (MV.badWindow X : ℝ) ≤ (C / c ^ 2) * (X : ℝ) ^ θ := by
  classical
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have h := count_from_energy (f := error) (a := c * (X : ℝ))
    (by positivity)
    (s := (Icc (X / 2 + 1) X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n))
    (t := (range (X + 1)).filter Even)
    (fun n hn => mem_filter.mpr ⟨mem_range.mpr
      (by have := (mem_Icc.mp (mem_filter.mp hn).1).2; omega), (mem_filter.mp hn).2.1⟩)
    (fun n hn => hlarge n (mem_filter.mp hn).1 (mem_filter.mp hn).2.1
      (mem_filter.mp hn).2.2) henergy
  have hp : (X : ℝ) ^ (θ + 2) = (X : ℝ) ^ θ * (X : ℝ) ^ 2 := by
    rw [Real.rpow_add hx, Real.rpow_two]
  change (((Icc (X / 2 + 1) X).filter
    (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤ _
  convert h using 1
  rw [hp]
  field_simp

end

end LeanLab.ExceptionalSet.BG2026.Supply385

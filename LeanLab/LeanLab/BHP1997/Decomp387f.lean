/-
BHP1997, pages 3 and 52. The logarithmic center transfer on supported intervals.
The raw variable-center cancellation estimate remains explicit.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp387e

namespace LeanLab.BHP1997.Task387
open Classical

/-- Pages 3 and 52, auxiliary supported normalization. On an Ioc interval
inside the dyadic range, logarithmic rescaling changes the variable
reciprocal-log center to the constant center at cost at most three.
CONDITIONAL on the raw centered prefix estimates. -/
theorem logarithmic_center_rescaling_Ioc (Y : ℝ) (L U : ℕ)
    (c : ℕ → ℂ) (d v : ℂ) {R : ℝ}
    (hY : 2 ≤ Y) (hL : Y ≤ ((L+1 : ℕ) : ℝ)) (hU : (U : ℝ) ≤ 2*Y)
    (hLU : L < U) (hR : 0 ≤ R)
    (hc : ∀ k ≤ U-L, ‖∑ m ∈ Finset.Ioc L (L+k),
      (c m-d*v/(Real.log m : ℂ))‖ ≤ R) :
    ‖∑ m ∈ Finset.Ioc L U,
      (((Real.log m/Real.log Y : ℝ) : ℂ)*c m-d*v/(Real.log Y : ℂ))‖ ≤ 3*R := by
  have hsum (k : ℕ) (F : ℕ → ℂ) :
      (∑ m ∈ Finset.Ioc L (L+k), F m) =
        ∑ i ∈ Finset.range k, F (L+1+i) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
    rw [show L+k+1-(L+1) = k by omega]
  have hpref : ∀ k ≤ U-L, ‖∑ i ∈ Finset.range k,
      (c ((L+1)+i)-d*v/(Real.log ((L+1)+i) : ℂ))‖ ≤ R := by
    intro k hk
    have hh := hc k hk
    rw [hsum] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hlast : (((L+1)+((U-L)-1) : ℕ) : ℝ) ≤ 2*Y := by
    have he : (L+1)+((U-L)-1) = U := by omega
    simpa only [he] using hU
  have hh := logarithmic_center_rescaling Y (L+1) (U-L) c d v hY hL hlast hR
    (by simpa only [Nat.cast_add, Nat.cast_one] using hpref)
  have he : L+(U-L) = U := by omega
  rw [← he, hsum]
  simpa only [Nat.cast_add, Nat.cast_one] using hh

end LeanLab.BHP1997.Task387

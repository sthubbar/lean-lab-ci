/-
BHP1997, page 52. The integer endpoint error in a density center.
The containment premise is essential near the endpoints of J.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp387a

namespace LeanLab.BHP1997.Task387
open Classical Complex MeasureTheory

/-- Page 3 condition iv and page 52 normalization. If the full integer
window lies in the support, the filtered window is the expected integer interval. -/
theorem window_eq_integer_interval {S : Finset ℕ} {y z : ℝ}
    (hyz : 0 ≤ y+y*z)
    (hs : Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ ⊆ S) :
    window S y z = Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ := by
  ext m
  simp only [window, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hm, hyl, hyu⟩
    exact ⟨Nat.ceil_le.mpr hyl, (Nat.le_floor_iff hyz).mpr hyu⟩
  · rintro ⟨hyl, hyu⟩
    exact ⟨hs (Finset.mem_Icc.mpr ⟨hyl, hyu⟩),
      Nat.ceil_le.mp hyl, (Nat.le_floor_iff hyz).mp hyu⟩

/-- Page 52 normalization. Away from support clipping, the integer count
in a closed moving window differs from its real length by at most one. -/
theorem window_card_length_error {S : Finset ℕ} {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ ⊆ S) :
    |((window S y z).card : ℝ)-y*z| ≤ 1 := by
  have hlen : 0 ≤ y*z := mul_nonneg hy hz
  have hyz : 0 ≤ y+y*z := by linarith
  have hceil : ⌈y⌉₊ ≤ ⌊y+y*z⌋₊+1 :=
    (Nat.ceil_mono (by linarith : y ≤ y+y*z)).trans (Nat.ceil_le_floor_add_one _)
  rw [window_eq_integer_interval hyz hs, Nat.card_Icc, Nat.cast_sub hceil, Nat.cast_add]
  norm_num only [Nat.cast_one]
  have hfl := Nat.floor_le hyz
  have hfu := Nat.lt_floor_add_one (y+y*z)
  have hcl := Nat.le_ceil y
  have hcu := Nat.ceil_lt_add_one hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Page 52 normalization. The endpoint count error changes a constant
complex density center by at most the norm of that density. -/
theorem window_center_length_error {S : Finset ℕ} {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : Finset.Icc ⌈y⌉₊ ⌊y+y*z⌋₊ ⊆ S) (u : ℂ) :
    ‖windowCenter S u z y-((y*z : ℝ) : ℂ)*u‖ ≤ ‖u‖ := by
  have he : windowCenter S u z y-((y*z : ℝ) : ℂ)*u =
      (((((window S y z).card : ℕ) : ℝ)-y*z : ℝ) : ℂ)*u := by
    simp only [windowCenter, Complex.ofReal_sub, Complex.ofReal_natCast]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (window_card_length_error hy hz hs) (norm_nonneg u)).trans_eq
    (one_mul _)

/-- Page 3 condition iv. Intersecting the actual support Ioc with the
closed moving window gives this clipped integer interval exactly. -/
theorem supported_window_eq_interval (L U : ℕ) {y z : ℝ}
    (hyz : 0 ≤ y+y*z) :
    window (Finset.Ioc L U) y z =
      Finset.Icc (max (L+1) ⌈y⌉₊) (min U ⌊y+y*z⌋₊) := by
  ext m
  simp only [window, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
    max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hmL, hmU⟩, hyl, hyu⟩
    exact ⟨⟨by omega, Nat.ceil_le.mpr hyl⟩, ⟨hmU, (Nat.le_floor_iff hyz).mpr hyu⟩⟩
  · rintro ⟨⟨hmL, hyl⟩, hmU, hyu⟩
    exact ⟨⟨by omega, hmU⟩, Nat.ceil_le.mp hyl, (Nat.le_floor_iff hyz).mp hyu⟩

/-- Page 3 condition iv. The exact cardinality formula retains clipping
at both endpoints of the supported sequence. Natural subtraction handles
an empty intersection without an extra analytic assumption. -/
theorem supported_window_card (L U : ℕ) {y z : ℝ}
    (hyz : 0 ≤ y+y*z) :
    (window (Finset.Ioc L U) y z).card =
      min U ⌊y+y*z⌋₊+1-max (L+1) ⌈y⌉₊ := by
  rw [supported_window_eq_interval L U hyz, Nat.card_Icc]

end LeanLab.BHP1997.Task387

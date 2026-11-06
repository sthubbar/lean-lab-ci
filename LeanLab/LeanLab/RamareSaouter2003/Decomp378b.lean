import LeanLab.RamareSaouter2003.Decomp378a
import LeanLab.RamareSaouter2003.Decomp359a
import LeanLab.RamareSaouter2003.Decomp359c

/-!
P0099 p. 14, Lemma 2, and pp. 19 and 20, displays 13 to 15.
Qualitative convergence needs no explicit Rosser count constant.
PNTPort already proves the required reciprocal product summability.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp378b
open Real Smooth L3Zeta Decomp290c

/-- LEAF. P0099 p. 14, the convergence underlying Lemma 2.
On the ordinate tail, the product of the two complex norms is at most
four times the ordinate square. This compares two summable majorants. -/
theorem reciprocal_power_bound (m : ℕ) (hm : 1 ≤ m) (i : ZI) :
    (if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0) ≤
      4 * (1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖) := by
  by_cases hi : (1000 : ℝ) < |gZ i|
  · rw [if_pos hi]
    have h0 := (bZ_mem i).1
    have h1 := (bZ_mem i).2
    have hn : ‖(i.1 : ℂ)‖ ≤ 2 * |gZ i| := by
      have hh := Complex.norm_le_abs_re_add_abs_im (i.1 : ℂ)
      change ‖(i.1 : ℂ)‖ ≤ |bZ i| + |gZ i| at hh
      rw [abs_of_nonneg h0] at hh
      linarith
    have hn1 : ‖(i.1 : ℂ) + 1‖ ≤ 2 * |gZ i| := by
      have hh := Complex.norm_le_abs_re_add_abs_im ((i.1 : ℂ) + 1)
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
        add_zero] at hh
      change ‖(i.1 : ℂ) + 1‖ ≤ |bZ i + 1| + |gZ i| at hh
      rw [abs_of_nonneg (by linarith)] at hh
      linarith
    have hprod : ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖ ≤ 4 * |gZ i| ^ 2 := by
      rw [norm_mul]
      calc _ ≤ (2 * |gZ i|) * (2 * |gZ i|) :=
                 mul_le_mul hn hn1 (norm_nonneg _) (by positivity)
           _ = _ := by ring
    have hne : (i.1 : ℂ) ≠ 0 := by
      intro hh
      have hr := (mem_strip i.1).2.1
      rw [hh] at hr
      norm_num at hr
    have hne1 : (i.1 : ℂ) + 1 ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
      have := (mem_strip i.1).2.1
      linarith
    have hp : 0 < ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖ := norm_pos_iff.mpr (mul_ne_zero hne hne1)
    calc
      1 / |gZ i| ^ (m + 1) ≤ 1 / |gZ i| ^ 2 :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by linarith : 1 ≤ |gZ i|) (by omega))
      _ ≤ 4 * (1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖) := by
        rw [mul_one_div]
        exact (div_le_div_iff₀ (by positivity : 0 < |gZ i| ^ 2) hp).mpr
          (by simpa only [one_mul] using hprod)
  · rw [if_neg hi]
    positivity

/-- P0099 p. 14, exactly the original reciprocal_tail_summable statement.
The qualitative PNTPort bound suffices, with no explicit count citation. -/
theorem reciprocal_tail_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      1 / |gZ i| ^ (m + 1) else 0) := by
  exact Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (reciprocal_power_bound m hm) (Decomp378a.reciprocal_product_summable.mul_left 4)

/-- P0099 pp. 19 and 20, exactly the original zeroTerm_summable statement.
Finite near support and the proved far majorant now give unconditional convergence. -/
theorem zeroTerm_summable (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Summable (zeroTerm m X u) := by
  classical
  obtain ⟨C, _, hC⟩ := Decomp359c.far_norm_majorant m X u hm hX hu hmu
  have hf : Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then zeroTerm m X u i else 0) :=
    Summable.of_norm_bounded ((reciprocal_tail_summable m (by omega)).mul_left C) hC
  have hn : Summable (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then zeroTerm m X u i else 0) :=
    summable_of_hasFiniteSupport (Decomp359a.near_support_finite m X u)
  convert hn.add hf using 1
  funext i
  by_cases hi : |gZ i| ≤ (1000 : ℝ)
  · simp [hi, not_lt.mpr hi]
  · simp [hi, lt_of_not_ge hi]

end LeanLab.RamareSaouter2003.Decomp378b
#print axioms LeanLab.RamareSaouter2003.Decomp378b.reciprocal_power_bound
#print axioms LeanLab.RamareSaouter2003.Decomp378b.reciprocal_tail_summable
#print axioms LeanLab.RamareSaouter2003.Decomp378b.zeroTerm_summable

import LeanLab.ChenDoubleSieve.Task587SharpTail
import LeanLab.ChenDoubleSieve.Task587Kernel
import LeanLab.ChenDoubleSieve.Task562Boxes
import LeanLab.ChenDoubleSieve.Task587Row3NineIdentity
import LeanLab.ChenDoubleSieve.Task587Row3TenCertificate
import LeanLab.ChenDoubleSieve.Task587Row3ElevenCertificate
import LeanLab.ChenDoubleSieve.Task587Row3ThirteenCertificate
import LeanLab.ChenDoubleSieve.Task587Row3FourteenCertificate

/-!
Earlier certified phi tails for the five row four integrals of Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- A three dimensional reciprocal polynomial controls the phi tail from thirteen fifths.
Wu 2004 page 26, derived uniform reduction on positive boxes below two fifths. -/
theorem integral_le_poly_early {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    (lo hi : Fin 3 → ℝ) {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ)
    (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j ≤ (2 / 5 : ℝ))
    (P : (Fin 3 → ℝ) → ℝ) (hP : IntegrableOn P (domain lo hi) volume)
    (hmajor : ∀ x ∈ domain lo hi, 1 / ((∏ j, x j) * x 1) ≤ P x) :
    buchstabIntegral ω 1 lo hi φ ≤ (5618 / 10000 : ℝ) * ∫ x in domain lo hi, P x := by
  have harg (x : Fin 3 → ℝ) (hx : x ∈ domain lo hi) :
      (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x 1 := by
    apply Task562.argument_ge_of_box (1 : Fin 3) (lo := lo)
      (hi := fun _ => (2 / 5 : ℝ)) (P := 13 / 5) (by norm_num)
      ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2.trans (hhi j)⟩
      ((hlo 1).trans_le (hx.2 1).1) hφ
    norm_num
  have hf := kernel_integrable_above_one hω lo hi φ hlo
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 7 / 2).trans (harg x hx))
  have hm := setIntegral_mono_on hf (hP.const_mul (5618 / 10000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin 3) : 0 < x j := (hlo j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x 1 := mul_pos (prod_pos fun j _ => hp j) (hp 1)
      have hw := div_le_div_of_nonneg_right (buchstab_le_5618 hω (harg x hx)) hd.le
      calc
        _ ≤ (5618 / 10000 : ℝ) / ((∏ j, x j) * x 1) := hw
        _ = (5618 / 10000 : ℝ) * (1 / ((∏ j, x j) * x 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmajor x hx) (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

/-- The exact row four D2,9 budget already holds from phi thirteen fifths.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Nine_integral_early_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤
      (12408337 / 1000000000 : ℝ) := by
  have h := integral_le_poly_early hω (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ))
    hφ (by intros; norm_num) (by intros; norm_num) r3NinePoly r3NinePoly_integrable
    (fun x hx => r3Nine_reciprocal_le_poly hx)
  exact h.trans ((mul_le_mul_of_nonneg_left r3Nine_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 5618 / 10000)).trans (by norm_num))

/-- The exact row four D2,10 budget already holds from phi thirteen fifths.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Ten_integral_early_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3TenLo r3TenHi φ ≤ (2710363 / 500000000 : ℝ) := by
  have h := integral_le_poly_early hω r3TenLo r3TenHi hφ
    (by intro j; fin_cases j <;> norm_num [r3TenLo])
    (by intro j; fin_cases j <;> norm_num [r3TenHi])
    r3TenPoly r3TenPoly_integrable (fun x hx => r3Ten_reciprocal_le_poly hx)
  exact h.trans ((mul_le_mul_of_nonneg_left r3Ten_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 5618 / 10000)).trans (by norm_num))

/-- The exact row four D2,11 budget already holds from phi thirteen fifths.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Eleven_integral_early_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3ElevenLo r3ElevenHi φ ≤ (1821597 / 500000000 : ℝ) := by
  have h := integral_le_poly_early hω r3ElevenLo r3ElevenHi hφ
    (by intro j; fin_cases j <;> norm_num [r3ElevenLo])
    (by intro j; fin_cases j <;> norm_num [r3ElevenHi])
    r3ElevenPoly r3ElevenPoly_integrable (fun x hx => r3Eleven_reciprocal_le_poly hx)
  exact h.trans ((mul_le_mul_of_nonneg_left r3Eleven_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 5618 / 10000)).trans (by norm_num))

/-- The exact row four D2,13 budget already holds from phi thirteen fifths.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Thirteen_integral_early_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3ThirteenLo r3ThirteenHi φ ≤ (8106273 / 1000000000 : ℝ) := by
  have h := integral_le_poly_early hω r3ThirteenLo r3ThirteenHi hφ
    (by intro j; fin_cases j <;> norm_num [r3ThirteenLo])
    (by intro j; fin_cases j <;> norm_num [r3ThirteenHi])
    r3ThirteenPoly r3ThirteenPoly_integrable (fun x hx => r3Thirteen_reciprocal_le_poly hx)
  exact h.trans ((mul_le_mul_of_nonneg_left r3Thirteen_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 5618 / 10000)).trans (by norm_num))

/-- The exact row four D2,14 budget already holds from phi thirteen fifths.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Fourteen_integral_early_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 r3FourteenLo r3FourteenHi φ ≤ (2640381 / 1000000000 : ℝ) := by
  have h := integral_le_poly_early hω r3FourteenLo r3FourteenHi hφ
    (by intro j; fin_cases j <;> norm_num [r3FourteenLo])
    (by intro j; fin_cases j <;> norm_num [r3FourteenHi])
    r3FourteenPoly r3FourteenPoly_integrable (fun x hx => r3Fourteen_reciprocal_le_poly hx)
  exact h.trans ((mul_le_mul_of_nonneg_left r3Fourteen_polynomial_certificate
    (by norm_num : (0 : ℝ) ≤ 5618 / 10000)).trans (by norm_num))

end LeanLab.ChenDoubleSieve.Task587

/-
Helpers for `leaf_338_exponent` in SPLIT_lemma10_small_L_338.
P0069 page 24, the exponent count under (3.38): the three norm bounds multiply to at most
2 L^(B1+B2+B3+|A0|) x^(1/2 - 5 eps/48), and x^(5 eps/48) beats every power of L.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Filter Asymptotics
open scoped Real

/-- Eventually every power of `L x` is at most `x ^ δ`, for `δ > 0`. -/
theorem exp338_log_pow_le_rpow (K δ : ℝ) (hδ : 0 < δ) :
    ∃ X : ℝ, ∀ x, X ≤ x → L x ^ K ≤ x ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop K hδ).bound one_pos
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hb := hX x ((le_max_left _ _).trans hx)
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
  exact hb

/-- The pointwise exponent count, page 24, under (3.38) and T <= T1, for one configuration. -/
theorem exp338_core (ε A0 B1 B2 B3 A x q T Ml Nl : ℝ) (hε : 0 < ε)
    (hx1 : 1 ≤ x) (hℓ1 : 1 ≤ L x) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hqA : q ≤ L x ^ A0) (hT1 : T ≤ x ^ (0.45 - 2 * ε / 3))
    (h338 : max Ml (x ^ (0.45 : ℝ)) * max Nl (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8))
    (hpow : L x ^ (B1 + B2 + B3 + |A0| + A) ≤ x ^ (5 * ε / 48)) :
    (L x ^ B1 * (q * T + max Ml 0) ^ (1 / 2 : ℝ)) *
        (L x ^ B2 * (q * T + max Nl 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (L x ^ B3 * (q * T) ^ (1 / 4 : ℝ)) ≤ 2 * x ^ (1 / 2 : ℝ) / L x ^ A := by
  set ℓ := L x with hℓ
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set m := max Ml (x ^ (0.45 : ℝ)) with hm
  set n := max Nl (x ^ (0.225 : ℝ)) with hn
  set D : ℝ := 2 * ℓ ^ |A0| with hD
  have hA1 : 1 ≤ ℓ ^ |A0| := Real.one_le_rpow hℓ1 (abs_nonneg _)
  have hD2 : 2 ≤ D := by rw [hD]; linarith
  have hD0 : 0 ≤ D := by linarith
  have hx45 : 0 < x ^ (0.45 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hx225 : 0 < x ^ (0.225 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hm0 : x ^ (0.45 : ℝ) ≤ m := le_max_right _ _
  have hn0 : x ^ (0.225 : ℝ) ≤ n := le_max_right _ _
  have hmpos : 0 < m := lt_of_lt_of_le hx45 hm0
  have hnpos : 0 < n := lt_of_lt_of_le hx225 hn0
  have hsq : x ^ (0.45 : ℝ) = (x ^ (0.225 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  -- q T bounds
  have hqT0 : 0 ≤ q * T := mul_nonneg hq hT
  have hqAabs : q ≤ ℓ ^ |A0| := hqA.trans (Real.rpow_le_rpow_of_exponent_le hℓ1 (le_abs_self _))
  have hTpos : 0 ≤ x ^ (0.45 - 2 * ε / 3) := Real.rpow_nonneg hx0.le _
  have hqT : q * T ≤ ℓ ^ |A0| * x ^ (0.45 - 2 * ε / 3) :=
    mul_le_mul hqAabs hT1 hT (by linarith)
  have hT45 : x ^ (0.45 - 2 * ε / 3) ≤ x ^ (0.45 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hqT45 : q * T ≤ ℓ ^ |A0| * x ^ (0.45 : ℝ) :=
    hqT.trans (mul_le_mul_of_nonneg_left hT45 (by linarith))
  -- the three factors
  have hF1 : (q * T + max Ml 0) ^ (1 / 2 : ℝ) ≤ D ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hD0 hmpos.le]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have h1 : max Ml 0 ≤ m := max_le (le_max_left _ _) hmpos.le
    have h2 : ℓ ^ |A0| * x ^ (0.45 : ℝ) ≤ ℓ ^ |A0| * m :=
      mul_le_mul_of_nonneg_left hm0 (by linarith)
    rw [hD]; nlinarith
  have hF2 : (q * T + max Nl 0 ^ 2) ^ (1 / 4 : ℝ) ≤ D ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ) := by
    have hn2 : (n ^ 2) ^ (1 / 4 : ℝ) = n ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
    rw [← hn2, ← Real.mul_rpow hD0 (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have h1 : max Nl 0 ^ 2 ≤ n ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) (max_le (le_max_left _ _) hnpos.le) 2
    have h0 : (x ^ (0.225 : ℝ)) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hx225.le hn0 2
    have h2 : ℓ ^ |A0| * x ^ (0.45 : ℝ) ≤ ℓ ^ |A0| * n ^ 2 := by
      rw [hsq]; exact mul_le_mul_of_nonneg_left h0 (by linarith)
    rw [hD]; nlinarith
  set b : ℝ := (0.45 - 2 * ε / 3) * (1 / 4) with hb
  have hF3 : (q * T) ^ (1 / 4 : ℝ) ≤ D ^ (1 / 4 : ℝ) * x ^ b := by
    have hxb : (x ^ (0.45 - 2 * ε / 3)) ^ (1 / 4 : ℝ) = x ^ b := by
      rw [← Real.rpow_mul hx0.le]
    rw [← hxb, ← Real.mul_rpow hD0 hTpos]
    apply Real.rpow_le_rpow hqT0 _ (by norm_num)
    rw [hD]; nlinarith
  set a : ℝ := (0.775 + ε / 8) * (1 / 2) with ha
  have hmn : m ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) ≤ x ^ a := by
    rw [← Real.mul_rpow hmpos.le hnpos.le, ha, Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (by positivity) h338 (by norm_num)
  have hDD : D ^ (1 / 2 : ℝ) * D ^ (1 / 4 : ℝ) * D ^ (1 / 4 : ℝ) = D := by
    rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
    norm_num
  set δ : ℝ := 5 * ε / 48 with hδ
  have hab : x ^ a * x ^ b = x ^ (1 / 2 : ℝ) * x ^ (-δ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ha, hb, hδ]
    congr 1
    ring
  have hprod : (ℓ ^ B1 * (q * T + max Ml 0) ^ (1 / 2 : ℝ)) *
        (ℓ ^ B2 * (q * T + max Nl 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (ℓ ^ B3 * (q * T) ^ (1 / 4 : ℝ)) ≤
      (ℓ ^ B1 * (D ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ))) *
        (ℓ ^ B2 * (D ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ))) *
        (ℓ ^ B3 * (D ^ (1 / 4 : ℝ) * x ^ b)) := by
    gcongr
  have hS : ℓ ^ B1 * ℓ ^ B2 * ℓ ^ B3 * ℓ ^ |A0| * ℓ ^ A = ℓ ^ (B1 + B2 + B3 + |A0| + A) := by
    rw [Real.rpow_add hℓ0, Real.rpow_add hℓ0, Real.rpow_add hℓ0, Real.rpow_add hℓ0]
  have hδ1 : x ^ δ * x ^ (-δ) = 1 := by
    rw [← Real.rpow_add hx0]; simp
  have hℓA : 0 < ℓ ^ A := Real.rpow_pos_of_pos hℓ0 A
  rw [le_div_iff₀ hℓA]
  have hxd : 0 ≤ x ^ (-δ) := Real.rpow_nonneg hx0.le _
  have hxh : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  calc _ ≤ (ℓ ^ B1 * (D ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ))) *
        (ℓ ^ B2 * (D ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ))) *
        (ℓ ^ B3 * (D ^ (1 / 4 : ℝ) * x ^ b)) * ℓ ^ A :=
        mul_le_mul_of_nonneg_right hprod hℓA.le
    _ = ℓ ^ B1 * ℓ ^ B2 * ℓ ^ B3 * (D ^ (1 / 2 : ℝ) * D ^ (1 / 4 : ℝ) * D ^ (1 / 4 : ℝ)) *
        (m ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ)) * x ^ b * ℓ ^ A := by ring
    _ ≤ ℓ ^ B1 * ℓ ^ B2 * ℓ ^ B3 * (D ^ (1 / 2 : ℝ) * D ^ (1 / 4 : ℝ) * D ^ (1 / 4 : ℝ)) *
        x ^ a * x ^ b * ℓ ^ A := by
        gcongr
    _ = 2 * x ^ (1 / 2 : ℝ) * ((ℓ ^ B1 * ℓ ^ B2 * ℓ ^ B3 * ℓ ^ |A0| * ℓ ^ A) * x ^ (-δ)) := by
        rw [hDD, mul_assoc _ (x ^ a) (x ^ b), hab, hD]; ring
    _ ≤ 2 * x ^ (1 / 2 : ℝ) * (x ^ δ * x ^ (-δ)) := by
        rw [hS]; gcongr
    _ = 2 * x ^ (1 / 2 : ℝ) := by rw [hδ1, mul_one]

#print axioms exp338_log_pow_le_rpow
#print axioms exp338_core

end LeanLab.BakerHarmanPintz1997

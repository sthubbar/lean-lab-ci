/-
Scale bookkeeping for Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Periodicity

namespace LeanLab.BhowmikGrimmelt2026

/-- At scales K R q, the weight is bounded globally and small away from one selected pair. -/
theorem scaled_GThat_bounds {G : ℝ → ℝ} (hG : IsMajorWeight G) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ K R q β : ℝ, 1 ≤ K → 1 ≤ R → 1 ≤ q →
      ‖GThat G (K * R * q) β‖ ≤ C * (1 + K ^ (-A)) ∧
      (1 / 2 ≤ q * R * intDist β →
        ‖GThat G (K * R * q) β‖ ≤ C * (2 ^ A + 1) * K ^ (-A)) := by
  obtain ⟨C, hC, hbound⟩ := GThat_bound hG.supp hG.smooth A
  refine ⟨C, hC, fun K R q β hK hR hq => ?_⟩
  have hK0 : 0 < K := by linarith
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  have hRq : 1 ≤ R * q := by
    have h := mul_le_mul_of_nonneg_left hq hR0.le
    nlinarith only [h, hR]
  have hKT : K ≤ K * R * q := by
    have h := mul_le_mul_of_nonneg_left hRq hK0.le
    nlinarith only [h]
  have hT1 : 1 ≤ K * R * q := hK.trans hKT
  have hp := Real.rpow_le_rpow_of_nonpos hK0 hKT (neg_nonpos.mpr hA.le)
  have hb := hbound (K * R * q) β hT1
  constructor
  · have hz : (1 + K * R * q * intDist β) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [mul_nonneg (show 0 ≤ K * R * q by positivity) (intDist_nonneg β)])
        (neg_nonpos.mpr hA.le)
    exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hz hp) hC.le)
  · intro hgap
    have hs : K / 2 ≤ 1 + K * R * q * intDist β := by
      have h := mul_le_mul_of_nonneg_left hgap hK0.le
      nlinarith only [h]
    have hd := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < K / 2) hs
      (neg_nonpos.mpr hA.le)
    have heq : (K / 2) ^ (-A) = 2 ^ A * K ^ (-A) := by
      rw [Real.div_rpow hK0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
      ring
    rw [heq] at hd
    calc
      _ ≤ C * ((1 + K * R * q * intDist β) ^ (-A) + (K * R * q) ^ (-A)) := hb
      _ ≤ C * (2 ^ A * K ^ (-A) + K ^ (-A)) := mul_le_mul_of_nonneg_left (add_le_add hd hp) hC.le
      _ = C * (2 ^ A + 1) * K ^ (-A) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.scaled_GThat_bounds

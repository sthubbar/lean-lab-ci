import LeanLab.OpenProblems.KohonenOverlap
import LeanLab.OpenProblems.KohonenSumset

/-!
# Size normalization of the three-segment construction

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2, page 5 Section 3.
Placement lists are duplicate-free, as the paper uses finite sets of indices.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

open Filter
open scoped Topology Pointwise

/-- Actual basis size divided by t tends to the total number of segments. -/
theorem basis_card_div_t_tendsto (I J K : List ℕ) (hI : I.Nodup) (hJ : J.Nodup) (hK : K.Nodup) :
    Tendsto (fun t : ℕ => ((basis t I J K).card : ℝ) / (t : ℝ)) atTop
      (𝓝 ((I.length + J.length + K.length : ℕ) : ℝ)) := by
  let l : ℝ := ((I.length + J.length + K.length : ℕ) : ℝ)
  let C : ℝ := ((2 * I.length + J.length : ℕ) : ℝ)
  have hi : Tendsto (fun t : ℕ => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun t : ℕ => l - C / (t : ℝ)) atTop (𝓝 l) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hi) :
        Tendsto (fun t : ℕ => l - C * (t : ℝ)⁻¹) atTop (𝓝 (l - C * 0)))
  have hhi : Tendsto (fun t : ℕ => l + (I.length : ℝ) / (t : ℝ)) atTop (𝓝 l) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
        Tendsto (fun t : ℕ => l + (I.length : ℝ) * (t : ℝ)⁻¹) atTop
          (𝓝 (l + (I.length : ℝ) * 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 2] with t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hn := card_basis_lower t I J K ht
    rw [List.toFinset_card_of_nodup hI, List.toFinset_card_of_nodup hJ,
      List.toFinset_card_of_nodup hK] at hn
    have hr : l * (t : ℝ) ≤ ((basis t I J K).card : ℝ) + C := by
      dsimp [l, C]
      have hn' : (I.length + J.length + K.length) * t ≤
          (basis t I J K).card + (2 * I.length + J.length) := by omega
      exact_mod_cast hn' 
    rw [le_div_iff₀ htpos]
    have heq : (l - C / (t : ℝ)) * (t : ℝ) = l * t - C := by
      field_simp [htpos.ne']
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hr : ((basis t I J K).card : ℝ) ≤ l * t + I.length := by
      dsimp [l]
      exact_mod_cast card_basis_le t I J K
    rw [div_le_iff₀ htpos]
    have heq : (l + (I.length : ℝ) / (t : ℝ)) * (t : ℝ) = l * t + I.length := by
      field_simp [htpos.ne']
    rwa [heq]

/-- The full geometric sumset has the mixed-pair leading upper coefficient after normalization. -/
theorem basis_sumset_limsup_le_mixed_ratio (I J K : List ℕ)
    (hI : I.Nodup) (hJ : J.Nodup) (hK : K.Nodup)
    (hL : 0 < I.length + J.length + K.length) :
    limsup (fun t : ℕ =>
      ((basis t I J K + basis t I J K).card : ℝ) / ((basis t I J K).card : ℝ) ^ 2) atTop ≤
      ((I.length * J.length + I.length * K.length + J.length * K.length : ℕ) : ℝ) /
        (((I.length + J.length + K.length : ℕ) : ℝ) ^ 2) := by
  let l : ℝ := ((I.length + J.length + K.length : ℕ) : ℝ)
  let M : ℝ := ((I.length * J.length + I.length * K.length + J.length * K.length : ℕ) : ℝ)
  let C : ℝ := ((2 * (I.length ^ 2 + J.length ^ 2 + K.length ^ 2) +
    I.length * J.length + I.length * K.length : ℕ) : ℝ)
  let D : ℝ := ((2 * (I.length ^ 2 + J.length ^ 2 + K.length ^ 2) : ℕ) : ℝ)
  let f := fun t : ℕ => ((basis t I J K).card : ℝ) / (t : ℝ)
  let r := fun t : ℕ =>
    ((basis t I J K + basis t I J K).card : ℝ) / ((basis t I J K).card : ℝ) ^ 2
  let u := fun t : ℕ => (M + C / (t : ℝ) + D / (t : ℝ) ^ 2) / (f t) ^ 2
  have hl : 0 < l := by dsimp [l]; exact_mod_cast hL
  have hf : Tendsto f atTop (𝓝 l) := basis_card_div_t_tendsto I J K hI hJ hK
  have hi : Tendsto (fun t : ℕ => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun t : ℕ => C / (t : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hi :
      Tendsto (fun t : ℕ => C * (t : ℝ)⁻¹) atTop (𝓝 (C * 0)))
  have hD : Tendsto (fun t : ℕ => D / (t : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using (tendsto_const_nhds.mul (hi.pow 2) :
      Tendsto (fun t : ℕ => D * ((t : ℝ)⁻¹) ^ 2) atTop (𝓝 (D * 0 ^ 2)))
  have hnum : Tendsto (fun t : ℕ => M + C / (t : ℝ) + D / (t : ℝ) ^ 2) atTop (𝓝 M) := by
    simpa using ((tendsto_const_nhds.add hC).add hD :
      Tendsto (fun t : ℕ => M + C / (t : ℝ) + D / (t : ℝ) ^ 2) atTop (𝓝 (M + 0 + 0)))
  have hu : Tendsto u atTop (𝓝 (M / l ^ 2)) := hnum.div (hf.pow 2) (by positivity)
  have hco : IsCoboundedUnder (· ≤ ·) atTop r :=
    isCoboundedUnder_le_of_le atTop (fun t => by dsimp [r]; positivity)
  have hupper : ∀ᶠ t : ℕ in atTop, r t ≤ u t := by
    filter_upwards [eventually_ge_atTop 2] with t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hp := card_basis_add_le t I J K
    have hpR : ((basis t I J K + basis t I J K).card : ℝ) ≤
        M * (t : ℝ) ^ 2 + C * (t : ℝ) + D := by
      dsimp [M, C, D]
      exact_mod_cast hp
    by_cases hk : (basis t I J K).card = 0
    · simp [r, u, f, hk]
    · have hkpos : (0 : ℝ) < (basis t I J K).card := by
        exact_mod_cast (show 0 < (basis t I J K).card by omega)
      calc
        r t ≤ (M * (t : ℝ) ^ 2 + C * (t : ℝ) + D) / ((basis t I J K).card : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hpR (sq_nonneg _)
        _ = u t := by
          dsimp [u, f]
          field_simp [htpos.ne', hkpos.ne']
  have hle := limsup_le_limsup hupper hco hu.isBoundedUnder_le
  rw [hu.limsup_eq] at hle
  exact hle

/-- The size-normalized one-third ceiling in Kohonen's page-five discussion. -/
theorem three_kind_geometric_limsup_le (I J K : List ℕ)
    (hI : I.Nodup) (hJ : J.Nodup) (hK : K.Nodup)
    (hL : 0 < I.length + J.length + K.length) :
    limsup (fun t : ℕ =>
      ((basis t I J K + basis t I J K).card : ℝ) / ((basis t I J K).card : ℝ) ^ 2) atTop ≤ 1 / 3 := by
  refine (basis_sumset_limsup_le_mixed_ratio I J K hI hJ hK hL).trans ?_
  have hl : (0 : ℝ) < (((I.length + J.length + K.length : ℕ) : ℝ) ^ 2) := by positivity
  rw [div_le_iff₀ hl]
  push_cast
  nlinarith [sq_nonneg ((I.length : ℝ) - J.length),
    sq_nonneg ((I.length : ℝ) - K.length), sq_nonneg ((J.length : ℝ) - K.length)]

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.basis_card_div_t_tendsto

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.basis_sumset_limsup_le_mixed_ratio
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.three_kind_geometric_limsup_le

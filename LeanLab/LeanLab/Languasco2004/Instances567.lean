/-
Jia 1996 pages 275 to 277, concrete nonempty source strips.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp567a
import LeanLab.Languasco2004.Polynomial567

namespace LeanLab.Languasco2004.Instances567
open Real Finset Decomp567a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 275 to 277: the 32 source strips, with kind and six affine parameters. -/
def stripData : Fin 32 → Fin 7 → ℚ
  | ⟨0, _⟩ => ![0,11/27,34/81,17/12,-23/8,25/72,-1/4]
  | ⟨1, _⟩ => ![0,34/81,65/154,17/12,-29/10,25/72,-1/4]
  | ⟨2, _⟩ => ![1,65/154,49/114,17/12,-29/10,1/3,-1/3]
  | ⟨3, _⟩ => ![0,65/154,49/114,1/3,-1/3,25/72,-1/4]
  | ⟨4, _⟩ => ![1,49/114,70/159,17/12,-29/10,1/3,-1/3]
  | ⟨5, _⟩ => ![0,49/114,70/159,1/3,-1/3,4/21,1/7]
  | ⟨6, _⟩ => ![2,70/159,4/9,17/12,-29/10,1/4,-1/4]
  | ⟨7, _⟩ => ![1,70/159,4/9,1/4,-1/4,1/3,-1/3]
  | ⟨8, _⟩ => ![0,70/159,4/9,1/3,-1/3,4/21,1/7]
  | ⟨9, _⟩ => ![2,4/9,701/1566,17/12,-29/10,1/4,-1/4]
  | ⟨10, _⟩ => ![1,4/9,701/1566,1/4,-1/4,1/3,-1/3]
  | ⟨11, _⟩ => ![0,4/9,701/1566,1/3,-1/3,3/10,-1/5]
  | ⟨12, _⟩ => ![0,4/9,701/1566,34/45,-6/5,4/21,1/7]
  | ⟨13, _⟩ => ![2,701/1566,41/90,16/135,0,1/4,-1/4]
  | ⟨14, _⟩ => ![1,701/1566,41/90,1/4,-1/4,1/3,-1/3]
  | ⟨15, _⟩ => ![0,701/1566,41/90,1/3,-1/3,3/10,-1/5]
  | ⟨16, _⟩ => ![0,701/1566,41/90,34/45,-6/5,4/21,1/7]
  | ⟨17, _⟩ => ![2,41/90,17/36,16/135,0,1/4,-1/4]
  | ⟨18, _⟩ => ![1,41/90,17/36,1/4,-1/4,1/3,-1/3]
  | ⟨19, _⟩ => ![0,41/90,17/36,1/3,-1/3,4/21,1/7]
  | ⟨20, _⟩ => ![2,17/36,16/33,16/135,0,1/4,-1/4]
  | ⟨21, _⟩ => ![1,17/36,16/33,1/4,-1/4,1/3,-1/3]
  | ⟨22, _⟩ => ![0,17/36,16/33,1/3,-1/3,46/63,-1]
  | ⟨23, _⟩ => ![2,16/33,307/630,16/135,0,1/4,-1/4]
  | ⟨24, _⟩ => ![1,16/33,307/630,1/4,-1/4,89/27,-58/9]
  | ⟨25, _⟩ => ![0,16/33,307/630,17/99,0,46/63,-1]
  | ⟨26, _⟩ => ![2,307/630,329/669,16/135,0,1/4,-1/4]
  | ⟨27, _⟩ => ![1,307/630,329/669,1/4,-1/4,89/27,-58/9]
  | ⟨28, _⟩ => ![2,329/669,281/570,16/135,0,89/27,-58/9]
  | ⟨29, _⟩ => ![0,307/630,281/570,17/99,0,19/6,-6]
  | ⟨30, _⟩ => ![2,281/570,143/290,16/135,0,89/27,-58/9]
  | ⟨31, _⟩ => ![0,143/290,1/2,17/99,0,40/57,-1]

  | _ => ![0,0,1,0,0,1,0]

/-- Pages 275 to 277: every source strip contains its strict rational midpoint.
Each kernel denominator is positive there. Logarithmic numerators have the required sign. -/
theorem strip_midpoint_certificate : ∀ i : Fin 32,
    let r := stripData i
    let t := (r 1 + r 2) / 2
    let u := (r 3 + r 4 * t + r 5 + r 6 * t) / 2
    r 1 < t ∧ t < r 2 ∧ r 3 + r 4*t < u ∧ u < r 5 + r 6*t ∧
      0 < t ∧ 0 < u ∧ 0 < 1-t-u ∧ (r 0 = 1 → 0 ≤ 1-t-3*u) := by
  decide +kernel

/-- Page 270 rough integer model: the integer 2 survives the cutoff 2 in B at Y = 1. -/
theorem roughCount_nonzero_instance : roughCount 1 2 2 = 1 := by
  have hp (a : ℕ) : ∀ r : ℕ, r.Prime → (r : ℝ) < 2 → ¬ r ∣ a := by
    intro r hr hlt
    have hge : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
    exact False.elim ((not_lt_of_ge hge) hlt)
  have he (a : ℕ) : (∀ r : ℕ, r.Prime → (r : ℝ) < 2 → ¬ r ∣ a) ↔ True :=
    iff_true_intro (hp a)
  simp only [roughCount, he, and_true]
  norm_num [Finset.range_add_one, Finset.filter_insert]

/-- Page 270 rough model: zero finite prime caps give zero without an analytic estimate. -/
theorem roughModel47_empty (N Y : ℝ) : roughModel47 N Y 0 = 0 := by
  norm_num [roughModel47, Finset.sum_filter, Finset.sum_range_succ]

/-- Page 275: the finite coefficient comparison has a positive mass instance. -/
theorem absorption_nonzero_instance : (0.005888 : ℝ) ≤ 0.0058884 := by
  simpa only [mul_one] using coefficient_comparison 0.0058884 0 0 1 1 0.0058884 0.0058884
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms strip_midpoint_certificate
#print axioms roughCount_nonzero_instance
#print axioms roughModel47_empty
#print axioms absorption_nonzero_instance
end
end LeanLab.Languasco2004.Instances567

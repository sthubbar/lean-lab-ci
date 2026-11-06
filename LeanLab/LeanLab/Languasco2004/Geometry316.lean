/-
Exact checks of Jia's region table, pages 267 to 269 display 52.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
This checks the printed partition. It is not a range extension computation.
-/
import LeanLab.Languasco2004.Decomp316c

namespace LeanLab.Languasco2004.Geometry316
open Finset Real Decomp316c
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Pages 267 to 269: every two distinct rows separate either in the p
interval or in the q interval. The q comparison is checked at both endpoints
of the overlap of the p intervals. All arithmetic is rational and kernel checked. -/
theorem region_separation_certificate : ∀ i j : Fin 69, i < j →
    let r := regionData (i.val + 1)
    let s := regionData (j.val + 1)
    let l := max (r 0) (s 0)
    let u := min (r 1) (s 1)
    u ≤ l ∨
      (r 4 * l + r 5 ≤ s 2 * l + s 3 ∧ r 4 * u + r 5 ≤ s 2 * u + s 3) ∨
      (s 4 * l + s 5 ≤ r 2 * l + r 3 ∧ s 4 * u + s 5 ≤ r 2 * u + r 3) := by
  decide +kernel

/-- Elementary endpoint interpolation used to interpret the rational certificate. -/
theorem affine_le_on_interval (a b c d l u x : ℝ) (hl : l ≤ x) (hu : x ≤ u)
    (hleft : a * l + b ≤ c * l + d) (hright : a * u + b ≤ c * u + d) :
    a * x + b ≤ c * x + d := by
  by_cases hac : a ≤ c
  · nlinarith [mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hl)]
  · have hca : c ≤ a := le_of_not_ge hac
    nlinarith [mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hu)]

/-- Pages 267 to 269: in logarithmic coordinates no point lies in two
region rows. The priority convention in regionIndex loses no overlap. -/
theorem normalized_regions_disjoint (i j : Fin 69) (hij : i ≠ j) (x y : ℝ)
    (hi : (regionData (i.val + 1) 0 : ℝ) < x ∧ x ≤ (regionData (i.val + 1) 1 : ℝ) ∧
      (regionData (i.val + 1) 2 : ℝ) * x + (regionData (i.val + 1) 3 : ℝ) < y ∧
      y < (regionData (i.val + 1) 4 : ℝ) * x + (regionData (i.val + 1) 5 : ℝ))
    (hj : (regionData (j.val + 1) 0 : ℝ) < x ∧ x ≤ (regionData (j.val + 1) 1 : ℝ) ∧
      (regionData (j.val + 1) 2 : ℝ) * x + (regionData (j.val + 1) 3 : ℝ) < y ∧
      y < (regionData (j.val + 1) 4 : ℝ) * x + (regionData (j.val + 1) 5 : ℝ)) : False := by
  suffices h : ∀ i j : Fin 69, i < j →
      (regionData (i.val + 1) 0 : ℝ) < x → x ≤ (regionData (i.val + 1) 1 : ℝ) →
      (regionData (i.val + 1) 2 : ℝ) * x + (regionData (i.val + 1) 3 : ℝ) < y →
      y < (regionData (i.val + 1) 4 : ℝ) * x + (regionData (i.val + 1) 5 : ℝ) →
      (regionData (j.val + 1) 0 : ℝ) < x → x ≤ (regionData (j.val + 1) 1 : ℝ) →
      (regionData (j.val + 1) 2 : ℝ) * x + (regionData (j.val + 1) 3 : ℝ) < y →
      y < (regionData (j.val + 1) 4 : ℝ) * x + (regionData (j.val + 1) 5 : ℝ) → False by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact h i j hij hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
    · exact h j i hji hj.1 hj.2.1 hj.2.2.1 hj.2.2.2 hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  intro i j hij hi0 hi1 hi2 hi3 hj0 hj1 hj2 hj3
  have hc := region_separation_certificate i j hij
  dsimp only at hc
  have hcr : min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) ≤
      max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) ∨
    ((regionData (i.val + 1) 4 : ℝ) * max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) +
        (regionData (i.val + 1) 5 : ℝ) ≤
      (regionData (j.val + 1) 2 : ℝ) * max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) +
        (regionData (j.val + 1) 3 : ℝ) ∧
     (regionData (i.val + 1) 4 : ℝ) * min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) +
        (regionData (i.val + 1) 5 : ℝ) ≤
      (regionData (j.val + 1) 2 : ℝ) * min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) +
        (regionData (j.val + 1) 3 : ℝ)) ∨
    ((regionData (j.val + 1) 4 : ℝ) * max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) +
        (regionData (j.val + 1) 5 : ℝ) ≤
      (regionData (i.val + 1) 2 : ℝ) * max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) +
        (regionData (i.val + 1) 3 : ℝ) ∧
     (regionData (j.val + 1) 4 : ℝ) * min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) +
        (regionData (j.val + 1) 5 : ℝ) ≤
      (regionData (i.val + 1) 2 : ℝ) * min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) +
        (regionData (i.val + 1) 3 : ℝ)) := by exact_mod_cast hc
  have hl : max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) ≤ x :=
    max_le hi0.le hj0.le
  have hu : x ≤ min (regionData (i.val + 1) 1 : ℝ) (regionData (j.val + 1) 1 : ℝ) :=
    le_min hi1 hj1
  rcases hcr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hstrict : max (regionData (i.val + 1) 0 : ℝ) (regionData (j.val + 1) 0 : ℝ) < x :=
      max_lt hi0 hj0
    linarith
  · have h := affine_le_on_interval _ _ _ _ _ _ x hl hu h1 h2
    linarith
  · have h := affine_le_on_interval _ _ _ _ _ _ x hl hu h1 h2
    linarith

/-- Pages 267 to 269: positive power cutoffs become affine bounds after
normalizing both logarithms by log Y. -/
theorem region_coordinates (r : Fin 6 → ℚ) (Y p q : ℝ)
    (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (h : Y ^ (r 0 : ℝ) < p ∧ p ≤ Y ^ (r 1 : ℝ) ∧
      p ^ (r 2 : ℝ) * Y ^ (r 3 : ℝ) < q ∧ q < p ^ (r 4 : ℝ) * Y ^ (r 5 : ℝ)) :
    (r 0 : ℝ) < Real.log p / Real.log Y ∧ Real.log p / Real.log Y ≤ (r 1 : ℝ) ∧
      (r 2 : ℝ) * (Real.log p / Real.log Y) + (r 3 : ℝ) < Real.log q / Real.log Y ∧
      Real.log q / Real.log Y < (r 4 : ℝ) * (Real.log p / Real.log Y) + (r 5 : ℝ) := by
  have hY0 : 0 < Y := by linarith
  have hLY : 0 < Real.log Y := Real.log_pos hY
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hLY).mpr
    have hh := Real.log_lt_log (Real.rpow_pos_of_pos hY0 (r 0 : ℝ)) h.1
    rwa [Real.log_rpow hY0] at hh
  · apply (div_le_iff₀ hLY).mpr
    have hh := Real.log_le_log hp h.2.1
    rwa [Real.log_rpow hY0] at hh
  · apply (lt_div_iff₀ hLY).mpr
    have hh := Real.log_lt_log (mul_pos (Real.rpow_pos_of_pos hp (r 2 : ℝ))
      (Real.rpow_pos_of_pos hY0 (r 3 : ℝ))) h.2.2.1
    rw [Real.log_mul (Real.rpow_pos_of_pos hp _).ne' (Real.rpow_pos_of_pos hY0 _).ne',
      Real.log_rpow hp, Real.log_rpow hY0] at hh
    have heq : ((r 2 : ℝ) * (Real.log p / Real.log Y) + (r 3 : ℝ)) * Real.log Y =
        (r 2 : ℝ) * Real.log p + (r 3 : ℝ) * Real.log Y := by field_simp
    rwa [heq]
  · apply (div_lt_iff₀ hLY).mpr
    have hh := Real.log_lt_log hq h.2.2.2
    rw [Real.log_mul (Real.rpow_pos_of_pos hp _).ne' (Real.rpow_pos_of_pos hY0 _).ne',
      Real.log_rpow hp, Real.log_rpow hY0] at hh
    have heq : ((r 4 : ℝ) * (Real.log p / Real.log Y) + (r 5 : ℝ)) * Real.log Y =
        (r 4 : ℝ) * Real.log p + (r 5 : ℝ) * Real.log Y := by field_simp
    rwa [heq]

/-- Pages 267 to 269: the actual power regions are pairwise disjoint. -/
theorem power_regions_disjoint (i j : Fin 69) (hij : i ≠ j) (Y p q : ℝ)
    (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hi : Y ^ (regionData (i.val + 1) 0 : ℝ) < p ∧ p ≤ Y ^ (regionData (i.val + 1) 1 : ℝ) ∧
      p ^ (regionData (i.val + 1) 2 : ℝ) * Y ^ (regionData (i.val + 1) 3 : ℝ) < q ∧
      q < p ^ (regionData (i.val + 1) 4 : ℝ) * Y ^ (regionData (i.val + 1) 5 : ℝ))
    (hj : Y ^ (regionData (j.val + 1) 0 : ℝ) < p ∧ p ≤ Y ^ (regionData (j.val + 1) 1 : ℝ) ∧
      p ^ (regionData (j.val + 1) 2 : ℝ) * Y ^ (regionData (j.val + 1) 3 : ℝ) < q ∧
      q < p ^ (regionData (j.val + 1) 4 : ℝ) * Y ^ (regionData (j.val + 1) 5 : ℝ)) : False := by
  exact normalized_regions_disjoint i j hij _ _
    (region_coordinates _ Y p q hY hp hq hi) (region_coordinates _ Y p q hY hp hq hj)

/-- Display 52: under the positive source domain, the least label convention
returns the unique source label. It discards no point of any D_i. -/
theorem regionIndex_eq_of_mem (i : Fin 69) (Y : ℝ) (p q : ℕ)
    (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hi : Y ^ (regionData (i.val + 1) 0 : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ Y ^ (regionData (i.val + 1) 1 : ℝ) ∧
      (p : ℝ) ^ (regionData (i.val + 1) 2 : ℝ) * Y ^ (regionData (i.val + 1) 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData (i.val + 1) 4 : ℝ) * Y ^ (regionData (i.val + 1) 5 : ℝ)) :
    regionIndex Y p q = i.val + 1 := by
  have hex : ∃ k : ℕ, k ∈ Icc 1 69 ∧
      Y ^ (regionData k 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData k 1 : ℝ) ∧
      (p : ℝ) ^ (regionData k 2 : ℝ) * Y ^ (regionData k 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData k 4 : ℝ) * Y ^ (regionData k 5 : ℝ) := by
    refine ⟨i.val + 1, mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩, hi⟩
  rw [regionIndex, dite_eq_left hex]
  obtain ⟨hkI, hk⟩ := Nat.find_spec hex
  have hk1 := (mem_Icc.mp hkI).1
  have hk69 := (mem_Icc.mp hkI).2
  let j : Fin 69 := ⟨Nat.find hex - 1, by omega⟩
  have hj : j.val + 1 = Nat.find hex := by dsimp [j]; omega
  by_contra heq
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  apply power_regions_disjoint i j hij Y p q hY (by exact_mod_cast hp) (by exact_mod_cast hq) hi
  simpa only [hj] using hk

/-- Pages 267 to 269: exact endpoint certificate that every printed region
lies in the recovery domain in logarithmic coordinates. -/
theorem recovery_containment_certificate : ∀ i : Fin 69,
    let r := regionData (i.val + 1)
    (16 / 135 : ℚ) ≤ r 0 ∧ r 1 ≤ 1 / 2 ∧
    (16 / 135 : ℚ) ≤ r 2 * r 0 + r 3 ∧ (16 / 135 : ℚ) ≤ r 2 * r 1 + r 3 ∧
    r 4 * r 0 + r 5 ≤ r 0 ∧ r 4 * r 1 + r 5 ≤ r 1 ∧
    r 0 + 2 * (r 4 * r 0 + r 5) ≤ 1 ∧ r 1 + 2 * (r 4 * r 1 + r 5) ≤ 1 := by
  decide +kernel

/-- Display 52: each normalized source region stays strictly above the
small cutoff and strictly below both upper recovery cutoffs. -/
theorem normalized_recovery_containment (i : Fin 69) (x y : ℝ)
    (hi : (regionData (i.val + 1) 0 : ℝ) < x ∧ x ≤ (regionData (i.val + 1) 1 : ℝ) ∧
      (regionData (i.val + 1) 2 : ℝ) * x + (regionData (i.val + 1) 3 : ℝ) < y ∧
      y < (regionData (i.val + 1) 4 : ℝ) * x + (regionData (i.val + 1) 5 : ℝ)) :
    (16 / 135 : ℝ) < x ∧ x ≤ 1 / 2 ∧ (16 / 135 : ℝ) < y ∧ y < x ∧ x + 2 * y < 1 := by
  have hc := recovery_containment_certificate i
  dsimp only at hc
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7⟩ := hc
  have h0 : (((16 / 135 : ℚ) : ℚ) : ℝ) ≤ ((regionData (i.val + 1) 0 : ℚ) : ℝ) := by exact_mod_cast q0
  have h1 : ((regionData (i.val + 1) 1 : ℚ) : ℝ) ≤ (((1 / 2 : ℚ) : ℚ) : ℝ) := by exact_mod_cast q1
  have h2 : (((16 / 135 : ℚ) : ℚ) : ℝ) ≤ ((regionData (i.val + 1) 2 * regionData (i.val + 1) 0 + regionData (i.val + 1) 3 : ℚ) : ℝ) := by exact_mod_cast q2
  have h3 : (((16 / 135 : ℚ) : ℚ) : ℝ) ≤ ((regionData (i.val + 1) 2 * regionData (i.val + 1) 1 + regionData (i.val + 1) 3 : ℚ) : ℝ) := by exact_mod_cast q3
  have h4 : ((regionData (i.val + 1) 4 * regionData (i.val + 1) 0 + regionData (i.val + 1) 5 : ℚ) : ℝ) ≤ ((regionData (i.val + 1) 0 : ℚ) : ℝ) := by exact_mod_cast q4
  have h5 : ((regionData (i.val + 1) 4 * regionData (i.val + 1) 1 + regionData (i.val + 1) 5 : ℚ) : ℝ) ≤ ((regionData (i.val + 1) 1 : ℚ) : ℝ) := by exact_mod_cast q5
  have h6 : ((regionData (i.val + 1) 0 + 2 * (regionData (i.val + 1) 4 * regionData (i.val + 1) 0 + regionData (i.val + 1) 5) : ℚ) : ℝ) ≤ (((1 : ℚ) : ℚ) : ℝ) := by exact_mod_cast q6
  have h7 : ((regionData (i.val + 1) 1 + 2 * (regionData (i.val + 1) 4 * regionData (i.val + 1) 1 + regionData (i.val + 1) 5) : ℚ) : ℝ) ≤ (((1 : ℚ) : ℚ) : ℝ) := by exact_mod_cast q7
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h0 h1 h2 h3 h4 h5 h6 h7
  have hlow := affine_le_on_interval 0 (16 / 135) _ _ _ _ x hi.1.le hi.2.1
    (by simpa using h2) (by simpa using h3)
  have hhigh := affine_le_on_interval _ _ 1 0 _ _ x hi.1.le hi.2.1
    (by simpa using h4) (by simpa using h5)
  have hsum := affine_le_on_interval (1 + 2 * (regionData (i.val + 1) 4 : ℝ))
    (2 * (regionData (i.val + 1) 5 : ℝ)) 0 1 _ _ x hi.1.le hi.2.1 (by nlinarith) (by nlinarith)
  refine ⟨h0.trans_lt hi.1, hi.2.1.trans h1, ?_, ?_, ?_⟩
  · nlinarith [hi.2.2.1]
  · nlinarith [hi.2.2.2]
  · nlinarith [hi.2.2.2]

/-- Display 52: clipping to the sealed power cutoffs loses no source pair. -/
theorem power_recovery_containment (i : Fin 69) (Y p q : ℝ)
    (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hi : Y ^ (regionData (i.val + 1) 0 : ℝ) < p ∧ p ≤ Y ^ (regionData (i.val + 1) 1 : ℝ) ∧
      p ^ (regionData (i.val + 1) 2 : ℝ) * Y ^ (regionData (i.val + 1) 3 : ℝ) < q ∧
      q < p ^ (regionData (i.val + 1) 4 : ℝ) * Y ^ (regionData (i.val + 1) 5 : ℝ)) :
    Y ^ (16 / 135 : ℝ) < p ∧ p ≤ Real.sqrt (2 * Y) ∧ Y ^ (16 / 135 : ℝ) < q ∧
      q < min p (Real.sqrt (2 * Y / p)) := by
  have hY0 : 0 < Y := by linarith
  have hLY : 0 < Real.log Y := Real.log_pos hY
  obtain ⟨hx0,hx1,hy0,hyx,hsum⟩ := normalized_recovery_containment i _ _
    (region_coordinates _ Y p q hY hp hq hi)
  have hplow : Y ^ (16 / 135 : ℝ) < p := by
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp).mp
    rw [Real.log_rpow hY0]
    exact (lt_div_iff₀ hLY).mp hx0
  have hqlow : Y ^ (16 / 135 : ℝ) < q := by
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hq).mp
    rw [Real.log_rpow hY0]
    exact (lt_div_iff₀ hLY).mp hy0
  have hpsq : p ^ (2 : ℕ) ≤ Y := by
    apply (Real.log_le_log_iff (sq_pos_of_pos hp) hY0).mp
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h := (div_le_iff₀ hLY).mp hx1
    nlinarith
  have hqp : q < p := by
    apply (Real.log_lt_log_iff hq hp).mp
    exact (div_lt_div_iff_of_pos_right hLY).mp hyx
  have hqsq : q ^ (2 : ℕ) * p < Y := by
    apply (Real.log_lt_log_iff (mul_pos (sq_pos_of_pos hq) hp) hY0).mp
    rw [Real.log_mul (sq_pos_of_pos hq).ne' hp.ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h := (div_lt_iff₀ hLY).mp (show (Real.log p + 2 * Real.log q) / Real.log Y < 1 by
      convert hsum using 1 <;> ring)
    nlinarith
  refine ⟨hplow, ?_, hqlow, lt_min hqp ?_⟩
  · apply (Real.le_sqrt hp.le (by positivity : (0 : ℝ) ≤ 2 * Y)).mpr
    linarith
  · apply (Real.lt_sqrt hq.le).mpr
    apply (lt_div_iff₀ hp).mpr
    linarith

#print axioms region_separation_certificate
#print axioms affine_le_on_interval
#print axioms normalized_regions_disjoint
#print axioms region_coordinates
#print axioms power_regions_disjoint
#print axioms regionIndex_eq_of_mem
#print axioms recovery_containment_certificate
#print axioms normalized_recovery_containment
#print axioms power_recovery_containment
end
end LeanLab.Languasco2004.Geometry316

/-
P0093 pages 156 and 159 through 165. Upstream local major arc decomposition.
Geometry proofs are ported from Geometry491 because that file imports the target.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.CircleSplit111
import LeanLab.Perelli1996.Ramanujan103
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace LeanLab.Linnik1951
open Finset MeasureTheory
/-- LEAF. P0093 page 165 before equation 8.1. Distinct rational centres are
separated by the reciprocal product of their denominators. -/
theorem rational_separation520 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hne : a * (r : ℤ) - b * (q : ℤ) ≠ 0) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hi : (1 : ℤ) ≤ |a * (r : ℤ) - b * (q : ℤ)| := by
    have hp := abs_pos.mpr hne
    omega
  have hn : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by exact_mod_cast hi
  have heq : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hq0 hr0)]
  exact div_le_div_of_nonneg_right hn (mul_pos hq0 hr0).le

/-- LEAF. P0093 page 165 before equation 8.1. Two rational major arcs are
disjoint when their denominator sum is strictly smaller than tau. -/
theorem rational_arcs_disjoint520 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hne : a * (r : ℤ) - b * (q : ℤ) ≠ 0) (τ : ℝ)
    (hτsum : (q : ℝ) + r < τ) :
    Disjoint
      (Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ))
        ((a : ℝ) / q + 1 / ((q : ℝ) * τ)))
      (Set.Icc ((b : ℝ) / r - 1 / ((r : ℝ) * τ))
        ((b : ℝ) / r + 1 / ((r : ℝ) * τ))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hτ : 0 < τ := by linarith
  have hrad : 1 / ((q : ℝ) * τ) + 1 / ((r : ℝ) * τ) < 1 / ((q : ℝ) * r) := by
    apply (lt_div_iff₀ (mul_pos hq0 hr0)).mpr
    have heq : (1 / ((q : ℝ) * τ) + 1 / ((r : ℝ) * τ)) * ((q : ℝ) * r) =
        ((q : ℝ) + r) / τ := by field_simp; ring
    rw [heq]
    exact (div_lt_one hτ).mpr hτsum
  rw [Set.disjoint_left]
  intro α hα hβ
  have ha : |(a : ℝ) / q - α| ≤ 1 / ((q : ℝ) * τ) := by
    apply abs_le.mpr
    constructor <;> linarith [hα.1, hα.2]
  have hb : |α - (b : ℝ) / r| ≤ 1 / ((r : ℝ) * τ) := by
    apply abs_le.mpr
    constructor <;> linarith [hβ.1, hβ.2]
  have hd := rational_separation520 a b q r hq hr hne
  have ht := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / r)
  linarith


/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The finite reduced rational centres, including both endpoint representatives at modulus one. -/
noncomputable def arcIndices520 (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (Icc 0 Q)).filter fun p => p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The full closed rational arc of radius one over q tau. -/
noncomputable def rationalArc520 (q a : ℕ) (τ : ℝ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ)) ((a : ℝ) / q + 1 / ((q : ℝ) * τ))
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The rational major arcs with natural denominator cutoff, clipped to the unit interval. -/
noncomputable def rationalMajor520 (Q : ℕ) (τ : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, r.den ≤ Q ∧ |α - r| ≤ 1 / ((r.den : ℝ) * τ)}

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Membership in the finite rational centre index set. -/
theorem arcIndices_mem520 (Q : ℕ) (p : ℕ × ℕ) :
    p ∈ arcIndices520 Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
  constructor
  · intro h
    obtain ⟨hpair, ha, hcop⟩ := Finset.mem_filter.mp h
    obtain ⟨hq, haQ⟩ := Finset.mem_product.mp hpair
    exact ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2, ha, hcop⟩
  · rintro ⟨hq, hqQ, ha, hcop⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨mem_Icc.mpr ⟨hq, hqQ⟩,
      mem_Icc.mpr ⟨Nat.zero_le _, ha.trans hqQ⟩⟩, ha, hcop⟩


/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The rational definition equals the explicit finite union of clipped arcs. -/
theorem rational_major_cover520 (Q : ℕ) (τ : ℝ) (hτ : 1 < τ) :
    rationalMajor520 Q τ =
      ⋃ p ∈ arcIndices520 Q, Set.Icc (0 : ℝ) 1 ∩ rationalArc520 p.1 p.2 τ := by
  ext α
  constructor
  · rintro ⟨hα, r, hrQ, hrα⟩
    have hq : 0 < r.den := r.pos
    have hqr : (0 : ℝ) < r.den := by exact_mod_cast hq
    have hc : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ (ne_of_gt hqr)]
    have hm := mul_le_mul_of_nonneg_right hrα hqr.le
    have hdist : |α * (r.den : ℝ) - (r.num : ℝ)| < 1 := by
      have he : |α - (r : ℝ)| * (r.den : ℝ) =
          |α * (r.den : ℝ) - (r.num : ℝ)| := by
        calc
          _ = |(α - (r : ℝ)) * (r.den : ℝ)| := by rw [abs_mul, abs_of_pos hqr]
          _ = _ := by rw [sub_mul, hc]
      rw [he] at hm
      have he' : (1 / ((r.den : ℝ) * τ)) * (r.den : ℝ) = 1 / τ := by field_simp
      rw [he'] at hm
      exact hm.trans_lt ((div_lt_one (by linarith : 0 < τ)).mpr hτ)
    have hlow : (-1 : ℝ) < (r.num : ℝ) := by
      have hh := (abs_lt.mp hdist).2
      nlinarith [hα.1]
    have hhigh : (r.num : ℝ) < (r.den : ℝ) + 1 := by
      have hh := (abs_lt.mp hdist).1
      nlinarith [hα.2]
    have hn0 : 0 ≤ r.num := by
      have hi : (-1 : ℤ) < r.num := by exact_mod_cast hlow
      omega
    have hnq : r.num ≤ (r.den : ℤ) := by
      have hi : r.num < (r.den : ℤ) + 1 := by exact_mod_cast hhigh
      omega
    let a := r.num.toNat
    have ha : (a : ℤ) = r.num := Int.toNat_of_nonneg hn0
    have haq : a ≤ r.den := by omega
    have hcop : Nat.Coprime a r.den := by
      have hh := r.reduced
      simpa [← ha] using hh
    have hp : (r.den, a) ∈ arcIndices520 Q :=
      (arcIndices_mem520 Q _).mpr ⟨hq, hrQ, haq, hcop⟩
    have heq : (a : ℝ) / r.den = (r : ℝ) := by
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast ha
    apply Set.mem_iUnion.mpr
    refine ⟨(r.den, a), Set.mem_iUnion.mpr ⟨hp, hα, ?_⟩⟩
    change α ∈ Set.Icc ((a : ℝ) / r.den - 1 / ((r.den : ℝ) * τ))
      ((a : ℝ) / r.den + 1 / ((r.den : ℝ) * τ))
    rw [heq]
    have hh := abs_le.mp hrα
    constructor <;> linarith
  · intro hα
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hα
    obtain ⟨hp, hunit, harc⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hq, hqQ, ha, hcop⟩ := (arcIndices_mem520 Q p).mp hp
    let r : ℚ := (p.2 : ℚ) / p.1
    have hd : r.den = p.1 := by
      have hh := Rat.den_div_eq_of_coprime
        (a := (p.2 : ℤ)) (b := (p.1 : ℤ))
        (by exact_mod_cast hq : (0 : ℤ) < (p.1 : ℤ)) (by simpa using hcop)
      have hdi : ((((p.2 : ℚ) / p.1).den : ℤ)) = (p.1 : ℤ) := by
        simpa only [Int.cast_natCast] using hh
      exact Int.ofNat_inj.mp hdi
    refine ⟨hunit, r, by simpa [hd] using hqQ, ?_⟩
    rw [hd]
    have heq : (r : ℝ) = (p.2 : ℝ) / p.1 := by simp [r]
    rw [heq]
    apply abs_le.mpr
    change α ∈ Set.Icc ((p.2 : ℝ) / p.1 - 1 / ((p.1 : ℝ) * τ))
      ((p.2 : ℝ) / p.1 + 1 / ((p.1 : ℝ) * τ)) at harc
    constructor <;> linarith [harc.1, harc.2]
/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Distinct reduced rational representatives have nonzero cross difference. -/
theorem arcIndices_cross_ne520 (Q : ℕ) (p t : ℕ × ℕ)
    (hp : p ∈ arcIndices520 Q) (ht : t ∈ arcIndices520 Q) (hne : p ≠ t) :
    (p.2 : ℤ) * t.1 - (t.2 : ℤ) * p.1 ≠ 0 := by
  obtain ⟨hp1, hpQ, hp2, hpc⟩ := (arcIndices_mem520 Q p).mp hp
  obtain ⟨ht1, htQ, ht2, htc⟩ := (arcIndices_mem520 Q t).mp ht
  intro h
  have hm : p.2 * t.1 = t.2 * p.1 := by exact_mod_cast sub_eq_zero.mp h
  have hpt : p.1 ∣ t.1 := hpc.symm.dvd_mul_left.mp (by rw [hm]; exact dvd_mul_left _ _)
  have htp : t.1 ∣ p.1 := htc.symm.dvd_mul_left.mp (by rw [← hm]; exact dvd_mul_left _ _)
  have heq : p.1 = t.1 := Nat.dvd_antisymm hpt htp
  have ha : p.2 = t.2 := by
    rw [heq] at hm
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < t.1) hm
  exact hne (Prod.ext heq ha)

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The integral over the major arcs is the sum of the clipped arc integrals. -/
theorem rational_clipped_integral520 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in rationalMajor520 Q τ, f α) =
      ∑ p ∈ arcIndices520 Q,
        ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 p.1 p.2 τ, f α := by
  have hτ1 : 1 < τ := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  rw [rational_major_cover520 Q τ hτ1]
  apply integral_biUnion_finset
  · intro p hp
    exact measurableSet_Icc.inter measurableSet_Icc
  · intro p hp t ht hne
    have hpQ := ((arcIndices_mem520 Q p).mp hp).2.1
    have htQ := ((arcIndices_mem520 Q t).mp ht).2.1
    have hsum : (p.1 : ℝ) + t.1 < τ := by
      have hpr : (p.1 : ℝ) ≤ Q := by exact_mod_cast hpQ
      have htr : (t.1 : ℝ) ≤ Q := by exact_mod_cast htQ
      linarith
    have hd := rational_arcs_disjoint520 (p.2 : ℤ) (t.2 : ℤ) p.1 t.1
      ((arcIndices_mem520 Q p).mp hp).1 ((arcIndices_mem520 Q t).mp ht).1
      (arcIndices_cross_ne520 Q p t hp ht hne) τ hsum
    exact hd.mono Set.inter_subset_right Set.inter_subset_right
  · intro p hp
    exact hf.integrableOn_Icc.mono_set Set.inter_subset_left

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Translation converts a full rational arc integral to its symmetric local coordinate integral. -/
theorem rational_arc_integral520 (q a : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 0 < τ)
    (f : ℝ → ℂ) :
    (∫ α in rationalArc520 q a τ, f α) =
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  have hR : 0 ≤ 1 / ((q : ℝ) * τ) := by positivity
  unfold rationalArc520
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_add_left]
  congr 1 <;> ring

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. For denominator at least two, every reduced representative arc lies inside the unit interval. -/
theorem interior_arc_subset520 (q a : ℕ) (hq : 2 ≤ q) (ha : a < q)
    (hc : Nat.Coprime a q) (τ : ℝ) (hτ : 1 ≤ τ) :
    rationalArc520 q a τ ⊆ Set.Icc 0 1 := by
  have ha1 : 1 ≤ a := by
    by_contra hh
    have hz : a = 0 := by omega
    simp [hz] at hc
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrad : 1 / ((q : ℝ) * τ) ≤ 1 / (q : ℝ) := by
    apply one_div_le_one_div_of_le hq0
    nlinarith
  have hlo : 1 / (q : ℝ) ≤ (a : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha1) hq0.le
  have hhi : (a : ℝ) / q + 1 / q ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hq0).mpr
    exact_mod_cast (show a + 1 ≤ q by omega)
  intro α hα
  change α ∈ Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ))
    ((a : ℝ) / q + 1 / ((q : ℝ) * τ)) at hα
  constructor <;> linarith [hα.1, hα.2]

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The clipped endpoint arcs join into the symmetric unit modulus arc by period one. -/
theorem unit_arc_join520 (τ : ℝ) (hτ : 2 < τ) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 0 τ, f α) +
      (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 1 τ, f α) =
      ∫ z in -(1 / τ)..(1 / τ), f z := by
  let R : ℝ := 1 / τ
  have hτ0 : 0 < τ := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := (div_le_one hτ0).mpr (by linarith)
  have hh : Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 0 τ = Set.Icc 0 R := by
    ext α
    simp only [rationalArc520, Nat.cast_one, Nat.cast_zero, zero_div, one_mul, zero_sub,
      zero_add, Set.mem_inter_iff, Set.mem_Icc]
    dsimp [R] at *
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.1, h2.2⟩
    · intro h
      constructor <;> constructor <;> linarith [h.1, h.2]
  have ht : Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 1 τ = Set.Icc (1 - R) 1 := by
    ext α
    simp only [rationalArc520, Nat.cast_one, div_one, one_mul, Set.mem_inter_iff, Set.mem_Icc]
    dsimp [R] at *
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.1, h1.2⟩
    · intro h
      constructor <;> constructor <;> linarith [h.1, h.2]
  rw [hh, ht, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hR0,
    ← intervalIntegral.integral_of_le (show 1 - R ≤ 1 by linarith)]
  have hs : (∫ x in (1 - R)..1, f x) = ∫ x in -R..0, f x := by
    have h := intervalIntegral.integral_comp_add_right (a := -R) (b := (0 : ℝ)) f 1
    have hfun : (fun x : ℝ => f (x + 1)) = f := funext hp
    rw [hfun] at h
    simpa only [zero_add, neg_add_eq_sub] using h.symm
  rw [hs, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. At each denominator the clipped representatives give the required full local arc sum. -/
theorem denominator_arc_sum520 (q : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 2 < τ)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q),
      ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 q a τ, f α) =
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  classical
  by_cases hq1 : q = 1
  · subst q
    have hi : (Icc 0 (1 : ℕ)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
    have hr : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    rw [hi, hr]
    simpa using unit_arc_join520 τ hτ f hf hp
  · have hq2 : 2 ≤ q := by omega
    have heq : (Icc 0 q).filter (fun a => Nat.Coprime a q) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_Icc, mem_range]
      constructor
      · rintro ⟨ha, hc⟩
        have hne : a ≠ q := by intro h; subst a; exact hq1 (by simpa using hc)
        exact ⟨by omega, hc⟩
      · rintro ⟨ha, hc⟩
        exact ⟨⟨Nat.zero_le _, ha.le⟩, hc⟩
    rw [heq]
    apply Finset.sum_congr rfl
    intro a ha
    have has := (mem_filter.mp ha).1
    have hac := (mem_filter.mp ha).2
    have hsub := interior_arc_subset520 q a hq2 (mem_range.mp has) hac τ (by linarith)
    rw [Set.inter_eq_right.mpr hsub]
    exact rational_arc_integral520 q a hq τ (by linarith) f

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The pair index sum equals the iterated denominator and reduced numerator sum. -/
theorem arcIndices_sum520 (Q : ℕ) (H : ℕ × ℕ → ℂ) :
    (∑ p ∈ arcIndices520 Q, H p) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q), H (q, a) := by
  classical
  simp only [arcIndices520, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  have hqQ : q ≤ Q := (mem_Icc.mp hq).2
  have hset : (Icc 0 Q).filter (fun a => a ≤ q ∧ Nat.Coprime a q) =
      (Icc 0 q).filter (fun a => Nat.Coprime a q) := by
    ext a
    simp only [mem_filter, mem_Icc]
    omega
  rw [← Finset.sum_filter, ← Finset.sum_filter, hset]

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. A continuous periodic function has the exact rational arc partition when tau exceeds twice Q. -/
theorem rational_partition520 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in rationalMajor520 Q τ, f α) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  rw [rational_clipped_integral520 Q hQ τ hτ f hf, arcIndices_sum520]
  apply Finset.sum_congr rfl
  intro q hq
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  exact denominator_arc_sum520 q (mem_Icc.mp hq).1 τ (by linarith) f hf hp

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Above two to power seventy the chosen tau exceeds twice the integer Q. -/
theorem major_parameters_separated520 (N : ℕ) (hN : 2 ^ 70 < N) :
    1 ≤ ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ ∧
      2 * (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by positivity
  have hbase : (2 : ℝ) ^ (70 : ℕ) < N := by exact_mod_cast hN
  have hpow := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (70 : ℕ)) hbase
    (show (0 : ℝ) < 3 / 70 by norm_num)
  have he : ((2 : ℝ) ^ (70 : ℕ)) ^ (3 / 70 : ℝ) = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [he] at hpow
  have hsave : 2 * (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hm := mul_lt_mul_of_pos_right (show (2 : ℝ) < (N : ℝ) ^ (3 / 70 : ℝ) by linarith)
      (Real.rpow_pos_of_pos hN0 (1 / 10 : ℝ))
    have heq : (N : ℝ) ^ (3 / 70 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) =
        (N : ℝ) ^ (1 / 7 : ℝ) := by
      rw [← Real.rpow_add hN0]
      norm_num
    rwa [heq] at hm
  constructor
  · apply (Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)).mpr
    simpa only [Nat.cast_one] using Real.one_le_rpow hNr (show (0 : ℝ) ≤ 1 / 10 by norm_num)
  · exact (mul_le_mul_of_nonneg_left (Nat.floor_le (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity))
      (show (0 : ℝ) ≤ 2 by norm_num)).trans_lt hsave

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The exact major arc partition at the parameters used by the sealed target. -/
theorem major_arc_partition_proved520 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ f : ℝ → ℂ,
      Continuous f → Function.Periodic f 1 →
      (∫ α in majorArcs280_up111 N, f α) =
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              f ((a : ℝ) / q + z) := by
  refine ⟨2 ^ 70, ?_⟩
  intro N hN f hf hp
  have hsep := major_parameters_separated520 N hN
  have heq : majorArcs280_up111 N = rationalMajor520 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
      ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    ext α
    simp only [majorArcs280_up111, rationalMajor520, Set.mem_setOf_eq,
      Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)]
  rw [heq]
  exact rational_partition520 _ hsep.1 _ hsep.2 f hf hp

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 159 before equation 5.1. The principal character prime series
is the prime series with the prime divisors of the modulus removed. -/
noncomputable def principalPrime520 (N q : ℕ) (z : ℝ) : ℂ :=
  primeFourier111_up111 N z - ∑ p ∈ q.primeFactors,
    (Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)

/-- P0093 page 156 equation 3.4. The principal rational coefficient. -/
noncomputable def principalCoefficient520 (q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ)

/-- P0093 page 156 equation 3.4. The residue error retains the omitted
prime divisor terms after removing the principal character contribution. -/
noncomputable def residueError520 (N q a : ℕ) (z : ℝ) : ℂ :=
  primeFourier111_up111 N ((a : ℝ) / q + z) -
    principalCoefficient520 q * principalPrime520 N q z

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The local prime square integral. -/
noncomputable def localArc520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (primeFourier111_up111 N ((a : ℝ) / q + z) ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The mixed local contribution. -/
noncomputable def mixedIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The square of the residue error. -/
noncomputable def errorIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (residueError520 N q a z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 160 equation 6.1. The principal square on one centred arc. -/
noncomputable def principalIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
    principalPrime520 N q z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. The Ramanujan phase at a signed residual. -/
noncomputable def signedRamanujan520 (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 161 after equation 6.3. The exact logarithmic convolution. -/
noncomputable def logConvolution520 (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- P0093 page 161 equation 6.4. The exact damped local main term. -/
noncomputable def localMain520 (N q : ℕ) (n : ℤ) : ℂ :=
  principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
    ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)

/-- P0093 page 159 equation 5.1. The principal series is continuous. -/
theorem continuous_principal520 (N q : ℕ) (hN : 1 ≤ N) :
    Continuous (principalPrime520 N q) := by
  unfold principalPrime520
  exact (continuous_prime_fourier111_up111 N hN).sub (by fun_prop)

/-- P0093 page 156 equation 3.4. Every residue error is continuous. -/
theorem continuous_residue520 (N q a : ℕ) (hN : 1 ≤ N) :
    Continuous (residueError520 N q a) := by
  unfold residueError520
  exact ((continuous_prime_fourier111_up111 N hN).comp (by fun_prop)).sub
    (continuous_const.mul (continuous_principal520 N q hN))

/-- P0093 page 156 equation 3.4. Exact square expansion at one residue. -/
theorem residue_square520 (N q a : ℕ) (z : ℝ) :
    primeFourier111_up111 N ((a : ℝ) / q + z) ^ 2 =
      principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2 +
        2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z +
        residueError520 N q a z ^ 2 := by
  unfold residueError520
  ring

/-- P0093 page 156 equation 3.4. The centred phase factors exactly. -/
theorem centred_phase520 (q a : ℕ) (n : ℤ) (z : ℝ) :
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0093 page 156 equation 3.4. Exact principal, mixed and error square split. -/
theorem local_decomposition520 (N q : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    localArc520 N q n =
      principalCoefficient520 q ^ 2 * signedRamanujan520 q n * principalIntegral520 N q n +
        mixedIntegral520 N q n + errorIntegral520 N q n := by
  classical
  have hmain : principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
      principalIntegral520 N q n =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))), principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) := by
    unfold signedRamanujan520 principalIntegral520
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [centred_phase520]
    ring
  unfold localArc520 mixedIntegral520 errorIntegral520
  rw [hmain, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have hA := continuous_principal520 N q hN
  have hE := continuous_residue520 N q a hN
  have hp : Continuous (fun z : ℝ => Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have h1 : IntervalIntegrable (fun z : ℝ =>
      (principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun z : ℝ =>
      (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun z : ℝ =>
      (residueError520 N q a z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (residueError520 N q a z ^ 2) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add h1 h2,
    ← intervalIntegral.integral_add (h1.add h2) h3]
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [residue_square520]
  ring

/-- LEAF. P0093 pages 159 and 160 equations 3.4, 5.2 and 5.4.
The residue error square means summed over the reduced residues are bounded.
The error retains the omitted prime divisor terms of equation 3.4.
GRH Mellin square estimates and character orthogonality supply this bound. -/
theorem residue_square_mean520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))), ‖residueError520 N q a z‖ ^ 2) ≤
        C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  sorry

/-- LEAF. P0093 page 160 equations 5.3 and 5.5 with equation 3.4.
The mixed contribution has square root of q tau in its denominator.
The residue error retains the omitted prime divisors of the modulus. -/
theorem mixed_bound520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- P0093 page 161 equation 6.3. The damped reciprocal logarithm coefficient,
extended by zero at frequencies zero and one. -/
noncomputable def logCoefficient520 (N m : ℕ) : ℂ :=
  if 2 ≤ m then ((Real.exp (-(m : ℝ) / N) / Real.log m : ℝ) : ℂ) else 0

/-- P0093 page 161 equation 6.3. The model series S one. -/
noncomputable def logFourier520 (N : ℕ) (z : ℝ) : ℂ :=
  ∑' m : ℕ, logCoefficient520 N m *
    Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)

/-- P0093 page 161 equation 6.3. The logarithmic coefficients are absolutely
summable by comparison with the geometric damping series. -/
theorem logCoefficient_summable520 (N : ℕ) (hN : 1 ≤ N) :
    Summable (logCoefficient520 N) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _
    ((damping_summable111_up111 N hN).mul_right (1 / Real.log 2))
  intro m
  by_cases hm : 2 ≤ m
  · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hl : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hmR
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [logCoefficient520, if_pos hm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.exp_pos _).le (hl2.le.trans hl))]
    simpa only [mul_one_div] using div_le_div_of_nonneg_left (Real.exp_pos _).le hl2 hl
  · simp only [logCoefficient520, if_neg hm, norm_zero]
    positivity

/-- P0093 page 161 equation 6.3. Mathlib Cauchy multiplication groups the
square of an absolutely convergent Fourier series by its total frequency. -/
theorem fourier_square_group520 (a : ℕ → ℂ) (ha : Summable a) (z : ℝ) :
    (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 =
      ∑' m : ℕ, (∑ j ∈ range (m + 1), a j * a (m - j)) *
        Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) := by
  have hs : Summable (fun m : ℕ => ‖a m *
      Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)‖) := by
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using ha.norm
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  apply tsum_congr
  intro m
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast [Nat.cast_sub hjm]
  ring

/-- P0093 page 161 equation 6.3. The full period coefficient of the square
is its Cauchy convolution at nonnegative residuals and zero at negative residuals. -/
theorem fourier_square_integral520 (a : ℕ → ℂ) (ha : Summable a) (n : ℤ) :
    (∫ z in (0 : ℝ)..1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      if 0 ≤ n then ∑ j ∈ range (n.toNat + 1), a j * a (n.toNat - j) else 0 := by
  let b : ℕ → ℂ := fun m => ∑ j ∈ range (m + 1), a j * a (m - j)
  have hb : Summable b := (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  have hc := negative_series_coefficient_proved357_up111 b hb (-n)
  rw [coefficient_integral357_up111] at hc
  have he (z : ℝ) : LeanLab.Perelli1996.Kernel.e (-((-n : ℤ) : ℝ) * z) =
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    unfold LeanLab.Perelli1996.Kernel.e
    congr 1
    push_cast
    ring
  simp_rw [he] at hc
  have hi : (∫ z in (0 : ℝ)..1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in (0 : ℝ)..1, Complex.exp
        (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
          ∑' m : ℕ, b m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [fourier_square_group520 a ha]
    exact mul_comm _ _
  rw [hi, hc]
  by_cases hn : 0 ≤ n
  · have habs : (-n).natAbs = n.toNat := by omega
    simp [hn, neg_nonpos.mpr hn, habs, b]
  · have hp : ¬ -n ≤ 0 := by omega
    simp [hn, hp]

/-- P0093 page 161 after equation 6.3. The Cauchy coefficient of S one
squared is exactly the exponentially damped finite logarithmic convolution. -/
theorem logCoefficient_convolution520 (N m : ℕ) :
    (∑ j ∈ range (m + 1), logCoefficient520 N j * logCoefficient520 N (m - j)) =
      ((Real.exp (-(m : ℝ) / N) * logConvolution520 m : ℝ) : ℂ) := by
  classical
  have hsum : (∑ j ∈ range (m + 1), logCoefficient520 N j * logCoefficient520 N (m - j)) =
      ∑ j ∈ Icc 2 (m - 2), logCoefficient520 N j * logCoefficient520 N (m - j) := by
    symm
    apply sum_subset
    · intro j hj
      have hh := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro j hj hout
      by_cases hj2 : 2 ≤ j
      · have hmj : ¬ 2 ≤ m - j := by
          intro h
          apply hout
          exact mem_Icc.mpr ⟨hj2, by omega⟩
        simp [logCoefficient520, hmj]
      · simp [logCoefficient520, hj2]
  rw [hsum, logConvolution520, mul_sum, Complex.ofReal_sum]
  apply sum_congr rfl
  intro j hj
  obtain ⟨hj2, hjm⟩ := mem_Icc.mp hj
  have hjle : j ≤ m := by omega
  have hmj : 2 ≤ m - j := by omega
  simp only [logCoefficient520, if_pos hj2, if_pos hmj, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, ← Real.exp_add]
  have he : -(j : ℝ) / N + -((m - j : ℕ) : ℝ) / N = -(m : ℝ) / N := by
    push_cast [Nat.cast_sub hjle]
    ring
  rw [he]
  ring

/-- P0093 page 161 after equation 6.3. The exact signed full period
model integral is the damped convolution, including every negative residual. -/
theorem logFourier_square_integral520 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ) := by
  unfold logFourier520
  rw [fourier_square_integral520 _ (logCoefficient_summable520 N hN)]
  by_cases hn : 0 ≤ n
  · rw [if_pos hn, logCoefficient_convolution520]
    have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [hc]
  · rw [if_neg hn]
    have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [hz, logConvolution520]

/-- LEAF. P0093 pages 160 and 161 equations 6.1 through 6.3.
Replace the principal square by the full period S one square model.
This is the analytic contour comparison. Fourier extraction is proved separately. -/
theorem principal_model520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- P0093 pages 160 and 161 equations 6.1 through 6.3.
CONDITIONAL on principal_model520. Extend the principal square to a full period and read its exact convolution.
No fixed one over N shoulder is removed. -/
theorem principal_convolution520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, N0, hmodel⟩ := principal_model520 hG
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have h := hmodel N hN0 q hq hqQ n hn
  rwa [logFourier_square_integral520 N hN1 n] at h

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 160 equation 5.4. The phase has unit norm, so the error
square integral is bounded by its square mean at every signed residual. -/
theorem error_integral_le520 (N q : ℕ) (n : ℤ) :
    ‖errorIntegral520 N q n‖ ≤
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖residueError520 N q a z‖ ^ 2 := by
  unfold errorIntegral520
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a ha
  calc
    _ ≤ ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖residueError520 N q a z ^ 2 * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by
        have hr : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
        linarith)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      dsimp only
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 161 after equation 6.3. The convolution vanishes below four. -/
theorem logConvolution_vanish520 (n : ℕ) (hn : n ≤ 3) :
    logConvolution520 n = 0 := by
  unfold logConvolution520
  exact sum_eq_zero (fun m hm => by have := mem_Icc.mp hm; omega)

/-- P0093 page 161 after equation 6.3. The first nonzero convolution. -/
theorem logConvolution_four520 :
    logConvolution520 4 = 1 / (Real.log 2 * Real.log 2) := by
  simp [logConvolution520]

/-- P0093 page 156 equation 3.4. Nonnegative signed phases equal the
natural Ramanujan sum already formalized in Ramanujan103. -/
theorem signedRamanujan_toNat520 (q : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    signedRamanujan520 q n = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat := by
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  unfold signedRamanujan520 LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    LeanLab.Perelli1996.Kernel.e
  apply sum_congr rfl
  intro a ha
  rw [hc]
  congr 1
  push_cast
  ring

/-- P0093 page 161 equation 6.4. The Ramanujan sum is real by its
integer Mobius divisor expansion. -/
theorem ramanujan_im_zero520 (q m : ℕ) (hq : 1 ≤ q) :
    (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q m).im = 0 := by
  rw [LeanLab.Perelli1996.Ramanujan103.ramanujanSum_divisor_expansion q m (by omega)]
  simp only [Complex.im_sum]
  apply sum_eq_zero
  intro d hd
  split_ifs <;> simp

/-- P0093 page 161 equation 6.4. The complex Ramanujan sum is exactly
the cast of the finite real cosine sum used in the sealed target. -/
theorem ramanujan_cos520 (q m : ℕ) (hq : 1 ≤ q) :
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum q m =
      ((∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Real.cos (2 * Real.pi * (m : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) := by
  apply Complex.ext
  · unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum LeanLab.Perelli1996.Kernel.e
    rw [Complex.re_sum, Complex.ofReal_re]
    apply sum_congr rfl
    intro a ha
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  · simp only [Complex.ofReal_im, ramanujan_im_zero520 q m hq]

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset
/-- P0093 page 156 equation 3.4. The principal arithmetic coefficient
has norm at most one for every positive modulus and every signed frequency. -/
theorem principal_coefficient_norm_real520 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖(((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      signedRamanujan520 q n‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hμ 2
  have hr : ‖signedRamanujan520 q n‖ ≤ (q.totient : ℝ) := by
    unfold signedRamanujan520
    calc
      _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
      _ = (q.totient : ℝ) := by
        simp only [Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one]
        congr 1
        rw [Nat.totient_eq_card_coprime]
        congr 1
        ext a
        simp [Nat.coprime_comm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) * q.totient := by
      gcongr
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < (q.totient : ℝ) ^ 2 by positivity)).mpr
      have hsq : (q.totient : ℝ) ≤ (q.totient : ℝ) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hμ2 (by positivity)).trans (by simpa using hsq)


/-- P0093 page 156 equation 3.4. The coefficient in the square expansion
has the same norm bound as its real fraction form. -/
theorem principal_coefficient_norm520 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n‖ ≤ 1 := by
  have hc : principalCoefficient520 q ^ 2 =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp [principalCoefficient520, div_pow]
  rw [hc]
  exact principal_coefficient_norm_real520 q hq n

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 pages 160 and 161 equations 5.4, 5.5 and 6.3.
CONDITIONAL on the three explicit local analytic leaves. The elementary
assembly retains the exact Ramanujan coefficient and damped convolution. -/
theorem local_expansion520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖localArc520 N q n - localMain520 N q n‖ ≤
        B * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := mixed_bound520 hG
  obtain ⟨C2, hC2, N2, h2⟩ := residue_square_mean520 hG
  obtain ⟨C3, hC3, N3, h3⟩ := principal_convolution520 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨C1 + C2 + C3, by positivity, max 2 (max L (max N1 (max N2 N3))), ?_⟩
  intro N hN q hq hqQ n hn
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNL : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNs : max N1 (max N2 N3) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hN2' : N2 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hNs
  have hN3 : N3 < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hNs
  have hlog : 1 ≤ Real.log N := by
    have hreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hreal).le
    simpa using hh
  have hlog6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by omega)
  let τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ)
  let X : ℝ := (N : ℝ) * Real.log N ^ 13
  let E : ℝ := X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ))
  have hτ : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hfirst : X / τ ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_right (show 0 ≤ X / Real.sqrt ((q : ℝ) * τ) by positivity) :
        X / τ ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  have hsecond : X / Real.sqrt ((q : ℝ) * τ) ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_left (show 0 ≤ X / τ by positivity) :
        X / Real.sqrt ((q : ℝ) * τ) ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  have hb : ‖mixedIntegral520 N q n‖ ≤ C1 * E := by
    calc
      _ ≤ C1 * N * Real.log N ^ 6 / Real.sqrt ((q : ℝ) * τ) := h1 N hN1 q hq hqQ n hn
      _ ≤ C1 * N * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * τ) := by gcongr
      _ = C1 * (X / Real.sqrt ((q : ℝ) * τ)) := by dsimp [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond hC1.le
  have hc : ‖errorIntegral520 N q n‖ ≤ C2 * E := by
    calc
      _ ≤ C2 * N / τ * Real.log N ^ 13 :=
        (error_integral_le520 N q n).trans (h2 N hN2' q hq hqQ)
      _ = C2 * (X / τ) := by dsimp [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hC2.le
  have hd : ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
      principalIntegral520 N q n - localMain520 N q n‖ ≤ C3 * E := by
    unfold localMain520
    rw [← mul_sub, norm_mul]
    have hp := h3 N hN3 q hq hqQ n hn
    have hcoef := principal_coefficient_norm520 q hq n
    have hrec : 1 / ((q : ℝ) * τ) ≤ 1 / τ := by
      apply one_div_le_one_div_of_le hτ
      have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    calc
      _ ≤ 1 * ‖principalIntegral520 N q n -
          ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ C3 * X * (1 / ((q : ℝ) * τ) + 1 / Real.sqrt ((q : ℝ) * τ)) := by
        simpa [X, τ, mul_assoc] using hp
      _ ≤ C3 * X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ)) := by gcongr
      _ = _ := by dsimp [E]; ring
  rw [local_decomposition520 N q (by omega) n]
  have heq (p m e t : ℂ) : p + m + e - t = (p - t) + m + e := by ring
  rw [heq]
  calc
    _ ≤ ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
        principalIntegral520 N q n - localMain520 N q n‖ +
        ‖mixedIntegral520 N q n‖ + ‖errorIntegral520 N q n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C3 * E + C1 * E + C2 * E := add_le_add (add_le_add hd hb) hc
    _ = _ := by dsimp [E, X, τ]; ring

/-- P0093 page 165 equation 8.1. The signed residual integrand has period
one. The proof also covers every negative integer residual. -/
theorem residual_periodic520 (N : ℕ) (n : ℤ) :
    Function.Periodic (fun α : ℝ => primeFourier111_up111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)) 1 := by
  have hS : Function.Periodic (primeFourier111_up111 N) 1 := by
    intro α
    unfold primeFourier111_up111
    apply tsum_congr
    intro p
    congr 1
    have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
        ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
          ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by push_cast; ring
    rw [he, Complex.exp_add]
    have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
    rw [hp, mul_one]
  intro α
  dsimp only
  rw [hS α]
  congr 1
  have he : (((2 * Real.pi * (α + 1) * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  have hp : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;> ring
  rw [he, Complex.exp_add, hp, mul_one]

/-- P0093 page 165 equation 8.1. Join the clipped endpoints and sum the
local prime square integrals over disjoint rational arcs. -/
theorem major_integral_partition520 (N : ℕ) (hN : 2 ^ 70 < N) (n : ℤ) :
    (∫ α in majorArcs280_up111 N, primeFourier111_up111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localArc520 N q n := by
  have hsep := major_parameters_separated520 N hN
  have hset : majorArcs280_up111 N = rationalMajor520 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
      ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    ext α
    simp only [majorArcs280_up111, rationalMajor520, Set.mem_setOf_eq,
      Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)]
  rw [hset, rational_partition520 _ hsep.1 _ hsep.2 _
    (by have hS := continuous_prime_fourier111_up111 N (show 1 ≤ N by omega); fun_prop)
    (residual_periodic520 N n)]
  apply sum_congr rfl
  intro q hq
  unfold localArc520
  apply sum_congr rfl
  intro a ha
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  congr 1
  congr 1
  push_cast
  ring

/-- P0093 page 161 equation 6.4. A local main term is the real cosine
coefficient times the exact damped convolution, even for negative residuals. -/
theorem local_main_cos520 (N q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    localMain520 N q n =
      ((Real.exp (-(n : ℝ) / N) *
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
        logConvolution520 n.toNat : ℝ) : ℂ) := by
  by_cases hn : 0 ≤ n
  · unfold localMain520
    rw [signedRamanujan_toNat520 q n hn, ramanujan_cos520 q n.toNat hq]
    simp only [principalCoefficient520]
    push_cast
    ring
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [localMain520, hz, logConvolution_vanish520 0 (by omega)]

/-- P0093 pages 161 and 165 equations 6.4 and 8.1. The per modulus
expansion and the exact disjoint arc partition give the summed expansion.
CONDITIONAL on residue_square_mean520, mixed_bound520 and principal_model520. -/
theorem major_expansion520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℤ, n ≤ N →
      ‖(∫ α in majorArcs280_up111 N, primeFourier111_up111 N α ^ 2 *
          Complex.exp (((2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I)) -
        ((Real.exp (-(n : ℝ) / N) *
          (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
              ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
                Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
          logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
        B * N * Real.log N ^ 13 * ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨B, hB, N0, hlocal⟩ := local_expansion520 hG
  refine ⟨B, hB, max N0 (2 ^ 70), ?_⟩
  intro N hN n hn
  have hN0 := lt_of_le_of_lt (le_max_left N0 (2 ^ 70)) hN
  have hN70 := lt_of_le_of_lt (le_max_right N0 (2 ^ 70)) hN
  rw [major_integral_partition520 N hN70 n]
  have hmain : (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localMain520 N q n) =
      ((Real.exp (-(n : ℝ) / N) *
        (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
            ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
              Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
        logConvolution520 n.toNat : ℝ) : ℂ) := by
    rw [mul_sum, sum_mul, Complex.ofReal_sum]
    apply sum_congr rfl
    intro q hq
    exact local_main_cos520 N q (mem_Icc.mp hq).1 n
  rw [← hmain, ← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  have hqr : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le (by positivity))
  exact hlocal N hN0 q (mem_Icc.mp hq).1 hqr n hn

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset

/-- P0093 page 156 equation 3.4. At modulus one no prime divisor is removed. -/
theorem principal_unit520 (N : ℕ) (z : ℝ) :
    principalPrime520 N 1 z = primeFourier111_up111 N z := by
  simp [principalPrime520]

/-- P0093 page 156 equation 3.4. At the unit modulus residue zero
is exactly principal, so its residue error vanishes pointwise. -/
theorem residue_unit520 (N : ℕ) (z : ℝ) : residueError520 N 1 0 z = 0 := by
  simp [residueError520, principalCoefficient520, principal_unit520]

/-- P0093 page 160 equation 5.4. The unit modulus error square is zero. -/
theorem error_unit520 (N : ℕ) (n : ℤ) : errorIntegral520 N 1 n = 0 := by
  have hs : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  simp [errorIntegral520, hs, residue_unit520]

/-- P0093 page 160 equation 5.5. The unit modulus mixed term is zero. -/
theorem mixed_unit520 (N : ℕ) (n : ℤ) : mixedIntegral520 N 1 n = 0 := by
  have hs : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  simp [mixedIntegral520, hs, residue_unit520]

/-- P0093 page 161 equation 6.4. At modulus one and residual four
the main term is positive and has the exact first convolution value. -/
theorem local_main_four_unit520 (N : ℕ) :
    localMain520 N 1 4 =
      ((Real.exp (-(4 : ℝ) / N) / (Real.log 2 * Real.log 2) : ℝ) : ℂ) := by
  simp [localMain520, principalCoefficient520, signedRamanujan520,
    logConvolution_four520, div_eq_mul_inv]

/-- P0093 pages 161 and 165 equations 6.4 and 8.1. There are arbitrarily
large admissible parameters with modulus one and a nonzero convolution. -/
theorem local_parameters_instance520 (N0 : ℕ) :
    ∃ N : ℕ, N0 < N ∧ 2 ^ 70 < N ∧ 1 ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      (4 : ℤ) ≤ N ∧ 0 < (Real.exp (-(4 : ℝ) / N) / (Real.log 2 * Real.log 2)) := by
  refine ⟨max N0 (2 ^ 70) + 4, by omega, by omega, ?_, by omega, ?_⟩
  · apply Real.one_le_rpow
    · exact_mod_cast (show 1 ≤ max N0 (2 ^ 70) + 4 by omega)
    · norm_num
  · exact div_pos (Real.exp_pos _) (mul_pos (Real.log_pos (by norm_num))
      (Real.log_pos (by norm_num)))

end LeanLab.Linnik1951

/-
Uniform weight control from weighted Farey shells.
Source: P0029 page 26 display 7.5 and page 27 display 7.8.
The shell summation keeps the full discrete transform.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.FareyCount451
import LeanLab.BhowmikGrimmelt2026.SumEstimates

namespace LeanLab.BhowmikGrimmelt2026

/-- The weighted Farey kernel is uniformly summable by its integer distance shells. -/
theorem weighted_pair_kernel451 {R : ℝ} (hR : 1 ≤ R) (α : ℝ) :
    (∑ p ∈ reducedPairs ⌊R⌋₊,
      (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ))) ≤
        6 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
  classical
  let s := reducedPairs ⌊R⌋₊
  let d : (Σ _ : ℕ, ℕ) → ℝ := fun p => R * p.1 * intDist (α - p.2 / p.1)
  let k : (Σ _ : ℕ, ℕ) → ℕ := fun p => ⌊d p⌋₊
  let t := s.image k
  have hd (p : Σ _ : ℕ, ℕ) : 0 ≤ d p := by
    dsimp [d]
    exact mul_nonneg (mul_nonneg (by linarith : 0 ≤ R) (Nat.cast_nonneg _)) (intDist_nonneg _)
  have hz : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : (-(2 : ℝ)) < -1))
  have hmaps : ∀ p ∈ s, k p ∈ t := fun p hp => Finset.mem_image_of_mem k hp
  calc
    _ = ∑ n ∈ t, ∑ p ∈ s.filter (fun p => k p = n), (1 + d p) ^ (-(4 : ℝ)) :=
      (Finset.sum_fiberwise_of_maps_to hmaps (fun p => (1 + d p) ^ (-(4 : ℝ)))).symm
    _ ≤ ∑ n ∈ t, 6 * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      let u := s.filter (fun p => k p = n)
      have hsub : u ⊆ nearPairs451 R α (n + 1) := by
        intro p hp
        obtain ⟨hp, hk⟩ := Finset.mem_filter.mp hp
        have hlt := Nat.lt_floor_add_one (d p)
        change ⌊d p⌋₊ = n at hk
        rw [hk] at hlt
        apply Finset.mem_filter.mpr
        exact ⟨hp, by simpa only [Nat.cast_add, Nat.cast_one] using hlt.le⟩
      have hcard : (u.card : ℝ) ≤ 6 * ((n : ℝ) + 1) ^ 2 := by
        have hh := (Finset.card_le_card hsub).trans (nearPairs_card451 hR (by omega : 1 ≤ n + 1))
        have hh' : (u.card : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 + 2 := by exact_mod_cast hh
        nlinarith only [hh', sq_nonneg (n : ℝ), (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
      have hterm (p : Σ _ : ℕ, ℕ) (hp : p ∈ u) :
          (1 + d p) ^ (-(4 : ℝ)) ≤ ((n : ℝ) + 1) ^ (-(4 : ℝ)) := by
        have hk := (Finset.mem_filter.mp hp).2
        have hh := Nat.floor_le (hd p)
        change ⌊d p⌋₊ = n at hk
        rw [hk] at hh
        exact Real.rpow_le_rpow_of_nonpos
          (by positivity : (0 : ℝ) < (n : ℝ) + 1)
          (by linarith : (n : ℝ) + 1 ≤ 1 + d p) (by norm_num : (-(4 : ℝ)) ≤ 0)
      calc
        _ ≤ ∑ _p ∈ u, ((n : ℝ) + 1) ^ (-(4 : ℝ)) := Finset.sum_le_sum hterm
        _ = (u.card : ℝ) * ((n : ℝ) + 1) ^ (-(4 : ℝ)) := by simp
        _ ≤ (6 * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) ^ (-(4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 6 * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
          norm_num
    _ ≤ ∑' n : ℕ, 6 * ((n : ℝ) + 1) ^ (-(2 : ℝ)) :=
      Summable.sum_le_tsum t (fun n _ => by positivity) (hz.mul_left 6)
    _ = _ := tsum_mul_left

/-- The full reduced pair transform has a uniform bound when its scale is at least R q.
No cardinality remainder is discarded. -/
theorem scaledPairSum_uniform451 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ D : ℝ, 0 < D ∧ ∀ R K α : ℝ, 1 ≤ R → 1 ≤ K →
      ‖scaledPairSum G R K α‖ ≤ D := by
  obtain ⟨C, hC, hc⟩ := GThat_bound hG.supp hG.smooth 4
  let Z : ℝ := 6 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))
  have hZ : 0 ≤ Z := by dsimp [Z]; exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => by positivity))
  refine ⟨C * (Z + 1), by positivity, ?_⟩
  intro R K α hR hK
  have hRp : 0 < R := by linarith
  let s := reducedPairs ⌊R⌋₊
  have hcard : (s.card : ℝ) ≤ R ^ 2 := by
    have hh : (s.card : ℝ) ≤ (⌊R⌋₊ : ℝ) ^ 2 := by exact_mod_cast reducedPairs_card_le ⌊R⌋₊
    exact hh.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hRp.le) 2)
  have halias : (s.card : ℝ) * R ^ (-(4 : ℝ)) ≤ 1 := by
    calc
      _ ≤ R ^ 2 * R ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = R ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hRp]
        norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hterm (p : Σ _ : ℕ, ℕ) (hp : p ∈ s) :
      ‖GThat G (K * R * p.1) (α - p.2 / p.1)‖ ≤
        C * ((1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ)) + R ^ (-(4 : ℝ))) := by
    have hq : (1 : ℝ) ≤ p.1 := by exact_mod_cast ((mem_reducedPairs _ _).mp hp).1
    have hRq : R ≤ K * R * p.1 := by nlinarith [mul_le_mul_of_nonneg_left hK hRp.le]
    have hT : 1 ≤ K * R * p.1 := hR.trans hRq
    have hdist := intDist_nonneg (α - p.2 / p.1)
    have hmul : R * p.1 * intDist (α - p.2 / p.1) ≤
        (K * R * p.1) * intDist (α - p.2 / p.1) := by
      have hh := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ R * p.1 * intDist (α - p.2 / p.1))
      nlinarith only [hh]
    exact (hc _ _ hT).trans (mul_le_mul_of_nonneg_left
      (add_le_add
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num))
        (Real.rpow_le_rpow_of_nonpos hRp hRq (by norm_num))) hC.le)
  have hkernel := weighted_pair_kernel451 hR α
  calc
    _ ≤ ∑ p ∈ s, ‖GThat G (K * R * p.1) (α - p.2 / p.1)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, C * ((1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ)) + R ^ (-(4 : ℝ))) :=
      Finset.sum_le_sum hterm
    _ = C * ((∑ p ∈ s, (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ))) +
        (s.card : ℝ) * R ^ (-(4 : ℝ))) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
    _ ≤ C * (Z + 1) := mul_le_mul_of_nonneg_left (add_le_add hkernel halias) hC.le

/-- The actual full discrete weight is uniformly bounded at every allowed scale. -/
theorem bRhat_uniform451 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, ∀ R η : ℝ, 1 ≤ R → 0 < η →
      10 * R ^ 2 ≤ η * X → ∀ α : ℝ,
        ‖bRhat G R (fun q => η * X * q / R) α‖ ≤ D := by
  obtain ⟨D, hD, hd⟩ := scaledPairSum_uniform451 hG
  refine ⟨D, hD, ?_⟩
  intro X R η hR hη hscale α
  have hRp : 0 < R := by linarith
  have hXp : (0 : ℝ) < X := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hη.le (le_of_not_gt hn)
    nlinarith [sq_nonneg (R - 1)]
  let K : ℝ := η * X / R ^ 2
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
    nlinarith
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 ⌊R⌋₊) : 0 < η * X * q / R := by
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  have heq : bRhat G R (fun q => η * X * q / R) α = scaledPairSum G R K α := by
    rw [bRhat_eq hG.supp hG.even R _ hT, scaledPairSum,
      sum_reducedPairs ⌊R⌋₊ (fun q a => GThat G (K * R * q) (α - a / q))]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    dsimp [K]
    field_simp
    <;> ring
  rw [heq]
  exact hd R K α hR hK

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_pair_kernel451
#print axioms LeanLab.BhowmikGrimmelt2026.scaledPairSum_uniform451
#print axioms LeanLab.BhowmikGrimmelt2026.bRhat_uniform451

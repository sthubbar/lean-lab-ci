import LeanLab.ChenDoubleSieve.Decomp366c

/-!
Finite symmetry and diagonal control for the F4 prime triangle.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
These identities isolate a smaller part of the two dimensional limit.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- A symmetric finite square is twice its strict upper triangle plus its diagonal. -/
theorem symmetric_pair_sum (S : Finset ℕ) (g : ℕ × ℕ → ℝ)
    (hg : ∀ p q, g (p,q) = g (q,p)) :
    (∑ x ∈ S ×ˢ S, g x) =
      2 * (∑ x ∈ (S ×ˢ S).filter (fun x => x.1 < x.2), g x) +
        ∑ p ∈ S, g (p,p) := by
  have hp : (∑ x ∈ S ×ˢ S, g x) =
      (∑ x ∈ (S ×ˢ S).filter (fun x => x.1 < x.2), g x) +
      (∑ x ∈ (S ×ˢ S).filter (fun x => x.2 < x.1), g x) +
      (∑ x ∈ (S ×ˢ S).filter (fun x => x.1 = x.2), g x) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    rcases lt_trichotomy x.1 x.2 with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hs : (∑ x ∈ (S ×ˢ S).filter (fun x => x.2 < x.1), g x) =
      ∑ x ∈ (S ×ˢ S).filter (fun x => x.1 < x.2), g x := by
    simp only [sum_filter, sum_product]
    rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro p hp
    rw [hg p q]
  have hd : (∑ x ∈ (S ×ˢ S).filter (fun x => x.1 = x.2), g x) =
      ∑ p ∈ S, g (p,p) := by
    simp only [sum_filter, sum_product]
    apply sum_congr rfl
    intro p hp
    simp [hp]
  rw [hs, hd] at hp
  linarith

/-- The exact one dimensional prime band for the F4 triangle. -/
def primeBand4 (N : ℕ) : Finset ℕ :=
  (lowerPrimeBand N).filter (fun p => (p : ℝ) < (N : ℝ) ^ kappa2)

/-- The full F4 domain is precisely the strict upper triangle in this band. -/
theorem fullPairs4_as_triangle (N : ℕ) :
    fullPairs4 N = (primeBand4 N ×ˢ primeBand4 N).filter (fun p => p.1 < p.2) := by
  ext p
  simp only [fullPairs4, primeBand4, lowerPrimeBand, mem_filter, mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨hpN, hqN⟩, hp, hq, hlo, hpq, hhi⟩
    have hpqR : (p.1 : ℝ) < p.2 := by exact_mod_cast hpq
    exact ⟨⟨⟨⟨hpN, hp, hlo⟩, hpqR.trans hhi⟩,
      ⟨⟨hqN, hq, hlo.trans hpqR.le⟩, hhi⟩⟩, hpq⟩
  · rintro ⟨⟨⟨⟨hpN, hp, hlo⟩, _⟩, ⟨⟨hqN, hq, _⟩, hhi⟩⟩, hpq⟩
    exact ⟨⟨hpN, hqN⟩, hp, hq, hlo, hpq, hhi⟩

/-- The exact band has uniformly bounded reciprocal mass. -/
theorem primeBand4_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → (∑ p ∈ primeBand4 N, 1 / (p : ℝ)) ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := Task367.lowerPrimeBand_mass_bounded
  refine ⟨K, hK, M, ?_⟩
  intro N hN
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans
    (hM N hN)

/-- The diagonal mass saves one inverse lower cutoff. -/
theorem primeBand4_diagonal_le {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ primeBand4 N, 1 / ((p : ℝ) * p)) ≤
      (1 / (N : ℝ) ^ kappa1) * (∑ p ∈ primeBand4 N, 1 / (p : ℝ)) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpprime, hlo, _⟩ := lowerPrimeBand_range N p (mem_filter.mp hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hz : 0 < (N : ℝ) ^ kappa1 :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  calc
    _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hz hlo) (by positivity)

/-- The prime diagonal has vanishing reciprocal square mass. -/
theorem primeBand4_diagonal_tendsto :
    Tendsto (fun N : ℕ => ∑ p ∈ primeBand4 N, 1 / ((p : ℝ) * p))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, M, hM⟩ := primeBand4_mass_bounded
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => (1 / (N : ℝ) ^ kappa1) * K) atTop (𝓝 0) := by
    simpa using (hz.const_div_atTop 1).mul_const K
  apply squeeze_zero' (Eventually.of_forall (fun N => sum_nonneg (by intros; positivity))) _ ht
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_ge_atTop M] with N hN hNM
  exact (primeBand4_diagonal_le hN).trans
    (mul_le_mul_of_nonneg_left (hM N hNM) (by positivity))

/-- The ordered reciprocal mass equals half the square mass with its diagonal removed. -/
theorem fullPairs4_mass_formula (N : ℕ) :
    pairMass (fullPairs4 N) =
      ((∑ p ∈ primeBand4 N, 1 / (p : ℝ)) ^ 2 -
        ∑ p ∈ primeBand4 N, 1 / ((p : ℝ) * p)) / 2 := by
  have he := symmetric_pair_sum (primeBand4 N)
    (fun p => 1 / ((p.1 : ℝ) * p.2)) (fun p q => by simp [mul_comm])
  rw [← fullPairs4_as_triangle N] at he
  change pairMass (primeBand4 N ×ˢ primeBand4 N) =
    2 * pairMass (fullPairs4 N) + _ at he
  rw [pairMass_product] at he
  nlinarith

/-- A one dimensional exact band mass limit supplies the unweighted ordered mass limit.
CONDITIONAL ON the displayed band mass limit only. -/
theorem fullPairs4_mass_of_band {L : ℝ}
    (hband : Tendsto (fun N : ℕ => ∑ p ∈ primeBand4 N, 1 / (p : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => pairMass (fullPairs4 N)) atTop (𝓝 (L ^ 2 / 2)) := by
  have ht := ((hband.pow 2).sub primeBand4_diagonal_tendsto).div_const 2
  simpa only [sub_zero, fullPairs4_mass_formula] using ht

/-- The F4 full triangle has a concrete nonempty even instance. -/
theorem fullPairs4_instance : (11, 13) ∈ fullPairs4 68719476736 := by
  have he (r : ℝ) : ((68719476736 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ (36 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  have hlo : ((68719476736 : ℕ) : ℝ) ^ kappa1 = 8 := by
    rw [he]
    norm_num [kappa1]
  have hhi : (16 : ℝ) ≤ ((68719476736 : ℕ) : ℝ) ^ kappa2 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (4 : ℝ) ≤ 36 * kappa2)
    norm_num at h
    exact h
  simp only [fullPairs4, mem_filter, mem_product, Finset.mem_range]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · rw [hlo]
    norm_num
  · exact lt_of_lt_of_le (by norm_num : (13 : ℝ) < 16) hhi

/-- The same nonempty triangle instance is coprime to the even modulus. -/
theorem lowerPairs4_instance : (11, 13) ∈ lowerPairs4 68719476736 := by
  have he (r : ℝ) : ((68719476736 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ (36 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  have hlo : ((68719476736 : ℕ) : ℝ) ^ kappa1 = 8 := by
    rw [he]
    norm_num [kappa1]
  have hhi : (16 : ℝ) ≤ ((68719476736 : ℕ) : ℝ) ^ kappa2 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (4 : ℝ) ≤ 36 * kappa2)
    norm_num at h
    exact h
  have h11 : Nat.Coprime 11 68719476736 := by
    simpa using (show Nat.Coprime 11 2 by decide).pow_right 36
  have h13 : Nat.Coprime 13 68719476736 := by
    simpa using (show Nat.Coprime 13 2 by decide).pow_right 36
  simp only [lowerPairs4, Wu08Sum.P2, mem_filter, mem_product, Finset.mem_range]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, h11, h13, ?_, by norm_num, ?_⟩
  · rw [hlo]
    norm_num
  · exact lt_of_lt_of_le (by norm_num : (13 : ℝ) < 16) hhi


end LeanLab.ChenDoubleSieve.Task366

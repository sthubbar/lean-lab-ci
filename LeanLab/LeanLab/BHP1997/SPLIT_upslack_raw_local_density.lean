/-
P0069 Baker Harman Pintz 1997, Section 5, page 53, with 5.17 on page 51.
Burst burst-20261124, session S4, unit S4-22: a split of the LEAF `upslack_raw_local_density` of
Prep1121UpslackRoute along the page 53 four-term identity. By `upper_rough_four_term`,
psi(m, Y^c4) = g_m - h_m + j_m - k_m, so the raw weight b1 = g - h + j - kept part of k equals
psi(m, Y^c4) plus the deleted part k_m - kept part of k_m, the terms over the set E of page 53.
The page 53 constant v1 = w(1/c4)/c4 + the integral over E is exactly the sum of the two local
densities, so the density leaf splits into two cited prime number theorem leaves:
1. upslack_rough_c4_density, HARD: the Buchstab density of psi(m, Y^c4) on J.
2. upslack_deleted_density, HARD: the density of the deleted part of k_m on J, bounded by the
   lab's conservative deleted integral upperDeletedIntegral.
upslack_raw_local_density_of_leaves has the exact statement of upslack_raw_local_density and is
PROVED from the two LEAFs. The hypotheses Theorem 4 and Lemma 9 of the target are not used.
New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 page 53, the display for v1 "from the prime number theorem", its first summand
w(1/c4)/c4, with 5.17 on page 51: the sifted indicator psi(m, Y^c4) on J has a local density
profile `D x m` over `log Y`, the Buchstab density w(log m / log Y^c4) / c4 up to the prime
number theorem error. `D` is at least some `c > 0`, varies by at most `K / Y` per unit step on J,
is at most w(1/c4)/c4 plus any `eta > 0` uniformly on J for large x, and the prefix sums of
psi(m, Y^c4) minus `D / log Y` over J are `O(Y L^-A)` for every `A`. Buchstab's theorem with the
prime number theorem with error term `Y exp(-eps L^(1/2))`. HARD. -/
theorem upslack_rough_c4_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (D : ℝ → ℕ → ℝ) (c K : ℝ), 0 < c ∧ (∀ x m, c ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (upperRough m ((x ^ (11 / 20 + ε)) ^ upperC4 ε) -
            D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  sorry

/-- LEAF: P0069 page 53, the display for v1 "from the prime number theorem", its second summand,
the integral over the deleted set E, with 5.17 on page 51: the deleted part k_m minus the kept
part of k_m, the terms p1 p2 p3 n4 = m with psi(n4, p3) whose exponents fail the Lemma 33 test,
has on J a nonnegative local density profile `D x m` over `log Y` that varies by at most `K / Y`
per unit step on J, is at most the conservative deleted integral upperDeletedIntegral plus any
`eta > 0` uniformly on J for large x, and the prefix sums of the deleted part minus `D / log Y`
over J are `O(Y L^-A)` for every `A`. The prime number theorem with error term for the three
primes and Buchstab's theorem for psi(n4, p3). HARD. -/
theorem upslack_deleted_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (D : ℝ → ℕ → ℝ) (K : ℝ), (∀ x m, 0 ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ upperDeletedIntegral ω ε + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperK ε (x ^ (11 / 20 + ε)) m - upperKept ε (x ^ (11 / 20 + ε)) m) -
            D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  sorry

/-- P0069 page 53: the exact statement of the LEAF `upslack_raw_local_density` of
Prep1121UpslackRoute, from the two LEAFs of this file and the PROVED four-term identity
`upper_rough_four_term`. PROVED from those LEAFs; Theorem 4 and Lemma 9 are carried and not
used. -/
theorem upslack_raw_local_density_of_leaves
    (_h4 : Thm4.Theorem4Paper) (_h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (D : ℝ → ℕ → ℝ) (c K : ℝ), 0 < c ∧ (∀ x m, c ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  obtain ⟨D₁, c, K₁, hc, hD₁c, hL₁, hconv₁, hpre₁⟩ := upslack_rough_c4_density hω hz hε hε8
  obtain ⟨D₂, K₂, hD₂, hL₂, hconv₂, hpre₂⟩ := upslack_deleted_density hω hz hε hε8
  refine ⟨fun x m => D₁ x m + D₂ x m, c, K₁ + K₂, hc, fun x m => ?_, ?_, ?_, ?_⟩
  · linarith [hD₁c x m, hD₂ x m]
  · intro x m hm m' hm'
    have h1 := hL₁ x m hm m' hm'
    have h2 := hL₂ x m hm m' hm'
    calc |D₁ x m + D₂ x m - (D₁ x m' + D₂ x m')|
        = |(D₁ x m - D₁ x m') + (D₂ x m - D₂ x m')| := by ring_nf
      _ ≤ |D₁ x m - D₁ x m'| + |D₂ x m - D₂ x m'| := abs_add_le _ _
      _ ≤ K₁ * |(m : ℝ) - m'| / x ^ (11 / 20 + ε) + K₂ * |(m : ℝ) - m'| / x ^ (11 / 20 + ε) :=
          add_le_add h1 h2
      _ = (K₁ + K₂) * |(m : ℝ) - m'| / x ^ (11 / 20 + ε) := by ring
  · intro η hη
    obtain ⟨X₁, hX₁⟩ := hconv₁ (η / 2) (by linarith)
    obtain ⟨X₂, hX₂⟩ := hconv₂ (η / 2) (by linarith)
    refine ⟨max X₁ X₂, fun x hx m hm => ?_⟩
    have a1 := hX₁ x (le_trans (le_max_left _ _) hx) m hm
    have a2 := hX₂ x (le_trans (le_max_right _ _) hx) m hm
    show D₁ x m + D₂ x m ≤ _
    linarith
  · intro A hA
    obtain ⟨C₁, hC₁⟩ := hpre₁ A hA
    obtain ⟨C₂, hC₂⟩ := hpre₂ A hA
    refine ⟨|C₁| + |C₂| + 1, fun x hx t ht => ?_⟩
    have hx1 : (1 : ℝ) ≤ x := by
      have := abs_nonneg C₁; have := abs_nonneg C₂; linarith
    have hxC₁ : C₁ ≤ x := by have := le_abs_self C₁; have := abs_nonneg C₂; linarith
    have hxC₂ : C₂ ≤ x := by have := le_abs_self C₂; have := abs_nonneg C₁; linarith
    have hY : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
    have b1 := hC₁ x hxC₁ t ht
    have b2 := hC₂ x hxC₂ t ht
    have hsplit : ∀ m : ℕ,
        upperRawWeight ε (x ^ (11 / 20 + ε)) m -
            (D₁ x m + D₂ x m) / Real.log (x ^ (11 / 20 + ε)) =
          (upperRough m ((x ^ (11 / 20 + ε)) ^ upperC4 ε) -
              D₁ x m / Real.log (x ^ (11 / 20 + ε))) +
            ((upperK ε (x ^ (11 / 20 + ε)) m - upperKept ε (x ^ (11 / 20 + ε)) m) -
              D₂ x m / Real.log (x ^ (11 / 20 + ε))) := by
      intro m
      rw [upper_rough_four_term ε hY m]
      unfold upperRawWeight
      ring
    simp only [hsplit, Finset.sum_add_distrib]
    have hZ : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
      positivity
    have e1 : C₁ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        |C₁| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hZ
    have e2 : C₂ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        |C₂| * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hZ
    refine le_trans (abs_add_le _ _) ?_
    calc _ ≤ C₁ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
          C₂ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := add_le_add b1 b2
      _ ≤ (|C₁| + |C₂| + 1) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
          nlinarith

/-- Helper: the Buchstab function is strictly positive above one.
This follows from the defining delay equation: ω u = 1/u on [1,2], and for u > 2,
u·ω u = 2·ω 2 + ∫₂ᵘ ω(t-1) dt > 0 since ω > 0 on [1,2] and ω ≥ 0 above 1. -/
theorem buchstab_pos_above_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 1 < u) :
    0 < ω u := by
  have hnonneg : ∀ v : ℝ, 1 ≤ v → 0 ≤ ω v := by
    intro v hv
    exact buchstab_nonneg hω hv
  have hpos_interval : ∀ v : ℝ, 1 ≤ v → v ≤ 2 → 0 < ω v := by
    intro v hv1 hv2
    have hωv : ω v = 1 / v := hω.2.1 v hv1 (by linarith)
    rw [hωv]
    have hv0 : 0 < v := by linarith [hv1]
    positivity
  by_cases hle2 : u ≤ 2
  · have hωu : ω u = 1 / u := hω.2.1 u (by linarith [hu, hle2]) (by linarith)
    rw [hωu]
    have hu0 : 0 < u := by linarith [hu]
    positivity
  · have hu2 : 2 < u := by linarith [hle2]
    have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc 2 u) :=
      continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
    have hder : ∀ t ∈ Ioo (2 : ℝ) u,
        HasDerivAt (fun v => v * ω v) (ω (t - 1)) t := by
      intro t ht
      have h₁ := hω.2.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2, hu2])
      simpa only [h₁, one_div] using hω.2.2 t ht.1
    have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 2 u) := by
      rw [uIcc_of_le hu2]
      apply hω.1.comp (by fun_prop)
      intro t ht
      change 1 ≤ t - 1
      linarith [ht.1]
    have hFTC := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hder hci.intervalIntegrable
    have hI : (∫ t in (2 : ℝ)..u, ω (t - 1)) ≥ 0 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht
      have ht' : 2 ≤ t := by linarith [ht.1]
      have ht'' : t ≤ u := by linarith [ht.2]
      have ht''' : 1 ≤ t - 1 := by linarith
      exact hnonneg (t - 1) ht'''
    have h2w2 : 0 < 2 * ω 2 := by
      have hω2 : ω 2 = 1 / 2 := hω.2.1 2 (by norm_num) (by norm_num)
      rw [hω2]
      norm_num
    have hwu : u * ω u = 2 * ω 2 + ∫ t in (2 : ℝ)..u, ω (t - 1) := by
      have h₁ := hFTC
      have h₂ : (∫ t in (2 : ℝ)..u, ω (t - 1)) = (u * ω u - 2 * ω 2) := by
        linarith
      linarith
    have hwu_pos : 0 < u * ω u := by
      have h₁ : 0 ≤ ∫ t in (2 : ℝ)..u, ω (t - 1) := hI
      have h₂ : 0 < 2 * ω 2 := h2w2
      rw [hwu]
      linarith
    have hu0 : 0 < u := by linarith [hu]
    have hωu_pos : 0 < ω u := by
      by_contra h
      have hωu_nonpos : ω u ≤ 0 := by linarith
      have h₁ : u * ω u ≤ 0 := by
        nlinarith
      linarith
    exact hωu_pos

/-- Attempt at the rough density leaf. Stuck on the prefix sum condition,
which requires Buchstab's counting theorem with PNT error terms on short intervals -
not formalized in the lab or Mathlib. -/
theorem upslack_rough_c4_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (D : ℝ → ℕ → ℝ) (c K : ℝ), 0 < c ∧ (∀ x m, c ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (upperRough m ((x ^ (11 / 20 + ε)) ^ upperC4 ε) -
            D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  have h₁ : 0 < ω (1 / (1/4 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 8 - ε)) := by
    have hc4 : 1 / 4 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 8 - ε > 1 := by
      norm_num at hε8 ⊢
      linarith
    have hinv : 1 < 1 / (1/4 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 8 - ε) := by
      apply one_div_lt_one
      · norm_num at hε8 ⊢
        linarith
      · linarith
    exact buchstab_pos_above_one hω hinv
  sorry
end LeanLab.BHP1997.DecompC165d

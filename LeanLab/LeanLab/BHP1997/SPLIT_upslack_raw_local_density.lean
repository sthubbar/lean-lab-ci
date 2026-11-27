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

end LeanLab.BHP1997.DecompC165d

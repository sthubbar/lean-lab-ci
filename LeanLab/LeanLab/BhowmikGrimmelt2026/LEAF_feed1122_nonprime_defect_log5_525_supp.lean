/-
Repaired form of nonprime_defect_log5_525 from SPLIT_minor_bare_multi525,
burst-20261122 feed1122.

The statement nonprime_defect_log5_525 asks only that phi be bounded by M. Its
prime restricted sum runs over all primes up to X, with weight phi of n over N,
while the full smoothed sum Sphi stops at N. Without a support condition the
primes between N and X stay in the defect, and a heuristic from the prime number
theorem, checked numerically, shows the defect coefficient then grows like X,
so the summed bound X to thirteen fifths fails for very large X. See the burst
note for the numbers. That statement is left unchanged and reported as FALSE as
stated.

Here the missing hypothesis is added: phi vanishes to the right of one, which
holds for every admissible phi of display 7.1 on page 25 of P0029, whose support
lies in the open interval from one fifth to four fifths. Under it the prime
restricted sum equals primeSphi451, and the bound is the proved
prime_power_family_log5_451 of PrimePowerMinor451 with the minor arc mask and
the phase as the bounded multiplier.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp525a
import LeanLab.BhowmikGrimmelt2026.PrimePowerMinor451

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

private theorem norm_ee_feed1122 (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

/-- When phi vanishes to the right of one, the prime restricted sum over the
primes up to X with weight phi of n over N is the prime part primeSphi451 at
cutoff N, for every N between one and X. -/
theorem primeSum_eq_primeSphi451_feed1122 {ϕ : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, 1 < x → ϕ x = 0) {X N : ℕ} (hN : N ∈ Finset.Icc 1 X) (α : ℝ) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) =
      primeSphi451 ϕ N α := by
  have hN1 := (Finset.mem_Icc.mp hN).1
  have hNX := (Finset.mem_Icc.mp hN).2
  unfold primeSphi451
  rw [Finset.sum_filter]
  have hcongr : (∑ n ∈ Finset.range (X + 1),
      if n.Prime then ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n) else 0) =
      ∑ n ∈ Finset.range (X + 1),
        ((if n.Prime then vonMangoldt n * ϕ (n / N) else 0 : ℝ) : ℂ) * ee (α * n) := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime <;> simp [hp]
  rw [hcongr]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_range] at hn hn'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hgt : (1 : ℝ) < (n : ℝ) / N := by
      rw [one_lt_div hNpos]
      exact_mod_cast (by omega : N < n)
    by_cases hp : n.Prime <;> simp [hp, hsupp _ hgt]

/-- The higher prime power defect of SPLIT_minor_bare_multi525, with the support
hypothesis that phi vanishes to the right of one added. PROVED from
prime_power_family_log5_451. -/
theorem nonprime_defect_log5_525_of_supp {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (hsupp : ∀ x : ℝ, 1 < x → ϕ x = 0)
    {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2)
      ≤ 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  let W : ℕ → ℝ → ℂ := fun N α =>
    if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else ee (-(N * α))
  have hW : ∀ N α, ‖W N α‖ ≤ 1 := by
    intro N α
    simp only [W]
    split_ifs
    · simp
    · rw [norm_ee_feed1122]
  refine le_trans (le_of_eq ?_) (prime_power_family_log5_451 hM hbound hX W hW)
  apply Finset.sum_congr rfl
  intro N hN
  congr 2
  apply intervalIntegral.integral_congr
  intro α _
  simp only [W]
  rw [primeSum_eq_primeSphi451_feed1122 hsupp hN α]
  split_ifs <;> simp

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.primeSum_eq_primeSphi451_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.nonprime_defect_log5_525_of_supp

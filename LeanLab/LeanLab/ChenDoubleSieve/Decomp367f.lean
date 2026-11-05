import LeanLab.ChenDoubleSieve.Decomp367a
import LeanLab.ChenDoubleSieve.Decomp363d

/-!
Finite progression setup for the pair discrepancy in Wu equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39 error display and equation 10.5.
No analytic sieve or mean value leaf is used by these helpers.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348

/-- The pair discrepancy is exactly a sum of progression discrepancies. -/
theorem rawRemainder5_AP (B : ℝ) (N : ℕ) :
    rawRemainder5 B N = ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
      |(#((range (N + 1)).filter (fun r => r.Prime ∧
          r % (p.1 * p.2 * q) = N % (p.1 * p.2 * q))) : ℝ) -
        Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| := by
  unfold rawRemainder5
  simp_rw [Task363.primeSequence_divisor_card]

/-- Increasing the logarithmic loss shrinks each residual pair modulus set. -/
theorem pairModuli5_antitone {N : ℕ} (hlog : 1 ≤ log (N : ℝ))
    {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) (p : ℕ × ℕ) :
    pairModuli5 B₂ N p ⊆ pairModuli5 B₁ N p := by
  intro q hq
  obtain ⟨hqI, hgood⟩ := mem_filter.mp hq
  obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hqI
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨hq1, hqQ.trans (Nat.floor_mono ?_)⟩, hgood⟩
  exact div_le_div_of_nonneg_right (Task363.sieveLevel_antitone hlog hB) (Nat.cast_nonneg _)

/-- The total absolute pair discrepancy decreases as the loss increases. -/
theorem rawRemainder5_antitone {N : ℕ} (hlog : 1 ≤ log (N : ℝ))
    {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) : rawRemainder5 B₂ N ≤ rawRemainder5 B₁ N := by
  apply sum_le_sum
  intro p hp
  exact sum_le_sum_of_subset_of_nonneg (pairModuli5_antitone hlog hB p)
    (by intros; exact abs_nonneg _)

/-- The residual modulus domain is nonempty when its real cutoff is at least one. -/
theorem one_mem_pairModuli5 {B : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hQ : 1 ≤ Task363.sieveLevel B N / (p.1 * p.2 : ℕ)) :
    1 ∈ pairModuli5 B N p := by
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨le_refl _, Nat.le_floor (by simpa using hQ)⟩, squarefree_one, ?_⟩
  exact Nat.coprime_one_left _

/-- A concrete residual domain instance with positive loss and even N. -/
theorem pairModuli5_instance : 1 ∈ pairModuli5 1 16 (1, 1) := by
  simpa only [pairModuli5, Nat.one_mul, Nat.mul_one, Nat.cast_one, div_one, Task363.remainderModuli] using
    Task363.remainderModuli_instance

end LeanLab.ChenDoubleSieve.Task367

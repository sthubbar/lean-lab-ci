import LeanLab.ChenDoubleSieve.Decomp363b

/-!
Finite arithmetic progression setup for Wu 2004 page 38 remainder display.
No distribution theorem is used in the counting identities or level monotonicity.
Source: https://arxiv.org/pdf/0705.1652, pages 6 and 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348

/-- Divisibility in the prime difference sequence is the exact residue N count. -/
theorem primeSequence_divisor_card (N q : ℕ) :
    #((primeSequence N).filter (fun a => q ∣ a)) =
      #((range (N + 1)).filter (fun p => p.Prime ∧ p % q = N % q)) := by
  unfold primeSequence
  rw [Finset.filter_image]
  have hfilter : ((range (N + 1)).filter Nat.Prime).filter (fun p => q ∣ N - p) =
      (range (N + 1)).filter (fun p => p.Prime ∧ p % q = N % q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hpN, hp⟩, hd⟩
      exact ⟨hpN, hp, (Nat.modEq_iff_dvd' (by omega : p ≤ N)).2 hd⟩
    · rintro ⟨hpN, hp, heq⟩
      exact ⟨⟨hpN, hp⟩, (Nat.modEq_iff_dvd' (by omega : p ≤ N)).1 heq⟩
  rw [hfilter]
  apply Finset.card_image_of_injOn
  intro p hp r hr heq
  dsimp only at heq
  have hpN := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hrN := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  omega

/-- The finite discrepancy is literally the arithmetic progression discrepancy
at the endpoint and residue used in the written proof. -/
theorem rawRemainder_AP (B : ℝ) (N : ℕ) :
    rawRemainder B N = ∑ q ∈ remainderModuli B N,
      |(#((range (N + 1)).filter (fun p => p.Prime ∧ p % q = N % q)) : ℝ) -
        Wu04.li N / (q.totient : ℝ)| := by
  unfold rawRemainder
  simp_rw [primeSequence_divisor_card]

/-- Increasing the logarithmic loss decreases the available sieve level. -/
theorem sieveLevel_antitone {N : ℕ} (hlog : 1 ≤ log (N : ℝ))
    {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) : sieveLevel B₂ N ≤ sieveLevel B₁ N := by
  unfold sieveLevel
  exact div_le_div_of_nonneg_left (rpow_nonneg (Nat.cast_nonneg N) _)
    (rpow_pos_of_pos (by linarith) _)
    (rpow_le_rpow_of_exponent_le hlog hB)

/-- The discrepancy modulus set decreases with the logarithmic level loss. -/
theorem remainderModuli_antitone {N : ℕ} (hlog : 1 ≤ log (N : ℝ))
    {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) : remainderModuli B₂ N ⊆ remainderModuli B₁ N := by
  intro q hq
  obtain ⟨hqI, hqgood⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hqI
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hq1, hqQ.trans (Nat.floor_mono (sieveLevel_antitone hlog hB))⟩, hqgood⟩

/-- The absolute discrepancy sum also decreases as B increases. -/
theorem rawRemainder_antitone {N : ℕ} (hlog : 1 ≤ log (N : ℝ))
    {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) : rawRemainder B₂ N ≤ rawRemainder B₁ N := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (remainderModuli_antitone hlog hB)
    (fun _ _ _ => abs_nonneg _)

/-- The modulus one is present whenever the real level is at least one. -/
theorem one_mem_remainderModuli {B : ℝ} {N : ℕ} (hQ : 1 ≤ sieveLevel B N) :
    1 ∈ remainderModuli B N := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨le_refl _, Nat.le_floor (by simpa using hQ)⟩, squarefree_one, ?_⟩
  exact Nat.coprime_one_left N

/-- A concrete nonempty discrepancy domain with positive B and even N. -/
theorem remainderModuli_instance : 1 ∈ remainderModuli 1 16 := by
  apply one_mem_remainderModuli
  have hpos : 0 < log (16 : ℝ) := log_pos (by norm_num)
  have hlog2 : log (2 : ℝ) < 1 := by
    have h := log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have he : log (16 : ℝ) = 4 * log 2 := by
    have h := log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  have hb : log (16 : ℝ) < 4 := by linarith
  unfold sieveLevel
  norm_num
  exact (one_le_div hpos).2 hb.le

/-- A single signed sieve weight row is dominated by the absolute discrepancy.
This is the elementary triangle inequality step in the page 38 display. -/
theorem weighted_remainder_bound (B : ℝ) (N : ℕ) (weights : ℕ → ℝ) (C : ℝ)
    (hweights : ∀ q ∈ remainderModuli B N, |weights q| ≤ C) :
    |∑ q ∈ remainderModuli B N,
      weights q * ((#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
        Wu04.li N / (q.totient : ℝ))| ≤ C * rawRemainder B N := by
  calc
    _ ≤ ∑ q ∈ remainderModuli B N,
        |weights q * ((#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
          Wu04.li N / (q.totient : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ remainderModuli B N,
        C * |(#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
          Wu04.li N / (q.totient : ℝ)| := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hweights q hq) (abs_nonneg _)
    _ = C * rawRemainder B N := by rw [rawRemainder, Finset.mul_sum]

/-- A finite family of bounded sieve weight rows loses only its cardinal factor.
Source: page 38, the sum over l below L. -/
theorem rows_remainder_bound (B : ℝ) (N : ℕ) {ι : Type*} (I : Finset ι)
    (weights : ι → ℕ → ℝ) (hweights : ∀ l ∈ I, ∀ q ∈ remainderModuli B N, |weights l q| ≤ 1) :
    |∑ l ∈ I, ∑ q ∈ remainderModuli B N,
      weights l q * ((#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
        Wu04.li N / (q.totient : ℝ))| ≤ (I.card : ℝ) * rawRemainder B N := by
  calc
    _ ≤ ∑ l ∈ I, |∑ q ∈ remainderModuli B N,
        weights l q * ((#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
          Wu04.li N / (q.totient : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ I, rawRemainder B N := by
      apply Finset.sum_le_sum
      intro l hl
      simpa only [one_mul] using weighted_remainder_bound B N (weights l) 1 (hweights l hl)
    _ = _ := by simp

end LeanLab.ChenDoubleSieve.Task363

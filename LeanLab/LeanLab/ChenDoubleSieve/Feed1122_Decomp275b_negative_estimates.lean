import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Task693Quotients
import LeanLab.ChenDoubleSieve.Task693Switching

/-!
SPLIT of `Task275.negative_estimates` into its nine printed upper bounds, one per index.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 39 to 41, equations 10.3, 10.4, 10.10 to 10.12.
This file imports Decomp275b because the parent's statement uses the definitions
`sieveTerms`, `integralTerms` and `Θ` that live there; the original is not edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 39 equation 10.3, upper bound for Upsilon 1, the sum over primes p between N to the kappa one and N to the kappa two of S at level p, giving F1. Index 1 of sieveTerms. Class HARD. -/
theorem leaf_term1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 1 ≤ (integralTerms F f ω 1 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.4 with sigma one, upper bound for the sum over p between N to the kappa one and N to the sigma one, giving F2. Index 2 of sieveTerms. Class HARD. -/
theorem leaf_term2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 2 ≤ (integralTerms F f ω 2 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.4 with sigma two, upper bound for the sum over p between N to the kappa one and N to the sigma two, giving F3. Index 3 of sieveTerms. Class HARD. -/
theorem leaf_term3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 3 ≤ (integralTerms F f ω 3 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 40 equation 10.10, upper bound for Upsilon 7 obtained by inserting 10.7 to 10.9 into 10.6, giving F7. Index 6 of sieveTerms. Class HARD. -/
theorem leaf_term6 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 6 ≤ (integralTerms F f ω 6 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.11 with i equal 8, upper bound for Upsilon 8, giving F8. Index 7 of sieveTerms. Class HARD. -/
theorem leaf_term7 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 7 ≤ (integralTerms F f ω 7 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 9, upper bound for Upsilon 9 via Lemma 2.6 and 3 sigma one plus kappa one above 1, giving F9. Index 8 of sieveTerms. Class HARD. -/
theorem leaf_term8 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 8 ≤ (integralTerms F f ω 8 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.11 with i equal 10, upper bound for Upsilon 10 using 2 sigma one plus sigma two plus kappa two above 1, giving F10. Index 9 of sieveTerms. Class HARD. -/
theorem leaf_term9 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 9 ≤ (integralTerms F f ω 9 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 13, upper bound for Upsilon 13 via Lemma 2.6 and Lemma 2.10, giving F13. Index 10 of sieveTerms. Class HARD. -/
theorem leaf_term10 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 10 ≤ (integralTerms F f ω 10 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 14, upper bound for Upsilon 14 via Lemma 2.6 and Lemma 2.10, giving F14. Index 11 of sieveTerms. Class HARD. -/
theorem leaf_term11 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 11 ≤ (integralTerms F f ω 11 + ε) * Θ N := by
  sorry

/-- The parent `negative_estimates`, exactly as stated in Decomp275b, from the nine leaves. -/
theorem negative_estimates_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  intro ε hε
  obtain ⟨A1, h1⟩ := leaf_term1 F f ω h hω ε hε
  obtain ⟨A2, h2⟩ := leaf_term2 F f ω h hω ε hε
  obtain ⟨A3, h3⟩ := leaf_term3 F f ω h hω ε hε
  obtain ⟨A6, h6⟩ := leaf_term6 F f ω h hω ε hε
  obtain ⟨A7, h7⟩ := leaf_term7 F f ω h hω ε hε
  obtain ⟨A8, h8⟩ := leaf_term8 F f ω h hω ε hε
  obtain ⟨A9, h9⟩ := leaf_term9 F f ω h hω ε hε
  obtain ⟨A10, h10⟩ := leaf_term10 F f ω h hω ε hε
  obtain ⟨A11, h11⟩ := leaf_term11 F f ω h hω ε hε
  refine ⟨A1 + A2 + A3 + A6 + A7 + A8 + A9 + A10 + A11, ?_⟩
  intro N hN hle i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 N hN (by omega)
  · exact h2 N hN (by omega)
  · exact h3 N hN (by omega)
  · exact h6 N hN (by omega)
  · exact h7 N hN (by omega)
  · exact h8 N hN (by omega)
  · exact h9 N hN (by omega)
  · exact h10 N hN (by omega)
  · exact h11 N hN (by omega)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

/-- The lower prime cuts in Upsilon seven and eight force the cofactor below q squared.
Wu 2004 pages 39 to 41, the switching step before equation 10.6. -/
theorem pair_cut_six_seven {N p q : ℕ} (hN : 2 ≤ N) (hpq : p < q)
    (hp : (N : ℝ) ^ sigma2 ≤ p) : N < p * q ^ 3 := by
  have hx : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hq : (N : ℝ) ^ sigma2 ≤ q := hp.trans (by exact_mod_cast hpq.le)
  have hb := Task693.power_cut_product hx hp hq hq (by norm_num [sigma2])
  have hc : (N : ℝ) < ((p * q ^ 3 : ℕ) : ℝ) := by
    push_cast
    convert hb using 1 <;> ring
  exact_mod_cast hc

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

/-- The mixed prime cuts in Upsilon nine force the cofactor below q squared.
Wu 2004 page 41, the condition after equation 10.12. -/
theorem pair_cut_eight {N p q : ℕ} (hN : 2 ≤ N)
    (hp : (N : ℝ) ^ kappa1 ≤ p) (hq : (N : ℝ) ^ sigma1 ≤ q) :
    N < p * q ^ 3 := by
  have hx : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hb := Task693.power_cut_product hx hp hq hq (by norm_num [kappa1, sigma1])
  have hc : (N : ℝ) < ((p * q ^ 3 : ℕ) : ℝ) := by
    push_cast
    convert hb using 1 <;> ring
  exact_mod_cast hc

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

/-- The crossing prime cuts in Upsilon ten force the cofactor below the fixed level squared.
Wu 2004 page 41, the condition after equation 10.11. -/
theorem pair_cut_nine {N p q : ℕ} (hN : 2 ≤ N)
    (hp : (N : ℝ) ^ kappa2 ≤ p) (hq : (N : ℝ) ^ sigma2 ≤ q) :
    (N : ℝ) < (p : ℝ) * q * ((N : ℝ) ^ sigma1) ^ 2 := by
  have hx : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact Task693.power_cut_product hx hp hq le_rfl (by norm_num [kappa2, sigma1, sigma2])

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Finset Real
open scoped Classical

/-- Exact elementary upper reduction of Upsilon seven and eight before Wu 2004 equation 10.6.
The prime quotient count and all three exceptional counts are retained. -/
theorem terms_six_seven_switching (N : ℕ) (i : Fin 12) (hN : 2 ≤ N)
    (hi : i ∈ ({6, 7} : Finset (Fin 12))) :
    sieveTerms N i ≤ ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ (if i = 6 then sigma1 else sigma2) ≤ p ∧ p < q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      (#{a ∈ primeSequence N | (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2 ∣ a ∧ (a / ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2)).Prime} +
      #{a ∈ primeSequence N | a = (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2} +
      #{a ∈ primeSequence N | (q : ℕ × ℕ).1 ^ 2 * (q : ℕ × ℕ).2 ∣ a} +
      #{a ∈ primeSequence N | ¬ a.Coprime N}) : ℕ) : ℝ) := by
  have hseq : ∀ a ∈ primeSequence N, a ≤ N := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    exact Nat.sub_le _ _
  have hS : sieveTerms N i = ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ (if i = 6 then sigma1 else sigma2) ≤ p ∧ p < q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      Wu41.S (primeSequence N) ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2) (N * (q : ℕ × ℕ).1) (q : ℕ × ℕ).2 : ℕ) : ℝ) := by
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num [sieveTerms]
  rw [hS]
  apply Nat.cast_le.mpr
  apply sum_le_sum
  intro q hq
  have hprops := hq
  simp only [Wu08Sum.P2, mem_filter] at hprops
  obtain ⟨_, hpp, hqp, hpc, hqc, hband, hpq, hroot⟩ := hprops
  have hband2 : (N : ℝ) ^ sigma2 ≤ (q : ℕ × ℕ).1 := by
    apply le_trans _ hband
    apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    split_ifs <;> norm_num [sigma1, sigma2]
  exact Task693.sieve_switching_count (primeSequence N) N (q : ℕ × ℕ).1 (q : ℕ × ℕ).2 hpp hseq
    (pair_cut_six_seven hN hpq hband2)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Finset Real
open scoped Classical

/-- Exact elementary upper reduction of Upsilon nine in Wu 2004 equation 10.12.
The prime quotient and all exceptional counts are retained. -/
theorem term_eight_switching (N : ℕ) (hN : 2 ≤ N) :
    sieveTerms N 8 ≤ ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma1 ∧
          (N : ℝ) ^ sigma1 ≤ q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      (#{a ∈ primeSequence N | (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2 ∣ a ∧ (a / ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2)).Prime} +
      #{a ∈ primeSequence N | a = (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2} +
      #{a ∈ primeSequence N | (q : ℕ × ℕ).1 ^ 2 * (q : ℕ × ℕ).2 ∣ a} +
      #{a ∈ primeSequence N | ¬ a.Coprime N}) : ℕ) : ℝ) := by
  have hseq : ∀ a ∈ primeSequence N, a ≤ N := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    exact Nat.sub_le _ _
  have hS : sieveTerms N 8 = ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma1 ∧
          (N : ℝ) ^ sigma1 ≤ q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      Wu41.S (primeSequence N) ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2) (N * (q : ℕ × ℕ).1) (q : ℕ × ℕ).2 : ℕ) : ℝ) := by
    norm_num [sieveTerms]
  rw [hS]
  apply Nat.cast_le.mpr
  apply sum_le_sum
  intro q hq
  have hprops := hq
  simp only [Wu08Sum.P2, mem_filter] at hprops
  obtain ⟨_, hpp, hqp, hpc, hqc, hband, hpupper, hbandq, hroot⟩ := hprops
  exact Task693.sieve_switching_count (primeSequence N) N (q : ℕ × ℕ).1 (q : ℕ × ℕ).2 hpp hseq
    (pair_cut_eight hN hband hbandq)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Finset Real
open scoped Classical

/-- Exact elementary upper reduction of Upsilon ten in Wu 2004 equation 10.11.
The fixed real sifting level and all exceptional counts are retained. -/
theorem term_nine_switching (N : ℕ) (hN : 2 ≤ N) :
    sieveTerms N 9 ≤ ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
          (N : ℝ) ^ sigma2 ≤ q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      (#{a ∈ primeSequence N | (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2 ∣ a ∧ (a / ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2)).Prime} +
      #{a ∈ primeSequence N | a = (q : ℕ × ℕ).1 * (q : ℕ × ℕ).2} +
      #{a ∈ primeSequence N | (q : ℕ × ℕ).1 ^ 2 * (q : ℕ × ℕ).2 ∣ a} +
      #{a ∈ primeSequence N | ¬ a.Coprime N}) : ℕ) : ℝ) := by
  have hseq : ∀ a ∈ primeSequence N, a ≤ N := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    exact Nat.sub_le _ _
  have hS : sieveTerms N 9 = ((∑ q ∈ Wu08Sum.P2 N (fun p q =>
        (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
          (N : ℝ) ^ sigma2 ≤ q ∧
          (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      Wu41.S (primeSequence N) ((q : ℕ × ℕ).1 * (q : ℕ × ℕ).2) (N * (q : ℕ × ℕ).1) ((N : ℝ) ^ sigma1) : ℕ) : ℝ) := by
    norm_num [sieveTerms]
  rw [hS]
  apply Nat.cast_le.mpr
  apply sum_le_sum
  intro q hq
  have hprops := hq
  simp only [Wu08Sum.P2, mem_filter] at hprops
  obtain ⟨_, hpp, hqp, hpc, hqc, hband, hpupper, hbandq, hroot⟩ := hprops
  exact Task693.sieve_switching_count_at_level (primeSequence N) N (q : ℕ × ℕ).1 (q : ℕ × ℕ).2 hpp hseq
    ((N : ℝ) ^ sigma1) (by positivity) (pair_cut_nine hN hband hbandq)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Finset
open scoped Classical

/-- Exact cofactor reductions for the three ordinary sums of Wu equations 10.3 and 10.4. -/
theorem ordinary_terms_quotients (N : ℕ) (i : Fin 12)
    (hi : i ∈ ({1, 2, 3} : Finset (Fin 12))) :
    sieveTerms N i = ((∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1)
        ((N : ℝ) ^ (if i = 1 then kappa2 else if i = 2 then sigma1 else sigma2)),
      #{m ∈ range (N / p + 1) | (N - p * m).Prime ∧
        Wu41.Sifted N (if i = 1 then (p : ℝ) else (N : ℝ) ^ kappa1) (p * m)} : ℕ) : ℝ) := by
  have hraw : sieveTerms N i = ((∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1)
        ((N : ℝ) ^ (if i = 1 then kappa2 else if i = 2 then sigma1 else sigma2)),
      Wu41.S (primeSequence N) p N (if i = 1 then (p : ℝ) else (N : ℝ) ^ kappa1) : ℕ) : ℝ) := by
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> norm_num [sieveTerms]
  rw [hraw]
  apply congrArg (fun n : ℕ => (n : ℝ))
  apply Finset.sum_congr rfl
  intro p hp
  exact Task693.sieve_primeSequence_eq N p N _ (Wu41.mem_PS.mp hp).1.pos

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Finset
open scoped Classical

/-- Exact cofactor reductions on the two four-prime domains of Wu equation 10.12. -/
theorem quad_terms_quotients (N : ℕ) (i : Fin 12)
    (hi : i ∈ ({10, 11} : Finset (Fin 12))) :
    let Q := if i = 10 then Wu08Sum.P4 N (fun p q r s =>
        (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧ (s : ℝ) < (N : ℝ) ^ kappa2)
      else Wu08Sum.P4 N (fun p q r s =>
        (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ kappa2 ∧
          (N : ℝ) ^ kappa2 ≤ s ∧ (s : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / r)
    sieveTerms N i = ((∑ q ∈ Q,
      #{m ∈ range (N / (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) + 1) |
        (N - (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) * m).Prime ∧
          Wu41.Sifted (N * q.1) q.2.1 ((q.1 * q.2.1 * q.2.2.1 * q.2.2.2) * m)} : ℕ) : ℝ) := by
  dsimp only
  let Q := if i = 10 then Wu08Sum.P4 N (fun p q r s =>
        (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧ (s : ℝ) < (N : ℝ) ^ kappa2)
      else Wu08Sum.P4 N (fun p q r s =>
        (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ kappa2 ∧
          (N : ℝ) ^ kappa2 ≤ s ∧ (s : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / r)
  have hraw : sieveTerms N i = ((∑ q ∈ Q,
      Wu41.S (primeSequence N) (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ) : ℝ) := by
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num [sieveTerms, Q]
  rw [hraw]
  apply congrArg (fun n : ℕ => (n : ℝ))
  apply Finset.sum_congr rfl
  intro q hq
  have hprime : q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime := by
    by_cases he : i = 10
    · have hprops := hq
      simp only [Q, if_pos he, Wu08Sum.P4, mem_filter] at hprops
      exact ⟨hprops.2.1, hprops.2.2.1, hprops.2.2.2.1, hprops.2.2.2.2.1⟩
    · have hprops := hq
      simp only [Q, if_neg he, Wu08Sum.P4, mem_filter] at hprops
      exact ⟨hprops.2.1, hprops.2.2.1, hprops.2.2.2.1, hprops.2.2.2.2.1⟩
  exact Task693.sieve_primeSequence_eq N _ (N * q.1) q.2.1
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hprime.1.pos hprime.2.1.pos)
      hprime.2.2.1.pos) hprime.2.2.2.pos)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

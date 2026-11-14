import LeanLab.ChenDoubleSieve.Decomp347b
import LeanLab.ChenDoubleSieve.Burst8P2

/-!
The finite S3 raising step with its explicit forced prime correction.
Source: https://arxiv.org/pdf/0705.1652, page 36 S3 expansion.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- Raising a pair level is bounded by the count exempting both forced primes
and its Buchstab descendants. Source: page 36 S3 expansion. -/
theorem forced_pair_raise_le (A : Finset ℕ) (N p q : ℕ) (hq : q.Prime) (y : ℝ) :
    S A (p * q) (N * p) q ≤ S A (p * q) (N * p * q) y +
      ∑ r ∈ PS (N * p * q) q y, S A (p * q * r) (N * p * q) r := by
  by_cases hqy : (q : ℝ) ≤ y
  · exact (forced_pair_buchstab A N p q hq hqy).le
  · have hyq : y ≤ (q : ℝ) := (lt_of_not_ge hqy).le
    calc
      _ ≤ S A (p * q) (N * p) y := Burst8P2.S_anti hyq
      _ = S A (p * q) (N * p * q) y :=
        (sieve_modulus_prime A (p * q) (N * p) q hq y hyq).symm
      _ ≤ _ := Nat.le_add_right _ _

/-- All descendants of the S3 raising step lie in the third Delta one domain.
Source: page 36 S3 expansion and page 37 definition of Delta one. -/
theorem raising_triple_sum_le (N : ℕ) (hN : 1 ≤ N) :
    ((∑ q ∈ crossingPairs N,
      ∑ r ∈ PS (N * q.1 * q.2) q.2 ((N : ℝ) ^ sigma1),
        S (primeSequence N) (q.1 * q.2 * r) (N * q.1 * q.2) r) : ℝ) ≤
      tripleTerms N 2 := by
  let T := (crossingPairs N).sigma (fun q => PS (N * q.1 * q.2) q.2 ((N : ℝ) ^ sigma1))
  let e : (Σ _ : ℕ × ℕ, ℕ) → ℕ × ℕ × ℕ := fun t => (t.1.1, t.1.2, t.2)
  let g : ℕ × ℕ × ℕ → ℕ := fun t =>
    S (primeSequence N) (t.1 * t.2.1 * t.2.2) (N * t.1 * t.2.1) t.2.2
  have hyN : (N : ℝ) ^ sigma1 ≤ N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show sigma1 ≤ 1 by norm_num [sigma1])
  have hinj : Set.InjOn e T := by
    rintro ⟨⟨p, q⟩, r⟩ _ ⟨⟨p', q'⟩, r'⟩ _ he
    simp only [e, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rfl
  have hsub : T.image e ⊆ primeTriples N (fun p q r =>
      (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
      (N : ℝ) ^ sigma2 ≤ q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ sigma1) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
    obtain ⟨hpq, hr⟩ := mem_sigma.mp hu
    simp only [crossingPairs, Wu08Sum.P2, mem_filter, mem_product] at hpq
    obtain ⟨hNP, hp, hq, hpc, hqc, hKp, hpT, hTq, _⟩ := hpq
    obtain ⟨hrp, hqr, hry, hrc⟩ := Wu41.mem_PS.mp hr
    have hrnot : ¬ u.2 ∣ N * u.1.1 * u.1.2 := (hrp.coprime_iff_not_dvd).mp hrc
    have hrne : u.2 ≠ u.1.2 := by
      intro heq
      apply hrnot
      rw [heq]
      exact dvd_mul_left _ _
    have hqrN : u.1.2 < u.2 := by
      have hle : u.1.2 ≤ u.2 := by exact_mod_cast hqr
      omega
    have hrN : u.2 < N := by exact_mod_cast hry.trans_le hyN
    have hrcN : u.2.Coprime N := by
      apply (hrp.coprime_iff_not_dvd).mpr
      intro hd
      exact hrnot (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd u.1.1) u.1.2)
    simp only [e, primeTriples, mem_filter, mem_product]
    exact ⟨⟨hNP.1, hNP.2, mem_range.mpr hrN⟩, hp, hq, hrp,
      hpc, hqc, hrcN, hKp, hpT, hTq, hqrN, hry⟩
  have hs := Finset.sum_le_sum_of_injOn e hinj hsub
    (fun u (_ : u ∈ T) => (le_rfl : g (e u) ≤ g (e u)))
    (fun t _ _ => Nat.zero_le (g t))
  simp only [T, Finset.sum_sigma, e, g] at hs
  change _ ≤ ((∑ t ∈ primeTriples N (fun p q r =>
    (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
    (N : ℝ) ^ sigma2 ≤ q ∧ q < r ∧ (r : ℝ) < (N : ℝ) ^ sigma1),
      S (primeSequence N) (t.1 * t.2.1 * t.2.2) (N * t.1 * t.2.1) t.2.2 : ℕ) : ℝ)
  exact_mod_cast hs

/-- The S3 raising bound with the exact corrected Upsilon 10 and Delta one term.
Source: page 36 S3 expansion. Positive discarded terms are not needed for this bound. -/
theorem S3_raising_le (N : ℕ) (hN : 1 ≤ N) :
    (Wu08.S₃ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ) ≤
      exemptUpsilon10 N + tripleTerms N 2 := by
  have hdom : Wu08.pairs N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) ((N : ℝ) ^ sigma2) =
      crossingPairs N := pairs_eq_cross N _ _
  have hp : ∀ q ∈ crossingPairs N,
      S (primeSequence N) (q.1 * q.2) (N * q.1) q.2 ≤
        S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1) +
        ∑ r ∈ PS (N * q.1 * q.2) q.2 ((N : ℝ) ^ sigma1),
          S (primeSequence N) (q.1 * q.2 * r) (N * q.1 * q.2) r := by
    intro q hq
    simp only [crossingPairs, Wu08Sum.P2, mem_filter, mem_product] at hq
    have hprime : q.2.Prime := hq.2.2.1
    exact forced_pair_raise_le _ _ _ _ hprime _
  have hsum := sum_le_sum hp
  rw [sum_add_distrib] at hsum
  have hsumR : ((∑ q ∈ crossingPairs N,
      S (primeSequence N) (q.1 * q.2) (N * q.1) q.2) : ℝ) ≤
      exemptUpsilon10 N + ((∑ q ∈ crossingPairs N,
        ∑ r ∈ PS (N * q.1 * q.2) q.2 ((N : ℝ) ^ sigma1),
          S (primeSequence N) (q.1 * q.2 * r) (N * q.1 * q.2) r) : ℝ) := by
    dsimp only [exemptUpsilon10]
    exact_mod_cast hsum
  unfold Wu08.S₃
  rw [hdom]
  simpa only [Nat.cast_sum] using
    hsumR.trans (add_le_add le_rfl (raising_triple_sum_le N hN))

/-- The sealed Upsilon 10 version retains the explicit nonnegative crossing defect.
Source: page 36 S3 expansion, derived correction required by the sealed modulus. -/
theorem S3_raising_with_defect (N : ℕ) (hN : 1 ≤ N) :
    (Wu08.S₃ (primeSequence N) N ((N : ℝ) ^ kappa2) ((N : ℝ) ^ sigma2) : ℝ) ≤
      sieveTerms N 9 + tripleTerms N 2 + crossingDefect N := by
  have h := S3_raising_le N hN
  rw [exemptUpsilon10_eq] at h
  linarith only [h]

end LeanLab.ChenDoubleSieve.Task347

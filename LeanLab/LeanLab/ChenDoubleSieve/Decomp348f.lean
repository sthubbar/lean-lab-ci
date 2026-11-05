import LeanLab.ChenDoubleSieve.Decomp348e

/-!
Totient weighted coprimality removal for the finite prime sums in equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39, display after equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348

/-- The reciprocal totient of two distinct primes is at most four over their product. -/
theorem reciprocal_totient_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    1 / (Nat.totient (p * q) : ℝ) ≤ 4 / ((p : ℝ) * q) := by
  have hφ : (Nat.totient (p * q) : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq),
      Nat.totient_prime hp, Nat.totient_prime hq]
    simp only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  rw [hφ, div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by positivity)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ (p : ℝ) - 2) (by linarith : 0 ≤ (q : ℝ) - 2)]

/-- Removing coprimality changes a bounded totient weighted pair sum by a small mass. -/
theorem weighted_coprimality_error (N : ℕ) (P Q : Finset ℕ) (R : Finset (ℕ × ℕ))
    (g : ℕ × ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) (hsub : R ⊆ P ×ˢ Q)
    (hR : ∀ q ∈ R, q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2)
    (hg : ∀ q ∈ R, |g q| ≤ M) :
    |(∑ q ∈ R, g q / (Nat.totient (q.1 * q.2) : ℝ)) -
      ∑ q ∈ R.filter (fun q => q.1.Coprime N ∧ q.2.Coprime N),
        g q / (Nat.totient (q.1 * q.2) : ℝ)| ≤
      4 * M * pairMass (badPairs N P Q) := by
  let W := fun q : ℕ × ℕ => g q / (Nat.totient (q.1 * q.2) : ℝ)
  let C := fun q : ℕ × ℕ => q.1.Coprime N ∧ q.2.Coprime N
  have hs := Finset.sum_filter_add_sum_filter_not (s := R) (p := C) (f := W)
  have hd : (∑ q ∈ R, W q) - ∑ q ∈ R.filter C, W q =
      ∑ q ∈ R.filter (fun q => ¬ C q), W q := by linarith
  change |(∑ q ∈ R, W q) - ∑ q ∈ R.filter C, W q| ≤ _
  rw [hd]
  have hbad : R.filter (fun q => ¬ C q) ⊆ badPairs N P Q := by
    intro q hq
    obtain ⟨hqR, hqC⟩ := mem_filter.mp hq
    apply mem_filter.mpr
    refine ⟨hsub hqR, ?_⟩
    simpa only [C, not_and_or] using hqC
  calc
    _ ≤ ∑ q ∈ R.filter (fun q => ¬ C q), |W q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ R.filter (fun q => ¬ C q), 4 * M * (1 / ((q.1 : ℝ) * q.2)) := by
      apply sum_le_sum
      intro q hq
      have hqR := (mem_filter.mp hq).1
      obtain ⟨hp, hq', hpq⟩ := hR q hqR
      have hrec := reciprocal_totient_pair hp hq' hpq
      calc
        |W q| = |g q| * (1 / (Nat.totient (q.1 * q.2) : ℝ)) := by
          simp [W, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient (q.1 * q.2) : ℝ) from Nat.cast_nonneg _), div_eq_mul_inv]
        _ ≤ M * (4 / ((q.1 : ℝ) * q.2)) :=
          mul_le_mul (hg q hqR) hrec (by positivity) hM
        _ = _ := by ring
    _ = 4 * M * pairMass (R.filter (fun q => ¬ C q)) := by
      simp only [pairMass, Finset.mul_sum]
    _ ≤ 4 * M * pairMass (badPairs N P Q) :=
      mul_le_mul_of_nonneg_left (pairMass_mono hbad) (by positivity)

/-- The totient weighted coprimality error vanishes uniformly for bounded weights. -/
theorem weighted_coprimality_error_small {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ P Q : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ κ ≤ p ∧ p ≤ N) →
      (∀ q ∈ Q, q.Prime ∧ (N : ℝ) ^ κ ≤ q ∧ q ≤ N) →
      ∀ R : Finset (ℕ × ℕ), R ⊆ P ×ˢ Q →
      (∀ q ∈ R, q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2) →
      ∀ g : ℕ × ℕ → ℝ, (∀ q ∈ R, |g q| ≤ M) →
      |(∑ q ∈ R, g q / (Nat.totient (q.1 * q.2) : ℝ)) -
        ∑ q ∈ R.filter (fun q => q.1.Coprime N ∧ q.2.Coprime N),
          g q / (Nat.totient (q.1 * q.2) : ℝ)| ≤ ε := by
  have hden : 0 < 4 * M + 1 := by positivity
  obtain ⟨N0, hN0⟩ := badPairs_mass_small hκ (ε / (4 * M + 1)) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN P Q hP hQ R hRsub hR g hg
  calc
    _ ≤ 4 * M * pairMass (badPairs N P Q) :=
      weighted_coprimality_error N P Q R g hM hRsub hR hg
    _ ≤ 4 * M * (ε / (4 * M + 1)) :=
      mul_le_mul_of_nonneg_left (hN0 N hN P Q hP hQ) (by positivity)
    _ ≤ (4 * M + 1) * (ε / (4 * M + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε := mul_div_cancel₀ ε hden.ne'

end LeanLab.ChenDoubleSieve.Task348

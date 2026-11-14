import LeanLab.ChenDoubleSieve.Decomp315a

/-!
Supply for the first half of Wu 2004 equation 9.7.
Source: https://arxiv.org/pdf/0705.1652, pages 35 to 37.
The unresolved transport retains the sealed Upsilon 10 modulus.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S)

/-- The Chen weight at kappa two and sigma two before the Buchstab transport.
Source: page 35 equation 9.5, retaining its nonnegative triple term. -/
def baseline (N : ℕ) : ℝ :=
  let K := (N : ℝ) ^ kappa2
  let T := (N : ℝ) ^ sigma2
  2 * (S (primeSequence N) 1 N K : ℝ) -
    (Wu08.S₁ (primeSequence N) N K T : ℝ) -
    2 * (Wu08.S₂ (primeSequence N) N T : ℝ) -
    (Wu08.S₃ (primeSequence N) N K T : ℝ) +
    (Wu08.S₄ (primeSequence N) N K T : ℝ)

/-- The explicit square factor remainder at kappa two fits the same power bound.
Source: page 35 equation 9.5 and page 34 square factor error. -/
theorem remainder_kappa2 (N : ℕ) (hN : 4096 ≤ N) :
    2 * ((N : ℝ) / ((N : ℝ) ^ kappa2 - 1) + Real.sqrt N + 1) ≤
      8 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsmall : 1 < (N : ℝ) ^ kappa1 :=
    Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < N)) (by norm_num [kappa1])
  have hmono : (N : ℝ) ^ kappa1 ≤ (N : ℝ) ^ kappa2 :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, kappa2])
  have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg N)
    (by linarith : 0 < (N : ℝ) ^ kappa1 - 1) (sub_le_sub_right hmono 1)
  have hrem := lemma21_remainder_power N hN
  linarith

/-- Equation 9.5 for the full prime sequence with an explicit power error.
Source: page 35 equation 9.5, using the existing clean Lemma 9.1 supply. -/
theorem baseline_bound : ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
    baseline N ≤ 2 * (D12 N : ℝ) + 11 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨M, hM⟩ := primeFactors_card_absorbed
  obtain ⟨L, hL⟩ := log_ceiling_power_absorbed
  refine ⟨max 4096 (max M L), ?_⟩
  intro N hEven hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  let K := (N : ℝ) ^ kappa2
  let T := (N : ℝ) ^ sigma2
  have hK : 1 < K := Real.one_lt_rpow hNgt (by norm_num [kappa2])
  have hKT : K ≤ T :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa2, sigma2])
  have hChen := Wu08.lemma21_chen N hK hKT
  have hbase : (S (primeSequence N) 1 N K : ℝ) ≤
      (S (Wu08.Achen N) 1 N K : ℝ) + N.primeFactors.card := by
    exact_mod_cast primeSequence_sieve_transfer N 1 N K
  have h1 : (Wu08.S₁ (Wu08.Achen N) N K T : ℝ) ≤
      (Wu08.S₁ (primeSequence N) N K T : ℝ) := by
    exact_mod_cast (sum_le_sum (fun p (_ : p ∈ Wu41.PS N K T) => Achen_sieve_le N p N K))
  have h2 : (Wu08.S₂ (Wu08.Achen N) N T : ℝ) ≤
      (Wu08.S₂ (primeSequence N) N T : ℝ) := by
    exact_mod_cast (sum_le_sum (fun (q : ℕ × ℕ) (_ : q ∈ Wu08.pairs N T (N : ℝ) T) =>
      Achen_sieve_le N (q.1 * q.2) (N * q.1) q.2))
  have h3 : (Wu08.S₃ (Wu08.Achen N) N K T : ℝ) ≤
      (Wu08.S₃ (primeSequence N) N K T : ℝ) := by
    exact_mod_cast (sum_le_sum (fun (q : ℕ × ℕ) (_ : q ∈ Wu08.pairs N K T T) =>
      Achen_sieve_le N (q.1 * q.2) (N * q.1) q.2))
  have hTN : T ≤ (N : ℝ) := by
    dsimp only [T]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show sigma2 ≤ 1 by norm_num [sigma2])
  have htransfer := primeSequence_triple_transfer N hEven (by omega)
    (fun p q r => K ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < T)
    (fun q => N * q.1) (fun q => (q.2.1 : ℝ))
  rw [triple_sum_eq_S4 (primeSequence N) N K T hTN,
    triple_sum_eq_S4 (Wu08.Achen N) N K T hTN] at htransfer
  have h4 : (Wu08.S₄ (primeSequence N) N K T : ℝ) ≤
      (Wu08.S₄ (Wu08.Achen N) N K T : ℝ) +
        (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 4 := by
    exact_mod_cast htransfer
  have hlog := hL N (by omega)
  have hcard := hM N (by omega)
  have herr := remainder_kappa2 N (by omega)
  change 2 * (S (primeSequence N) 1 N K : ℝ) -
    (Wu08.S₁ (primeSequence N) N K T : ℝ) -
    2 * (Wu08.S₂ (primeSequence N) N T : ℝ) -
    (Wu08.S₃ (primeSequence N) N K T : ℝ) +
    (Wu08.S₄ (primeSequence N) N K T : ℝ) ≤ _
  nlinarith only [hChen, hbase, h1, h2, h3, h4, hcard, herr, hlog]


end LeanLab.ChenDoubleSieve.Task347

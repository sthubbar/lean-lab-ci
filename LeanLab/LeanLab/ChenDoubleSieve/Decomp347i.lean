import LeanLab.ChenDoubleSieve.Decomp347b

/-!
An elementary counting bound for the retained Upsilon 10 correction.
Source: https://arxiv.org/pdf/0705.1652, page 36 S3 expansion.
The bound itself does not fit the power error required by first_half.
This does not prove that the actual correction has no power bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S)

/-- A pair of prime divisors of a positive integer lies in its prime factor square.
Source: page 36 pair counts, derived elementary counting bound. -/
theorem pair_divisor_card (N a : ℕ) (ha : 0 < a) (C : ℕ → ℕ → Prop) :
    #{q ∈ Wu08Sum.P2 N C | q.1 * q.2 ∣ a} ≤ a.primeFactors.card ^ 2 := by
  have hsub : {q ∈ Wu08Sum.P2 N C | q.1 * q.2 ∣ a} ⊆
      a.primeFactors ×ˢ a.primeFactors := by
    intro q hq
    obtain ⟨hq, hd⟩ := mem_filter.mp hq
    simp only [Wu08Sum.P2, mem_filter, mem_product] at hq
    obtain ⟨_, hp, hqprime, _⟩ := hq
    exact mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, (dvd_mul_right _ _).trans hd, ha.ne'⟩,
        Nat.mem_primeFactors.mpr ⟨hqprime, (dvd_mul_left _ _).trans hd, ha.ne'⟩⟩
  calc
    _ ≤ (a.primeFactors ×ˢ a.primeFactors).card := card_le_card hsub
    _ = _ := by simp [pow_two]

/-- A uniform prime factor bound controls every finite pair sieve sum.
Source: page 36 pair counts, derived elementary counting bound. -/
theorem pair_sum_bound (A : Finset ℕ) (N K : ℕ) (C : ℕ → ℕ → Prop)
    (M : ℕ × ℕ → ℕ) (y : ℕ × ℕ → ℝ)
    (hA : ∀ a ∈ A, 0 < a ∧ a.primeFactors.card ≤ K) :
    (∑ q ∈ Wu08Sum.P2 N C, S A (q.1 * q.2) (M q) (y q)) ≤ A.card * K ^ 2 := by
  rw [Wu08Sum.swap1]
  calc
    _ ≤ ∑ a ∈ A, K ^ 2 := by
      apply sum_le_sum
      intro a ha
      have hsub : {q ∈ Wu08Sum.P2 N C | q.1 * q.2 ∣ a ∧ Wu41.Sifted (M q) (y q) a} ⊆
          {q ∈ Wu08Sum.P2 N C | q.1 * q.2 ∣ a} := by
        intro q hq
        obtain ⟨hq, hd, _⟩ := mem_filter.mp hq
        exact mem_filter.mpr ⟨hq, hd⟩
      exact (card_le_card hsub).trans
        ((pair_divisor_card N a (hA a ha).1 C).trans (pow_le_pow_left' (hA a ha).2 2))
    _ = _ := by simp

/-- The elementary correction bound is N times a squared logarithmic ceiling.
Source: page 36 S3 expansion, derived bound that retains its actual strength. -/
theorem crossingDefect_counting_bound (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    crossingDefect N ≤ (N : ℝ) * (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 2 := by
  let K : ℕ := ⌈log (N : ℝ) / log 2⌉₊
  have hK : log (N : ℝ) / log 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hA : ∀ a ∈ primeSequence N, 0 < a ∧ a.primeFactors.card ≤ K := by
    intro a ha
    have hab := primeSequence_bounds hEven hN a ha
    refine ⟨hab.1, ?_⟩
    have halog := primeFactors_card_log hab.1
    have hlog := Real.log_le_log (by exact_mod_cast hab.1 : (0 : ℝ) < a)
      (by exact_mod_cast hab.2.le : (a : ℝ) ≤ N)
    have hle : (a.primeFactors.card : ℝ) ≤ (K : ℝ) := halog.trans
      ((div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans hK)
    exact_mod_cast hle
  have hcard : (primeSequence N).card ≤ N := by
    calc
      _ ≤ (range N).card := card_le_card (by
        intro a ha
        exact mem_range.mpr (primeSequence_bounds hEven hN a ha).2)
      _ = N := card_range N
  have hdrop : (∑ q ∈ crossingPairs N,
      if (q.2 : ℝ) < (N : ℝ) ^ sigma1 then
        S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1)
      else 0) ≤ ∑ q ∈ crossingPairs N,
        S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1) := by
    apply sum_le_sum
    intro q _
    split_ifs <;> omega
  have hpairs := pair_sum_bound (primeSequence N) N K
    (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
      (N : ℝ) ^ sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p))
    (fun q => N * q.1 * q.2) (fun _ => (N : ℝ) ^ sigma1) hA
  have hnat := hdrop.trans (hpairs.trans (Nat.mul_le_mul_right _ hcard))
  dsimp only [crossingDefect]
  exact_mod_cast hnat

/-- The elementary majorant is at least N for N at least two.
Source: page 36 correction estimate, derived comparison of its strength. -/
theorem counting_majorant_ge (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ≤ (N : ℝ) * (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 2 := by
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : log (2 : ℝ) ≤ log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hquot : 1 ≤ log (N : ℝ) / log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlog)
  have hceil : (1 : ℝ) ≤ (⌈log (N : ℝ) / log 2⌉₊ : ℝ) := hquot.trans (Nat.le_ceil _)
  have hsquare : (1 : ℝ) ≤ (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((⌈log (N : ℝ) / log 2⌉₊ : ℝ) - 1)]
  simpa using mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

/-- This counting majorant cannot be absorbed by any fixed eleven twelfths power error.
Source: page 37 equation 9.7, derived negative result about the elementary bound.
It asserts nothing about the growth rate of crossingDefect itself. -/
theorem counting_majorant_not_power_error : ¬ ∃ C : ℝ, ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (N : ℝ) * (⌈log (N : ℝ) / log 2⌉₊ : ℝ) ^ 2 ≤ C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  rintro ⟨C, N0, hC⟩
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 12 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_atTop.1 hlim) (C + 1))
  let N := 2 * max 4 (max N0 M)
  have hN4 : 4 ≤ N := by dsimp [N]; omega
  have hN0 : N0 ≤ N := by dsimp [N]; omega
  have hNM : M ≤ N := by dsimp [N]; omega
  have hEven : Even N := even_two_mul _
  have hmajor := counting_majorant_ge N (by omega)
  have hbound := hC N hEven hN0
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < (N : ℝ) ^ (11 / 12 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hscaled := mul_le_mul_of_nonneg_right (hM N hNM) hp.le
  have hid : (N : ℝ) ^ (1 / 12 : ℝ) * (N : ℝ) ^ (11 / 12 : ℝ) = N := by
    rw [← Real.rpow_add hNp]
    norm_num
  rw [hid] at hscaled
  nlinarith only [hmajor, hbound, hscaled, hp]

end LeanLab.ChenDoubleSieve.Task347

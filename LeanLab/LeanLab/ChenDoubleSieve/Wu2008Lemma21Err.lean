import LeanLab.ChenDoubleSieve.Wu2008Lemma21
import LeanLab.ChenDoubleSieve.Lemma41Err

/-!
# Wu 2008 Lemma 2.1, the error term `E` is `O(N^{1-κ})`

P0043 J. Wu 2008, Lemma 2.1. Unit U-5409, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

`Esq_le`: for `A` inside `[0, N)` and `K > 1`, `E ≤ N/(K - 1) + √N + 1`, because an `a` in `E`
is divisible by `q²` for its least prime factor `q ≥ K`, with `q² ≤ a < N`, and
`Σ_{n ≥ m} 1/n² ≤ 1/(m - 1)`. With `K = N^κ` this is Wu's `O(N^{1-κ})`, so
`lemma21_explicit` is Lemma 2.1 with every term explicit. Binary Goldbach is OPEN.
-/

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu08

open Wu41 (Sifted S card_dvd_le)

/-- `Σ_{m ≤ n < M} 1/n² ≤ 1/(m-1) - 1/(M-1)` for `2 ≤ m ≤ M`. -/
lemma sum_inv_sq_Ico {m : ℕ} (hm : 2 ≤ m) : ∀ M, m ≤ M →
    ∑ n ∈ Ico m M, (1 / (n : ℝ) ^ 2) ≤ 1 / ((m : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hMm ih =>
    rw [sum_Ico_succ_top hMm]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast le_trans hm hMm
    have key : 1 / (M : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / (((M + 1 : ℕ) : ℝ) - 1) := by
      push_cast
      rw [add_sub_cancel_right, div_sub_div _ _ (by linarith) (by linarith),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith

lemma sum_inv_sq_le {m : ℕ} (hm : 2 ≤ m) (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∑ n ∈ s, (1 / (n : ℝ) ^ 2) ≤ 1 / ((m : ℝ) - 1) := by
  set M := max m (s.sup id + 1)
  have hsub : s ⊆ Ico m M := by
    intro n hn
    refine mem_Ico.2 ⟨hs n hn, lt_of_lt_of_le ?_ (le_max_right _ _)⟩
    have := le_sup (f := id) hn
    simp only [id] at this; omega
  have hM : m ≤ M := le_max_left _ _
  have h1 := sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => div_nonneg zero_le_one (sq_nonneg (n : ℝ)))
  have h2 := sum_inv_sq_Ico hm M hM
  have hM1 : (0 : ℝ) ≤ 1 / ((M : ℝ) - 1) := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast le_trans hm hM
    apply div_nonneg zero_le_one; linarith
  linarith

/-- **The error of Lemma 2.1**: `E ≤ N/(K - 1) + √N + 1` for `A` of integers `0 < a < N`
coprime to `N` and `K > 1`. -/
theorem Esq_le (A : Finset ℕ) (N : ℕ) {K : ℝ} (hK : 1 < K)
    (hA : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (Esq A N K : ℝ) ≤ N / (K - 1) + Real.sqrt N + 1 := by
  set m := ⌈K⌉₊ with hm
  have hm2 : 2 ≤ m := by
    have : (1 : ℝ) < m := lt_of_lt_of_le hK (Nat.le_ceil K)
    exact_mod_cast this
  have hKm : K ≤ m := Nat.le_ceil K
  set Q := ({q ∈ Ico m (Nat.sqrt N + 1) | q.Prime} : Finset ℕ) with hQ
  have hsub : ({a ∈ A | Sifted N K a ∧ a.minFac ^ 2 ∣ a} : Finset ℕ) ⊆
      insert 1 (Q.biUnion fun q => {a ∈ A | q ^ 2 ∣ a}) := by
    intro a ha
    obtain ⟨haA, hs, hsq⟩ := mem_filter.1 ha
    obtain ⟨ha0, haN, hcop⟩ := hA a haA
    by_cases ha1 : a = 1
    · rw [ha1]; exact mem_insert_self _ _
    apply mem_insert_of_mem
    rw [mem_biUnion]
    refine ⟨a.minFac, ?_, mem_filter.2 ⟨haA, hsq⟩⟩
    have hp := Nat.minFac_prime ha1
    have hKq : K ≤ a.minFac := by
      by_contra h
      push Not at h
      exact hs _ hp h (prime_dvd_not_dvd_N hcop hp (Nat.minFac_dvd a)) (Nat.minFac_dvd a)
    have hmq : m ≤ a.minFac := Nat.ceil_le.2 hKq
    have hsqN : a.minFac ^ 2 < N := lt_of_le_of_lt (Nat.le_of_dvd ha0 hsq) haN
    exact mem_filter.2 ⟨mem_Ico.2 ⟨hmq, Nat.lt_succ_of_le (Nat.le_sqrt'.2 hsqN.le)⟩, hp⟩
  have hA' : A ⊆ range (N + 1) := fun a ha => mem_range.2 (by have := (hA a ha).2.1; omega)
  have hE : Esq A N K ≤ 1 + ∑ q ∈ Q, #{a ∈ A | q ^ 2 ∣ a} := by
    unfold Esq
    have h1 := card_le_card hsub
    have h2 := card_insert_le 1 (Q.biUnion fun q => {a ∈ A | q ^ 2 ∣ a})
    have h3 := card_biUnion_le (s := Q) (t := fun q => {a ∈ A | q ^ 2 ∣ a})
    omega
  have hE' : (Esq A N K : ℝ) ≤ 1 + ∑ q ∈ Q, (#{a ∈ A | q ^ 2 ∣ a} : ℝ) := by
    exact_mod_cast hE
  have h4 : ∑ q ∈ Q, (#{a ∈ A | q ^ 2 ∣ a} : ℝ) ≤ ∑ q ∈ Q, ((N : ℝ) / ((q ^ 2 : ℕ) : ℝ) + 1) :=
    sum_le_sum fun q hq => card_dvd_le hA'
      (Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 (mem_filter.1 hq).2.ne_zero))
  have h5 : ∑ q ∈ Q, ((N : ℝ) / ((q ^ 2 : ℕ) : ℝ) + 1) =
      N * ∑ q ∈ Q, (1 / (q : ℝ) ^ 2) + #Q := by
    rw [sum_add_distrib, mul_sum, sum_const, nsmul_one]
    congr 1
    refine sum_congr rfl fun q _ => ?_
    push_cast; ring
  have h6 := sum_inv_sq_le hm2 Q (fun n hn => (mem_Ico.1 (mem_filter.1 hn).1).1)
  have h7 : 1 / ((m : ℝ) - 1) ≤ 1 / (K - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h8 : (#Q : ℝ) ≤ Real.sqrt N := by
    have hc : #Q ≤ Nat.sqrt N := by
      have hQs : Q ⊆ Ico m (Nat.sqrt N + 1) := filter_subset _ _
      have := card_le_card hQs
      rw [Nat.card_Ico] at this; omega
    calc (#Q : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hc
      _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h9 : (N : ℝ) * ∑ q ∈ Q, (1 / (q : ℝ) ^ 2) ≤ N / (K - 1) := by
    calc (N : ℝ) * ∑ q ∈ Q, (1 / (q : ℝ) ^ 2) ≤ N * (1 / (K - 1)) :=
          mul_le_mul_of_nonneg_left (h6.trans h7) hN0
      _ = N / (K - 1) := by ring
  linarith

/-- **Wu 2008 Lemma 2.1 with every term explicit**:
`2 S(A; P(N), K) + S₄ ≤ 2 D₁₂ + S₁ + 2 S₂ + S₃ + 2 (N/(K - 1) + √N + 1)`. -/
theorem lemma21_explicit (A : Finset ℕ) (N : ℕ) {K Sg : ℝ} (hK1 : 1 < K) (hK : K ≤ Sg)
    (hA : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (2 * S A 1 N K + S₄ A N K Sg : ℝ) ≤
      2 * D12 A + S₁ A N K Sg + 2 * S₂ A N Sg + S₃ A N K Sg
        + 2 * (N / (K - 1) + Real.sqrt N + 1) := by
  have h := lemma21_nat A N hK hA
  have h' : ((2 * S A 1 N K + S₄ A N K Sg : ℕ) : ℝ) ≤
      ((2 * D12 A + S₁ A N K Sg + 2 * S₂ A N Sg + S₃ A N K Sg + 2 * Esq A N K : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have := Esq_le A N hK1 hA
  linarith

end LeanLab.ChenDoubleSieve.Wu08

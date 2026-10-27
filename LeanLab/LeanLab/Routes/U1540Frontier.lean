/-
Unit U-1540, run 20261026T0403Z-9802, track T2 FRONTIER, idea I-0127, closing the gate of I-0103.
AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

Languasco and Zaccagnini 2009, P0079, arXiv 0811.3663 v2, Lemma 4 on p. 6 to 7: the constant
`C = 10.0219168340` of their display (4) is `2 B (1 + A(1))` with `B = 3.9171` from Chen 1978 in
their Lemma 3 on p. 6, the uniform bound `Z(X; 2n) < B S(n) X` for prime pairs at every even
distance, and `A(1) < 0.2792521041` from Khalfalah and Pintz, display (22). The bound enters
displays (27) and (28) linearly in `B`.

Johnston and Trudgian, arXiv 2605.17825 v2, Proposition 2 on p. 6, state from Lichtman
arXiv 2309.08522, Theorem 1.7 with its uniformity in the residue, that the number of prime
pairs `p1 - p2 = h`, `p1, p2 ≤ N`, is at most `(C1 + ε) C0 N / log² N · ∏_{p | h, p > 2} (p-1)/(p-2)`
uniformly for `h < N`, with `C1 = 6.7814`. In LZ's normalisation `S(n) = 2 c0 S'(n)` this is
`B = C1 / 2 + ε = 3.3907 + ε`, so `C` drops to `2 · 3.3908 · (1 + A(1)) < 8.6754`.

What is PROVED here, axioms propext Classical.choice Quot.sound only:
* the arithmetic of the new constant and the monotonicity of `s0` and of the Theorem in `C`;
* `lemma3_of_JT`: Johnston-Trudgian Proposition 2 with constant `C1` gives LZ Lemma 3 with
  every `B > C1 / 2`, including the log weights and the real parameter `X`;
* the assembly `lz_lichtman`: CONDITIONAL ON `JTProp2 c0 6.7814` and on `LZMethod`, the reading
  of LZ's own proof as a function of the Lemma 3 constant, LZ's Theorem holds with `C < 8.6754`;
* the worked value: at `λ1 = π`, `λ2 = -√2`, `q1 = q2 = 1`, `η = 1`, formula (2) gives at least
  52 with LZ's `C` and at most 51 with the new `C`.
The gain is small: at most 2 powers of two in the transcendental case and 1 in the algebraic
case, see Routes/numerics/U1540. Nothing here is progress on binary Goldbach.
-/
import Mathlib
import LeanLab.LZPowersOfTwo.Statements
import LeanLab.BrunGap.Uniform

open Real Finset

noncomputable section
namespace LeanLab.Routes.U1540

open LeanLab.LZPowersOfTwo

/-! ## 1. LZ's constant as a function of the Lemma 3 constant `B` -/

/-- Khalfalah-Pintz bound for `A(1)`, LZ display (22) on p. 5. -/
def A1 : ℝ := 0.2792521041

/-- LZ Lemma 4 constant `C = 2 B (1 + A(1))`, p. 6. -/
def lzC (B : ℝ) : ℝ := 2 * B * (1 + A1)

/-- LZ display (4) with the constant `C` as a parameter. -/
def CqC (C : ℝ) (q1 q2 : ℕ) : ℝ :=
  √(log 2 + C * Sprime q1) * √(log 2 + C * Sprime q2)

/-- LZ displays (2) and (3) with the constant `C` as a parameter. -/
def s0C (C ν l1 l2 : ℝ) (q1 q2 : ℕ) (η : ℝ) : ℤ :=
  2 + ⌈(log (2 * CqC C q1 q2 * |l1 * l2|) - log η) / (-log ν)⌉

/-- LZ's Theorem, exactly as `LZPowersOfTwo.MainStatement`, with the constant `C` of
display (4) as a parameter. -/
def MainStatementC (C ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ (l1 l2 : ℝ) (μ : ℕ → ℝ), 1 < l1 → l2 < -1 → 1 ≤ |l1 / l2| → Irrational (l1 / l2) →
    kind (l1 / l2) → (∀ i, μ i ≠ 0) →
    ∀ r1 r2 : ℚ, (r1 : ℝ) = l1 / μ 0 → (r2 : ℝ) = l2 / μ 1 →
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < l1 / r1.num → η < |l2 / r2.num| →
      ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → s0C C ν l1 l2 r1.den r2.den η ≤ s →
        (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite

theorem CqC_bigC : CqC bigC = Cq := rfl

theorem s0C_bigC : s0C bigC = s0 := rfl

/-- The parametrised Theorem at LZ's own `C` is the sealed `MainStatement`. -/
theorem mainC_bigC_iff (ν : ℝ) (kind : ℝ → Prop) :
    MainStatementC bigC ν kind ↔ MainStatement ν kind := Iff.rfl

theorem one_le_Sprime (n : ℕ) : 1 ≤ Sprime n := by
  unfold Sprime
  calc (1 : ℝ) = ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun p hp => by
        have h2 : (2 : ℝ) < p := by
          have := (Finset.mem_filter.1 hp).2
          exact_mod_cast this
        rw [one_le_div (by linarith)]
        linarith)

theorem CqC_pos {C : ℝ} (h0 : 0 ≤ C) (q1 q2 : ℕ) : 0 < CqC C q1 q2 := by
  unfold CqC
  have l2 : 0 < log 2 := log_pos (by norm_num)
  have s1 := one_le_Sprime q1
  have s2 := one_le_Sprime q2
  have a1 : 0 < log 2 + C * Sprime q1 := by nlinarith
  have a2 : 0 < log 2 + C * Sprime q2 := by nlinarith
  exact mul_pos (Real.sqrt_pos.2 a1) (Real.sqrt_pos.2 a2)

theorem CqC_mono {C C' : ℝ} (h : C ≤ C') (q1 q2 : ℕ) : CqC C q1 q2 ≤ CqC C' q1 q2 := by
  unfold CqC
  have s1 := one_le_Sprime q1
  have s2 := one_le_Sprime q2
  have a1 : log 2 + C * Sprime q1 ≤ log 2 + C' * Sprime q1 := by nlinarith
  have a2 : log 2 + C * Sprime q2 ≤ log 2 + C' * Sprime q2 := by nlinarith
  exact mul_le_mul (Real.sqrt_le_sqrt a1) (Real.sqrt_le_sqrt a2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

theorem CqC_one_one {C : ℝ} (h0 : 0 ≤ C) : CqC C 1 1 = log 2 + C := by
  have h : 0 ≤ log 2 + C := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); linarith
  rw [CqC, Sprime_one, mul_one, Real.mul_self_sqrt h]

/-- `s0` does not grow when `C` shrinks. -/
theorem s0C_mono {C C' ν l1 l2 η : ℝ} {q1 q2 : ℕ} (h0 : 0 ≤ C) (h : C ≤ C') (hν0 : 0 < ν)
    (hν1 : ν < 1) (hl : l1 * l2 ≠ 0) :
    s0C C ν l1 l2 q1 q2 η ≤ s0C C' ν l1 l2 q1 q2 η := by
  unfold s0C
  have hd : 0 < -log ν := by have := Real.log_neg hν0 hν1; linarith
  have hc := CqC_pos h0 q1 q2
  have ha : 0 < |l1 * l2| := abs_pos.2 hl
  have hp : 0 < 2 * CqC C q1 q2 * |l1 * l2| := by positivity
  have hle : 2 * CqC C q1 q2 * |l1 * l2| ≤ 2 * CqC C' q1 q2 * |l1 * l2| := by
    have := CqC_mono h q1 q2
    have : 2 * CqC C q1 q2 ≤ 2 * CqC C' q1 q2 := by linarith
    exact mul_le_mul_of_nonneg_right this ha.le
  have hlog := Real.log_le_log hp hle
  have hq : (log (2 * CqC C q1 q2 * |l1 * l2|) - log η) / (-log ν) ≤
      (log (2 * CqC C' q1 q2 * |l1 * l2|) - log η) / (-log ν) := by
    apply div_le_div_of_nonneg_right _ hd.le
    linarith
  have := Int.ceil_mono hq
  linarith

/-- A smaller admissible `C` gives a stronger Theorem; conversely the Theorem at `C` implies
it at every larger `C'`. -/
theorem mainC_mono {C C' ν : ℝ} {kind : ℝ → Prop} (h0 : 0 ≤ C) (h : C ≤ C') (hν0 : 0 < ν)
    (hν1 : ν < 1) (hM : MainStatementC C ν kind) : MainStatementC C' ν kind := by
  intro l1 l2 μ h1 h2 h3 h4 h5 h6 r1 r2 hr1 hr2
  obtain ⟨η0, hη0, hη⟩ := hM l1 l2 μ h1 h2 h3 h4 h5 h6 r1 r2 hr1 hr2
  refine ⟨η0, hη0, fun η he he0 he1 he2 γ s hs hs0 => hη η he he0 he1 he2 γ s hs ?_⟩
  have hl : l1 * l2 ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  exact le_trans (s0C_mono h0 h hν0 hν1 hl) hs0

theorem lzC_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ lzC B := by
  unfold lzC A1; positivity

/-- Chen's `B = 3.9171` reproduces LZ's printed `C`, up to its last printed digit. -/
theorem lzC_chen_le : lzC 3.9171 ≤ bigC := by
  unfold lzC A1 bigC; norm_num

/-- Lichtman's `B`, with `3.3908 > 6.7814 / 2` to absorb the `ε`, gives `C < 8.6754`. -/
theorem lzC_lichtman_lt : lzC 3.3908 < 8.6754 := by
  unfold lzC A1; norm_num

theorem lzC_lichtman_lt_bigC : lzC 3.3908 < bigC := by
  unfold lzC A1 bigC; norm_num

/-! ## 2. From Johnston-Trudgian Proposition 2 to LZ Lemma 3 -/

/-- Johnston-Trudgian's `R(N, h)`: primes `p2 ≤ N` with `p1 = p2 + h ≤ N` prime. -/
def pairCount (N h : ℕ) : ℕ :=
  #{p ∈ range (N + 1) | p.Prime ∧ (p + h).Prime ∧ p + h ≤ N}

/-- Johnston-Trudgian, arXiv 2605.17825 v2, Proposition 2 on p. 6, display (12), for even
`h`, the only case LZ use, with the twin prime constant `C0` as the parameter `c0`. For odd `h`
the count is at most one and the statement is not needed. -/
def JTProp2 (c0 C1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ h : ℕ, Even h → 0 < h → h < N →
    (pairCount N h : ℝ) ≤ (C1 + ε) * c0 * Sprime h * N / log N ^ 2

/-- LZ display (20) on p. 5: `Z(X; 2n) = Σ log p log p'` over primes `εX ≤ p ≤ X`,
`p' = p + 2n ≤ X`. -/
def Zsum (ε X : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (⌊X⌋₊ + 1)).filter
      (fun p => p.Prime ∧ (p + 2 * n).Prime ∧ ε * X ≤ p ∧ ((p + 2 * n : ℕ) : ℝ) ≤ X),
    log p * log ((p + 2 * n : ℕ) : ℝ)

/-- LZ Lemma 3 on p. 6, Bombieri-Davenport form, for `1 ≤ n ≤ (1 - ε) X / 2` as in the
paper's setup on p. 5, with `S(n) = 2 c0 S'(n)`, display (21). -/
def LZLemma3 (c0 B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) ≤ (1 - ε) * X / 2 → Zsum ε X n < B * (2 * c0 * Sprime n) * X

/-- CONDITIONAL input, named: LZ's proof of their Theorem, pp. 6 to 13, read as a function of
the Lemma 3 constant. The constant enters only through Lemma 4, displays (27) and (28), where
it appears linearly as `2 B (1 + A(1))`, and then through `C(q1, q2)` in `c2(s)`. -/
def LZMethod (c0 ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ B : ℝ, 0 < B → LZLemma3 c0 B → MainStatementC (lzC B) ν kind

theorem Sprime_two_mul {n : ℕ} (hn : n ≠ 0) : Sprime (2 * n) = Sprime n := by
  unfold Sprime
  rw [Nat.primeFactors_mul (by norm_num) hn, Nat.Prime.primeFactors Nat.prime_two,
    Finset.filter_union, Finset.filter_singleton]
  simp

theorem Zsum_le (ε X : ℝ) (n : ℕ) (hX : 1 ≤ X) :
    Zsum ε X n ≤ log X ^ 2 * pairCount ⌊X⌋₊ (2 * n) := by
  unfold Zsum pairCount
  set S := (range (⌊X⌋₊ + 1)).filter
      (fun p => p.Prime ∧ (p + 2 * n).Prime ∧ ε * X ≤ p ∧ ((p + 2 * n : ℕ) : ℝ) ≤ X)
  have hX0 : 0 < X := by linarith
  have hterm : ∀ p ∈ S, log p * log ((p + 2 * n : ℕ) : ℝ) ≤ log X ^ 2 := by
    intro p hp
    obtain ⟨_, hpr, _, _, hle0⟩ := by simpa [S] using hp
    have hle : ((p + 2 * n : ℕ) : ℝ) ≤ X := by push_cast at hle0 ⊢; linarith
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
    have hq1 : (1 : ℝ) ≤ ((p + 2 * n : ℕ) : ℝ) := by
      have : (p : ℝ) ≤ ((p + 2 * n : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      linarith
    have hpX : (p : ℝ) ≤ X := by
      have : (p : ℝ) ≤ ((p + 2 * n : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      linarith
    have l1 := Real.log_le_log (by linarith) hpX
    have l2 := Real.log_le_log (by linarith) hle
    have l1' := Real.log_nonneg hp1
    have l2' := Real.log_nonneg hq1
    rw [sq]
    exact mul_le_mul l1 l2 l2' (le_trans l1' l1)
  have hsub : S ⊆ (range (⌊X⌋₊ + 1)).filter
      (fun p => p.Prime ∧ (p + 2 * n).Prime ∧ p + 2 * n ≤ ⌊X⌋₊) := by
    intro p hp
    obtain ⟨hr, hpr, hqr, _, hle0⟩ := by simpa [S] using hp
    have hle : ((p + 2 * n : ℕ) : ℝ) ≤ X := by push_cast at hle0 ⊢; linarith
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hpr, hqr, ?_⟩
    exact Nat.le_floor hle
  calc ∑ p ∈ S, log p * log ((p + 2 * n : ℕ) : ℝ) ≤ ∑ _p ∈ S, log X ^ 2 :=
        Finset.sum_le_sum hterm
    _ = S.card * log X ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [mul_comm]
        have := Finset.card_le_card hsub
        have hc : (S.card : ℝ) ≤ (((range (⌊X⌋₊ + 1)).filter
            (fun p => p.Prime ∧ (p + 2 * n).Prime ∧ p + 2 * n ≤ ⌊X⌋₊)).card : ℝ) := by
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)

/-- `log (N + 1) / log N ≤ 1 + 1 / N` for `N ≥ 3`. -/
theorem log_succ_div_le {N : ℕ} (hN : 3 ≤ N) :
    log ((N : ℝ) + 1) / log N ≤ 1 + 1 / N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog1 : 1 ≤ log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hdiff : log ((N : ℝ) + 1) ≤ log N + 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
    rw [Real.log_div (by positivity) hNpos.ne'] at h
    have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
    linarith
  have hl0 : 0 < log (N : ℝ) := by linarith
  rw [div_le_iff₀ hl0]
  have : 1 / (N : ℝ) ≤ 1 / N * log N := by
    have h0 : (0 : ℝ) ≤ 1 / N := by positivity
    nlinarith
  nlinarith

/-- **Johnston-Trudgian Proposition 2 gives LZ Lemma 3** with every `B > C1 / 2`. PROVED. -/
theorem lemma3_of_JT {c0 C1 B : ℝ} (hc0 : 0 < c0) (hC1 : 0 ≤ C1) (hJT : JTProp2 c0 C1)
    (hB : C1 / 2 < B) : LZLemma3 c0 B := by
  intro ε hε hε1
  set ε' := B - C1 / 2 with hε'
  have hε'0 : 0 < ε' := by linarith
  obtain ⟨N0, hN0⟩ := hJT ε' hε'0
  set K := C1 + ε' with hK
  have hK0 : 0 < K := by linarith
  -- ratio ρ = 2B / K > 1
  have hρ : K < 2 * B := by linarith
  set M : ℝ := max (N0 + 4 : ℝ) (max (1 / ε + 4) (3 * K / (2 * B - K) + 4)) with hM
  refine ⟨M, fun X hX n hn hnX => ?_⟩
  have hM1 : (N0 + 4 : ℝ) ≤ M := le_max_left _ _
  have hM2 : 1 / ε + 4 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3 : 3 * K / (2 * B - K) + 4 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hX4 : (4 : ℝ) ≤ X := by
    have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
    linarith
  set N := ⌊X⌋₊ with hNdef
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXN : X < N + 1 := Nat.lt_floor_add_one X
  have hN3 : 3 ≤ N := by
    have : (3 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hNge : N0 ≤ N := by
    have : (N0 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  -- 2n < N
  have hεX : 1 ≤ ε * X := by
    have h1 : 1 / ε < X := by linarith
    have := (div_lt_iff₀ hε).1 h1
    linarith
  have h2n : 2 * n < N := by
    have : (2 * n : ℝ) < N := by
      have : (2 * n : ℝ) ≤ (1 - ε) * X := by linarith
      nlinarith
    exact_mod_cast this
  have hn0 : n ≠ 0 := by omega
  have hJ := hN0 N hNge (2 * n) (even_two_mul n) (by omega) h2n
  rw [Sprime_two_mul hn0] at hJ
  have hS := one_le_Sprime n
  have hZ := Zsum_le ε X n (by linarith)
  -- log X ≤ log (N + 1)
  have hlogX : log X ≤ log ((N : ℝ) + 1) := Real.log_le_log (by linarith) hXN.le
  have hlogX0 : 0 ≤ log X := Real.log_nonneg (by linarith)
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith)
  set r := log ((N : ℝ) + 1) / log N with hr
  have hr0 : 0 ≤ r := div_nonneg (le_trans hlogX0 hlogX) hlogN.le
  have hr1 : r ≤ 1 + 1 / N := log_succ_div_le hN3
  have hlogsq : log X ^ 2 ≤ r ^ 2 * log N ^ 2 := by
    have : log ((N : ℝ) + 1) = r * log N := by rw [hr]; field_simp
    rw [← mul_pow, ← this]
    exact pow_le_pow_left₀ hlogX0 hlogX 2
  -- (1 + 1/N)^2 < 2B / K
  have hNbig : 3 * K / (2 * B - K) < N := by linarith
  have ht : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have ht0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hkey : K * (1 + 1 / N) ^ 2 < 2 * B := by
    have h1 : 3 * K * (1 / (N : ℝ)) < 2 * B - K := by
      have h := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * B - K)).1 hNbig
      have : 3 * K * (1 / (N : ℝ)) = 3 * K / N := by ring
      rw [this, div_lt_iff₀ hNpos]
      linarith
    nlinarith
  have hrsq : r ^ 2 ≤ (1 + 1 / N) ^ 2 := pow_le_pow_left₀ hr0 hr1 2
  -- assemble
  have hpc : (pairCount N (2 * n) : ℝ) * log N ^ 2 ≤ K * c0 * Sprime n * N := by
    rw [le_div_iff₀ (by positivity)] at hJ
    exact hJ
  have hpc0 : (0 : ℝ) ≤ pairCount N (2 * n) := Nat.cast_nonneg _
  calc Zsum ε X n ≤ log X ^ 2 * pairCount N (2 * n) := hZ
    _ ≤ r ^ 2 * (pairCount N (2 * n) * log N ^ 2) := by nlinarith
    _ ≤ r ^ 2 * (K * c0 * Sprime n * N) := by
        exact mul_le_mul_of_nonneg_left hpc (sq_nonneg _)
    _ ≤ (1 + 1 / N) ^ 2 * (K * c0 * Sprime n * N) := by
        apply mul_le_mul_of_nonneg_right hrsq
        positivity
    _ = (K * (1 + 1 / N) ^ 2) * (c0 * Sprime n * N) := by ring
    _ < (2 * B) * (c0 * Sprime n * N) := by
        apply mul_lt_mul_of_pos_right hkey
        positivity
    _ ≤ (2 * B) * (c0 * Sprime n * X) := by
        have hB0 : 0 < 2 * B := by linarith
        have : c0 * Sprime n * N ≤ c0 * Sprime n * X := by
          apply mul_le_mul_of_nonneg_left hNX; positivity
        exact mul_le_mul_of_nonneg_left this hB0.le
    _ = B * (2 * c0 * Sprime n) * X := by ring

/-! ## 3. The assembly, CONDITIONAL -/

/-- **LZ's Theorem with Lichtman's constant.** CONDITIONAL ON `JTProp2 c0 6.7814`, Johnston and
Trudgian's Proposition 2 from Lichtman's Theorem 1.7, and on `LZMethod`, LZ's own proof read as
a function of the Lemma 3 constant: the Theorem holds with `C = lzC 3.3908 < 8.6754` in place of
`10.0219168340`. -/
theorem lz_lichtman {c0 ν : ℝ} {kind : ℝ → Prop} (hc0 : 0 < c0) (hJT : JTProp2 c0 6.7814)
    (hM : LZMethod c0 ν kind) : MainStatementC (lzC 3.3908) ν kind :=
  hM 3.3908 (by norm_num) (lemma3_of_JT hc0 (by norm_num) hJT (by norm_num))

/-- The same with the rounded constant `8.6754`. CONDITIONAL as `lz_lichtman`. -/
theorem lz_86754 {c0 ν : ℝ} {kind : ℝ → Prop} (hc0 : 0 < c0) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hJT : JTProp2 c0 6.7814) (hM : LZMethod c0 ν kind) : MainStatementC 8.6754 ν kind :=
  mainC_mono (lzC_nonneg (by norm_num)) lzC_lichtman_lt.le hν0 hν1 (lz_lichtman hc0 hJT hM)

theorem lz_lichtman_tr {c0 : ℝ} (hc0 : 0 < c0) (hJT : JTProp2 c0 6.7814)
    (hM : LZMethod c0 nuTr IsTr) : MainStatementC 8.6754 nuTr IsTr :=
  lz_86754 hc0 nuTr_pos nuTr_lt_one hJT hM

theorem lz_lichtman_alg {c0 : ℝ} (hc0 : 0 < c0) (hJT : JTProp2 c0 6.7814)
    (hM : LZMethod c0 nuAlg IsAlg) : MainStatementC 8.6754 nuAlg IsAlg :=
  lz_86754 hc0 nuAlg_pos nuAlg_lt_one hJT hM

/-- The new Theorem is at least as strong as LZ's: it implies `MainStatement` with their `C`. -/
theorem main_of_lichtman {ν : ℝ} {kind : ℝ → Prop} (hν0 : 0 < ν) (hν1 : ν < 1)
    (h : MainStatementC (lzC 3.3908) ν kind) : MainStatement ν kind :=
  (mainC_bigC_iff ν kind).1 (mainC_mono (lzC_nonneg (by norm_num)) lzC_lichtman_lt_bigC.le
    hν0 hν1 h)

/-! ## 4. The worked value, `λ1 = π`, `λ2 = -√2`, `q1 = q2 = 1`, `η = 1`, formula (2) -/

theorem exp4_gt : (54 : ℝ) < exp 4 := by
  have h := Real.exp_one_gt_d9
  have : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (54 : ℝ) < 2.7182818283 ^ 4 := by norm_num
    _ ≤ exp 1 ^ 4 := by gcongr

theorem exp4_lt : exp 4 < 54.6 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
    _ < 54.6 := by norm_num

/-- Upper bound for `exp x` on `[0, 1]` by three Taylor terms and Mathlib's remainder. -/
theorem exp_le3 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / 18 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `-log ν ≥ 0.0916` for `ν = 0.91237810306`. -/
theorem neglog_nuTr_ge : (0.0916 : ℝ) ≤ -log nuTr := by
  have hν : (0 : ℝ) < nuTr := nuTr_pos
  have h : log nuTr ≤ -0.0916 := by
    rw [Real.log_le_iff_le_exp hν, Real.exp_neg]
    have he := exp_le3 (x := 0.0916) (by norm_num) (by norm_num)
    have hp := Real.exp_pos 0.0916
    rw [le_inv_comm₀ hν hp]
    calc exp 0.0916 ≤ 1 + 0.0916 + 0.0916 ^ 2 / 2 + 0.0916 ^ 3 * 4 / 18 := he
      _ ≤ nuTr⁻¹ := by norm_num [nuTr]
  linarith

/-- `-log ν ≤ 0.0919` for `ν = 0.91237810306`. -/
theorem neglog_nuTr_le : -log nuTr ≤ 0.0919 := by
  have hν : (0 : ℝ) < nuTr := nuTr_pos
  have h : -0.0919 ≤ log nuTr := by
    rw [Real.le_log_iff_exp_le hν, Real.exp_neg]
    have he := Real.quadratic_le_exp_of_nonneg (x := 0.0919) (by norm_num)
    have hp := Real.exp_pos 0.0919
    rw [inv_le_comm₀ hp hν]
    calc nuTr⁻¹ ≤ 1 + 0.0919 + 0.0919 ^ 2 / 2 := by norm_num [nuTr]
      _ ≤ exp 0.0919 := he
  linarith

theorem abs_pi_sqrt2 : |π * -√2| = π * √2 := by
  rw [mul_neg, abs_neg, abs_of_nonneg (by positivity)]

/-- With LZ's `C`, formula (2) at this point is at least 52, Python: exactly 52. -/
theorem s0_example2_ge : 52 ≤ s0 nuTr π (-√2) 1 1 1 := by
  rw [← s0C_bigC]
  unfold s0C
  rw [CqC_one_one (by norm_num [bigC]), abs_pi_sqrt2, Real.log_one, sub_zero]
  have hd := neglog_nuTr_le
  have hd0 : 0 < -log nuTr := by linarith [neglog_nuTr_ge]
  have hpi := Real.pi_gt_d2
  have hs2 : (1.414 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hy : exp 4.54 < 2 * (log 2 + bigC) * (π * √2) := by
    have e : exp 4.54 = exp 4 * exp 0.54 := by rw [← Real.exp_add]; norm_num
    have h54 := exp_le3 (x := 0.54) (by norm_num) (by norm_num)
    have h4 := exp4_lt
    have hp54 := Real.exp_pos 0.54
    have hprod : (3.14 : ℝ) * 1.414 < π * √2 := by
      have : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
      nlinarith
    rw [e]
    calc exp 4 * exp 0.54 ≤ 54.6 * (1 + 0.54 + 0.54 ^ 2 / 2 + 0.54 ^ 3 * 4 / 18) := by
          apply mul_le_mul h4.le h54 hp54.le (by norm_num)
      _ < 2 * (0.6931471803 + 10.0219168340) * (3.14 * 1.414) := by norm_num
      _ < 2 * (log 2 + bigC) * (π * √2) := by
          have hb : (0.6931471803 + 10.0219168340 : ℝ) < log 2 + bigC := by
            norm_num [bigC]; linarith
          have h1 : (0 : ℝ) < 3.14 * 1.414 := by norm_num
          nlinarith
  have hpos : 0 < 2 * (log 2 + bigC) * (π * √2) := lt_trans (Real.exp_pos _) hy
  have hnum : (4.54 : ℝ) < log (2 * (log 2 + bigC) * (π * √2)) := by
    rw [Real.lt_log_iff_exp_lt hpos]; exact hy
  have hq : (49 : ℝ) < log (2 * (log 2 + bigC) * (π * √2)) / (-log nuTr) := by
    rw [lt_div_iff₀ hd0]
    nlinarith
  have := Int.lt_ceil.2 (show ((49 : ℤ) : ℝ) < _ by exact_mod_cast hq)
  omega

/-- With Lichtman's `C`, formula (2) at this point is at most 51. -/
theorem s0_example2_new_le : s0C (lzC 3.3908) nuTr π (-√2) 1 1 1 ≤ 51 := by
  unfold s0C
  rw [CqC_one_one (lzC_nonneg (by norm_num)), abs_pi_sqrt2, Real.log_one, sub_zero]
  have hd := neglog_nuTr_ge
  have hd0 : 0 < -log nuTr := by linarith
  have hpi := Real.pi_lt_d2
  have hs2 : √2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hC := lzC_lichtman_lt
  have hC0 := lzC_nonneg (B := 3.3908) (by norm_num)
  have hpos : 0 < 2 * (log 2 + lzC 3.3908) * (π * √2) := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  have hy : 2 * (log 2 + lzC 3.3908) * (π * √2) ≤ exp 4.48 := by
    have e : exp 4.48 = exp 4 * exp 0.48 := by rw [← Real.exp_add]; norm_num
    have h48 := Real.quadratic_le_exp_of_nonneg (x := 0.48) (by norm_num)
    have h4 := exp4_gt
    have hprod : π * √2 < 3.15 * 1.4143 := by
      have : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
      nlinarith [Real.pi_pos]
    have hps : 0 ≤ π * √2 := by positivity
    rw [e]
    calc 2 * (log 2 + lzC 3.3908) * (π * √2)
        ≤ 2 * (0.6931471808 + 8.6754) * (3.15 * 1.4143) := by
          have hb : log 2 + lzC 3.3908 ≤ 0.6931471808 + 8.6754 := by linarith
          have hb0 : 0 ≤ log 2 + lzC 3.3908 := by
            have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith
          nlinarith
      _ ≤ 54 * (1 + 0.48 + 0.48 ^ 2 / 2) := by norm_num
      _ ≤ exp 4 * exp 0.48 := by
          apply mul_le_mul h4.le h48 (by norm_num) (Real.exp_pos 4).le
  have hnum : log (2 * (log 2 + lzC 3.3908) * (π * √2)) ≤ 4.48 := by
    rw [Real.log_le_iff_le_exp hpos]; exact hy
  have hq : log (2 * (log 2 + lzC 3.3908) * (π * √2)) / (-log nuTr) ≤ 49 := by
    rw [div_le_iff₀ hd0]
    nlinarith
  have := Int.ceil_le.2 (show _ ≤ ((49 : ℤ) : ℝ) by exact_mod_cast hq)
  omega

/-- **The worked gain**: formula (2) drops from at least 52 to at most 51. -/
theorem s0_example2_gain : s0C (lzC 3.3908) nuTr π (-√2) 1 1 1 < s0 nuTr π (-√2) 1 1 1 := by
  have := s0_example2_ge; have := s0_example2_new_le; omega

/-! ## 5. Vacuity instances for the new `Prop` definitions -/

/-- `∏_{p | h} (1 + 1/p) ≤ (3/2) ∏_{p | h, p > 2} (p - 1)/(p - 2)`. -/
theorem singProd_le_Sprime (h : ℕ) :
    LeanLab.SchnirelmannGoldbach.singProd h ≤ 3 / 2 * Sprime h := by
  unfold LeanLab.SchnirelmannGoldbach.singProd Sprime
  rw [← Finset.prod_filter_mul_prod_filter_not h.primeFactors (fun p => 2 < p)]
  have hA : ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (1 + 1 / (p : ℝ)) ≤
      ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      have h2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hp).2
      have hne : (p : ℝ) - 2 ≠ 0 := by linarith
      have e : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
        field_simp; ring
      rw [e]
      have : 1 / (p : ℝ) ≤ 1 / ((p : ℝ) - 2) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
  have hB : ∏ p ∈ h.primeFactors.filter (fun p => ¬ 2 < p), (1 + 1 / (p : ℝ)) ≤ 3 / 2 := by
    have hsub : h.primeFactors.filter (fun p => ¬ 2 < p) ⊆ {2} := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpr := Nat.prime_of_mem_primeFactors hp.1
      have := hpr.two_le
      rw [Finset.mem_singleton]; omega
    rcases Finset.subset_singleton_iff.1 hsub with h0 | h0
    · rw [h0]; norm_num
    · rw [h0]; norm_num
  have hA0 : 0 ≤ ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (1 + 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg; intro p _; positivity
  have hS := one_le_Sprime h
  unfold Sprime at hS
  have hB0 : 0 ≤ ∏ p ∈ h.primeFactors.filter (fun p => ¬ 2 < p), (1 + 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg; intro p _; positivity
  calc _ ≤ (∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
        (3 / 2) := mul_le_mul hA hB hB0 (by linarith)
    _ = _ := by ring

theorem pairCount_le_gapCount {N h : ℕ} (hh : 0 < h) :
    pairCount N h ≤ LeanLab.BrunGap.gapCount h N := by
  unfold pairCount LeanLab.BrunGap.gapCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2.1, hp.2.2.1⟩

/-- Vacuity for `JTProp2`: Brun's uniform bound from the lab, `BrunGap.gapUpper_uniform`,
gives it with `c0 = 1` and `C1 = (3/2) C₀`. PROVED. -/
theorem jtProp2_vacuity : JTProp2 1 (3 / 2 * LeanLab.BrunGap.C₀) := by
  intro ε hε
  refine ⟨3, fun N hN h he h0 _ => ?_⟩
  have hc := pairCount_le_gapCount (N := N) h0
  have hU := LeanLab.BrunGap.gapUpper_uniform h he (by omega) N hN
  have hsp := singProd_le_Sprime h
  have hS := one_le_Sprime h
  have hC := LeanLab.BrunGap.C₀_pos
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < log (N : ℝ) ^ 2 := by
    have := Real.log_pos (show (1 : ℝ) < N by linarith); positivity
  have hcR : (pairCount N h : ℝ) ≤ (LeanLab.BrunGap.gapCount h N : ℝ) := by exact_mod_cast hc
  calc (pairCount N h : ℝ) ≤ LeanLab.BrunGap.C₀ * LeanLab.SchnirelmannGoldbach.singProd h * N /
        log N ^ 2 := hcR.trans hU
    _ ≤ (3 / 2 * LeanLab.BrunGap.C₀ + ε) * 1 * Sprime h * N / log N ^ 2 := by
        apply div_le_div_of_nonneg_right _ hl.le
        have hN0 : (0 : ℝ) ≤ N := by linarith
        apply mul_le_mul_of_nonneg_right _ hN0
        nlinarith

/-- Vacuity for `LZLemma3`: it holds with `c0 = 1` and `B = C₀`, from `jtProp2_vacuity`
through `lemma3_of_JT`. PROVED. -/
theorem lzLemma3_vacuity : LZLemma3 1 LeanLab.BrunGap.C₀ := by
  have hC := LeanLab.BrunGap.C₀_pos
  exact lemma3_of_JT one_pos (by positivity) jtProp2_vacuity (by linarith)

/-- Vacuity for `MainStatementC`: it holds for the empty kind. -/
theorem mainC_vacuity (C ν : ℝ) : MainStatementC C ν (fun _ => False) := by
  intro l1 l2 μ _ _ _ _ hk
  exact hk.elim

/-- Vacuity for `LZMethod`: it holds for the empty kind. -/
theorem lzMethod_vacuity (c0 ν : ℝ) : LZMethod c0 ν (fun _ => False) :=
  fun B _ _ => mainC_vacuity (lzC B) ν

end LeanLab.Routes.U1540

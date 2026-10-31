/-
P0048 A. Dudek, L. Dunn 2026, An Explicit Result for the Sum of Two Almost Primes,
arXiv 2602.22720, read in full on 2026-10-18 by run 20261018T0503Z-16389, unit U-0918,
through Claude in Chrome, arxiv.org/html/2602.22720, per Lean Lab RULES_BLOCKERS B1.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

Theorem 1.2: every `N ≥ 2` is `a + b` with positive `a, b` and `Ω(ab) ≤ 40`; Theorem 3.3
sharpens it to 39 for even `N`. Three cases: `N ≤ 4 · 10^18` by Lemma 3.1 and the
Oliveira e Silva, Herzog, Pardi gap bound 1476; `4 · 10^18 < N ≤ 10^200` by a computer
check that `S(A, z) > 0`; `N > 10^200` by the Friedlander-Iwaniec sieve. Lemma 3.2 turns
`S(A, N^{1/20}) > 0` into the theorem; it is Campbell's Lemma 5.2 with `r = 20` and no
pre-sieving, so the lab reuses `Campbell2026.lemma5_2`, whose sequence `aSeq` is the same.
Goldbach itself is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.Campbell2026

namespace LeanLab.AlmostPrimes.DudekDunn2026
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.Campbell2026

/-- The gap bound of Oliveira e Silva, Herzog and Pardi as Lemma 3.1 uses it:
`p_{i+1} - p_i ≤ 1476` for `p_i ≤ 4 · 10^18`. -/
def GapTable1476 : Prop :=
  ∀ q : ℕ, q.Prime → q < 4 * 10 ^ 18 → ∃ q' : ℕ, q'.Prime ∧ q < q' ∧ q' - q ≤ 1476

/-- **Lemma 3.1, PROVED from the gap bound**, for `N ≥ 2`: with `m` 1 or a prime and
`1476 m ≤ 2^(M-2)`, every `2 ≤ N ≤ 4 · 10^18 m` is `a + b` with `Ω(ab) ≤ M`. The printed
lemma says every `N ≤ m · 4 · 10^18`; `N = 1` has no such decomposition, QUESTION. -/
theorem lemma3_1 (hG : GapTable1476) {m M : ℕ} (hm : m = 1 ∨ m.Prime)
    (hmM : 1476 * m ≤ 2 ^ (M - 2)) :
    ∀ N : ℕ, 2 ≤ N → N ≤ 4 * 10 ^ 18 * m → TwoAlmostPrimes M N := by
  have hm1 : 1 ≤ m := by
    rcases hm with h | h
    · omega
    · exact h.one_lt.le
  have hM3 : 3 ≤ M := by
    by_contra h
    have : M - 2 ≤ 0 := by omega
    have : 2 ^ (M - 2) ≤ 1 := by
      calc 2 ^ (M - 2) ≤ 2 ^ 0 := Nat.pow_le_pow_right (by norm_num) this
        _ = 1 := by norm_num
    omega
  have hpow : 2 ^ (M - 2) < 2 ^ (M - 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  intro N h2 hN
  rcases Nat.lt_or_ge (2 * m) N with hbig | hsmall
  · let P : ℕ → Prop := fun q => q.Prime ∧ m * q < N
    have hP2 : P 2 := ⟨Nat.prime_two, by omega⟩
    let q := Nat.findGreatest P N
    have hq : P q := Nat.findGreatest_spec (P := P) (m := 2) (by omega) hP2
    have hqG : q < 4 * 10 ^ 18 := by
      by_contra h
      have : 4 * 10 ^ 18 * m ≤ q * m := Nat.mul_le_mul_right m (by omega)
      have : q * m = m * q := Nat.mul_comm q m
      have := hq.2
      omega
    obtain ⟨q', hq', hqq', hgap⟩ := hG q hq.1 hqG
    have hmq' : N ≤ m * q' := by
      by_contra h
      push_neg at h
      have hq'N : q' ≤ N := by nlinarith
      exact Nat.findGreatest_is_greatest (P := P) hqq' hq'N ⟨hq', h⟩
    have hd : N - m * q ≤ 1476 * m := by
      have : m * q' - m * q = m * (q' - q) := (Nat.mul_sub m q' q).symm
      have : m * (q' - q) ≤ m * 1476 := Nat.mul_le_mul_left m hgap
      omega
    have hpos : 0 < N - m * q := by have := hq.2; omega
    have hmq0 : 0 < m * q := Nat.mul_pos (by omega) hq.1.pos
    refine ⟨m * q, N - m * q, hmq0, hpos, by omega, ?_⟩
    rw [bigOmega_mul hmq0.ne' hpos.ne']
    have h1 : bigOmega (m * q) ≤ 2 := by
      rcases hm with h | h
      · subst h; rw [one_mul, bigOmega_prime hq.1]; norm_num
      · rw [bigOmega_mul h.ne_zero hq.1.ne_zero, bigOmega_prime h, bigOmega_prime hq.1]
    have h2' : bigOmega (N - m * q) ≤ M - 2 := bigOmega_le_of_lt hpos (by omega)
    omega
  · refine ⟨1, N - 1, by norm_num, by omega, by omega, ?_⟩
    rw [one_mul]
    have : bigOmega (N - 1) ≤ M - 2 := bigOmega_le_of_lt (by omega) (by omega)
    omega

/-- **Case 1 of Theorem 3.3, CONDITIONAL ON the gap bound:** Lemma 3.1 with `m = 1` and
`M = 13`, since `1476 ≤ 2^11`, gives `Ω(ab) ≤ 13` for `2 ≤ N ≤ 4 · 10^18`. -/
theorem case1 (hG : GapTable1476) :
    ∀ N : ℕ, 2 ≤ N → N ≤ 4 * 10 ^ 18 → TwoAlmostPrimes 13 N := by
  intro N h2 hN
  exact lemma3_1 hG (m := 1) (M := 13) (Or.inl rfl) (by norm_num) N h2 (by omega)

/-- **Theorem 3.3, CONDITIONAL ON** the gap bound and on `S(A, N^{1/20}) > 0` for every
`N > 4 · 10^18`, which Cases 2 and 3 give: every `N ≥ 2` is `a + b` with `Ω(ab) ≤ 39` for
even `N` and `≤ 40` for odd `N`. Zero sorry of its own. -/
theorem theorem3_3_of (hG : GapTable1476)
    (hS : ∀ N : ℕ, 4 * 10 ^ 18 < N → SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ)))) :
    ∀ N : ℕ, 2 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 := by
  intro N h2
  rcases Nat.lt_or_ge (4 * 10 ^ 18) N with h | h
  · obtain ⟨a, b, ha, hb, hab, he, ho⟩ := lemma5_2 h2 (by norm_num) (hS N h)
    refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
    · intro hN
      have := he hN
      have : (bigOmega (a * b) : ℝ) < 40 := by linarith
      have : bigOmega (a * b) < 40 := by exact_mod_cast this
      omega
    · by_cases hN : Even N
      · have := he hN
        have : (bigOmega (a * b) : ℝ) < 41 := by linarith
        have : bigOmega (a * b) < 41 := by exact_mod_cast this
        omega
      · have := ho hN
        have : (bigOmega (a * b) : ℝ) < 41 := by linarith
        have : bigOmega (a * b) < 41 := by exact_mod_cast this
        omega
  · obtain ⟨a, b, ha, hb, hab, hO⟩ := case1 hG N h2 h
    exact ⟨a, b, ha, hb, hab, fun _ => by omega, by omega⟩

/-- Theorem 1.2, the abstract statement `dudek_dunn` of Statements.lean, from the same
two inputs. -/
theorem dudek_dunn_of (hG : GapTable1476)
    (hS : ∀ N : ℕ, 4 * 10 ^ 18 < N → SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ)))) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := by
  intro N h2
  obtain ⟨a, b, ha, hb, hab, -, h40⟩ := theorem3_3_of hG hS N h2
  exact ⟨a, b, ha, hb, hab, h40⟩

/-! ### The printed arithmetic -/

/-- Lemma 2.1, Case 3: `2 · 1.86 (log² z / log² 3) ≤ 1.49 (log² z / log² 2)`, that is
`3.72 log² 2 ≤ 1.49 log² 3`. MATCHES. -/
theorem lemma2_1_case3 : 3.72 * Real.log 2 ^ 2 ≤ 1.49 * Real.log 3 ^ 2 := by
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  nlinarith

/-- Theorem 3.3, Case 3: `2 · 0.591 = 1.182` from Lemma 2.3 and `N^{0.92} = (N^{1/20})^{18.4}`.
MATCHES. -/
theorem case3_consts : 2 * (0.591 : ℝ) = 1.182 ∧ (18.4 : ℝ) / 20 = 0.92 := by norm_num

/-- Theorem 3.3, Case 3, at `N = 10^200`: `(1.182 / 20^8) N^{0.92} log^{10} N < 4 (N - 1)`,
with `N^{0.92} = 10^184` exactly. MATCHES, about a factor 2 to spare. -/
theorem case3_at_1e200 :
    (1.182 / 20 ^ 8) * 10 ^ 184 * (200 * Real.log 10) ^ 10 < 4 * ((10 : ℝ) ^ 200 - 1) := by
  have hl := log_ten_lt
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 : (1.182 / 20 ^ 8) * 10 ^ 184 * (200 * Real.log 10) ^ 10 ≤
      (1.182 / 20 ^ 8) * 10 ^ 184 * (200 * 2.30261 : ℝ) ^ 10 := by gcongr
  have h2 : (1.182 / 20 ^ 8) * 10 ^ 184 * (200 * 2.30261 : ℝ) ^ 10 <
      4 * ((10 : ℝ) ^ 200 - 1) := by norm_num
  linarith

end LeanLab.AlmostPrimes.DudekDunn2026

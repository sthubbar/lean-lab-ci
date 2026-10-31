/-
P0066 Vaughan 1977, J. reine angew. Math. 290, 93-108, read from papers/P0066.pdf, pages 101,
102 and 106 checked on rendered page images. Unit U-6848, CLOUD MANUAL-M1, 2026-10-21, T1.

VERIFY of Vaughan1977.lean against the version of record:
* `Statement27` and `even26_of_density26`: the Theorem p. 93, "Every even natural number is the
  sum of at most twenty six prime numbers, and thus every natural number greater than unity is
  the sum of at most twenty seven", MATCH.
* `VaughanDensity26 := DensityC 26`, N(x) > x/26 for x ≥ 2 with N the lab's `NCount`: p. 106
  "Thus, for every x ≥ 2, A(x) > x/26", where A(x) counts the set 𝒜 of even numbers that are a
  sum of at most two primes, p. 94; `NCount x` counts even n in [1, ⌊x⌋] with
  `AtMostPrimes 2 n`, the same set. MATCH: the U-1273 reconstruction is the paper's statement.
* `atMost_of_densityC` is the last paragraph of Section 6, Mann's theorem with σ(ℬ) ≥ 1/13. MATCH.

This file states Lemmas 9, 10 and 12 as printed and PROVES Section 6: (6.1) from Lemmas 9 and
10, and A(x) > x/26 for every x ≥ 2 from (6.1) and Lemma 12 by the dyadic identity
A(x) = A(x2^{-K}) + Σ_{k=1}^{K} N(x2^{-k}). Lemma 9 is PROVED CONDITIONAL ON Rosser-Schoenfeld
(3.3), the paper's (2.14), through Riesel-Vaughan's count N(x) ≥ (3/2)π(⌊x⌋ - 5), a stronger
count than the paper's A(x) ≥ π(x - 3); the conclusion is the printed one.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977
import LeanLab.RieselVaughan1983.Lemma7
import LeanLab.Common.U1391RS33

open Finset Real

namespace LeanLab.SchnirelmannBounds.Vaughan1977Sec6
open LeanLab.SchnirelmannConstant LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977

/-- `A(x)`, p. 94: the number of elements of 𝒜 not exceeding `x`; the lab's `NCount`. -/
noncomputable def A (x : ℝ) : ℝ := (NCount x : ℝ)

/-- `N(x)`, p. 103: the number of `a ∈ 𝒜` with `x < a ≤ 2x`, that is `A(2x) - A(x)`. -/
noncomputable def NN (x : ℝ) : ℝ := A (2 * x) - A x

/-- Lemma 9, p. 101: `A(x) > x/25` for `2 ≤ x ≤ 10^11`. -/
def Lemma9 : Prop := ∀ x : ℝ, 2 ≤ x → x ≤ 10 ^ 11 → x / 25 < A x

/-- Lemma 10, p. 102: `A(x) > x/26` for `3.6·10^9 ≤ x ≤ 2.6·10^53`. -/
def Lemma10 : Prop := ∀ x : ℝ, 3.6 * 10 ^ 9 ≤ x → x ≤ 2.6 * 10 ^ 53 → x / 26 < A x

/-- Lemma 12, p. 104: `N(x) > x/25.7` for `x ≥ 10^52`. -/
def Lemma12 : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x → x / 25.7 < NN x

/-- (6.1), p. 106: `A(x) > x/26` for `2 ≤ x ≤ 2.6·10^53`, from Lemmas 9 and 10. -/
theorem eq61 (h9 : Lemma9) (h10 : Lemma10) :
    ∀ x : ℝ, 2 ≤ x → x ≤ 2.6 * 10 ^ 53 → x / 26 < A x := by
  intro x hx2 hx
  rcases le_or_gt x (10 ^ 11) with hs | hl
  · have := h9 x hx2 hs
    have : x / 26 ≤ x / 25 := div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    linarith
  · exact h10 x (by linarith) hx

/-- The dyadic identity: `A(x) = A(x 2^{-K}) + Σ_{k=1}^{K} N(x 2^{-k})`. -/
theorem dyadic (x : ℝ) (K : ℕ) :
    A x = A (x / 2 ^ K) + ∑ k ∈ range K, NN (x / 2 ^ (k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have : 2 * (x / 2 ^ (K + 1)) = x / 2 ^ K := by rw [pow_succ]; field_simp
    unfold NN; rw [this]; ring

/-- `2^{-K} + Σ_{k=1}^{K} 2^{-k} = 1`. -/
theorem geom (K : ℕ) : (1 : ℝ) / 2 ^ K + ∑ k ∈ range K, 1 / (2 : ℝ) ^ (k + 1) = 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have : (1 : ℝ) / 2 ^ K = 1 / 2 ^ (K + 1) + 1 / 2 ^ (K + 1) := by rw [pow_succ]; ring
    linarith

/-- The choice of `K`: for `x ≥ 10^52` there is `K` with `10^52 ≤ x 2^{-K} < 2·10^52`. -/
theorem exists_K (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∃ K : ℕ, 10 ^ 52 ≤ x / 2 ^ K ∧ x / 2 ^ K < 2 * 10 ^ 52 := by
  have hpos : (0 : ℝ) < 10 ^ 52 := by norm_num
  have hy1 : (1 : ℝ) ≤ x / 10 ^ 52 := by rw [le_div_iff₀ hpos]; linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊x / (10 : ℝ) ^ 52⌋₊ := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := hm ▸ (Nat.one_le_floor_iff _ |>.mpr hy1)
  refine ⟨Nat.log 2 m, ?_, ?_⟩
  · have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ Nat.log 2 m : ℕ) : ℝ) ≤ x / 10 ^ 52 :=
      le_trans (by exact_mod_cast h1) (hm ▸ Nat.floor_le (by linarith))
    push_cast at h2
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hpos] at h2
    linarith
  · have h1 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h2 : x / 10 ^ 52 < m + 1 := hm ▸ Nat.lt_floor_add_one _
    have h3 : (m : ℝ) + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by exact_mod_cast h1
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at h2
    rw [pow_succ] at h3
    nlinarith

/-- **Section 6, PROVED from (6.1) and Lemma 12**: `A(x) > x/26` for every `x ≥ 2`. -/
theorem density26_of (h61 : ∀ x : ℝ, 2 ≤ x → x ≤ 2.6 * 10 ^ 53 → x / 26 < A x)
    (h12 : Lemma12) : VaughanDensity26 := by
  intro x hx2
  show x / 26 < A x
  rcases le_or_gt x (2.6 * 10 ^ 53) with hs | hl
  · exact h61 x hx2 hs
  obtain ⟨K, hK1, hK2⟩ := exists_K x (by linarith)
  have hx0 : 0 < x := by linarith
  rw [dyadic x K]
  have hfirst : x / 2 ^ K / 26 < A (x / 2 ^ K) :=
    h61 _ (by linarith) (by linarith)
  have hterm : ∀ k ∈ range K, x / 2 ^ (k + 1) / 26 ≤ NN (x / 2 ^ (k + 1)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hge : x / 2 ^ K ≤ x / 2 ^ (k + 1) :=
      div_le_div_of_nonneg_left hx0.le (by positivity) (pow_le_pow_right₀ (by norm_num) hk)
    have := h12 _ (le_trans hK1 hge)
    have hp : 0 ≤ x / 2 ^ (k + 1) := by positivity
    have : x / 2 ^ (k + 1) / 26 ≤ x / 2 ^ (k + 1) / 25.7 :=
      div_le_div_of_nonneg_left hp (by norm_num) (by norm_num)
    linarith
  have hsum := Finset.sum_le_sum hterm
  have hg := geom K
  have hsplit : x / 26 = x / 2 ^ K / 26 + ∑ k ∈ range K, x / 2 ^ (k + 1) / 26 := by
    have : x / 26 = x / 26 * (1 / 2 ^ K + ∑ k ∈ range K, 1 / (2 : ℝ) ^ (k + 1)) := by
      rw [hg, mul_one]
    rw [this, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro k _; ring
  linarith

/-- The Theorem, CONDITIONAL ON Lemmas 9, 10 and 12: every `n > 1` is a sum of at most 27
primes. -/
theorem statement27_of_lemmas (h9 : Lemma9) (h10 : Lemma10) (h12 : Lemma12) : Statement27 :=
  statement27_of_density26 (density26_of (eq61 h9 h10) h12)

/-- The Theorem's even form, CONDITIONAL ON Lemmas 9, 10 and 12. -/
theorem even26_of_lemmas (h9 : Lemma9) (h10 : Lemma10) (h12 : Lemma12) :
    ∀ n : ℕ, Even n → AtMostPrimes 26 n :=
  even26_of_density26 (density26_of (eq61 h9 h10) h12)

/-! ### Lemma 9 from Rosser-Schoenfeld (3.3) -/

/-- `e^26 > 10^11`. -/
theorem exp26_gt : (10 : ℝ) ^ 11 < Real.exp 26 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 26 = Real.exp 1 ^ 26 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (10 : ℝ) ^ 11 < 2.7182818283 ^ 26 := by norm_num
    _ ≤ Real.exp 1 ^ 26 := by gcongr

/-- **Lemma 9, CONDITIONAL ON Rosser-Schoenfeld (3.3)**, the paper's (2.14). -/
theorem lemma9_of_RS (hRS : RS33) : Lemma9 := by
  intro x hx2 hx
  unfold A
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) < n + 1 := by linarith
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast this
  obtain ⟨hs1, hs8⟩ := ncount_small x n hn.symm
  rcases lt_or_ge n 8 with h8 | h8
  · have : (1 : ℝ) ≤ NCount x := by exact_mod_cast hs1 hn2
    have : x < 8 := by
      have : (n : ℝ) ≤ 7 := by exact_mod_cast (show n ≤ 7 by omega)
      linarith
    linarith
  rcases lt_or_ge n 72 with h72 | h72
  · have : (4 : ℝ) ≤ NCount x := by exact_mod_cast hs8 h8
    have : (n : ℝ) ≤ 71 := by exact_mod_cast (show n ≤ 71 by omega)
    linarith
  -- n ≥ 72: N(x) ≥ (3/2) π(n - 5) > (3/2)(n - 5)/(log(n - 5) - 1/2)
  have hpi := ncount_ge_pi x n hn.symm h8
  have hrs := hRS (n - 5) (by omega)
  have hm : ((n - 5 : ℕ) : ℝ) = (n : ℝ) - 5 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hm] at hrs
  have hn72 : (72 : ℝ) ≤ n := by exact_mod_cast h72
  have hlog : Real.log ((n : ℝ) - 5) < 26 := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]
    have := exp26_gt
    linarith
  have hlog0 : 1 < Real.log ((n : ℝ) - 5) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hden : 0 < Real.log ((n : ℝ) - 5) - 1 / 2 := by linarith
  have hq : ((n : ℝ) - 5) / 26 < ((n : ℝ) - 5) / (Real.log ((n : ℝ) - 5) - 1 / 2) := by
    apply div_lt_div_of_pos_left (by linarith) hden (by linarith)
  have : x / 25 < (3 / 2) * (((n : ℝ) - 5) / 26) := by
    have : x / 25 < ((n : ℝ) + 1) / 25 := by linarith
    have : ((n : ℝ) + 1) / 25 ≤ (3 / 2) * (((n : ℝ) - 5) / 26) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  nlinarith

/-- The Theorem, CONDITIONAL ON Rosser-Schoenfeld (3.3), Lemma 10 and Lemma 12. -/
theorem statement27_of_RS (hRS : RS33) (h10 : Lemma10) (h12 : Lemma12) : Statement27 :=
  statement27_of_lemmas (lemma9_of_RS hRS) h10 h12

/-- The Theorem, CONDITIONAL ON Rosser-Schoenfeld 1975 θ(t) ≥ t - t/(40 log t), Lemma 10 and
Lemma 12, through the lab's `rs33_of_rs1975`. -/
theorem statement27_of_RS1975 (h75 : Lemma6Theta.RS1975Cor2Thm7) (h10 : Lemma10) (h12 : Lemma12) :
    Statement27 :=
  statement27_of_RS (fun n hn => LeanLab.Common.U1391.rs33_of_rs1975 h75 n hn) h10 h12

/-- Vacuity: Lemma 12's bound is consistent with the trivial `N(x) ≤ x/2 + 1`, and the
lemmas imply the reconstructed density, so they are not weaker than needed. -/
theorem lemmas_imply_density (h9 : Lemma9) (h10 : Lemma10) (h12 : Lemma12) : VaughanDensity26 :=
  density26_of (eq61 h9 h10) h12

end LeanLab.SchnirelmannBounds.Vaughan1977Sec6

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.eq61
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.dyadic
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.geom
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.exists_K
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.density26_of
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.statement27_of_lemmas
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.even26_of_lemmas
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.exp26_gt
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.lemma9_of_RS
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.statement27_of_RS
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.statement27_of_RS1975
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Sec6.lemmas_imply_density

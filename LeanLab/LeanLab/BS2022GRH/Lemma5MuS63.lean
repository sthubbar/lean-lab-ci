/-
AI wrote this Lean code, ROUTE BURST S63, burst-20261122, unit lemma5_mu.
P0021 journal Lemma 5 first estimate p. 1216, cited there as Buthe 2014 display 4.6,
J. Buthe, A Brun-Titchmarsh inequality for weighted sums over prime numbers,
Acta Arith. 166 2014, arXiv 1410.7561v2, Section 4, display 4.6:
Q(z) = 6 z / pi^2 + Theta(0.68 sqrt z) for z at least 1.
Buthe's own proof: Cohen, Dress, El Marraki 2007 Theorem 3 plus a short computer calculation.
This file splits that proof: a cited large range leaf, a finite computation leaf,
and a finite computation proved here by decide +kernel for the smallest range.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.Lemma5Coeffs138
import LeanLab.BS2022GRH.Lemma5MuMidS70All

namespace LeanLab.BS2022GRH.Lemma5MuS63
open Real Finset

/-- Trial division witness search used in the finite computation of Buthe 2014 display 4.6:
`noSq f d n` is false exactly when some e with d ≤ e and e * e ≤ n divides n as a square
is found within fuel f. Only the direction false implies not squarefree is used. -/
def noSq : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f + 1, d, n => if n < d * d then true else (n % (d * d) != 0 && noSq f (d + 1) n)

theorem not_squarefree_of_noSq_false (n : ℕ) :
    ∀ (f d : ℕ), 2 ≤ d → noSq f d n = false → ¬ Squarefree n := by
  intro f
  induction f with
  | zero => intro d _ h; simp [noSq] at h
  | succ f ih =>
    intro d hd h hsq
    simp only [noSq] at h
    split_ifs at h with h1
    · simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
      rcases h with h | h
      · have hdvd : d * d ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h)
        have hu := hsq d hdvd
        rw [Nat.isUnit_iff] at hu
        omega
      · exact ih (d + 1) (by omega) h hsq

/-- The count of n in [1, N] passing the trial division test; an upper bound for the
squarefree count Q(N) of display 4.6. -/
def cP (N : ℕ) : ℕ := ((Icc 1 N).filter (fun n => noSq n 2 n = true)).card

theorem sqf_card_le_cP (N : ℕ) :
    ((Icc 1 N).filter (fun n => Squarefree n)).card ≤ cP N := by
  unfold cP
  apply card_le_card
  intro n hn
  simp only [mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  by_contra h
  exact not_squarefree_of_noSq_false n n 2 le_rfl (by simpa using h) hn.2

theorem cP_succ (N : ℕ) :
    cP (N + 1) = cP N + (if noSq (N + 1) 2 (N + 1) = true then 1 else 0) := by
  unfold cP
  rw [card_filter, card_filter, Finset.sum_Icc_succ_top (by omega)]

/-- The integer form of the inequality Q(N) ≤ 0.6079 N + 0.68 sqrt N checked by the
short computer calculation behind Buthe 2014 display 4.6. -/
def good (m q : ℕ) : Bool :=
  decide (10000 * q ≤ 6079 * m) || decide ((10000 * q - 6079 * m) ^ 2 ≤ 46240000 * m)

/-- Running check over n + 1, ..., n + k with running count q. -/
def chk : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k + 1, n, q =>
    let q' := if noSq (n + 1) 2 (n + 1) = true then q + 1 else q
    good (n + 1) q' && chk k (n + 1) q'

theorem chk_sound : ∀ (k n : ℕ), chk k n (cP n) = true →
    ∀ m, n < m → m ≤ n + k → good m (cP m) = true := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    simp only [chk, Bool.and_eq_true] at h
    have hq : (if noSq (n + 1) 2 (n + 1) = true then cP n + 1 else cP n) = cP (n + 1) := by
      rw [cP_succ]; split_ifs <;> simp
    rw [hq] at h
    rcases Nat.lt_or_ge (n + 1) m with hm | hm
    · exact ih (n + 1) h.2 m hm (by omega)
    · have : m = n + 1 := by omega
      subst this; exact h.1

/-- Small range bound of the finite computation. -/
def K0 : ℕ := 3000

theorem chk_K0 : chk K0 0 (cP 0) = true := by decide +kernel

theorem good_le_K0 (N : ℕ) (h1 : 1 ≤ N) (h2 : N ≤ K0) : good N (cP N) = true :=
  chk_sound K0 0 chk_K0 N (by omega) (by simpa using h2)

theorem real_of_good (N q : ℕ) (h : good N q = true) :
    (q : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) := by
  simp only [good, Bool.or_eq_true, decide_eq_true_eq] at h
  have hs : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  rcases h with h | h
  · have : (10000 : ℝ) * q ≤ 6079 * N := by exact_mod_cast h
    nlinarith
  · by_cases hc : 10000 * q ≤ 6079 * N
    · have : (10000 : ℝ) * q ≤ 6079 * N := by exact_mod_cast hc
      nlinarith
    · have hc' : 6079 * N ≤ 10000 * q := by omega
      have hr : ((10000 * q - 6079 * N : ℕ) : ℝ) = 10000 * (q : ℝ) - 6079 * N := by
        push_cast [Nat.cast_sub hc']; ring
      have hsq : ((10000 : ℝ) * q - 6079 * N) ^ 2 ≤ 46240000 * N := by
        rw [← hr]; exact_mod_cast h
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hss : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hN
      have : (10000 : ℝ) * q - 6079 * N ≤ 6800 * √(N : ℝ) := by
        apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
        nlinarith
      nlinarith

theorem six_div_pi_sq_ge : (0.6079 : ℝ) ≤ 6 / π ^ 2 := by
  have hp : π < 3.1416 := Real.pi_lt_d4
  have hp0 : 0 < π := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem mMu_mul (x : ℝ) (hx : 0 < x) :
    Lemma5Coeffs138.mMu x * x = 6 / π ^ 2 * x + 0.68 * √x := by
  unfold Lemma5Coeffs138.mMu
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have h3 : √x ^ 2 = x := Real.sq_sqrt hx.le
  field_simp
  linear_combination (-(17 / 25) * π ^ 2) * h3

/-- Reduction from integer N = floor x to real x for the upper half of display 4.6. -/
theorem real_bound_of_nat (x : ℝ) (hx : 1 ≤ x)
    (h : (cP ⌊x⌋₊ : ℝ) ≤ 0.6079 * ⌊x⌋₊ + 0.68 * √(⌊x⌋₊ : ℝ)) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ Lemma5Coeffs138.mMu x * x := by
  rw [mMu_mul x (by linarith)]
  have h1 : (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ cP ⌊x⌋₊ := by
    exact_mod_cast sqf_card_le_cP _
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 : √(⌊x⌋₊ : ℝ) ≤ √x := Real.sqrt_le_sqrt h2
  have h4 := six_div_pi_sq_ge
  have h5 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  nlinarith

/-- PROVED here. The finite computation of Buthe 2014 display 4.6, upper half,
for 1 ≤ x < K0 + 1, by decide +kernel over the trial division count. -/
theorem lemma5_mu_small (x : ℝ) (hx : 1 ≤ x) (hx2 : x < K0 + 1) :
    (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ Lemma5Coeffs138.mMu x * x := by
  apply real_bound_of_nat x hx
  apply real_of_good
  apply good_le_K0
  · exact Nat.one_le_floor_iff _ |>.2 hx
  · have : ⌊x⌋₊ < K0 + 1 := by
      rw [Nat.floor_lt (by linarith)]; exact_mod_cast hx2
    omega

/-- LEAF: Buthe 2014 display 4.6 via Cohen, Dress, El Marraki 2007 Theorem 3, the
large range: for x ≥ 438653, |Q(x) - 6 x / pi^2| ≤ 0.02767 sqrt x. Class HARD, cited
analytic and computational input, a citation wall. QUESTION: the constant 0.02767 and
the threshold 438653 are taken from secondary descriptions of CDEM07, the paper itself was
not read in this unit. -/
theorem cdem07_thm3 : ∀ x : ℝ, 438653 ≤ x →
    |(((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) - 6 / π ^ 2 * x|
      ≤ 0.02767 * √x := by
  sorry

/-- PROVED in S70, was a LEAF: Buthe 2014 display 4.6, the short computer calculation,
upper half, on the middle range K0 + 1 ≤ x < 438653 not covered by the kernel check of this
file. Proved in Lemma5MuMidS70All by a kernel checked Legendre count at 1117 checkpoints. -/
theorem buthe_compute_mid : ∀ x : ℝ, (K0 + 1 : ℝ) ≤ x → x < 438653 →
    (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ Lemma5Coeffs138.mMu x * x := by
  intro x h1 h2
  have h3 : (3001 : ℝ) ≤ x := by
    have : ((K0 : ℕ) : ℝ) = 3000 := by norm_num [K0]
    linarith
  exact Lemma5MuMidS70.buthe_compute_mid_proved x h3 h2

/-- Buthe 2014 display 4.6, upper half, as journal Lemma 5 uses it, assembled from the
two leaves and the proved small range. CONDITIONAL ON the leaves through sorry. -/
theorem lemma5_mu_assembled : PaperInputs148.Lemma5MuJ := by
  intro x hx
  rcases lt_or_ge x (K0 + 1) with h | h
  · exact lemma5_mu_small x hx h
  rcases lt_or_ge x 438653 with h' | h'
  · exact buthe_compute_mid x h h'
  · have hA := cdem07_thm3 x h'
    rw [mMu_mul x (by linarith)]
    have := (abs_le.1 hA).2
    have hs : 0 ≤ √x := Real.sqrt_nonneg _
    linarith

end LeanLab.BS2022GRH.Lemma5MuS63

#print axioms LeanLab.BS2022GRH.Lemma5MuS63.lemma5_mu_small
#print axioms LeanLab.BS2022GRH.Lemma5MuS63.sqf_card_le_cP
#print axioms LeanLab.BS2022GRH.Lemma5MuS63.real_of_good
#print axioms LeanLab.BS2022GRH.Lemma5MuS63.lemma5_mu_assembled
#print axioms LeanLab.BS2022GRH.Lemma5MuS63.buthe_compute_mid

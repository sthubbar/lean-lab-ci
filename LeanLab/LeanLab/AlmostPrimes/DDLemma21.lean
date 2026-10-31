/-
AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1271.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
Section 2, Lemma 2.1, Case 1, read on arxiv.org/html/2602.22720 this run.

Lemma 2.1: for `2 ≤ w < z`, `∏_{w ≤ p < z} (1 - g(p))⁻¹ ≤ K (log z / log w)²` with `K = 3`, where
`g(2) = 1/2`, `g(p) = 2/p` for odd `p ∤ N`, `g(p) = 1/p` for odd `p ∣ N`.
Case 1, `w ≥ 286`: `-log(1 - 2/p) ≤ 2/p + 2/(p(p - 2))` by the Taylor series, Rosser-Schoenfeld
Theorem 5 for `2 Σ 1/p`, the tail `Σ 1/(p(p-2)) ≤ 1/3 + Σ_{p ≥ 3} 1/p² - 0.463 < 0.073`, the
additive constant at most `0.21`, and `e^{0.21} ≤ 1.24`, so `K ≤ 1.24`.

PROVED, no cited input:
* `neg_log_one_sub_le`: `-log(1 - x) ≤ x + x²/(2(1 - x))` for `0 ≤ x < 1`, the series step.
* `neg_log_one_sub_two_div`: `-log(1 - 2/p) ≤ 2/p + 2/(p(p - 2))` for `p ≥ 3`.
* `tail_lt`: `Σ 1/(p(p - 2)) ≤ 2/285 < 0.073` over any finite set of integers `≥ 286`.
* `paper_const`: `2 · 0.073 + 2/log² 286 ≤ 0.21` and `e^{0.21} ≤ 1.24`, the paper's arithmetic.
CONDITIONAL ON the Rosser-Schoenfeld input `2 Σ_{w ≤ p < z} 1/p ≤ 2 log(log z / log w)
+ 1/log² z + 1/log² w`, taken as hypothesis `hRS`:
* `lemma2_1_case1`: `∏_{w ≤ p < z} (1 - g(p))⁻¹ ≤ 1.24 (log z / log w)²` for `286 ≤ w < z`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDLemma22

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.DDLemma21

/-- The sieve density of Dudek-Dunn Section 2. -/
def g (N p : ℕ) : ℝ := if p = 2 then 1 / 2 else if p ∣ N then 1 / (p : ℝ) else 2 / (p : ℝ)

/-- The primes `p` with `w ≤ p < z`. -/
def primesIn (w z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)

/-- The series step: `-log(1 - x) ≤ x + x²/(2(1 - x))` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    -log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  have hL := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have hG : HasSum (fun n : ℕ => x / 2 * x ^ n) (x / 2 * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left (x / 2)
  have hI : HasSum (fun n : ℕ => if n = 0 then x / 2 else 0) (x / 2) := hasSum_ite_eq 0 (x / 2)
  have hR := hG.add hI
  have hle := hasSum_le (fun n => ?_) hL hR
  · have e : x / 2 * (1 - x)⁻¹ + x / 2 = x + x ^ 2 / (2 * (1 - x)) := by
      have : (1 - x) ≠ 0 := by linarith
      field_simp; ring
    linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : n ≠ 0 := by omega
      simp only [hn', ite_false, add_zero]
      have hxn : 0 ≤ x ^ (n + 1) := pow_nonneg h0 _
      have h2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      calc x ^ (n + 1) / ((n : ℝ) + 1) ≤ x ^ (n + 1) / 2 :=
            div_le_div_of_nonneg_left hxn (by norm_num) h2
        _ = x / 2 * x ^ n := by ring

/-- `-log(1 - 2/p) ≤ 2/p + 2/(p(p - 2))` for `p ≥ 3`. -/
theorem neg_log_one_sub_two_div {p : ℝ} (hp : 3 ≤ p) :
    -log (1 - 2 / p) ≤ 2 / p + 2 / (p * (p - 2)) := by
  have hp0 : 0 < p := by linarith
  have h := neg_log_one_sub_le (x := 2 / p) (by positivity) (by rw [div_lt_one hp0]; linarith)
  have e : (2 / p) ^ 2 / (2 * (1 - 2 / p)) = 2 / (p * (p - 2)) := by
    have : p - 2 ≠ 0 := by linarith
    field_simp
    try ring
  linarith

/-- The tail: over any finite set of integers `n ≥ 286`, `Σ 1/(n(n - 2)) ≤ 2/285`. -/
theorem tail_le (S : Finset ℕ) (hS : ∀ n ∈ S, 286 ≤ n) :
    ∑ n ∈ S, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ≤ 2 / 285 := by
  set M := S.sup id + 1
  have hsub : S ⊆ Ico 286 M := by
    intro n hn
    rw [Finset.mem_Ico]
    exact ⟨hS n hn, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  have hterm : ∀ n ∈ Ico 286 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ≤ 2 * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have : (286 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    rw [div_le_iff₀ (by nlinarith)]
    field_simp
    nlinarith
  calc ∑ n ∈ S, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))
      ≤ ∑ n ∈ Ico 286 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        have : (286 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
        apply div_nonneg (by norm_num); nlinarith
    _ ≤ ∑ n ∈ Ico 286 M, 2 * (1 / (n : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = 2 * ∑ n ∈ Ico 286 M, (1 / (n : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 / ((286 : ℕ) - 1 : ℝ)) := by
        have := DDLemma22.tail_le 286 (by norm_num) M
        push_cast at this ⊢; linarith
    _ = 2 / 285 := by norm_num

theorem tail_lt (S : Finset ℕ) (hS : ∀ n ∈ S, 286 ≤ n) :
    ∑ n ∈ S, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) < 0.073 := by
  have := tail_le S hS; norm_num at this ⊢; linarith

lemma log286_gt : (5.6 : ℝ) < log 286 := by
  have h2 := Real.log_two_gt_d9
  have e : log (286 : ℝ) = 8 * log 2 + log (286 / 256) := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h3 : 1 - (286 / 256 : ℝ)⁻¹ ≤ log (286 / 256) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (286 / 256 : ℝ)) (by norm_num)
    exact this
  rw [e]; norm_num at h3 ⊢; linarith

lemma exp021_le : exp (0.21 : ℝ) ≤ 1.24 := by
  have h := Real.exp_bound' (x := (0.21 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

/-- The paper's arithmetic in Case 1: `2 · 0.073 + 2/log² 286 ≤ 0.21` and `e^{0.21} ≤ 1.24`. -/
theorem paper_const : 2 * 0.073 + 2 / (log 286) ^ 2 ≤ (0.21 : ℝ) ∧ exp (0.21 : ℝ) ≤ 1.24 := by
  refine ⟨?_, exp021_le⟩
  have h := log286_gt
  have : (5.6 : ℝ) ^ 2 ≤ (log 286) ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
  have : 2 / (log 286) ^ 2 ≤ 2 / (5.6 : ℝ) ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
  norm_num at this ⊢; linarith

lemma one_sub_g_pos (N p : ℕ) (hp : 3 ≤ p) : 0 < 1 - 2 / (p : ℝ) ∧
    1 - 2 / (p : ℝ) ≤ 1 - g N p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : p ≠ 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [sub_pos, div_lt_one (by linarith)]; linarith
  · unfold g; simp only [hp2, ite_false]
    split_ifs
    · have : 1 / (p : ℝ) ≤ 2 / p := div_le_div_of_nonneg_right (by norm_num) (by linarith)
      linarith
    · exact le_refl _

/-- **Dudek-Dunn Lemma 2.1, Case 1**, CONDITIONAL ON the Rosser-Schoenfeld bound `hRS`:
for `286 ≤ w < z`, `∏_{w ≤ p < z} (1 - g(p))⁻¹ ≤ 1.24 (log z / log w)²`. -/
theorem lemma2_1_case1 (N : ℕ) (w z : ℝ) (hw : 286 ≤ w) (hwz : w < z)
    (hRS : 2 * ∑ p ∈ primesIn w z, (1 : ℝ) / p ≤
      2 * log (log z / log w) + 1 / (log z) ^ 2 + 1 / (log w) ^ 2) :
    ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ 1.24 * (log z / log w) ^ 2 := by
  set S := primesIn w z
  have hS : ∀ p ∈ S, 286 ≤ p := by
    intro p hp
    simp only [S, primesIn, Finset.mem_filter] at hp
    have : (286 : ℝ) ≤ p := le_trans hw hp.2.2.1
    exact_mod_cast this
  -- each factor is at most exp(2/p + 2/(p(p-2)))
  have hfac : ∀ p ∈ S, (1 - g N p)⁻¹ ≤ exp (2 / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    intro p hp
    have h3 : 3 ≤ p := le_trans (by norm_num) (hS p hp)
    have hp' : (3 : ℝ) ≤ p := by exact_mod_cast h3
    obtain ⟨hpos, hle⟩ := one_sub_g_pos N p h3
    calc (1 - g N p)⁻¹ ≤ (1 - 2 / (p : ℝ))⁻¹ := inv_anti₀ hpos hle
      _ = exp (-log (1 - 2 / (p : ℝ))) := by rw [exp_neg, exp_log hpos]
      _ ≤ _ := exp_le_exp.mpr (neg_log_one_sub_two_div hp')
  have hprod : ∏ p ∈ S, (1 - g N p)⁻¹ ≤
      ∏ p ∈ S, exp (2 / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have h3 : 3 ≤ p := le_trans (by norm_num) (hS p hp)
      obtain ⟨hpos, hle⟩ := one_sub_g_pos N p h3
      have : 0 < 1 - g N p := lt_of_lt_of_le hpos hle
      exact (inv_pos.mpr this).le
    · exact hfac
  rw [← Real.exp_sum, Finset.sum_add_distrib] at hprod
  have hsum1 : ∑ p ∈ S, 2 / (p : ℝ) = 2 * ∑ p ∈ S, (1 : ℝ) / p := by
    rw [Finset.mul_sum]; congr 1; ext p; ring
  have hsum2 : ∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 2)) =
      2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
    rw [Finset.mul_sum]; congr 1; ext p; ring
  have htail := tail_le S hS
  -- the log terms
  have hlw : log 286 ≤ log w := log_le_log (by norm_num) hw
  have hlz : log 286 ≤ log z := log_le_log (by norm_num) (by linarith)
  have h286 := log286_gt
  have hsq : ∀ y : ℝ, log 286 ≤ y → 1 / y ^ 2 ≤ 1 / (5.6 : ℝ) ^ 2 := by
    intro y hy
    have : (5.6 : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
  have hz2 := hsq _ hlz
  have hw2 := hsq _ hlw
  have hlw0 : 0 < log w := by linarith
  have hL : 0 < log z / log w := div_pos (by linarith) hlw0
  have hexp : ∑ p ∈ S, 2 / (p : ℝ) + ∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
      2 * log (log z / log w) + 0.21 := by
    have hc : (1 : ℝ) / (5.6 : ℝ) ^ 2 ≤ 0.032 := by norm_num
    rw [hsum1, hsum2]; linarith
  calc ∏ p ∈ S, (1 - g N p)⁻¹ ≤ exp (2 * log (log z / log w) + 0.21) :=
        hprod.trans (exp_le_exp.mpr hexp)
    _ = exp 0.21 * (log z / log w) ^ 2 := by
        rw [exp_add, mul_comm, ← Real.log_rpow hL, exp_log (by positivity)]; norm_num
    _ ≤ 1.24 * (log z / log w) ^ 2 := by
        apply mul_le_mul_of_nonneg_right exp021_le (by positivity)

#print axioms neg_log_one_sub_le
#print axioms neg_log_one_sub_two_div
#print axioms tail_lt
#print axioms paper_const
#print axioms lemma2_1_case1

end LeanLab.AlmostPrimes.DDLemma21

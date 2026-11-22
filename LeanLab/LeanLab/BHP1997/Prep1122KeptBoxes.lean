/-
P0069 Baker Harman Pintz 1997, page 53 with Lemma 33 on page 48. Burst S15 burst-20261122, unit
P1122-0088, the route leaf upD_kept_51 of branch claude/BHP1997-upper_normalized_raw_conditions_slack-p2.

The page 53 sentence is: we obtain b1 from psi(m, Y^c4) by deleting from k_m the terms for which
Lemma 33 does not apply to any arrangement of the variables. So 5.1 for the kept part of k_m is
Lemma 33 applied term by term. Lemma 33 is stated for M = Y^beta1, N = Y^beta2 with fixed
exponents, so the kept part is first cut into dyadic boxes, one for each triple of ranges
2^i1 <= p1 < 2^(i1+1), and so on, and the boxes are recombined by Cauchy Schwarz. There are at most
(5 log x)^3 boxes, and the log power is absorbed because A in 5.1 is arbitrary.

This file proves upK_kept_51, the exact statement of upD_kept_51, from one LEAF, upK_box_51,
which is 5.1 for one dyadic box with a constant uniform in the box. The dyadic identity, the
Cauchy Schwarz step, the box count and the assembly are PROVED. The name upK_kept_51 differs
from upD_kept_51 so that the stacked branch, once its file name clash with main is repaired,
can close its leaf by `upK_kept_51 h4 h9 hε hε8`.

New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312
import LeanLab.BHP1997.Thm4Statement
import LeanLab.BHP1997.MeanValue132

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- A Dirichlet polynomial window integrand of 5.1 on page 43 is continuous in t when the
frequencies are positive integers and T0 is positive. PROVED. -/
theorem upK_window_continuous (s : Finset ℕ) (hs : ∀ m ∈ s, m ≠ 0) (d : ℕ → ℂ) {T0 : ℝ}
    (hT : 0 < T0) :
    Continuous (fun t : ℝ => ‖∑ m ∈ s, d m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
      (T0 ^ 2 + t ^ 2)) := by
  refine Continuous.div ?_ (by fun_prop) (fun t => by positivity)
  refine (continuous_norm.comp (continuous_finsetSum _ fun m hm => ?_)).pow 2
  refine continuous_const.div ?_ (fun t => ?_)
  · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hs m hm))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hs m hm))

/-- Cauchy Schwarz over a finite family of pieces inside the 5.1 integral of page 43: the
integral for a sum of |S| coefficient sequences is at most |S| times the sum of the integrals.
This is the step that lets a log power number of dyadic boxes be absorbed, since A in 5.1 is
arbitrary. PROVED. -/
theorem upK_window_cs {ι : Type*} (S : Finset ι) (s : Finset ℕ) (hs : ∀ m ∈ s, m ≠ 0)
    (c : ι → ℕ → ℂ) {T0 a b : ℝ} (hT : 0 < T0) (hab : a ≤ b) :
    ∫ t in a..b, ‖∑ m ∈ s, (∑ i ∈ S, c i m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T0 ^ 2 + t ^ 2) ≤
      (S.card : ℝ) * ∑ i ∈ S, ∫ t in a..b,
        ‖∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T0 ^ 2 + t ^ 2) := by
  have hpt : ∀ t : ℝ,
      ‖∑ m ∈ s, (∑ i ∈ S, c i m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          (T0 ^ 2 + t ^ 2) ≤
        (S.card : ℝ) * ∑ i ∈ S,
          ‖∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T0 ^ 2 + t ^ 2) := by
    intro t
    have hD : 0 < T0 ^ 2 + t ^ 2 := by positivity
    have hsw : ∑ m ∈ s, (∑ i ∈ S, c i m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
        ∑ i ∈ S, ∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_div _ _ _
    rw [hsw, ← Finset.sum_div, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hD.le
    calc ‖∑ i ∈ S, ∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (∑ i ∈ S, ‖∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hint : ∀ i ∈ S, IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T0 ^ 2 + t ^ 2))
        volume a b := fun i _ =>
    (upK_window_continuous s hs (c i) hT).intervalIntegrable a b
  have hL : IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ s, (∑ i ∈ S, c i m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T0 ^ 2 + t ^ 2)) volume a b :=
    (upK_window_continuous s hs (fun m => ∑ i ∈ S, c i m) hT).intervalIntegrable a b
  calc _ ≤ ∫ t in a..b, (S.card : ℝ) * ∑ i ∈ S,
          ‖∑ m ∈ s, c i m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T0 ^ 2 + t ^ 2) :=
        intervalIntegral.integral_mono_on hab hL
          ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
            upK_window_continuous s hs (c i) hT)).intervalIntegrable a b) (fun t _ => hpt t)
    _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint]

/-- The number of dyadic ranges for a prime factor of m in J, m at most 2 x^(11/20 + eps), is at
most five times log x once x is at least 3. PROVED. -/
theorem upK_box_count {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (hx : 3 ≤ x) :
    ((Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hY : x ^ (11 / 20 + ε) ≤ x := by
    calc x ^ (11 / 20 + ε) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num at hε8 ⊢; linarith)
      _ = x := Real.rpow_one x
  set n := ⌊2 * x ^ (11 / 20 + ε)⌋₊ with hn
  have hk : (Nat.log 2 n : ℝ) ≤ 4 * Real.log x := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; linarith
    have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hpos.ne'
    have hnle : (n : ℝ) ≤ 2 * x := by
      calc (n : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := Nat.floor_le (by positivity)
        _ ≤ 2 * x := by linarith
    have h1 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (2 * x) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity)
        (le_trans (by exact_mod_cast hpow) hnle)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have hl2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hl2' : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
    by_contra hcon
    push Not at hcon
    nlinarith
  push_cast
  linarith


/-- P0069 page 53: the dyadic split of the kept part of k_m. For m at most N, every prime
factor p of m has Nat.log 2 p below Nat.log 2 N + 1, so inserting the indicator of the box
(Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i and summing over the boxes i changes nothing.
PROVED. -/
theorem upK_kept_dyadic (ε Y : ℝ) {N m : ℕ} (hm : m ≤ N) :
    upperKept ε Y m =
      ∑ i ∈ (Finset.range (Nat.log 2 N + 1)) ×ˢ (Finset.range (Nat.log 2 N + 1)) ×ˢ
          (Finset.range (Nat.log 2 N + 1)),
        (∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log Y) (Real.log p2 / Real.log Y)
                    (Real.log p3 / Real.log Y)
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) := by
  unfold upperKept
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p1 hp1 => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 hp2 => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p3 hp3 => ?_
  simp only [ite_and]
  rw [Finset.sum_ite_eq, if_pos]
  have h1 : p1 ≤ m := Nat.le_of_mem_primeFactors (Finset.mem_filter.mp hp1).1
  have h2 : p2 ≤ m := le_trans (Nat.le_of_mem_primeFactors (Finset.mem_filter.mp hp2).1)
    (Nat.div_le_self _ _)
  have h3 : p3 ≤ m := le_trans (Nat.le_of_mem_primeFactors (Finset.mem_filter.mp hp3).1)
    (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right (h1.trans hm)),
    Nat.lt_succ_of_le (Nat.log_mono_right (h2.trans hm)),
    Nat.lt_succ_of_le (Nat.log_mono_right (h3.trans hm))⟩

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43, for one dyadic box of
the kept part of k_m: p1, p2, p3 in the ranges [2^i1, 2^(i1+1)), and so on, kept when
upperPrimeCovered holds. One set E for all boxes, constant uniform in the box. Paper: Lemma 33
with M, N the grouped primes, 3.2 by Lemma 5, L the rest; the removal of the cross conditions
psi(n4, p3), p3 < p2 < p1 and the pointwise region test is implicit. CONDITIONAL on the cited
Theorem 4 and Lemma 9. HARD. -/
theorem upK_box_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ i : ℕ × ℕ × ℕ,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
            C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
              Real.log x ^ (-A') := by
  sorry

/-- P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43 for the kept part of k_m: the
exact statement of the leaf upD_kept_51 of the stacked branch. PROVED from the LEAF upK_box_51 by
the dyadic split upK_kept_dyadic, Cauchy Schwarz upK_window_cs over at most (5 log x)^3 boxes, and
the choice A' + 6 in the leaf. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem upK_kept_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨E, hE⟩ := upK_box_51 h4 h9 hε hε8
  refine ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA (A' + 6) (by linarith)
  refine ⟨max (max C 3) (5 ^ 6 * max C 0), fun x hx q hq hqQ => ?_⟩
  have hxC : C ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hCout : 5 ^ 6 * max C 0 ≤ max (max C 3) (5 ^ 6 * max C 0) := le_max_right _ _
  have hCC : C ≤ max (max C 3) (5 ^ 6 * max C 0) := le_trans (le_max_left _ _) (le_max_left _ _)
  obtain ⟨hcard, hbox⟩ := hC x hxC q hq hqQ
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hQ1 : 1 ≤ sieveQ ε x := le_trans hq hqQ
  have hqQpos : (0 : ℝ) < (q : ℝ) * (sieveQ ε x : ℝ) := by
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ sieveQ ε x := by exact_mod_cast hQ1
    positivity
  have hT : 0 < x ^ (11 / 20 + ε) / ((q : ℝ) * (sieveQ ε x : ℝ)) := div_pos hY0 hqQpos
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < Real.log x := by linarith
  have hW : 0 ≤ x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 := by positivity
  refine ⟨le_trans hcard (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg hL0.le _)), ?_⟩
  set K := Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1 with hKdef
  have hJ : ∀ m ∈ rightInterval ε x, m ≠ 0 ∧ m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := by
    intro m hm
    have h := Finset.mem_Ioc.mp hm
    exact ⟨by omega, h.2⟩
  have hrw : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
        ∑ m ∈ rightInterval ε x, (∑ i ∈ (Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K),
          (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro χ t
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [upK_kept_dyadic ε (x ^ (11 / 20 + ε)) (hJ m hm).2, ← Finset.sum_mul]
    push_cast
    rfl
  set P : ℝ := C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
    Real.log x ^ (-(A' + 6)) with hP
  have hcardB : (((Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K)).card : ℝ) =
      (K : ℝ) ^ 3 := by
    simp [Finset.card_product]; ring
  have hK : (K : ℝ) ≤ 5 * Real.log x := upK_box_count hε hε8 hx3
  calc _ = ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                (∑ i ∈ (Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K),
                  (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) * χ (m : ZMod q)) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [hrw χ t]
    _ ≤ ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          (((Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K)).card : ℝ) *
          ∑ i ∈ (Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
        Finset.sum_le_sum fun χ _ => upK_window_cs _ _ (fun m hm => (hJ m hm).1) _ hT
          (neg_le_self hY0.le)
    _ = (((Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K)).card : ℝ) *
          ∑ i ∈ (Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K),
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (((Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K)).card : ℝ) *
          ∑ _i ∈ (Finset.range K) ×ˢ (Finset.range K) ×ˢ (Finset.range K), P :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbox i) (Nat.cast_nonneg _)
    _ = (K : ℝ) ^ 3 * (K : ℝ) ^ 3 * P := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardB]; ring
    _ ≤ max (max C 3) (5 ^ 6 * max C 0) *
          (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A') := by
        have hsplit : Real.log x ^ (-(A' + 6)) = Real.log x ^ (-A') * (Real.log x ^ 6)⁻¹ := by
          rw [show -(A' + 6) = -A' + -6 by ring, Real.rpow_add hL0, Real.rpow_neg hL0.le (6 : ℝ),
            show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hLA : 0 ≤ Real.log x ^ (-A') := Real.rpow_nonneg hL0.le _
        have hL6 : 0 < Real.log x ^ 6 := by positivity
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        have hK6 : (K : ℝ) ^ 3 * (K : ℝ) ^ 3 ≤ 5 ^ 6 * Real.log x ^ 6 := by
          have := pow_le_pow_left₀ hK0 hK 6
          calc (K : ℝ) ^ 3 * (K : ℝ) ^ 3 = (K : ℝ) ^ 6 := by ring
            _ ≤ (5 * Real.log x) ^ 6 := this
            _ = 5 ^ 6 * Real.log x ^ 6 := by ring
        have hPle : P ≤ max C 0 * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            (Real.log x ^ (-A') * (Real.log x ^ 6)⁻¹) := by
          rw [hP, hsplit]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hW)
            (mul_nonneg hLA (inv_nonneg.mpr hL6.le))
        have hM0 : 0 ≤ max C 0 * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            (Real.log x ^ (-A') * (Real.log x ^ 6)⁻¹) :=
          mul_nonneg (mul_nonneg (le_max_right _ _) hW) (mul_nonneg hLA (inv_nonneg.mpr hL6.le))
        calc (K : ℝ) ^ 3 * (K : ℝ) ^ 3 * P
            ≤ (K : ℝ) ^ 3 * (K : ℝ) ^ 3 * (max C 0 *
                (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
                (Real.log x ^ (-A') * (Real.log x ^ 6)⁻¹)) :=
              mul_le_mul_of_nonneg_left hPle (by positivity)
          _ ≤ (5 ^ 6 * Real.log x ^ 6) * (max C 0 *
                (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
                (Real.log x ^ (-A') * (Real.log x ^ 6)⁻¹)) :=
              mul_le_mul_of_nonneg_right hK6 hM0
          _ = (5 ^ 6 * max C 0) *
                (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
                Real.log x ^ (-A') := by
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCout hW) hLA

end LeanLab.BHP1997.DecompC165d


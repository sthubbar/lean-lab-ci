import LeanLab.HeathBrown1985.SingularSeries
import LeanLab.ExceptionalSet.MVMajorSing
import LeanLab.ChenExplicit.TwinCNumeric
import LeanLab.MissingDigit.KimFix

/-!
Kim 2024, arXiv 2412.19975v1, page 6, section 1.3, equation 1.8.
The digits restrict the argument of the ordinary binary Goldbach series.
The Euler product is the existing HeathBrown1985.singular.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.MissingDigit.KimSeries

open Finset
open scoped ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- The Ramanujan coefficient in Kim equation 1.8. -/
def term (m q : ℕ) : ℝ :=
  (μ q : ℝ) ^ 2 * LeanLab.HeathBrown1985.ramanujan q m / (q.totient : ℝ) ^ 2

/-- Kim's series at the positive argument m. The q = 0 term is zero. -/
def series (m : ℕ) : ℝ := ∑' q : ℕ, term m q

/-- The Euler product form, with parity and odd prime divisor factors explicit. -/
def euler (m : ℕ) : ℝ := LeanLab.HeathBrown1985.singular m

/-- Odd prime divisor correction in the binary Euler product. -/
def oddFactor (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The coefficient is the existing multiplicative binary coefficient for q positive. -/
theorem term_eq_f2 (m q : ℕ) : term m q = LeanLab.ExceptionalSet.MVMajor.f2 m q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [term]
  · exact (LeanLab.ExceptionalSet.MVMajor.f2_apply hq m).symm

/-- The two existing binary coefficient representations agree. -/
theorem term_eq_gm (m q : ℕ) : term m q = LeanLab.HeathBrown1985.gm m q := by
  open LeanLab.HeathBrown1985 LeanLab.ExceptionalSet.MVMajor in
    rw [term_eq_f2, gm_eq]
    by_cases hsq : Squarefree q
    · rw [if_pos hsq, ← (f2_mult m).prod_primeFactors hsq]
      apply Finset.prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      rw [f2_prime hprime]
      by_cases hd : p ∣ m
      · rw [if_pos hd, vloc_dvd hprime hd]
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      · rw [if_neg hd, vloc_not_dvd hprime hd]
    · rw [if_neg hsq]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · exact f2_eq_zero_of_not_sqf hq hsq

/-- The series converges to its Euler product at every positive argument. -/
theorem hasSum_term {m : ℕ} (hm : 1 ≤ m) : HasSum (term m) (euler m) := by
  have h : term m = LeanLab.HeathBrown1985.gm m := funext (term_eq_gm m)
  rw [h]
  exact LeanLab.HeathBrown1985.hasSum_gm m hm

/-- Kim's convergent Ramanujan series equals the Euler product. -/
theorem series_eq_euler {m : ℕ} (hm : 1 ≤ m) : series m = euler m :=
  (hasSum_term hm).tsum_eq

/-- The ordinary series has no additional digit-dependent Euler factor. -/
theorem series_even_eq {m : ℕ} (hm : 1 ≤ m) (he : Even m) :
    series m = 2 * LeanLab.ChenExplicit.twinC * oddFactor m := by
  rw [series_eq_euler hm]
  exact if_pos he

/-- A uniform positive lower bound for the series at every positive even argument. -/
theorem series_ge_thirteen_tenths {m : ℕ} (hm : 1 ≤ m) (he : Even m) :
    (13 / 10 : ℝ) ≤ series m := by
  rw [series_even_eq hm he]
  have hC := LeanLab.ChenExplicit.twinC_ge_065
  have hF := LeanLab.ChenExplicit.one_le_oddFactor m
  change (1 : ℝ) ≤ oddFactor m at hF
  nlinarith

/-- Uniform lower bound for the corrected main term on the whole closed interval. -/
theorem fixed_mainTerm_ge {X H m : ℕ} (hHX : H ≤ X) (hXm : X ≤ m)
    (hmXH : m ≤ X + H) (hm : 1 ≤ m) (he : Even m) :
    (13 / 10 : ℝ) * H ≤ (MstarFixed X H m : ℝ) * series m := by
  rw [MstarFixed_eq hHX hXm hmXH]
  nlinarith [mul_le_mul_of_nonneg_left (series_ge_thirteen_tenths hm he)
    (Nat.cast_nonneg H : (0 : ℝ) ≤ H)]

/-- Each odd prime correction is at most 2. This bound retains the divisor dependence. -/
theorem oddFactor_le_two_pow (m : ℕ) :
    oddFactor m ≤ (2 : ℝ) ^ (m.primeFactors.filter (2 < ·)).card := by
  unfold oddFactor
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- Explicit upper bound. Its dependence on the prime divisors is not suppressed. -/
theorem series_le_two_pow {m : ℕ} (hm : 1 ≤ m) (he : Even m) :
    series m ≤ (6614 / 5000 : ℝ) *
      (2 : ℝ) ^ (m.primeFactors.filter (2 < ·)).card := by
  rw [series_even_eq hm he]
  have hC := LeanLab.ChenExplicit.twinC_le_06614
  have hC0 := LeanLab.ChenExplicit.twinC_pos
  have hF := oddFactor_le_two_pow m
  have hF0 : 0 ≤ oddFactor m := le_trans (by norm_num)
    (LeanLab.ChenExplicit.one_le_oddFactor m)
  calc
    2 * LeanLab.ChenExplicit.twinC * oddFactor m ≤
        (6614 / 5000 : ℝ) * oddFactor m := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hF (by norm_num)

/-- Both bounds for the corrected main term. The upper bound depends on m. -/
theorem fixed_mainTerm_bounds {X H m : ℕ} (hHX : H ≤ X) (hXm : X ≤ m)
    (hmXH : m ≤ X + H) (hm : 1 ≤ m) (he : Even m) :
    (13 / 10 : ℝ) * H ≤ (MstarFixed X H m : ℝ) * series m ∧
    (MstarFixed X H m : ℝ) * series m ≤
      (6614 / 5000 : ℝ) * (2 : ℝ) ^ (m.primeFactors.filter (2 < ·)).card * H := by
  refine ⟨fixed_mainTerm_ge hHX hXm hmXH hm he, ?_⟩
  rw [MstarFixed_eq hHX hXm hmXH]
  nlinarith [mul_le_mul_of_nonneg_left (series_le_two_pow hm he)
    (Nat.cast_nonneg H : (0 : ℝ) ≤ H)]

/-- The negative argument in equation 1.8 has the same real Ramanujan value. -/
theorem ramanujan_neg_eq {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    (∑ a ∈ (Finset.range q).filter (fun a : ℕ => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e (-((m : ℝ) * a / q))) =
      (LeanLab.HeathBrown1985.ramanujan q m : ℂ) := by
  calc
    _ = (starRingEnd ℂ) (∑ a ∈ (Finset.range q).filter (fun a : ℕ => Nat.Coprime a q),
        LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * a / q)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact LeanLab.PNTPort.LargeSieve.e_neg _
    _ = _ := by
      rw [LeanLab.PNTPort.Vinogradov.ramanujan_sum hq m]
      simp

/-- Each real coefficient is exactly the complex coefficient printed in equation 1.8. -/
theorem term_eq_negative_exponential {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    (term m q : ℂ) = (μ q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
      ∑ a ∈ (Finset.range q).filter (fun a : ℕ => Nat.Coprime a q),
        LeanLab.PNTPort.LargeSieve.e (-((m : ℝ) * a / q)) := by
  rw [ramanujan_neg_eq hq m]
  unfold term
  push_cast
  ring

end LeanLab.MissingDigit.KimSeries

/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0002 Chen 1973, p. 163 display 5 and p. 171 display 24.
Finite unweighted Selberg helpers. The weighted analytic progression estimates remain inputs.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973Weights

open Finset

noncomputable section
attribute [local instance] Classical.propDecidable
namespace LeanLab.AlmostPrimeSums.Chen1973FiniteSieve

open Chen1973Display24 Chen1973Weights

/-- Exact finite expansion of the Selberg square. -/
lemma square_sum_eq_count (A s : Finset ℕ) (lam : ℕ → ℝ) :
    ∑ n ∈ A, (∑ d ∈ s, if d ∣ n then lam d else 0) ^ 2 =
      ∑ d ∈ s, ∑ e ∈ s, lam d * lam e * ((A.filter (d.lcm e ∣ ·)).card : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ A, ∑ d ∈ s, ∑ e ∈ s,
        if d.lcm e ∣ n then lam d * lam e else 0 := by
      apply sum_congr rfl
      intro n _
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff]
    _ = ∑ d ∈ s, ∑ e ∈ s, ∑ n ∈ A,
        if d.lcm e ∣ n then lam d * lam e else 0 := by
      rw [sum_comm]
      exact sum_congr rfl (fun d _ => sum_comm)
    _ = _ := by
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- A normalized Selberg square majorizes the finite sifted count. -/
theorem sieve_card_le (A s : Finset ℕ) (lam : ℕ → ℝ) (h1 : 1 ∈ s) (hlam : lam 1 = 1) :
    (((A.filter (fun n => ∀ d ∈ s, d ∣ n → d = 1)).card : ℕ) : ℝ) ≤
      ∑ d ∈ s, ∑ e ∈ s, lam d * lam e * ((A.filter (d.lcm e ∣ ·)).card : ℝ) := by
  classical
  let B := A.filter (fun n => ∀ d ∈ s, d ∣ n → d = 1)
  have hsum : ∀ n ∈ B, (∑ d ∈ s, if d ∣ n then lam d else 0) = 1 := by
    intro n hn
    rw [sum_eq_single_of_mem 1 h1]
    · simp [hlam]
    · intro d hd hdne
      have hnd : ¬ d ∣ n := fun hdvd => hdne ((mem_filter.mp hn).2 d hd hdvd)
      simp [hnd]
  rw [← square_sum_eq_count]
  calc
    _ = ∑ n ∈ B, (∑ d ∈ s, if d ∣ n then lam d else 0) ^ 2 := by
      symm
      calc
        _ = ∑ _n ∈ B, (1 : ℝ) := sum_congr rfl (fun n hn => by rw [hsum n hn]; norm_num)
        _ = _ := by simp [B]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- The prime sifted set has no supported divisor other than one. -/
lemma no_supported_divisor {x D n : ℕ}
    (hn : ∀ p ∈ range (D + 1), p.Prime → p.Coprime x → ¬ p ∣ n) :
    ∀ d ∈ sv x D, d ∣ n → d = 1 := by
  intro d hd hdn
  by_contra hdne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hdne
  have hdpos := (mem_Icc.mp (mem_filter.mp hd).1).1
  have hdD := (mem_Icc.mp (mem_filter.mp hd).1).2
  have hpD := (Nat.le_of_dvd hdpos hpd).trans hdD
  exact hn p (mem_range.mpr (by omega)) hp
    ((mem_filter.mp hd).2.2.coprime_dvd_left hpd) (hpd.trans hdn)

/-- Chen weights give a finite upper sieve before any analytic density input. -/
theorem chen_sieve_card_le (A : Finset ℕ) {x D : ℕ} (hx : Even x) (hD : 1 ≤ D) :
    (((A.filter (fun n => ∀ p ∈ range (D + 1), p.Prime → p.Coprime x → ¬ p ∣ n)).card : ℕ) : ℝ) ≤
      ∑ d ∈ sv x D, ∑ e ∈ sv x D,
        lamC x D d * lamC x D e * ((A.filter (d.lcm e ∣ ·)).card : ℝ) := by
  classical
  have h1 : 1 ∈ sv x D := by simp [sv, hD]
  have h := sieve_card_le A (sv x D) (lamC x D) h1 (lamC_one hx hD)
  apply le_trans _ h
  have hsub : A.filter (fun n => ∀ p ∈ range (D + 1), p.Prime → p.Coprime x → ¬ p ∣ n) ⊆
      A.filter (fun n => ∀ d ∈ sv x D, d ∣ n → d = 1) := by
    intro n hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn.1, no_supported_divisor hn.2⟩
  exact Nat.cast_le.mpr (card_le_card hsub)

/-- Finite Selberg upper bound from explicit divisibility-count remainders. -/
theorem chen_sieve_of_remainders (A : Finset ℕ) {x D : ℕ} (hx : Even x) (hD : 1 ≤ D)
    (X R : ℝ) (hR : 0 ≤ R)
    (hcount : ∀ d ∈ sv x D, ∀ e ∈ sv x D,
      |((A.filter (d.lcm e ∣ ·)).card : ℝ) - X / ((d.lcm e).totient : ℝ)| ≤ R) :
    (((A.filter (fun n => ∀ p ∈ range (D + 1), p.Prime → p.Coprime x → ¬ p ∣ n)).card : ℕ) : ℝ) ≤
      X / Sv x D + (D : ℝ) ^ 2 * R := by
  classical
  have hp : ∀ d ∈ sv x D, ∀ e ∈ sv x D,
      lamC x D d * lamC x D e * ((A.filter (d.lcm e ∣ ·)).card : ℝ) ≤
      lamC x D d * lamC x D e * (X / ((d.lcm e).totient : ℝ)) + R := by
    intro d hd e he
    have hcoeff : |lamC x D d * lamC x D e| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_lamC_le_one hx hD d) (abs_lamC_le_one hx hD e) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hh : |lamC x D d * lamC x D e *
        (((A.filter (d.lcm e ∣ ·)).card : ℝ) - X / ((d.lcm e).totient : ℝ))| ≤ R := by
      rw [abs_mul]
      exact (mul_le_mul hcoeff (hcount d hd e he) (abs_nonneg _) zero_le_one).trans_eq (one_mul R)
    have := le_abs_self (lamC x D d * lamC x D e *
        (((A.filter (d.lcm e ∣ ·)).card : ℝ) - X / ((d.lcm e).totient : ℝ)))
    nlinarith
  have hquad : (∑ d ∈ sv x D, ∑ e ∈ sv x D,
      lamC x D d * lamC x D e / ((d.lcm e).totient : ℝ)) = 1 / Sv x D := by
    simpa only [Nat.lcm] using chen_display24 hx hD
  have hcard : (sv x D).card ≤ D := by
    calc
      _ ≤ (Icc 1 D).card := card_le_card (filter_subset _ _)
      _ = _ := by simp
  calc
    _ ≤ ∑ d ∈ sv x D, ∑ e ∈ sv x D,
        lamC x D d * lamC x D e * ((A.filter (d.lcm e ∣ ·)).card : ℝ) := chen_sieve_card_le A hx hD
    _ ≤ ∑ d ∈ sv x D, ∑ e ∈ sv x D,
        (lamC x D d * lamC x D e * (X / ((d.lcm e).totient : ℝ)) + R) :=
      sum_le_sum (fun d hd => sum_le_sum (fun e he => hp d hd e he))
    _ = X * (∑ d ∈ sv x D, ∑ e ∈ sv x D,
        lamC x D d * lamC x D e / ((d.lcm e).totient : ℝ)) + ((sv x D).card : ℝ) ^ 2 * R := by
      simp_rw [sum_add_distrib]
      have heq : (∑ d ∈ sv x D, ∑ e ∈ sv x D,
          lamC x D d * lamC x D e * (X / ((d.lcm e).totient : ℝ))) =
          X * (∑ d ∈ sv x D, ∑ e ∈ sv x D,
          lamC x D d * lamC x D e / ((d.lcm e).totient : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        rw [mul_sum]
        apply sum_congr rfl
        intro e _
        ring
      rw [heq]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      rw [hquad, ← div_eq_mul_one_div]
      gcongr

end LeanLab.AlmostPrimeSums.Chen1973FiniteSieve

#print axioms LeanLab.AlmostPrimeSums.Chen1973FiniteSieve.square_sum_eq_count

#print axioms LeanLab.AlmostPrimeSums.Chen1973FiniteSieve.sieve_card_le

#print axioms LeanLab.AlmostPrimeSums.Chen1973FiniteSieve.no_supported_divisor

#print axioms LeanLab.AlmostPrimeSums.Chen1973FiniteSieve.chen_sieve_card_le

#print axioms LeanLab.AlmostPrimeSums.Chen1973FiniteSieve.chen_sieve_of_remainders

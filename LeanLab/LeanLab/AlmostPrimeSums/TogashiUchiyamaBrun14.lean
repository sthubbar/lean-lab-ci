/-
AI-written Lean code, Claude, 2026-10-21, CLOUD 20261021T0217Z-cloud56, unit U-6803.
P0072 Togashi and Uchiyama 1964, Section 2, p. 63: the upper bound
P(N^{1/14}) < 196.0022 A_N φ(N)/log² N, printed without its derivation ("in like manner").

Reconstruction, checked in numerics/tu_buhstab.py: Brun's upper sieve with the same
h = 5/4, τ = 2 log(5/4) < 0.4463, λ = (5/4)² < 1.5630 as the printed u = 15 lower bound, and
truncation exponent 2m + 7 in place of 2m + 8, gives the factor 1 + S₇ with
S₇ = Σ_{m ≥ 0} λ^{m+1}((m+1)τ)^{2m+7}/(2m+7)!, about 1.0805e-5 at the rounded τ, λ, and
196 (1 + S₇) = 196.00212, which rounds up to the printed 196.0022. The formula for u = 14 is our
reconstruction, not printed in the paper; the sieve inequality itself stays cited.

PROVED here: `brun14_upper_const`, 196 (1 + S₇) < 196.0022 with τ = 0.4463, λ = 1.5630.
S₇ is increasing in τ and λ, so it holds for the paper's true τ, λ below these.
Method copied from TogashiUchiyamaBrun.lean: 40 exact terms over ℚ, geometric tail.
Goldbach is open.
-/
import Mathlib

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaBrun14

def τq : ℚ := 4463 / 10000
def lamq : ℚ := 15630 / 10000
def cq : ℚ := 6066 / 10000

/-- The m-th term of the paper's series. -/
def T (m : ℕ) : ℝ :=
  (lamq : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * (τq : ℝ)) ^ (2 * m + 7) / ((2 * m + 7).factorial : ℝ)

def Tq (m : ℕ) : ℚ :=
  lamq ^ (m + 1) * (((m : ℚ) + 1) * τq) ^ (2 * m + 7) / ((2 * m + 7).factorial : ℚ)

lemma T_cast (m : ℕ) : T m = ((Tq m : ℚ) : ℝ) := by simp [T, Tq]

def G (m : ℕ) : ℝ := (lamq : ℝ) ^ (m + 1) * (cq : ℝ) ^ (2 * m + 7)

lemma T_nonneg (m : ℕ) : 0 ≤ T m := by unfold T; simp only [τq, lamq]; positivity

lemma T_le_G (m : ℕ) : T m ≤ G m := by
  set k := 2 * m + 7 with hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have he := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have he1 : exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have hek : exp (k : ℝ) = exp 1 ^ k := by rw [← Real.exp_nat_mul]; ring_nf
  have hm2 : ((m : ℝ) + 1) ≤ (k : ℝ) / 2 := by rw [hk]; push_cast; linarith
  have hpow : ((m : ℝ) + 1) ^ k ≤ ((k : ℝ) / 2) ^ k :=
    pow_le_pow_left₀ (by positivity) hm2 k
  -- (m+1)^k / k! ≤ (e/2)^k
  have h1 : ((m : ℝ) + 1) ^ k / (k.factorial : ℝ) ≤ (exp 1 / 2) ^ k := by
    rw [div_le_iff₀ hfac]
    calc ((m : ℝ) + 1) ^ k ≤ ((k : ℝ) / 2) ^ k := hpow
      _ = ((k : ℝ) ^ k / k.factorial) * k.factorial / 2 ^ k := by
          rw [div_pow]; field_simp
      _ ≤ exp (k : ℝ) * k.factorial / 2 ^ k := by gcongr
      _ = (exp 1 / 2) ^ k * k.factorial := by rw [hek, div_pow]; ring
  have hτ : (0 : ℝ) ≤ (τq : ℝ) := by simp [τq]; norm_num
  have hc : (τq : ℝ) * (exp 1 / 2) ≤ (cq : ℝ) := by
    simp only [τq, cq]; push_cast; nlinarith [exp_pos 1]
  unfold T G
  rw [← hk, mul_pow, mul_div_assoc]
  have hlam : (0 : ℝ) ≤ (lamq : ℝ) ^ (m + 1) := by simp [lamq]; positivity
  apply mul_le_mul_of_nonneg_left _ hlam
  calc ((m : ℝ) + 1) ^ k * (τq : ℝ) ^ k / (k.factorial : ℝ)
      = (τq : ℝ) ^ k * (((m : ℝ) + 1) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ (τq : ℝ) ^ k * (exp 1 / 2) ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((τq : ℝ) * (exp 1 / 2)) ^ k := by rw [mul_pow]
    _ ≤ (cq : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hc k

def ρ : ℝ := (lamq : ℝ) * (cq : ℝ) ^ 2

lemma ρ_lt : ρ < 1 := by simp [ρ, lamq, cq]; norm_num
lemma ρ_nonneg : 0 ≤ ρ := by simp [ρ, lamq, cq]; positivity

lemma G_eq (m : ℕ) : G m = (lamq : ℝ) * (cq : ℝ) ^ 7 * ρ ^ m := by
  unfold G ρ; rw [mul_pow, ← pow_mul]; ring

lemma G_summable : Summable G := by
  have := (summable_geometric_of_lt_one ρ_nonneg ρ_lt).mul_left ((lamq : ℝ) * (cq : ℝ) ^ 7)
  have e : G = fun i => (lamq : ℝ) * (cq : ℝ) ^ 7 * ρ ^ i := funext G_eq
  rw [e]; exact this

lemma T_summable : Summable T := G_summable.of_nonneg_of_le T_nonneg T_le_G

def K : ℕ := 40

def sumq : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumq n + Tq n

lemma sum_T_eq (n : ℕ) : ∑ i ∈ range n, T i = ((sumq n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [sumq]
  | succ n ih => rw [sum_range_succ, ih, sumq, T_cast]; push_cast; ring

def tailq : ℚ := lamq ^ (K + 1) * cq ^ (2 * K + 7) / (1 - lamq * cq ^ 2)

theorem key_q : sumq K + tailq < 11 / 1000000 := by decide +kernel

lemma tail_le : ∑' i, T (i + K) ≤ ((tailq : ℚ) : ℝ) := by
  have hs : Summable (fun i => T (i + K)) := (summable_nat_add_iff K).mpr T_summable
  have hg : Summable (fun i => G (i + K)) := (summable_nat_add_iff K).mpr G_summable
  have h1 : ∑' i, T (i + K) ≤ ∑' i, G (i + K) := hs.tsum_le_tsum (fun i => T_le_G _) hg
  have h2 : ∑' i, G (i + K) = (lamq : ℝ) * (cq : ℝ) ^ 7 * ρ ^ K * (1 - ρ)⁻¹ := by
    have : (fun i => G (i + K)) = fun i => ((lamq : ℝ) * (cq : ℝ) ^ 7 * ρ ^ K) * ρ ^ i := by
      funext i; rw [G_eq, pow_add]; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one ρ_nonneg ρ_lt]
  have h3 : (lamq : ℝ) * (cq : ℝ) ^ 7 * ρ ^ K * (1 - ρ)⁻¹ = ((tailq : ℚ) : ℝ) := by
    simp only [tailq, ρ, K]; push_cast; rw [div_eq_mul_inv]; ring
  linarith [h1, h2, h3]

/-- **The Brun upper constant for P(N^{1/14})**, Section 2 p. 63, reconstructed formula:
196 (1 + S₇) < 196.0022, where S₇ is the paper's u = 15 series with exponent 2m + 7. -/
theorem brun14_upper_const : 196 * (1 + ∑' m, T m) < 196.0022 := by
  have hsplit := T_summable.sum_add_tsum_nat_add K
  rw [sum_T_eq] at hsplit
  have ht := tail_le
  have hk := (Rat.cast_lt (K := ℝ)).mpr key_q
  push_cast at hk
  have : ∑' m, T m < 11 / 1000000 := by rw [← hsplit]; linarith
  linarith

end LeanLab.AlmostPrimeSums.TogashiUchiyamaBrun14

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaBrun14.brun14_upper_const

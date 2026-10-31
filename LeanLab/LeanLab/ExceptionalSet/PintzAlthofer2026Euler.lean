/-
# Pintz and Althöfer 2026, (4.17): the singular series lower bound, truncated form

Unit U-1129, T2 FRONTIER, idea I-0080, run 20261019T2303Z-16260.

arXiv 2610.15559v1 (4.17): for even n, 𝔖(n) = 2C₂ ∏_{p | n, p > 2} (p−1)/(p−2) ≥ 2C₂ > 0,
C₂ = ∏_{p>2} (1 − 1/(p−1)²). Here the truncation to the divisors of the primorial of P, the
form the lab's Routes/R5060Ramanujan.lean `bS_euler` gives:

  Σ_{d | P#} μ(d)² c_d(n)/φ(d)² = ∏_{p ≤ P} (1 + c_p(n)/(p−1)²) ≥ 2 ∏_{2 < p ≤ P} (1 − 1/(p−1)²),

for every even n and P ≥ 2, `sing_trunc_ge`, and the partial product is positive,
`partial_C2_pos`. The full series and the limit P → ∞ are not taken here.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Routes.R5060Ramanujan

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Euler

open Finset LeanLab.Routes.R5060

/-- The factor `1 − 1/(p−1)²` is in `[0, 1]` for `p ≥ 3`. -/
lemma gT_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  linarith

/-- Local factor bound for an odd prime: `1 + c_p(n)/(p−1)² ≥ 1 − 1/(p−1)²`. -/
lemma local_ge {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (N : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + bS N p := by
  rw [one_add_bS_prime hp]
  split_ifs
  · have h2 : (2 : ℝ) < p := by exact_mod_cast hp3
    have h1 : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

/-- **(4.17), truncated**: for even `N` and `P ≥ 2`, the singular series over the divisors of
`P#` is at least `2 ∏_{2 < p ≤ P} (1 − 1/(p−1)²)`. -/
theorem sing_trunc_ge {N P : ℕ} (hN : Even N) (hP : 2 ≤ P) :
    2 * ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ∑ d ∈ (primorial P).divisors, bS N d := by
  rw [bS_euler]
  have h2mem : 2 ∈ Nat.primesLE P := by
    rw [Nat.primesLE, Nat.mem_primesBelow]; exact ⟨by omega, Nat.prime_two⟩
  rw [← mul_prod_erase _ _ h2mem, one_add_bS_two hN]
  have hset : (Nat.primesLE P).erase 2 = (Nat.primesLE P).filter (2 < ·) := by
    ext p
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hne, hm⟩
      have hp := (Nat.mem_primesBelow.1 hm).2
      exact ⟨hm, lt_of_le_of_ne hp.two_le (Ne.symm hne)⟩
    · rintro ⟨hm, h2⟩; exact ⟨by omega, hm⟩
  rw [hset]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)) (by norm_num)
  · simp only [mem_filter] at hp
    exact gT_nonneg (by omega)
  · simp only [mem_filter] at hp
    exact local_ge (Nat.mem_primesBelow.1 hp.1).2 hp.2 N

/-- The partial twin prime product is positive. -/
theorem partial_C2_pos (P : ℕ) :
    0 < ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  refine prod_pos fun p hp => ?_
  simp only [mem_filter] at hp
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    linarith
  have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  linarith

/-- Vacuity: `N = 4`, `P = 2`: the sum is `2 ≥ 2 · 1`. -/
example : 2 * ∏ p ∈ (Nat.primesLE 2).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
    ∑ d ∈ (primorial 2).divisors, bS 4 d :=
  sing_trunc_ge (by decide) le_rfl

end LeanLab.ExceptionalSet.PintzAlthofer2026Euler

/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file a of three.

The linear sieve machinery behind Chen's theorem, part 1: the Buchstab identity and its
iteration on a finite set, and the linear sieve functions `F`, `f` of Jurkat-Richert, written
in closed form on the ranges `0 < s ≤ 5` for `F` and `0 < s ≤ 4` for `f`:
  `F(s) = 2e^γ/s` (0 < s ≤ 3),  `F(s) = (2e^γ/s)(1 + ∫_2^{s-1} log(t-1)/t dt)` (3 ≤ s ≤ 5),
  `f(s) = 0` (0 < s ≤ 2),       `f(s) = 2e^γ log(s-1)/s` (2 ≤ s ≤ 4),
Halberstam-Richert, Sieve Methods, ch. 8, (8.2.1) to (8.2.4) and Lemma 8.2 and 8.3;
Iwaniec-Kowalski, Analytic Number Theory, Section 6.4 and (11.62), (11.63).
The Lean definitions `Fsieve`, `fsieve` agree with these on the stated ranges; outside them they
are placeholders and nothing here claims the delay-differential equations there.

Numerical values (mpmath, 20 digits): f(3) = 0.82303, f(4) = 0.97835, F(3) = 1.18738,
F(4) = 1.02164, F(5) = 1.00174, ∫_2^3 log(t-1)/t dt = 0.147220677, γ = 0.5772156649.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

namespace LeanLab.AlmostPrimeSums.Decomp1527a
open Finset Real
attribute [local instance] Classical.propDecidable

/-! ### 1. The Buchstab identity on a finite set -/

/-- `S(A, z)`: the number of `n ∈ A` with no prime factor `p < z`. -/
noncomputable def siftCount (A : Finset ℕ) (z : ℝ) : ℕ :=
  #(A.filter fun n => ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n)

/-- The primes `p` with `w ≤ p < z`. -/
noncomputable def primesIco (w z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter fun p => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z

/-- `A_d`, the elements of `A` divisible by `d`. -/
def multiples (A : Finset ℕ) (d : ℕ) : Finset ℕ := A.filter (d ∣ ·)

/-- `S(A, z)` is antitone in `z`. -/
theorem siftCount_anti (A : Finset ℕ) {w z : ℝ} (hwz : w ≤ z) : siftCount A z ≤ siftCount A w := by
  unfold siftCount
  refine Finset.card_le_card fun n hn => ?_
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, fun p hp hpw => hn.2 p hp (lt_of_lt_of_le hpw hwz)⟩

/-- LEAF. Buchstab identity: for `w ≤ z`,
`S(A, w) = S(A, z) + Σ_{w ≤ p < z} S(A_p, p)`; each `n` counted on the left and not in `S(A,z)`
has a least prime factor `p ∈ [w, z)`. Halberstam-Richert ch. 1, (1.4.5) style, and
Iwaniec-Kowalski (6.4) with `P(w, z)`. Unit U-1527. -/
theorem buchstab_identity (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    siftCount A w = siftCount A z + ∑ p ∈ primesIco w z, siftCount (multiples A p) p := by
  sorry

/-- LEAF. Iterated Buchstab identity, two steps: for `w ≤ z`,
`S(A,z) = S(A,w) − Σ_{w≤p<z} S(A_p,w) + Σ_{w≤q<p<z} S(A_{pq},q)`, from `buchstab_identity`
applied to `A` and then to each `A_p` between `w` and `p`, with `(A_p)_q = A_{pq}` for primes
`q < p`. Iwaniec-Kowalski (6.5); Halberstam-Richert ch. 8, proof of Lemma 8.1. Unit U-1527. -/
theorem buchstab_iterated (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A z : ℤ) = siftCount A w - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      + ∑ p ∈ primesIco w z, ∑ q ∈ primesIco w p, (siftCount (multiples A (p * q)) q : ℤ) := by
  sorry

/-- Buchstab lower inequality `S(A,z) ≥ S(A,w) − Σ_{w≤p<z} S(A_p,w)`, from the identity and
`S(A_p, p) ≤ S(A_p, w)`. Proved here from the leaf `buchstab_identity`. -/
theorem buchstab_lower (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A w : ℤ) - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      ≤ siftCount A z := by
  have h := buchstab_identity A w z hwz
  have hle : ∑ p ∈ primesIco w z, (siftCount (multiples A p) p : ℤ)
      ≤ ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hwp : w ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.2.1
    exact_mod_cast siftCount_anti _ hwp
  have h' : (siftCount A w : ℤ) = siftCount A z
      + ∑ p ∈ primesIco w z, (siftCount (multiples A p) p : ℤ) := by exact_mod_cast h
  linarith

/-- Buchstab upper inequality
`S(A,z) ≤ S(A,w) − Σ_{w≤p<z} S(A_p,w) + Σ_{w≤q<p<z} S(A_{pq},w)`, from the leaf
`buchstab_iterated` and monotonicity. -/
theorem buchstab_upper (A : Finset ℕ) (w z : ℝ) (hwz : w ≤ z) :
    (siftCount A z : ℤ) ≤ siftCount A w - ∑ p ∈ primesIco w z, (siftCount (multiples A p) w : ℤ)
      + ∑ p ∈ primesIco w z, ∑ q ∈ primesIco w p, (siftCount (multiples A (p * q)) w : ℤ) := by
  rw [buchstab_iterated A w z hwz]
  gcongr with p hp q hq
  have hwq : w ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2.2.1
  exact_mod_cast siftCount_anti _ hwq

/-- Vacuity of the Buchstab setting: on `A = {1, …, 10}`, `primesIco 2 4 = {2, 3}`. -/
example : (2 : ℕ) ∈ primesIco 2 4 ∧ (3 : ℕ) ∈ primesIco 2 4 := by
  unfold primesIco
  refine ⟨?_, ?_⟩ <;> simp only [Finset.mem_filter, Finset.mem_range] <;>
    refine ⟨?_, by norm_num, by norm_num, by norm_num⟩ <;>
    · rw [show ⌈(4 : ℝ)⌉₊ = 4 by norm_num]; norm_num

/-! ### 2. The linear sieve functions `F` and `f` -/

/-- Jurkat-Richert's upper function `F(s)`, closed form valid for `0 < s ≤ 5`. -/
noncomputable def Fsieve (s : ℝ) : ℝ :=
  if s ≤ 3 then 2 * exp eulerMascheroniConstant / s
  else 2 * exp eulerMascheroniConstant / s * (1 + ∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t)

/-- Jurkat-Richert's lower function `f(s)`, closed form valid for `0 < s ≤ 4`. -/
noncomputable def fsieve (s : ℝ) : ℝ :=
  if s ≤ 2 then 0 else 2 * exp eulerMascheroniConstant * log (s - 1) / s

/-- `f(2) = 0`. -/
theorem fsieve_two : fsieve 2 = 0 := by simp [fsieve]

/-- `F(2) = e^γ`. -/
theorem Fsieve_two : Fsieve 2 = exp eulerMascheroniConstant := by
  rw [Fsieve, if_pos (by norm_num)]; ring

/-- `F(3) = 2e^γ/3`. -/
theorem Fsieve_three : Fsieve 3 = 2 * exp eulerMascheroniConstant / 3 := by
  rw [Fsieve, if_pos le_rfl]

/-- `f(3) = 2e^γ log 2 / 3`. -/
theorem fsieve_three : fsieve 3 = 2 * exp eulerMascheroniConstant * log 2 / 3 := by
  rw [fsieve, if_neg (by norm_num)]; norm_num

/-- `f(4) = e^γ log 3 / 2`. -/
theorem fsieve_four : fsieve 4 = exp eulerMascheroniConstant * log 3 / 2 := by
  rw [fsieve, if_neg (by norm_num)]; norm_num; ring

/-- `F(4) = (e^γ/2)(1 + ∫_2^3 log(t-1)/t dt)`. -/
theorem Fsieve_four : Fsieve 4 = exp eulerMascheroniConstant / 2 *
    (1 + ∫ t in (2 : ℝ)..3, log (t - 1) / t) := by
  rw [Fsieve, if_neg (by norm_num)]
  have : (4 : ℝ) - 1 = 3 := by norm_num
  rw [this]; ring

/-- LEAF. Delay-differential equation of `f`: `(s f(s))' = F(s-1)` for `2 < s < 4`; here
`s f(s) = 2e^γ log(s-1)` and `F(s-1) = 2e^γ/(s-1)`. Halberstam-Richert (8.2.4);
Iwaniec-Kowalski (11.63). Unit U-1527. -/
theorem fsieve_hasDerivAt (s : ℝ) (h2 : 2 < s) (h4 : s < 4) :
    HasDerivAt (fun t => t * fsieve t) (Fsieve (s - 1)) s := by
  sorry

/-- LEAF. Delay-differential equation of `F`: `(s F(s))' = f(s-1)` for `3 < s < 5`, by the
fundamental theorem of calculus for `∫_2^{s-1} log(t-1)/t dt`. Halberstam-Richert (8.2.3);
Iwaniec-Kowalski (11.62). Unit U-1527. -/
theorem Fsieve_hasDerivAt (s : ℝ) (h3 : 3 < s) (h5 : s < 5) :
    HasDerivAt (fun t => t * Fsieve t) (fsieve (s - 1)) s := by
  sorry

/-- LEAF. `f` is continuous on `s > 0`; at `s = 2` both pieces vanish.
Halberstam-Richert ch. 8, Lemma 8.2. Unit U-1527. -/
theorem fsieve_continuousOn : ContinuousOn fsieve (Set.Ioi 0) := by
  sorry

/-- LEAF. `F` is continuous on `s > 0`; at `s = 3` the integral `∫_2^{2}` vanishes.
Halberstam-Richert ch. 8, Lemma 8.2. Unit U-1527. -/
theorem Fsieve_continuousOn : ContinuousOn Fsieve (Set.Ioi 0) := by
  sorry

/-- LEAF. `f` is strictly increasing on `[2, 4]`: `f(2) = 0 < f(s)` for `s > 2`, and
`d/ds (log(s-1)/s) > 0` there since `log(s-1) ≤ log 3 < 4/3 ≤ s/(s-1)`.
Halberstam-Richert ch. 8, Lemma 8.3. Unit U-1527. -/
theorem fsieve_strictMonoOn : StrictMonoOn fsieve (Set.Icc 2 4) := by
  sorry

/-- LEAF. `F` is strictly decreasing on `(0, 5]`: `2e^γ/s` on `(0,3]`, and on `[3,5]`
`s F'(s) = f(s-1) − F(s) < 0` since `f(s-1) ≤ f(4) < 1 < F(5) ≤ F(s)`.
Halberstam-Richert ch. 8, Lemma 8.3. Unit U-1527. -/
theorem Fsieve_strictAntiOn : StrictAntiOn Fsieve (Set.Ioc 0 5) := by
  sorry

/-- LEAF. `F(s) > 1` for `0 < s ≤ 5` (true value `F(5) = 1.00174`).
Halberstam-Richert ch. 8, Lemma 8.3, `F(s) > 1`. Unit U-1527. -/
theorem one_lt_Fsieve (s : ℝ) (h0 : 0 < s) (h5 : s ≤ 5) : 1 < Fsieve s := by
  sorry

/-- LEAF. `f(s) < 1` for `0 < s ≤ 4` (true value `f(4) = 0.97835`), needs `e^γ < 2/log 3`.
Halberstam-Richert ch. 8, Lemma 8.3, `f(s) < 1`. Unit U-1527. -/
theorem fsieve_lt_one (s : ℝ) (h0 : 0 < s) (h4 : s ≤ 4) : fsieve s < 1 := by
  sorry

/-- LEAF. `0.5772 < γ < 0.5773` (`γ = 0.5772156649`), e.g. from
`eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` with an Euler-Maclaurin correction, or from
`eulerMascheroniConstant_eq_neg_integral_log`. numerics,
Mathlib `Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`. Unit U-1527. -/
theorem eulerMascheroni_bounds :
    0.5772 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.5773 := by
  sorry

/-- LEAF. `0.1472 < ∫_2^3 log(t-1)/t dt < 0.1473` (value `0.1472206770`), the integral in
`F(4)`; substitute `u = t - 1` to get `∫_1^2 log u/(u+1) du`. Halberstam-Richert (8.2.3).
Unit U-1527. -/
theorem int_F4_bounds :
    0.1472 < ∫ t in (2 : ℝ)..3, log (t - 1) / t ∧ ∫ t in (2 : ℝ)..3, log (t - 1) / t < 0.1473 := by
  sorry

/-- LEAF. Explicit values of the linear sieve functions at `s = 3, 4`:
`0.822 < f(3) < 0.824`, `0.978 < f(4) < 0.979`, `1.187 < F(3) < 1.188`, `1.021 < F(4) < 1.022`
(true values `0.82303, 0.97835, 1.18738, 1.02164`), from the closed forms
`fsieve_three`, `fsieve_four`, `Fsieve_three`, `Fsieve_four` and the two numeric leaves above.
Halberstam-Richert ch. 8, (8.2.1) to (8.2.4); Iwaniec-Kowalski (11.62), (11.63). Unit U-1527. -/
theorem sieve_values :
    (0.822 < fsieve 3 ∧ fsieve 3 < 0.824) ∧ (0.978 < fsieve 4 ∧ fsieve 4 < 0.979) ∧
    (1.187 < Fsieve 3 ∧ Fsieve 3 < 1.188) ∧ (1.021 < Fsieve 4 ∧ Fsieve 4 < 1.022) := by
  sorry

end LeanLab.AlmostPrimeSums.Decomp1527a

/-
Unit U-1525, run 20261025T2003Z-426, DECOMPOSE. P0066 R. C. Vaughan 1977, On the estimation of
Schnirelman's constant, J. reine angew. Math. 290, 93-108, read from copies/P0066.pdf (page
images 95, 97, 98, 99, 100, 101, 103, 104).

File a of three: the Euler-product constants of Lemma 1 (p. 95) and the arithmetic function g of
(3.3) (p. 97), the inputs of the sieve bound Lemma 8 (file b) and of the second-moment step
(5.10), whose numeric Euler bounds `EulerMassBound` and `EulerMomentBound` in
Vaughan1977Euler.lean are OPEN.

Route as Vaughan runs Schnirelmann's argument, and where each step lives:
* sieve upper bound for the representation count: Lemma 8, OPEN, split in Decomp1525b;
* second moment: Vaughan replaces Schnirelmann's Σ r(n)² by the Hölder moment
  Σ F(n) Π ((p-1)/(p-2))^{11/4}, (5.5)-(5.10); the bookkeeping is PROVED in the folder, the
  numeric Euler inputs (2.11), (2.12) are split here;
* first moment: Lemma 11, Ψ(x) ~ x²/log x, its `DistributionError` is split in Decomp1525c;
* Hölder in place of Cauchy-Schwarz, (5.4)-(5.5): PROVED, Vaughan1977Eq55.lean;
* density to basis: PROVED, Vaughan1977.lean through the lab's Mann theorem.
The classical Cauchy-Schwarz route with explicit constants is already PROVED in the lab's
SchnirelmannGoldbach folder (29920 primes), so it is not decomposed again here.

Only Mathlib and the Mathlib-only module Vaughan1977Eq56 are imported. `Cv` is the same
expression as `LeanLab.ChenExplicit.twinC`, the paper's C of (2.5).

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SchnirelmannBounds.Vaughan1977Eq56

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Decomp1525a
open LeanLab.SchnirelmannBounds.Vaughan1977Eq56

/-- `s(q)`, p. 97: the squarefree kernel `Π_{p | q} p`. -/
def sk (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

/-- The local value `g(p^m)` of (3.3): `0` at `p = 2` and at `m = 1`, else `2^{m-2} p^{-m}`. -/
def gloc (p m : ℕ) : ℝ := if p = 2 ∨ m = 1 then 0 else (2 : ℝ) ^ (m - 2) / (p : ℝ) ^ m

/-- The multiplicative function `g` of (3.3), p. 97, with `g(0) = 0`. -/
def g (d : ℕ) : ℝ := if d = 0 then 0 else ∏ p ∈ d.primeFactors, gloc p (d.factorization p)

/-- `C` of (2.5): `Π_{p>2} p(p-2)/(p-1)² = Π_{p>2} (1 - 1/(p-1)²)`, the lab's `twinC`. -/
def Cv : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `Γ` of (2.3): `Σ_{p>2} log p/(p-1)²`. -/
def Gam : ℝ := ∑' p : {p : ℕ // p.Prime ∧ 2 < p}, Real.log p / ((p : ℝ) - 1) ^ 2

/-- `C₀` of (2.4): `Π_{p>2} (1 + 1/(p^{1/2}(p-2)))`. -/
def C0v : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 + 1 / (Real.sqrt p * ((p : ℝ) - 2)))

theorem gloc_nonneg (p m : ℕ) : 0 ≤ gloc p m := by
  unfold gloc; split_ifs <;> positivity

theorem g_nonneg (d : ℕ) : 0 ≤ g d := by
  unfold g; split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg (fun p _ => gloc_nonneg _ _)

theorem g_one : g 1 = 1 := by simp [g]

/-! ### Leaves: the Euler products of Lemma 1 and of the proof of Lemma 7 -/

/-- LEAF. `Σ_{d ≥ 1} g(d) = C^{-1}`: the Euler product of `g` is
`Π_{p>2} (1 + 1/(p(p-2))) = Π_{p>2} (p-1)²/(p(p-2))`. Vaughan 1977 p. 100, display after
(3.12), "by (3.3) and (2.5), Σ g(d) = C^{-1}". Unit U-1525. -/
theorem hasSum_g : HasSum g (1 / Cv) := by
  sorry

/-- LEAF. (3.12): `Σ_d g(d) log s(d) = Γ Σ_d g(d) = Γ/C`, by writing `log s(d) = Σ_{p|d} log p`
and inverting the order of summation; the local ratio at `p` is `1/(p-1)²`. Vaughan 1977
p. 100, (3.12), with (2.3), (3.3). Unit U-1525. -/
theorem hasSum_g_log : HasSum (fun d => g d * Real.log (sk d)) (Gam / Cv) := by
  sorry

/-- LEAF. (2.8): `Γ < 0.535`. Vaughan 1977 p. 95, Lemma 1; the paper sums to `p ≤ 139` and
bounds the tail by partial summation with `θ(u) < 1.001102u`; summing further and bounding the
tail by `Σ_{n>M} log n/(n-1)²` also works. Unit U-1525. -/
theorem gam_lt : Gam < 0.535 := by
  sorry

/-- LEAF. The Euler product behind (2.4): `Σ_d s(d)^{1/2} g(d) = C₀`, the local factor at
`p > 2` being `1 + p^{1/2}/(p(p-2))`. Vaughan 1977 p. 100, last display, "by (3.3) and (2.4)".
Unit U-1525. -/
theorem hasSum_sqrt_g : HasSum (fun d => Real.sqrt (sk d) * g d) C0v := by
  sorry

/-- LEAF. (2.9): `C₀ < 2.35`. Vaughan 1977 p. 95, Lemma 1: the product over `2 < p ≤ 139` is
below 2.267 and the tail below `exp(0.0358)`. Unit U-1525. -/
theorem C0v_lt : C0v < 2.35 := by
  sorry

/-! ### Assembly: the tail of `Σ g` (Rankin's trick, p. 100) -/

/-- **PROVED from `hasSum_sqrt_g`**: `Σ_{s(d) > z} g(d) ≤ C₀ z^{-1/2}`, Vaughan 1977 p. 100,
last display. -/
theorem tail_le {z : ℝ} (hz : 0 < z) :
    ∑' d, (if z < (sk d : ℝ) then g d else 0) ≤ C0v / Real.sqrt z := by
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hbound : ∀ d, (if z < (sk d : ℝ) then g d else 0) ≤ Real.sqrt (sk d) * g d / Real.sqrt z := by
    intro d
    split_ifs with h
    · rw [le_div_iff₀ hsz]
      have : Real.sqrt z ≤ Real.sqrt (sk d) := Real.sqrt_le_sqrt h.le
      nlinarith [g_nonneg d]
    · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (g_nonneg d)) hsz.le
  have hnn : ∀ d, 0 ≤ (if z < (sk d : ℝ) then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have hs2 : Summable (fun d => Real.sqrt (sk d) * g d / Real.sqrt z) :=
    hasSum_sqrt_g.summable.div_const _
  have hs1 : Summable (fun d => if z < (sk d : ℝ) then g d else 0) :=
    Summable.of_nonneg_of_le hnn hbound hs2
  calc ∑' d, (if z < (sk d : ℝ) then g d else 0)
      ≤ ∑' d, Real.sqrt (sk d) * g d / Real.sqrt z := hs1.tsum_le_tsum hbound hs2
    _ = C0v / Real.sqrt z := by rw [tsum_div_const, hasSum_sqrt_g.tsum_eq]

/-- **PROVED from `hasSum_g` and `tail_le`'s summability**: the split
`Σ_{s(d) ≤ z} g(d) + Σ_{s(d) > z} g(d) = C^{-1}` used on p. 100. -/
theorem split_sum (z : ℝ) :
    (∑' d, (if (sk d : ℝ) ≤ z then g d else 0)) + ∑' d, (if z < (sk d : ℝ) then g d else 0)
      = 1 / Cv := by
  have hle : ∀ d, (if (sk d : ℝ) ≤ z then g d else 0) ≤ g d := by
    intro d; split_ifs
    · exact le_rfl
    · exact g_nonneg d
  have hle' : ∀ d, (if z < (sk d : ℝ) then g d else 0) ≤ g d := by
    intro d; split_ifs
    · exact le_rfl
    · exact g_nonneg d
  have hnn : ∀ d, 0 ≤ (if (sk d : ℝ) ≤ z then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have hnn' : ∀ d, 0 ≤ (if z < (sk d : ℝ) then g d else 0) := by
    intro d; split_ifs
    · exact g_nonneg d
    · exact le_rfl
  have s1 := Summable.of_nonneg_of_le hnn hle hasSum_g.summable
  have s2 := Summable.of_nonneg_of_le hnn' hle' hasSum_g.summable
  rw [← s1.tsum_add s2, ← hasSum_g.tsum_eq]
  congr 1; funext d
  by_cases h : (sk d : ℝ) ≤ z
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-! ### Leaves: the numeric Euler bounds (2.11) and (2.12) -/

/-- LEAF. Head of (2.11): `Π_{p ≤ min(N,1000)} (1 + (((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 6.2083`
for every `N`, the factor at `p = 2` being 1. Numerically the full head to 1000 is
6.20826. Vaughan 1977 p. 96, proof of (2.11), which takes the head to 307 (6.2022 to 6.2023).
Unit U-1525. -/
theorem C1_head (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (· ≤ 1000), (1 + primeWeight p / ((p : ℝ) - 1)) ≤ 6.2083 := by
  sorry

/-- LEAF. Tail of (2.11): `Π_{1000 < p ≤ N} (1 + (((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 1.0007`;
the true value is below 1.00036, the log of the factor is about `2.75/p²`, so Mathlib's
`θ(x) ≤ log 4 · x` with partial summation suffices. Vaughan 1977 p. 96, proof of (2.11), with
(2.13). Unit U-1525. -/
theorem C1_tail (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (fun p => ¬ p ≤ 1000), (1 + primeWeight p / ((p : ℝ) - 1))
      ≤ 1.0007 := by
  sorry

/-- LEAF. Head of (2.12): `Π_{p ≤ min(N,1000)} (1 + p^{3/8}(((p-1)/(p-2))^{11/4} - 1)/(p-1))
≤ 14.17`; numerically the head to 1000 is 14.1644. Vaughan 1977 p. 96, proof of (2.12).
Unit U-1525. -/
theorem C2_head (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (· ≤ 1000),
      (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 14.17 := by
  sorry

/-- LEAF. Tail of (2.12): `Π_{1000 < p ≤ N} (1 + p^{3/8}(((p-1)/(p-2))^{11/4} - 1)/(p-1)) ≤ 1.02`;
the true value is below 1.0071, the log of the factor is about `2.75 p^{-13/8}`. Vaughan 1977
p. 96, proof of (2.12), with (2.13). Unit U-1525. -/
theorem C2_tail (N : ℕ) :
    ∏ p ∈ N.primesLE.filter (fun p => ¬ p ≤ 1000),
      (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 1.02 := by
  sorry

/-! ### Assembly: `EulerMassBound 6.2130` and `EulerMomentBound`, unfolded -/

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs with h2
  · exact le_rfl
  · have h3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hb : 1 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      rw [one_le_div (by linarith)]; linarith
    have := Real.one_le_rpow hb (by norm_num : (0 : ℝ) ≤ 11 / 4)
    linarith

theorem factor_nonneg {p : ℕ} (hp : p.Prime) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ 1 + c * primeWeight p / ((p : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 0 ≤ c * primeWeight p / ((p : ℝ) - 1) :=
    div_nonneg (mul_nonneg hc (primeWeight_nonneg hp)) (by linarith)
  linarith

/-- **(2.11) upper half, PROVED from `C1_head` and `C1_tail`**: for every `N`,
`Π_{p ≤ N} (1 + f(p)/(p-1)) ≤ 6.2130`. This is `Vaughan1977Euler.EulerMassBound 6.2130`
unfolded, the input of `statement27_of_euler` with `C = 6.2130`. -/
theorem eulerMass_62130 (N : ℕ) :
    ∏ p ∈ N.primesLE, (1 + primeWeight p / ((p : ℝ) - 1)) ≤ 6.2130 := by
  rw [← Finset.prod_filter_mul_prod_filter_not N.primesLE (fun p : ℕ => p ≤ 1000)]
  have hnn : ∀ s : Finset ℕ, s ⊆ N.primesLE →
      0 ≤ ∏ p ∈ s, (1 + primeWeight p / ((p : ℝ) - 1)) := by
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp (hs hp)).2
    simpa using factor_nonneg hpp 1 zero_le_one
  have h1 := C1_head N
  have h2 := C1_tail N
  have h0' := hnn (N.primesLE.filter (fun p : ℕ => ¬ p ≤ 1000)) (Finset.filter_subset _ _)
  calc _ ≤ 6.2083 * 1.0007 := mul_le_mul h1 h2 h0' (by norm_num)
    _ ≤ 6.2130 := by norm_num

/-- **(2.12), PROVED from `C2_head` and `C2_tail`**: for every `N`,
`Π_{p ≤ N} (1 + p^{3/8} f(p)/(p-1)) ≤ 14.46`. This is `Vaughan1977Euler.EulerMomentBound`
unfolded. -/
theorem eulerMoment_1446 (N : ℕ) :
    ∏ p ∈ N.primesLE, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 14.46 := by
  rw [← Finset.prod_filter_mul_prod_filter_not N.primesLE (fun p : ℕ => p ≤ 1000)]
  have hnn : ∀ s : Finset ℕ, s ⊆ N.primesLE →
      0 ≤ ∏ p ∈ s, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) := by
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp (hs hp)).2
    exact factor_nonneg hpp _ (by positivity)
  have h1 := C2_head N
  have h2 := C2_tail N
  have h0' := hnn (N.primesLE.filter (fun p : ℕ => ¬ p ≤ 1000)) (Finset.filter_subset _ _)
  calc _ ≤ 14.17 * 1.02 := mul_le_mul h1 h2 h0' (by norm_num)
    _ ≤ 14.46 := by norm_num

end LeanLab.SchnirelmannBounds.Decomp1525a

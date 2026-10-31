/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1515Z-cloud27, unit U-5654, route R-5070.

# Two-dimensional Chebyshev certificates for the Goldbach count

`G N = Σ_{a + b = N} Λ(a) Λ(b)` and `D N j k = Σ_{j a + k b = N} log a · log b`, written over the
antidiagonal `u + v = N` with `j ∣ u`, `k ∣ v`, `a = u / j`, `b = v / k`.

* `goldbach_moebius`: the exact identity `G N = Σ_{j, k ≤ N} μ(j) μ(k) D N j k`, from `Λ = μ * log`.
  Chebyshev's method in one variable truncates the Möbius weights of `ψ = Σ μ(d) log ⌊x/d⌋!` to a
  finite weight; this is the binary analogue.
* `certificate_sound`: a finite weight `c` on pairs `(j, k)` whose response
  `U(d, e) = Σ c_{jk} #{(m, n) : j d m + k e n = N}` is at most `[d + e = N]` on every pair gives
  `Σ c_{jk} D_w(j, k) ≤ G_w` for every nonnegative weight `w` on pairs. So a fake `w ≥ 0` with no
  mass on `d + e = N` and the same data forces every such certificate bound to be `≤ 0`;
  `certificate_le_zero_of_fake`. The LP in `numerics/r5070_cheb2d.py` finds such `w` with at most
  `J²` atoms for every tested `N ≤ 210`, `J ≤ 6`.

KNOWN mathematics in substance; the identity is Möbius inversion. Not progress on Goldbach,
which is OPEN.
-/
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.Routes.R5070

/-- The weighted Goldbach count `Σ_{a + b = N} Λ(a) Λ(b)`. -/
def G (N : ℕ) : ℝ := ∑ x ∈ antidiagonal N, Λ x.1 * Λ x.2

/-- The dilated log data `Σ_{j a + k b = N} log a · log b`, as a sum over `u + v = N`. -/
def D (N j k : ℕ) : ℝ :=
  ∑ x ∈ antidiagonal N, if j ∣ x.1 ∧ k ∣ x.2 then
    Real.log ((x.1 / j : ℕ) : ℝ) * Real.log ((x.2 / k : ℕ) : ℝ) else 0

/-- `Λ u = Σ_{j ≤ N, j ∣ u} μ(j) log(u / j)` for `u ≤ N`. -/
lemma vonMangoldt_eq_sum {u N : ℕ} (hu : u ≤ N) :
    Λ u = ∑ j ∈ Icc 1 N, if j ∣ u then (μ j : ℝ) * Real.log ((u / j : ℕ) : ℝ) else 0 := by
  rcases Nat.eq_zero_or_pos u with h0 | hpos
  · subst h0; simp
  rw [← moebius_mul_log_eq_vonMangoldt, mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => ((μ : ArithmeticFunction ℝ) a) * (log b)), ← sum_filter]
  apply sum_subset
  · intro j hj
    rw [Nat.mem_divisors] at hj
    rw [mem_filter, mem_Icc]
    exact ⟨⟨Nat.pos_of_dvd_of_pos hj.1 hpos, (Nat.le_of_dvd hpos hj.1).trans hu⟩, hj.1⟩
  · intro j hj hnot
    rw [mem_filter] at hj
    exact absurd (Nat.mem_divisors.mpr ⟨hj.2, hpos.ne'⟩) hnot

/-- **The exact identity.** `G N = Σ_{j, k ≤ N} μ(j) μ(k) D N j k`. -/
theorem goldbach_moebius (N : ℕ) :
    G N = ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (μ j : ℝ) * μ k * D N j k := by
  unfold G D
  have hx : ∀ x ∈ antidiagonal N, x.1 ≤ N ∧ x.2 ≤ N := by
    intro x hx; rw [HasAntidiagonal.mem_antidiagonal] at hx; omega
  rw [sum_congr rfl (fun x h => by
    rw [vonMangoldt_eq_sum (hx x h).1, vonMangoldt_eq_sum (hx x h).2, sum_mul_sum])]
  rw [sum_comm]
  apply sum_congr rfl; intro j _
  rw [sum_comm]
  apply sum_congr rfl; intro k _
  rw [mul_sum]
  apply sum_congr rfl; intro x _
  by_cases hj : j ∣ x.1 <;> by_cases hk : k ∣ x.2 <;> simp [hj, hk] <;> ring

/-- Solutions of `x m + y n = N` in positive integers. -/
def R (N x y : ℕ) : ℕ := ((Icc 1 N ×ˢ Icc 1 N).filter (fun p => x * p.1 + y * p.2 = N)).card

/-- The response of a certificate `c` at a pair `(d, e)`. -/
def U (N : ℕ) (P : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℝ) (d e : ℕ) : ℝ :=
  ∑ q ∈ P, c q * R N (q.1 * d) (q.2 * e)

/-- The data of a weight `w` on pairs: `D_w(j, k) = Σ_{(d,e)} w(d, e) R(jd, ke)`. -/
def Dw (N : ℕ) (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (q : ℕ × ℕ) : ℝ :=
  ∑ x ∈ S, w x * R N (q.1 * x.1) (q.2 * x.2)

/-- The Goldbach mass of a weight: `Σ_{d + e = N} w(d, e)`. -/
def Gw (N : ℕ) (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) : ℝ :=
  ∑ x ∈ S, if x.1 + x.2 = N then w x else 0

/-- **Certificate soundness, weak duality.** If `U(d, e) ≤ [d + e = N]` on the support `S` and
`w ≥ 0` on `S`, then `Σ_q c_q D_w(q) ≤ G_w`. -/
theorem certificate_sound (N : ℕ) (P S : Finset (ℕ × ℕ)) (c w : ℕ × ℕ → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hU : ∀ x ∈ S, U N P c x.1 x.2 ≤ if x.1 + x.2 = N then 1 else 0) :
    ∑ q ∈ P, c q * Dw N S w q ≤ Gw N S w := by
  unfold Dw Gw
  calc ∑ q ∈ P, c q * ∑ x ∈ S, w x * R N (q.1 * x.1) (q.2 * x.2)
      = ∑ x ∈ S, w x * U N P c x.1 x.2 := by
        unfold U; simp only [mul_sum]; rw [sum_comm]
        apply sum_congr rfl; intro x _; apply sum_congr rfl; intro q _; ring
    _ ≤ ∑ x ∈ S, w x * (if x.1 + x.2 = N then 1 else 0) := by
        apply sum_le_sum; intro x hx
        exact mul_le_mul_of_nonneg_left (hU x hx) (hw x hx)
    _ = _ := by apply sum_congr rfl; intro x _; split_ifs <;> simp

/-- **The barrier.** If a fake weight `w' ≥ 0` has no mass on `d + e = N` and the same data as
`w` at every `q ∈ P`, every certificate bound for `w` is `≤ 0`. -/
theorem certificate_le_zero_of_fake (N : ℕ) (P S : Finset (ℕ × ℕ)) (c w w' : ℕ × ℕ → ℝ)
    (hw' : ∀ x ∈ S, 0 ≤ w' x) (hfake : Gw N S w' = 0)
    (hdata : ∀ q ∈ P, Dw N S w q = Dw N S w' q)
    (hU : ∀ x ∈ S, U N P c x.1 x.2 ≤ if x.1 + x.2 = N then 1 else 0) :
    ∑ q ∈ P, c q * Dw N S w q ≤ 0 := by
  rw [sum_congr rfl (fun q hq => by rw [hdata q hq])]
  exact (certificate_sound N P S c w' hw' hU).trans hfake.le

/-- Vacuity test of the definitions: `G 4 = Λ(2)² = (log 2)²`, the one partition `2 + 2`. -/
example : G 4 = Real.log 2 * Real.log 2 := by
  unfold G
  rw [show antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} by decide]
  simp [vonMangoldt_apply_prime Nat.prime_two]

end LeanLab.Routes.R5070

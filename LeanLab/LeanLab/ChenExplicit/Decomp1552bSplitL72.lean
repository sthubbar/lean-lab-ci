/-
AI wrote the Lean code. Claude, session S88, burst-20261122, OMOS FEED.
Yamada arXiv 1511.03409v2, Section 7, Lemma 7.2 eq 99, proof eqs 100 to 104, printed pages 22 to 24.
Split of `D1552.lemma72` through the conductor sectors of `Decomp324.discrepancy_le_sectors`.
The small conductor sector of eqs 101 and 102 is split into two new LEAFs:
* `small_cond_prime_sum`: the choice of the exceptional prime and the explicit
  Siegel-Walfisz bound for prime sums twisted by primitive characters of small conductor;
* `small_sector_of_prime_sum`: the bookkeeping over moduli and conductors turning that
  bound into the sector allowance.
The large conductor sector stays the existing LEAF `Decomp324.large_conductor_sector`.
`lemma72_of_leaves` has exactly the statement of `D1552.lemma72` and no sorry of its own.
It is CONDITIONAL ON the LEAFs. Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Decomp324a

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.Split1552bL72
open D1552 Decomp324

/-- LEAF: Yamada 2015, Lemma 7.2 proof, eqs 101 and 102, page 23, from Corollary 2.4 and the
explicit zero free region with one exceptional modulus `k₁` whose largest prime factor is `q₁`,
eq 46. For even `N > exp exp 36` there is an admissible `q₁` such that for every `Y, Z` in the
range of Lemma 7.2 and every nonprincipal primitive character `χ` of conductor `r < log¹⁰ Y`
with `q₁ ∤ r`, the twisted prime sum over `Z ≤ p < Y` is at most `e^{-147} Y / log¹⁶ Y`.
The true bound is of size `Y exp(-c √log Y)`, far smaller since `log Y > e^36 / 8`. Class HARD. -/
theorem small_cond_prime_sum (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, Adm N q₁ ∧
      ∀ (Y Z : ℝ), z8 N < Y → Y ≤ 2 * N → z8 N ≤ Z →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ≠ 1 →
          (r : ℝ) < log Y ^ 10 → ¬ q₁ ∣ r →
          ‖∑ p ∈ primesIco Z Y, χ (p : ZMod r)‖ ≤ exp (-147) * Y / log Y ^ 16 := by
  sorry

/-- LEAF: Yamada 2015, Lemma 7.2 proof, eq 100 and the sum over small conductors before eq 103,
pages 23 and 24. Given the prime sum bound of `small_cond_prime_sum` for `q₁`, the small
conductor sector mass is at most `e^{-146} XY / log⁴ Y`. Route: factor by
`productCharSum_factor`, bound the `n` sum by `X` using `|c n| ≤ 1`, pass from each character
mod `d` to the primitive character inducing it, losing at most `log₂ d` primes dividing `d`,
group the moduli `d < D*` by conductor `r < log¹⁰ Y`, with at most `φ(r)` primitive characters
mod `r` and `Σ_{d < D*, r ∣ d} 1/φ(d) ≤ 3(log D* + 1)/φ(r)`, and use `log D* ≤ 5 log Y` from
`XY < 2N`, `Y > N^{1/8}`. The resulting `16 e^{-147} XY/log⁵ Y + 160 X log¹² Y` fits. Class MEDIUM. -/
theorem small_sector_of_prime_sum (N : ℕ) (hN : exp (exp 36) < N) (q₁ : ℕ)
    (hP : ∀ (Y Z : ℝ), z8 N < Y → Y ≤ 2 * N → z8 N ≤ Z →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ≠ 1 →
          (r : ℝ) < log Y ^ 10 → ¬ q₁ ∣ r →
          ‖∑ p ∈ primesIco Z Y, χ (p : ZMod r)‖ ≤ exp (-147) * Y / log Y ^ 16)
    (c : ℕ → ℝ) (X Y Z : ℝ) (hc : ∀ n, |c n| ≤ 1)
    (hX : log Y ^ 10 < X) (hXupper : X ≤ N / z8 N) (hXY : X * Y < 2 * N)
    (hY : z8 N < Y) (hZ : z8 N ≤ Z) :
    sectorMass true q₁ c X Y Z ≤ exp (-146) * X * Y / log Y ^ 4 := by
  sorry

/-- The small conductor sector of `Decomp324`, assembled from the two new LEAFs.
CONDITIONAL ON `small_cond_prime_sum` and `small_sector_of_prime_sum`. -/
theorem small_conductor_sector_of_leaves (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, D1552.Adm N q₁ ∧
      ∀ (c : ℕ → ℝ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
        log Y ^ 10 < X → X ≤ N / D1552.z8 N → X * Y < 2 * N →
        D1552.z8 N < Y → D1552.z8 N ≤ Z →
        sectorMass true q₁ c X Y Z ≤ exp (-146) * X * Y / log Y ^ 4 := by
  obtain ⟨q₁, hq, hP⟩ := small_cond_prime_sum N hE hN
  exact ⟨q₁, hq, fun c X Y Z hc hX hXu hXY hY hZ =>
    small_sector_of_prime_sum N hN q₁ hP c X Y Z hc hX hXu hXY hY hZ⟩

/-- Exact statement of `D1552.lemma72`. CONDITIONAL ON `small_cond_prime_sum`,
`small_sector_of_prime_sum` and the existing LEAF `Decomp324.large_conductor_sector`. -/
theorem lemma72_of_leaves (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, Adm N q₁ ∧ ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z := by
  obtain ⟨q₁, hq, hs⟩ := small_conductor_sector_of_leaves N hE hN
  refine ⟨q₁, hq, ?_⟩
  intro c res X Y Z hc hres hX hXupper hXY hY hZ
  have hXp : 0 ≤ X := (by positivity : 0 ≤ log Y ^ 10).trans hX.le
  have hYp : 0 ≤ Y := (rpow_nonneg (Nat.cast_nonneg N) _).trans hY.le
  unfold Lemma72At
  calc
    _ ≤ sectorMass true q₁ c X Y Z + sectorMass false q₁ c X Y Z :=
      discrepancy_le_sectors q₁ c res X Y Z hres
    _ ≤ exp (-146) * X * Y / log Y ^ 4 + 2 * exp (-145) * X * Y / log Y ^ 4 :=
      add_le_add (hs c X Y Z hc hX hXupper hXY hY hZ)
        (large_conductor_sector N hE hN q₁ c X Y Z hc hX hXupper hXY hY hZ)
    _ ≤ _ := sector_budget X Y hXp hYp

end LeanLab.ChenExplicit.Split1552bL72

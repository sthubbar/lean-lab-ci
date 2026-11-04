import LeanLab.GoldbachAverage.BSPDecomp82

/-!
P0050 pages 4 and 5, the primorial progression argument for large G values.
The progression estimate and the finite averaging are separate OPEN leaves.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp287c
open Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The von Mangoldt mass in one residue class in the window x less than n at most two x.
P0050 page 5, the character window before the display defining S. -/
def progressionMass (x q a : ℕ) : ℝ :=
  ∑ n ∈ (Ioc x (2 * x)).filter (fun n => n % q = a), Λ n

/-- The finite primorial construction on P0050 page 5.
The prime premise is explicit in the scope of the divisor equivalence. -/
theorem finite_primorial (h : ℝ) (q₁ : ℕ) :
  ∃ q : ℕ, q > 0 ∧ (∀ p : ℕ, Nat.Prime p → (p ∣ q ↔ p < h ∧ p ≠ q₁)) := by
  let S := (range ⌈h⌉₊).filter (fun p => Nat.Prime p ∧ p ≠ q₁)
  refine ⟨∏ p ∈ S, p, Finset.prod_pos (fun p hp => (mem_filter.mp hp).2.1.pos), ?_⟩
  intro p hp
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨r, hr, hpr⟩
    obtain ⟨hrange, hrprime, hrne⟩ := mem_filter.mp hr
    have hpr_eq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrprime).mp hpr
    subst r
    exact ⟨Nat.lt_ceil.mp (mem_range.mp hrange), hrne⟩
  · rintro ⟨hph, hpne⟩
    exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hph), hp, hpne⟩, dvd_rfl⟩

/-- A source encoding check for the old primorial_exists declaration.
At h zero and excluded index zero its unparenthesized implication makes it false.
This is a Lean statement mismatch, not an assertion that the paper is wrong. -/
theorem old_primorial_zero_impossible :
    ¬ ∃ q : ℕ, q > 0 ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ q ↔ (p : ℝ) < 0 ∧ p ≠ 0) := by
  rintro ⟨q, _, hq⟩
  have hzero := (hq 0).mp (fun hp => (Nat.not_prime_zero hp).elim)
  norm_num at hzero

/-- LEAF. P0050 pages 4 and 5, Gallagher Theorem 7 and the primorial construction.
The exceptional prime is omitted from q. Mertens gives q over phi q of log log size.
Choose x a fixed sufficiently large power of q so the character estimate applies.
The window estimate is weakened to one half of its main term. -/
theorem primorial_progression_supply :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ x q : ℕ,
      B ≤ x ∧ 2 ≤ x ∧ 0 < q ∧ q ≤ x ∧
      c * Real.log (Real.log (4 * (x : ℝ))) ≤ (q : ℝ) / Nat.totient q ∧
      ∀ a : ℕ, a < q → Nat.Coprime a q →
        (x : ℝ) / (2 * Nat.totient q) ≤ progressionMass x q a := by
  sorry

/-- LEAF. P0050 page 5, the pair count and averaging displays following S.
Pairs in complementary coprime residue classes sum to a multiple of q.
There are at most a constant times x over q such multiples in the pair window.
The constant sixteen leaves room for all integer endpoint terms. -/
theorem progression_pair_average (x q : ℕ) (hx : 2 ≤ x) (hq : 0 < q) (hqx : q ≤ x)
    (hAP : ∀ a : ℕ, a < q → Nat.Coprime a q →
      (x : ℝ) / (2 * Nat.totient q) ≤ progressionMass x q a) :
    ∃ N : ℕ, 2 * x < N ∧ N ≤ 4 * x ∧
      (x : ℝ) * q / (16 * Nat.totient q) ≤ G N := by
  sorry

/-- The exact large_G statement follows from the progression supply and finite averaging.
CONDITIONAL ON primorial_progression_supply and progression_pair_average. -/
theorem large_G_assembled : ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    c * N * Real.log (Real.log N) ≤ G N := by
  obtain ⟨c, hc, hs⟩ := primorial_progression_supply
  refine ⟨c / 64, by positivity, ?_⟩
  intro B
  obtain ⟨x, q, hBx, hx, hq, hqx, hratio, hAP⟩ := hs B
  obtain ⟨N, hNlo, hNhi, hGN⟩ := progression_pair_average x q hx hq hqx hAP
  refine ⟨N, by omega, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNx : (N : ℝ) ≤ 4 * x := by exact_mod_cast hNhi
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogs : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (4 * (x : ℝ))) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hNx)
  have hratioN : c * Real.log (Real.log (N : ℝ)) ≤ (q : ℝ) / Nat.totient q :=
    (mul_le_mul_of_nonneg_left hlogs hc.le).trans hratio
  have hR : 0 ≤ (q : ℝ) / Nat.totient q := by positivity
  calc c / 64 * N * Real.log (Real.log N) =
        (N : ℝ) * (c * Real.log (Real.log N)) / 64 := by ring
    _ ≤ (N : ℝ) * ((q : ℝ) / Nat.totient q) / 64 := by gcongr
    _ ≤ (4 * (x : ℝ)) * ((q : ℝ) / Nat.totient q) / 64 := by gcongr
    _ = (x : ℝ) * q / (16 * Nat.totient q) := by ring
    _ ≤ G N := hGN

example : type_of% BSPDecomp82.large_G = type_of% large_G_assembled := rfl

end LeanLab.GoldbachAverage.Decomp287c

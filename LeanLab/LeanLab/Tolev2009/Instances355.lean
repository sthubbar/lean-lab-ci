/-
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 16 to 19 and Tolev 2009 page 3.
These instances check arithmetic content and nonempty analytic parameter ranges.
-/
import LeanLab.Tolev2009.Decomp355a
import LeanLab.Tolev2009.Gcd355
import LeanLab.Tolev2009.Instances336

open Finset Real
namespace LeanLab.Tolev2009.Instances355
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314b LeanLab.Tolev2009.Decomp355a

/-- Halupczok page 18, the common and pairwise gcd envelope has a positive unit instance. -/
theorem unit_rawWeight : rawWeight (fun _ => 1) = 1 := by
  norm_num [rawWeight, gcdWeight, Fin.prod_univ_three]

/-- Halupczok page 18, the first coefficient is one for every N at unit moduli. -/
theorem unit_weightedCoeff_one (N : ℕ) :
    weightedCoeff (fun _ => 1) (fun _ => 1) N 1 = 1 := by
  rw [weightedCoeff_one _ _ N (by simp) (by simp)]
  norm_num [phiProduct]

/-- Halupczok pages 15 to 16, the prime two coefficient is one for odd N at unit moduli. -/
theorem unit_ssTerm_two (N : ℕ) (hN : Odd N) :
    ssTerm (fun _ => 1) (fun _ => 1) N 2 = 1 := by
  have hhalf : ee ((1 : ℝ) / 2) = -1 := by
    unfold ee
    convert Complex.exp_pi_mul_I using 1 <;> push_cast <;> congr 1 <;> ring
  have hphase : ee (-((N : ℝ) / 2)) = -1 := by
    obtain ⟨r, hr⟩ := hN
    rw [hr]
    have he : -(((2 * r + 1 : ℕ) : ℝ) / 2) = ((-(r : ℤ) : ℤ) : ℝ) + (-(1 : ℝ) / 2) := by
      push_cast
      ring
    rw [he, ee_add, ee_int, one_mul]
    unfold ee
    convert Complex.exp_neg_pi_mul_I using 1 <;> push_cast <;> congr 1 <;> ring
  simp only [one_div] at hhalf
  have hr : range 2 = ({0, 1} : Finset ℕ) := by decide
  simp [ssTerm, localSum, liftRes, hr, hhalf, hphase, Finset.sum_filter]
  <;> norm_num

/-- Halupczok page 16, the first absolute moment has a nonzero prime two contribution. -/
theorem unit_weightedCoeff_two (N : ℕ) (hN : Odd N) :
    weightedCoeff (fun _ => 1) (fun _ => 1) N 2 = 2 := by
  norm_num [weightedCoeff, unit_ssTerm_two N hN, phiProduct]

/-- Halupczok pages 16 to 18, a summable unit modulus first moment is at least three. -/
theorem unit_mass_lower (N : ℕ) (hN : Odd N)
    (hs : Summable (fun q : ℕ => weightedCoeff (fun _ => 1) (fun _ => 1) N q)) :
    3 ≤ coefficientMass (fun _ => 1) (fun _ => 1) N := by
  have hh := hs.sum_le_tsum {1, 2}
    (fun q _ => weightedCoeff_nonneg (fun _ => 1) (fun _ => 1) N q)
  simpa only [coefficientMass, sum_insert (by norm_num : (1 : ℕ) ∉ ({2} : Finset ℕ)), sum_singleton,
    unit_weightedCoeff_one N, unit_weightedCoeff_two N hN, show (1 : ℝ) + 2 = 3 by norm_num] using hh

/-- Halupczok page 16, the first finite Euler comparison is an equality. -/
theorem finite_euler_one (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    (∑ q ∈ Icc (1 : ℕ) 1, (q : ℝ) * ‖ssTerm k l N q‖) = primeProduct k l N 1 := by
  have hr : range 2 = ({0, 1} : Finset ℕ) := by decide
  simp [primeProduct, hr, ssTerm_one hk hl, Finset.prod_filter]
  <;> norm_num

/-- Halupczok page 18, the local bound hypotheses have a nonzero fixed instance. -/
theorem local_parameters :
    Odd 7 ∧ (∀ i : Fin 3, 1 ≤ (fun _ => 1 : Fin 3 → ℕ) i) ∧
      (∀ i : Fin 3, Nat.Coprime ((fun _ => 1 : Fin 3 → ℕ) i) 1) ∧
      (7 : ℝ) ≤ 7 ∧ (∀ i : Fin 3, ((fun _ => 1 : Fin 3 → ℕ) i : ℝ) ≤ 7) ∧
      1 ≤ Real.log (7 : ℝ) ∧ primeProduct (fun _ => 1) (fun _ => 1) 7 1 = 1 := by
  have hL : 1 ≤ Real.log (7 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hr : range 2 = ({0, 1} : Finset ℕ) := by decide
  simp [primeProduct, hr, hL, Finset.prod_filter]
  <;> norm_num

/-- Halupczok pages 18 to 19, a concrete nontrivial seven factor reconstruction. -/
theorem gcd_factors_instance :
    12 = 6 * 1 * 1 * 2 ∧ 18 = 6 * 1 * 1 * 3 ∧ 30 = 6 * 1 * 1 * 5 ∧
      Nat.gcd 12 18 = 6 * 1 ∧ Nat.gcd 12 30 = 6 * 1 ∧ Nat.gcd 18 30 = 6 * 1 ∧
      Nat.gcd (Nat.gcd 12 18) 30 = 6 := by
  norm_num

/-- Halupczok pages 18 to 19, the finite reindexing weights agree at the unit cube. -/
theorem unit_cube_instance :
    (∑ a ∈ Icc (1 : ℕ) 1, ∑ b ∈ Icc (1 : ℕ) 1, ∑ c ∈ Icc (1 : ℕ) 1,
      rawWeight ![a, b, c] / ((a : ℝ) * b * c)) =
      (∑ d ∈ Icc (1 : ℕ) 1, (d.divisors.card : ℝ) ^ 12 / d) *
        (∑ a ∈ Icc (1 : ℕ) 1, (a.divisors.card : ℝ) ^ 8 / a) ^ 3 *
        (∑ e ∈ Icc (1 : ℕ) 1, (e.divisors.card : ℝ) ^ 4 / e) ^ 3 := by
  norm_num [rawWeight, gcdWeight, Fin.prod_univ_three]

/-- Tolev page 3 and Halupczok page 18, the exact mean hypotheses hold at arbitrary scales.
The actual third cutoff is positive and the first coefficient is one. -/
theorem large_odd_instances (A : ℝ) (hA : 10000 ≤ A) (T : ℝ) :
    ∃ N : ℕ, Odd N ∧ T ≤ N ∧ 1 ≤ Real.log N ∧
      1 ≤ Dyadic.cutoff3 (10000 * A) N ∧
      weightedCoeff (fun _ => 1) (fun _ => 1) N 1 = 1 := by
  obtain ⟨N, hodd, hNT, hL, hK, hα⟩ := Instances336.minor_arc_instances A hA T
  exact ⟨N, hodd, hNT, by linarith, hK, unit_weightedCoeff_one N⟩

end LeanLab.Tolev2009.Instances355

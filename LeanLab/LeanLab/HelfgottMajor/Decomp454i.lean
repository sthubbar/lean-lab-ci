import LeanLab.HelfgottMajor.Decomp454f

/-!
The ordinary cumulative count suffices for zero shift tail convergence.
Source P0014 page 38 display 4.26 and page 41 display 4.33.
The count theorem remains a cited input. No signed discrepancy cancellation is used.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454i
open Real Decomp454d ZeroCount1623

/-- A high unit shell contributes at most the cumulative strip multiplicity count.
Derived bookkeeping for P0014 page 38 display 4.26.
-/
theorem tail_shell_count_le_strip_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (n : ℕ) :
    (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n}, (mult χ ρ.val.val : ℝ)) ≤
      ∑' ρ : ZeroIdx χ ((n : ℝ) + 1), (mult χ ρ.val : ℝ) := by
  classical
  let j : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} → ZeroIdx χ ((n : ℝ) + 1) :=
    fun ρ => ⟨ρ.val.val, ρ.val.property.1, ρ.val.property.2.1, ρ.val.property.2.2.1, by
      have h := Nat.lt_floor_add_one |ρ.val.val.im|
      rw [ρ.property] at h
      exact h.le⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZeroIdx χ ((n : ℝ) + 1) => z.val) h
  have hs : Summable (fun ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} =>
      (mult χ ρ.val.val : ℝ)) := by
    let : Fintype {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} := (tail_shell_finite χ T n).fintype
    exact (hasSum_fintype _).summable
  exact hs.tsum_le_tsum_of_inj j hj (fun _ _ => Nat.cast_nonneg _)
    (fun _ => le_rfl) (summable_zeroIdx χ ((n : ℝ) + 1) _)

/-- A coarse quadratic majorant for the ordinary count budget in P0014 display 4.26.
This elementary bound is for convergence only.
-/
theorem classical_count_budget_le_quadratic (q U : ℝ) (hq : 1 ≤ q) (hU : 1 ≤ U) :
    U / π * log (q * U / (2 * π * exp 1)) + 0.5 * log (q * U) + 17.7 ≤
      (2 * q + 18) * U ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hU0 : 0 < U := by linarith
  have hlog : log (q * U) ≤ q * U := by
    linarith [log_le_sub_one_of_pos (mul_pos hq0 hU0)]
  have hratio : q * U / (2 * π * exp 1) ≤ q * U := by
    apply div_le_self (by positivity)
    nlinarith [pi_gt_three, Real.add_one_le_exp (1 : ℝ), exp_pos (1 : ℝ)]
  have hlogratio : log (q * U / (2 * π * exp 1)) ≤ q * U :=
    (log_le_log (by positivity) hratio).trans hlog
  have hdiv : U / π ≤ U := div_le_self hU0.le (by linarith [pi_gt_three])
  have hmain : U / π * log (q * U / (2 * π * exp 1)) ≤ q * U ^ 2 := by
    calc U / π * log (q * U / (2 * π * exp 1)) ≤ U / π * (q * U) :=
      mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ ≤ U * (q * U) := mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = q * U ^ 2 := by ring
  have hqgrowth : 0 ≤ q * (U ^ 2 - U) := mul_nonneg hq0.le (by nlinarith)
  have hU2 : 1 ≤ U ^ 2 := by nlinarith
  nlinarith [mul_nonneg hq0.le (sq_nonneg U)]

/-- The classical cumulative count implies the polynomial shell count needed for convergence.
CONDITIONAL ON hstrip, the upper side of P0014 page 38 display 4.26.
-/
theorem polynomial_shell_count_of_strip_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hstrip : ∀ U : ℝ, 1 ≤ U →
      (∑' ρ : ZeroIdx χ U, (mult χ ρ.val : ℝ)) ≤
        U / π * log ((q : ℝ) * U / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * U) + 17.7) :
    ∀ n : ℕ, (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n},
      (mult χ ρ.val.val : ℝ)) ≤ (2 * (q : ℝ) + 18) * ((n : ℝ) + 1) ^ 2 := by
  intro n
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hU : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hnat : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact (tail_shell_count_le_strip_count χ T n).trans
    ((hstrip _ hU).trans (classical_count_budget_le_quadratic q _ hq hU))

/-- Zero shift high Mellin mass convergence uses only the classical cumulative count.
CONDITIONAL ON hstrip, P0014 display 4.26. The Mellin decay is proved independently.
This proves no sharp tail integral estimate from display 4.35.
-/
theorem tail_mass_zero_shift_summable_of_strip_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 1 ≤ T)
    (hstrip : ∀ U : ℝ, 1 ≤ U →
      (∑' ρ : ZeroIdx χ U, (mult χ ρ.val : ℝ)) ≤
        U / π * log ((q : ℝ) * U / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * U) + 17.7) :
    Summable (fun ρ : TailZero χ T => Decomp269b.mellinMassTerm χ 0 ρ.val) := by
  exact Decomp454f.tail_mass_zero_shift_summable_of_shell_count χ T (2 * (q : ℝ) + 18)
    hT (by positivity) (polynomial_shell_count_of_strip_count χ T hstrip)

end LeanLab.HelfgottMajor.Decomp454i

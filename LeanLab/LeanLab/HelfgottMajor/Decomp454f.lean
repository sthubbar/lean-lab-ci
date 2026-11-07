import LeanLab.HelfgottMajor.Decomp454d
import LeanLab.HelfgottMajor.Decomp454e
import Mathlib.Analysis.PSeries

/-!
Unshifted high mass convergence from a coarse zero count alone.
Source P0014 page 29 before display 3.76 and page 41 display 4.33.
This closes only convergence at zero shift under the stated count input.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454f
open Real Decomp269b Decomp454d

/-- The zero shift high Mellin mass converges under a polynomial shell count.
CONDITIONAL ON hcount. The Mellin decay is proved by Gamma recurrence rather than assumed.
Source P0014 page 29 before display 3.76 and page 41 display 4.33.
-/
theorem tail_mass_zero_shift_summable_of_shell_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T C : ℝ) (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hcount : ∀ n : ℕ,
      (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) ≤
          C * ((n : ℝ) + 1) ^ 2) :
    Summable (fun ρ : TailZero χ T => mellinMassTerm χ 0 ρ.val) := by
  classical
  let M : TailZero χ T → ℝ := fun ρ => mellinMassTerm χ 0 ρ.val
  have hM : ∀ ρ, 0 ≤ M ρ := by intro ρ; dsimp [M, mellinMassTerm]; positivity
  apply (summable_partition hM (s := fun n => {ρ | ⌊|ρ.val.im|⌋₊ = n})
    (fun ρ => ⟨⌊|ρ.val.im|⌋₊, rfl, fun n hn => hn.symm⟩)).mpr
  have hinner (n : ℕ) : Summable (fun ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} => M ρ.val) := by
    let : Fintype {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} := (tail_shell_finite χ T n).fintype
    exact (hasSum_fintype _).summable
  refine ⟨hinner, ?_⟩
  have hmajor : Summable (fun n : ℕ => (1536 * C) / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (1536 * C)
  apply Summable.of_nonneg_of_le
    (fun n => tsum_nonneg (fun ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} => hM ρ.val)) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    have hempty : IsEmpty {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = 0} := by
      refine ⟨fun ρ => ?_⟩
      have hlt := Nat.lt_floor_add_one |ρ.val.val.im|
      rw [ρ.property] at hlt
      have hhigh := ρ.val.property.2.2.2
      norm_num only [Nat.cast_zero, zero_add] at hlt
      linarith
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hpoint (ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n}) :
        M ρ.val ≤ 384 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ) /
          (n : ℝ) ^ 4 := by
      have hheight : (n : ℝ) ≤ |ρ.val.val.im| := by
        simpa only [ρ.property] using Nat.floor_le (abs_nonneg ρ.val.val.im)
      have hpow : (n : ℝ) ^ 4 ≤ |ρ.val.val.im| ^ 4 := by gcongr
      have hdecay := Decomp454e.mellin_zero_shift_polynomial_decay ρ.val.val
        ρ.val.property.2.1 ρ.val.property.2.2.1.le
      have hmult := mul_le_mul_of_nonneg_left hdecay
        (Nat.cast_nonneg (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val) :
          (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ))
      apply (le_div_iff₀ (pow_pos hn0 4)).mpr
      have hm := mul_le_mul_of_nonneg_left hpow (hM ρ.val)
      dsimp only [M, mellinMassTerm] at hm ⊢
      nlinarith [hmult]
    have hsum : (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n}, M ρ.val) ≤
        384 * (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) / (n : ℝ) ^ 4 := by
      have hs : Summable (fun ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} =>
          384 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ) / (n : ℝ) ^ 4) := by
        let : Fintype {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n} := (tail_shell_finite χ T n).fintype
        exact (hasSum_fintype _).summable
      simpa only [tsum_div_const, tsum_mul_left] using (hinner n).tsum_le_tsum hpoint hs
    calc (∑' ρ : {ρ : TailZero χ T // ⌊|ρ.val.im|⌋₊ = n}, M ρ.val)
        ≤ 384 * (C * ((n : ℝ) + 1) ^ 2) / (n : ℝ) ^ 4 :=
          hsum.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcount n) (by norm_num)) (by positivity))
      _ ≤ 384 * (C * (4 * (n : ℝ) ^ 2)) / (n : ℝ) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith
      _ = (1536 * C) / (n : ℝ) ^ 2 := by
        field_simp
        ring

end LeanLab.HelfgottMajor.Decomp454f

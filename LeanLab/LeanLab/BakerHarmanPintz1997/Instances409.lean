/-
Concrete checks for the page 25 supply decomposition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409a
import LeanLab.BakerHarmanPintz1997.Decomp409b
import LeanLab.BakerHarmanPintz1997.Source409
import LeanLab.BakerHarmanPintz1997.Decomp409c
import LeanLab.BakerHarmanPintz1997.Audit1617
import LeanLab.HeathBrown1985.DivMoments

noncomputable section
namespace LeanLab.BakerHarmanPintz1997
open Decomp409a Finset MeasureTheory intervalIntegral

example : (polynomial (fun _ _ => 1) 4).supp = Finset.Icc 3 8 := by
  norm_num [polynomial]
  decide

example : window (fun _ _ => 1) 4 2 (1 : DirichletCharacter ℂ 1) = 2 := by
  have hχ : ∀ k : ℕ, (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 := by
    intro k
    apply MulChar.one_apply
    exact ⟨1, Subsingleton.elim _ _⟩
  norm_num [window, Finset.sum_Ioc_succ_top, hχ]

example (_x : ℝ) (k : ℕ) : ‖(1 : ℂ)‖ ≤ tau k ^ (0 : ℝ) := by simp

example : ‖kernel 4 2 1‖ ≤ 2 * 2 * (4 : ℝ) ^ (-1 / 2 : ℝ) :=
  kernel_norm_le (by norm_num) (by norm_num) (by norm_num) 1

example : Continuous fun t : ℝ => (polynomial (fun _ _ => 1) 4).eval
    (1 : DirichletCharacter ℂ 1) (half t) := eval_continuous _ _

example : Continuous (kernel 4 2) := kernel_continuous (by norm_num) (by norm_num)

example : kernel 4 2 1 = ∫ u in (4 - 2 : ℝ)..4, (u : ℂ) ^ (half 1 - 1) :=
  kernel_integral 4 2 1

example : ‖truncated (fun _ _ => 1) 4 2 2 (1 : DirichletCharacter ℂ 1) -
    truncated (fun _ _ => 1) 4 2 1 (1 : DirichletCharacter ℂ 1)‖ ≤
    2 * (4 : ℝ) ^ (-1 / 2 : ℝ) *
      ((∫ t in (1 : ℝ)..2, ‖(polynomial (fun _ _ => 1) 4).eval
          (1 : DirichletCharacter ℂ 1) (half t)‖) +
       (∫ t in (1 : ℝ)..2, ‖(polynomial (fun _ _ => 1) 4).eval
          (1 : DirichletCharacter ℂ 1) (half (-t))‖)) :=
  high_height_error _ 4 2 1 2 _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : (1 : ℝ) ^ (1 + (1 / 40 : ℝ) / 4) / T1 (1 / 40) 1 =
    (1 : ℝ) ^ (0.55 + 11 * (1 / 40 : ℝ) / 12) := truncation_scale (by norm_num)

example : ‖(2 : ℂ) - ((2 / 4 : ℝ) : ℂ) * 4‖ ≤ (2 * (1 : ℝ)) * (2 * 1 + 1) := by
  apply cancel_density (E := (1 : ℂ)) (d := 1) (r := 1)
  all_goals norm_num

example : Ev fun x => 1 < x ∧ y1 x ≤ x / 2 ∧ T0 x ≤ T1 (1 / 40) x :=
  eventual_geometry (by norm_num)

example : ‖kernel 4 2 1 - (2 : ℂ) * (4 : ℂ) ^ (half 1 - 1)‖ ≤
    8 * (|(1 : ℝ)| + 1) * 2 ^ 2 * (4 : ℝ) ^ (-3 / 2 : ℝ) :=
  kernel_taylor (by norm_num) (by norm_num) (by norm_num) 1

example : ‖truncated (fun _ _ => 0) 4 2 1 (1 : DirichletCharacter ℂ 1) -
    (2 : ℂ) * ((1 / (2 * Real.pi) : ℝ) •
      ∫ t in (-1 : ℝ)..1, (polynomial (fun _ _ => 0) 4).eval
        (1 : DirichletCharacter ℂ 1) (half t) * (4 : ℂ) ^ (half t - 1))‖ ≤
      32 * (0 : ℝ) * 1 ^ 2 * 2 ^ 2 * (4 : ℝ) ^ (-3 / 2 : ℝ) := by
  apply low_height_control _ 4 2 1 0 _
  all_goals try norm_num
  intro t ht
  simp [polynomial, DP.eval]

example : Ev fun x => 0 < L x ∧ 32 * |(1 : ℝ)| * L x ^ ((1 : ℝ) + 1) *
    Real.exp (-(L x ^ (1 / 3 : ℝ))) ≤ 1 := logarithmic_decay 1 1 1

-- A complete elementary witness for the arithmetic leaf at B = 0.
example : ∃ D : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    (∑ k ∈ Finset.Icc 1 N, tau k ^ (0 : ℝ)) ≤
      C * N * (1 + Real.log N) ^ D := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro N hN
  simp [Nat.card_Icc]

-- This verifies the exact sealed interface. The assembly remains conditional on two leaves.
example : Lemma11 := lemma11_decomposed

example : (∀ x k, ‖Audit1617.cP x k‖ ≤ tau k ^ (0 : ℝ)) ∧
    (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (T0 x)..(T1 (1 / 40) x),
        ‖(polynomial Audit1617.cP x).eval χ (half t)‖ ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A) ∧
      (∫ t in (T0 x)..(T1 (1 / 40) x),
        ‖(polynomial Audit1617.cP x).eval χ (half (-t))‖ ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A)) := by
  constructor
  · intro x k
    simpa only [Real.rpow_zero] using Audit1617.cP_norm x k
  · intro A hA
    obtain ⟨Xp, hp⟩ := Audit1617.plateau_mean (ε := 1 / 40) (by norm_num)
      id (fun _ => rfl) A hA
    obtain ⟨Xm, hm⟩ := Audit1617.plateau_mean (ε := 1 / 40) (by norm_num)
      Neg.neg (fun t => abs_neg t) A hA
    refine ⟨385, max Xp Xm, fun x hx q inst hq χ => ?_⟩
    exact ⟨hp x ((le_max_left _ _).trans hx) q hq χ,
      hm x ((le_max_right _ _).trans hx) q hq χ⟩

-- Full family witnesses for all three Lemma12 leaf interfaces.
example (ε : ℝ) : ∀ x : ℝ,
    max (x ^ (0.46 + ε / 8)) (x ^ (0.46 + ε / 8)) ≤ x ^ (0.46 + ε / 8) := by
  intro x
  simp

example (ε x : ℝ) : 1 < Decomp409b.cutoff ε x :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)

example : Ev fun x => Decomp409b.cutoff (1 / 40) x = x ^ ((1 / 40 : ℝ) / 12) :=
  Decomp409b.cutoff_eventually_eq (by norm_num)

example (ε : ℝ) : Holds42 ε fun x k => Decomp1518.conv2T
    (fun _ => 0) (fun _ => 0) (x ^ (0.46 + ε / 8)) (x ^ (0.46 + ε / 8))
      (wof x) (Decomp409b.cutoff ε x) k := by
  intro A hA
  refine ⟨0, 0, ?_⟩
  intro x hx q inst hq χ y hy hymax
  simp [Decomp1518.conv2T]

example (ε : ℝ) : Holds42 ε fun x k => ((Decomp1518.conv2E
    (fun _ => 0) (fun _ => 0) (x ^ (0.46 + ε / 8)) (x ^ (0.46 + ε / 8))
      (wof x) (Decomp409b.cutoff ε x) k : ℝ) : ℂ) := by
  intro A hA
  refine ⟨0, 0, ?_⟩
  intro x hx q inst hq χ y hy hymax
  simp [Decomp1518.conv2E]

example (ε : ℝ) : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, Decomp1518.conv2E
      (fun _ => 0) (fun _ => 0) (x ^ (0.46 + ε / 8)) (x ^ (0.46 + ε / 8))
        (wof x) (Decomp409b.cutoff ε x) k ≤ C * y1 x / L x ^ A := by
  intro A hA
  refine ⟨0, 0, ?_⟩
  intro x hx
  simp [Decomp1518.conv2E]

example : Lemma12 := Decomp409b.lemma12_decomposed

-- All three proper ranges have concrete positive integer examples.
example : Decomp409c.primeRegion ((2 : ℝ) ^ (50 : ℝ)) 1 3 = 0 ∧
    Decomp409c.primeRegion ((2 : ℝ) ^ (50 : ℝ)) 1048576 3 = 1 ∧
    Decomp409c.primeRegion ((2 : ℝ) ^ (50 : ℝ)) 1048576 11 = 2 := by
  have h4 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.4 : ℝ) = 1048576 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h46 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.46 : ℝ) = 8388608 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  norm_num [Decomp409c.primeRegion, h4, h46]

-- A nonzero family meets every prime range leaf premise.
example :
    (∀ x k, ‖((fun (_ : ℝ) (_ : ℕ) => (1 : ℂ)) x k)‖ ≤ tau k ^ (0 : ℝ)) ∧
    Ev (fun x => x ^ (0.1 : ℝ) = x ^ (0.1 : ℝ) ∧
      x ^ (0.4 : ℝ) ≤ x ^ (0.4 : ℝ) ∧ x ^ (0.4 : ℝ) ≤ x ^ (0.4 : ℝ)) := by
  constructor
  · intro x k
    simp
  · exact ⟨0, fun _ _ => ⟨rfl, le_rfl, le_rfl⟩⟩

example (j : Fin 3) (ε : ℝ) : Holds42 ε fun x k => Decomp409c.primePart j x
    (fun _ => 0) (fun _ => 0) (x ^ (0.4 : ℝ)) (x ^ (0.4 : ℝ))
      (wof x) (x ^ (0.1 : ℝ)) k := by
  intro A hA
  refine ⟨0, 0, ?_⟩
  intro x hx q inst hq χ y hy hymax
  simp [Decomp409c.primePart]

example : (1 : ℝ) ≤ ((2 : ℝ) ^ (50 : ℝ)) ^ (0.18 : ℝ) := by
  have hx : 0 < (2 : ℝ) ^ (50 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.1 : ℝ) = 32 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h46 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.46 : ℝ) = 8388608 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  apply Decomp409c.large_prime_cofactor (m := 1048576) (n := 1048576) (p := 11) hx
  all_goals norm_num [h4, h46]

example : (1048576 : ℝ) * 11 / 1048576 ≤ ((2 : ℝ) ^ (50 : ℝ)) ^ (0.1 : ℝ) ∧
    (1048576 : ℝ) / (1048576 * 11) ≤ 2 * ((2 : ℝ) ^ (50 : ℝ)) ^ (-0.06 : ℝ) := by
  have hx : 0 < (2 : ℝ) ^ (50 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.4 : ℝ) = 1048576 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h1 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.1 : ℝ) = 32 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h46 : ((2 : ℝ) ^ (50 : ℝ)) ^ (0.46 : ℝ) = 8388608 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  apply Decomp409c.large_prime_ratios hx
  all_goals norm_num [h4, h1, h46]

example : Lemma15 := Decomp409c.lemma15_decomposed

example : ∃ q : ℕ, max 2 2 ≤ q ∧
    (1 : ℝ) * Real.log q ^ (1 : ℝ) < Real.exp (Real.sqrt (Real.log q)) :=
  Source409.extra_factor_exceeds_log_power 1 1 2

-- The existing lab supplies the complete second and third moment instances.
example : ∃ D : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    (∑ k ∈ Icc 1 N, tau k ^ (2 : ℝ)) ≤ C * N * (1 + Real.log N) ^ D := by
  refine ⟨3, 1, by norm_num, ?_⟩
  intro N hN
  calc
    _ ≤ (N : ℝ) * LeanLab.HeathBrown1985.Hn N ^ 3 := by
      simpa [tau, ArithmeticFunction.sigma_zero_apply, Real.rpow_natCast] using
        LeanLab.HeathBrown1985.sum_sq_divisors_le N
    _ ≤ 1 * N * (1 + Real.log N) ^ 3 := by
      rw [one_mul]
      gcongr <;> first
      | exact LeanLab.HeathBrown1985.Hn_nonneg N
      | exact LeanLab.HeathBrown1985.Hn_le N

example : ∃ D : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    (∑ k ∈ Icc 1 N, tau k ^ (3 : ℝ)) ≤ C * N * (1 + Real.log N) ^ D := by
  refine ⟨7, 1, by norm_num, ?_⟩
  intro N hN
  calc
    _ ≤ (N : ℝ) * LeanLab.HeathBrown1985.Hn N ^ 3 * LeanLab.HeathBrown1985.Hn N ^ 4 := by
      simpa [tau, ArithmeticFunction.sigma_zero_apply, Real.rpow_natCast] using
        LeanLab.HeathBrown1985.sum_cube_divisors_le N
    _ ≤ N * (1 + Real.log N) ^ 3 * (1 + Real.log N) ^ 4 := by
      gcongr <;> first
      | exact LeanLab.HeathBrown1985.Hn_nonneg N
      | exact LeanLab.HeathBrown1985.Hn_le N
    _ = 1 * N * (1 + Real.log N) ^ 7 := by ring

#print axioms LeanLab.HeathBrown1985.sum_sq_divisors_le
#print axioms LeanLab.HeathBrown1985.sum_cube_divisors_le

#print axioms Audit1617.plateau_mean
#print axioms Audit1617.cP_norm

end LeanLab.BakerHarmanPintz1997

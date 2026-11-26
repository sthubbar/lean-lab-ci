import LeanLab.LPZ2007.Decomp407a
import LeanLab.LPZ2007.FamilyAudit407

/-!
Concrete instances for the task637 twins. These are consistency checks.
They supply no global witness for an OPEN analytic input.
AI wrote this Lean code. Goldbach is open.
-/

open Finset Real
open LeanLab.LPZ2007

example : ∃ s : Finset ℕ, s ⊆ {0} ∧ (s : Set ℕ).Pairwise (fun x y => x ≠ y) ∧
    (({0} : Finset ℕ).card : ℝ) ≤ 1 * s.card := by
  apply Selection637.packing
  · exact fun h => h.symm
  · exact fun _ h => h rfl
  · intro x hx v hv _
    have h := Finset.card_le_card hv
    norm_num at h ⊢
    exact_mod_cast h

example : ∃ s : Finset ℕ, s ⊆ {0} ∧ Set.InjOn id (s : Set ℕ) ∧
    s.image id = ({0} : Finset ℕ).image id := by
  exact ⟨{0}, Finset.Subset.refl _, Function.injective_id.injOn, rfl⟩

example : ∃ b : Bool, ({0, 1, 2} : Finset ℕ).card ≤
    2 * (({0, 1, 2} : Finset ℕ).filter (fun n => decide (Even n) = b)).card := by
  refine ⟨true, ?_⟩
  decide

example : (1 : ℝ) ≤ |0 - 2| := by
  apply Selection637.parity_spacing (δ := 1) (t := 0) (u := 2) <;> norm_num

example : Density637.pseudo 1 1 1 = 1 := by
  simp [Density637.pseudo]
  rw [Finset.sum_filter, Finset.sum_singleton, if_pos (squarefree_one : Squarefree (1 : ℕ))]
  norm_num

example : Density637.coefficient (Real.exp 1) 1 1 1 = 0 := by
  simp [Density637.coefficient]

example : (2 : ℕ) ∈ Density637.support (Real.exp 1) := by
  have hlo : Real.exp (57 / 100 : ℝ) < 2 := by
    calc
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  have hhi : (2 : ℝ) ≤ Real.exp (28 / 25 : ℝ) :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by norm_num))
  unfold Density637.support
  rw [Finset.mem_filter, Finset.mem_Icc]
  simp only [Real.exp_one_rpow, Real.log_exp, one_pow, mul_one]
  exact ⟨⟨by norm_num, (Nat.le_floor_iff (Real.exp_pos _).le).mpr hhi⟩, hlo⟩

example : 0 < Density637.window 0 1 1 := by
  exact Density637.window_pos (by norm_num) (by norm_num)

example : (2 : ℝ) ≤ (2 * 1 / 1 ^ 2) * 1 :=
  Density637.absorb (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ ξ η : ℝ,
    (99 / 100 : ℝ) * Real.log ((Real.exp 1) ^ (57 / 100 : ℝ)) ≤ ξ ∧
    ξ ≤ Real.log ((Real.exp 1) ^ (57 / 100 : ℝ)) ∧
    Real.log ((Real.exp 1) ^ (28 / 25 : ℝ) * Real.log (Real.exp 1) ^ 2) ≤ η ∧
    η ≤ (101 / 100 : ℝ) *
      Real.log ((Real.exp 1) ^ (28 / 25 : ℝ) * Real.log (Real.exp 1) ^ 2) ∧ ξ < η :=
  Density637.smoothing_parameters le_rfl

example : ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ z ∈ EZero X 1 1 2, False := by
  obtain ⟨X0, hx⟩ := Decomp407a.bounded_moduli_empty 1 1 2
  refine ⟨X0, fun X hX z hz => ?_⟩
  simpa only [hx X 2 hX le_rfl, Set.mem_empty_iff_false] using hz

example : ∃ ν : Unit → ℂ, (∀ j, ‖ν j‖ = 1) ∧
    (∑ j ∈ ({()} : Finset Unit), ν j * (1 : ℂ)) =
      ((∑ _j ∈ ({()} : Finset Unit), ‖(1 : ℂ)‖ : ℝ) : ℂ) :=
  Density637.aligned_sum _ (fun _ => 1)

example : Density637.vector (Real.exp 1) 1 1
    (⟨1, (1, 0)⟩ : Σ r : ℕ, DirichletCharacter ℂ r × ℂ) 1 = 1 := by
  have hχ : (1 : DirichletCharacter ℂ 1) (0 : ZMod 1) = 1 := by
    change (1 : DirichletCharacter ℂ 1) (1 : ZMod 1) = 1
    exact map_one _
  have hp : Density637.pseudo 1 1 1 = 1 := by
    simp [Density637.pseudo]
    rw [Finset.sum_filter, Finset.sum_singleton, if_pos (squarefree_one : Squarefree (1 : ℕ))]
    norm_num
  simp [Density637.vector, hp, hχ]

example : (1 / Real.log 16 + 2 / Real.log 4) * Real.log 3 + 1 ≤ (10 : ℝ) := by
  have h := Extraction637.width_cost_le (X := 16) (H := 1) (T := 1) (P := 2)
    (q := 1) (τ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : (1 : ℕ) = oddRad 1 ∨ 1 = 4 * oddRad 1 ∨ 1 = 8 * oddRad 1 := by
  apply realPrimitiveModulus 1 (by norm_num) 1
  · exact DirichletCharacter.isPrimitive_one_level_one
  · intro a
    have ha : a = 1 := Subsingleton.elim _ _
    rw [ha, map_one]
    rfl

example : ∃ z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ,
    z ∈ EZero (Real.exp 2) 6 1 2 ∧
    (∀ w ∈ ({z} : Finset _), w ∈ EZero (Real.exp 2) 6 1 2) ∧
    (∀ w ∈ ({z} : Finset _),
      (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ ∧
      |z.2.2.im - w.2.2.im| < 1 / Real.log 4) := by
  obtain ⟨z, hz⟩ := FamilyAudit407.nonempty_zero_box
  refine ⟨z, hz, ?_, ?_⟩
  · intro w hw
    simpa only [Finset.mem_singleton.mp hw] using hz
  · intro w hw
    obtain rfl := Finset.mem_singleton.mp hw
    exact ⟨rfl, by simpa using (one_div_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 4)))⟩

example : (2 : ℝ) ≤ Real.sqrt (Real.exp 2) := by
  have he : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  exact Real.exp_one_gt_two.le

example : (2 : ℝ) < Real.log 8 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

/-
P0079 page 3, the changes of variables used in the corollary.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293d

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 3, corollary proof. Permuting power variables preserves infinitude. -/
theorem sol_infinite_reindex293 {s : ℕ} {l1 l2 γ η : ℝ} {μ : Fin s → ℝ}
    (σ : Equiv.Perm (Fin s))
    (h : (Sol l1 l2 (fun i => μ (σ i)) γ η).Infinite) :
    (Sol l1 l2 μ γ η).Infinite := by
  let F : (ℕ × ℕ × (Fin s → ℕ)) → (ℕ × ℕ × (Fin s → ℕ)) :=
    fun x => (x.1, x.2.1, fun i => x.2.2 (σ.symm i))
  have hinj : Function.Injective F := by
    intro x y hxy
    have hp1 := congrArg Prod.fst hxy
    have hp2 := congrArg (fun z => z.2.1) hxy
    have hm : x.2.2 = y.2.2 := by
      funext i
      have H := congrArg (fun z => z.2.2 (σ i)) hxy
      simpa [F] using H
    exact Prod.ext hp1 (Prod.ext hp2 hm)
  apply (h.image hinj.injOn).mono
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hx.1, hx.2.1, fun i => hx.2.2.1 _, ?_⟩
  have heq : form l1 l2 μ γ x.1 x.2.1 (fun i => x.2.2 (σ.symm i)) =
      form l1 l2 (fun i => μ (σ i)) γ x.1 x.2.1 x.2.2 := by
    unfold form
    have H := Equiv.sum_comp σ (fun i => μ i * (2 : ℝ) ^ x.2.2 (σ.symm i))
    simpa using congrArg (fun z => l1 * x.1 + l2 * x.2.1 + z + γ) H.symm
  simpa [F, heq] using hx.2.2.2

/-- P0079 page 3, corollary proof. Interchanging the two primes preserves infinitude. -/
theorem sol_infinite_swap_primes293 {s : ℕ} {l1 l2 γ η : ℝ} {μ : Fin s → ℝ}
    (h : (Sol l2 l1 μ γ η).Infinite) : (Sol l1 l2 μ γ η).Infinite := by
  let F : (ℕ × ℕ × (Fin s → ℕ)) → (ℕ × ℕ × (Fin s → ℕ)) :=
    fun x => (x.2.1, x.1, x.2.2)
  have hinj : Function.Injective F := by
    intro x y hxy
    have h := congrArg F hxy
    simpa [F] using h
  apply (h.image hinj.injOn).mono
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hx.2.1, hx.1, hx.2.2.1, ?_⟩
  have heq : form l1 l2 μ γ x.2.1 x.1 x.2.2 = form l2 l1 μ γ x.1 x.2.1 x.2.2 := by
    unfold form
    ring
  simpa [F, heq] using hx.2.2.2

/-- P0079 page 3, corollary proof. The first two indices can be interchanged
both in the infinite coefficient sequence and in any finite box with at least two powers. -/
theorem swap_nat_fin293 (s : ℕ) (hs : 2 ≤ s) (i : Fin s) :
    ((Equiv.swap (⟨0, by omega⟩ : Fin s) ⟨1, by omega⟩ i : Fin s) : ℕ) =
      Equiv.swap (0 : ℕ) 1 (i : ℕ) := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- P0079 page 3, corollary proof. Swap primes and their paired power coefficients. -/
theorem sol_infinite_swap_coeff293 {s : ℕ} (hs : 2 ≤ s) {l1 l2 γ η : ℝ} {μ : ℕ → ℝ}
    (h : (Sol l2 l1 (fun i : Fin s => μ (Equiv.swap 0 1 (i : ℕ))) γ η).Infinite) :
    (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite := by
  have heq : (fun i : Fin s => μ (Equiv.swap 0 1 (i : ℕ))) =
      (fun i : Fin s => μ ((Equiv.swap (⟨0, by omega⟩ : Fin s) ⟨1, by omega⟩ i : Fin s) : ℕ)) := by
    funext i
    rw [swap_nat_fin293 s hs i]
  rw [heq] at h
  exact sol_infinite_swap_primes293 (sol_infinite_reindex293 _ h)

/-- P0079 page 3, corollary proof. An opposite-sign pair can be scaled into
the size regime. The ratio itself stays fixed. -/
theorem exists_scale293 (l1 l2 : ℝ) (hn : l1 / l2 < 0) :
    ∃ t : ℝ, t ≠ 0 ∧ 1 < t * l1 ∧ t * l2 < -1 ∧ (t * l1) / (t * l2) = l1 / l2 := by
  rcases (div_neg_iff).mp hn with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · let u := max (2 / l1) ((-2) / l2)
    have hu1 : 2 ≤ u * l1 := (div_le_iff₀ ha).mp (le_max_left _ _)
    have hu2 : u * l2 ≤ -2 := (div_le_iff_of_neg hb).mp (le_max_right _ _)
    have hu : 0 < u := lt_of_lt_of_le (div_pos (by norm_num) ha) (le_max_left _ _)
    refine ⟨u, hu.ne', by linarith, by linarith, ?_⟩
    field_simp
  · let u := max (2 / (-l1)) (2 / l2)
    have hu1 : 2 ≤ u * (-l1) := (div_le_iff₀ (by linarith)).mp (le_max_left _ _)
    have hu2 : 2 ≤ u * l2 := (div_le_iff₀ hb).mp (le_max_right _ _)
    have hu : 0 < u := lt_of_lt_of_le (div_pos (by norm_num) hb) (le_max_right _ _)
    refine ⟨-u, by linarith, by nlinarith, by nlinarith, ?_⟩
    field_simp

end LeanLab.LZPowersOfTwo

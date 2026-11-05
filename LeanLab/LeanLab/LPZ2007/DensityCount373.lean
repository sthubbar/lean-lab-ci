import LeanLab.LPZ2007.Density373

/-!
Jutila 1977 page 46, the definition of N star before Theorem 1.
This identifies the lab's distinct zero family count with the sum over primitive characters.
The source counts multiplicity. The distinct count is the weaker interface used here.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.DensityCount373

open Finset

/-- Jutila 1977 page 46, definition of the primitive family count.
The exceptional set cardinal equals the sum of its distinct zero counts at each modulus
and primitive character. Finiteness was proved in ZeroFamily373. -/
theorem EZero_ncard_eq_sum (X H T P : ℝ) :
    (EZero X H T P).ncard =
      ∑ r ∈ Finset.Icc 1 ⌊P⌋₊,
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          {ρ : ℂ | Lfun χ ρ = 0 ∧ 1 - H / Real.log X ≤ ρ.re ∧ |ρ.im| ≤ T}.ncard := by
  classical
  let s := Finset.Icc 1 ⌊P⌋₊
  let Z (r : ℕ) (χ : DirichletCharacter ℂ r) : Set ℂ :=
    {ρ | Lfun χ ρ = 0 ∧ 1 - H / Real.log X ≤ ρ.re ∧ |ρ.im| ≤ T}
  letI (r : s) (χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}) : Finite (Z r χ) :=
    (ZeroFamily373.primitive_zeros_finite (Finset.mem_Icc.mp r.2).1 χ.1 χ.2
      (1 - H / Real.log X) T).to_subtype
  let B := Σ r : s, Σ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Z r χ
  let e : (EZero X H T P) ≃ B :=
    { toFun := fun z => ⟨⟨z.1.1, Finset.mem_Icc.mpr ⟨z.2.1, Nat.le_floor z.2.2.1⟩⟩,
        ⟨⟨z.1.2.1, z.2.2.2.1⟩, ⟨z.1.2.2, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2⟩⟩⟩
      invFun := fun b => ⟨⟨b.1.1, b.2.1.1, b.2.2.1⟩,
        (Finset.mem_Icc.mp b.1.2).1,
        (Nat.le_floor_iff' (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp b.1.2).1))).1
          (Finset.mem_Icc.mp b.1.2).2,
        b.2.1.2, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2⟩
      left_inv := by rintro ⟨⟨r, χ, ρ⟩, hz⟩; rfl
      right_inv := by rintro ⟨⟨r, hr⟩, ⟨⟨χ, hχ⟩, ⟨ρ, hρ⟩⟩⟩; rfl }
  calc
    (EZero X H T P).ncard = Nat.card B := Nat.card_congr e
    _ = ∑ r : s, ∑ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, (Z r χ).ncard := by
      simp only [B, Nat.card_sigma]
      rfl
    _ = _ := by
      let F (r : ℕ) : ℕ := ∑ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, (Z r χ).ncard
      change (∑ r : s, F r) = _
      refine (Finset.sum_coe_sort s F).trans ?_
      apply Finset.sum_congr rfl
      intro r hr
      symm
      exact Finset.sum_subtype _ (by simp) (fun χ : DirichletCharacter ℂ r => (Z r χ).ncard)

/-- Jutila 1977 page 46, Theorem 1 display 1.8 at epsilon one half.
CONDITIONAL ON its summed distinct zero bound. The source counts multiplicities.
The primitive character sum is the same sum used in the source. -/
theorem jutila_of_summed_density
    (hdensity : ∃ C : ℝ, 0 ≤ C ∧ ∀ α T P : ℝ,
      (4 / 5 : ℝ) ≤ α → α ≤ 1 → 1 ≤ T → T ≤ P →
        ((∑ r ∈ Finset.Icc 1 ⌊P⌋₊,
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
            {ρ : ℂ | Lfun χ ρ = 0 ∧ α ≤ ρ.re ∧ |ρ.im| ≤ T}.ncard : ℕ) : ℝ) ≤
          C * (P ^ 2 * T) ^ ((5 / 2 : ℝ) * (1 - α))) : JutilaBound := by
  obtain ⟨C, hC, hD⟩ := hdensity
  apply Density373.jutila_of_rectangle_density
  refine ⟨C, hC, ?_⟩
  intro α T P hα0 hα1 hT hTP
  have hset : {z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ |
      1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun z.2.1 z.2.2 = 0 ∧
      α ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T} =
      EZero (Real.exp 1) (1 - α) T P := by
    ext z
    have he : 1 - (1 - α) / Real.log (Real.exp 1) = α := by rw [Real.log_exp]; ring
    change (1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun z.2.1 z.2.2 = 0 ∧
      α ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T) ↔ _
    simp only [EZero, Set.mem_setOf_eq, he]
    constructor
    · intro hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.2⟩
    · intro hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1,
        (ZeroFamily373.primitive_zero_re_lt_one hz.1 z.2.1 hz.2.2.1 hz.2.2.2.1).le,
        hz.2.2.2.2.2⟩
  rw [hset, EZero_ncard_eq_sum]
  simpa only [Real.log_exp, div_one, sub_sub_cancel] using hD α T P hα0 hα1 hT hTP

end LeanLab.LPZ2007.DensityCount373

#print axioms LeanLab.LPZ2007.DensityCount373.EZero_ncard_eq_sum

#print axioms LeanLab.LPZ2007.DensityCount373.jutila_of_summed_density

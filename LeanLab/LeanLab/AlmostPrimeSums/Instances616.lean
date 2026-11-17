/- AI wrote the Lean code. Goldbach is open.
Task616, explicit nonvacuity checks for the analytic interfaces. -/
import LeanLab.AlmostPrimeSums.Decomp616
import LeanLab.AlmostPrimeSums.Decomp1544b

open Filter Real
noncomputable section
namespace LeanLab.AlmostPrimeSums.Instances616
open TogashiUchiyamaScale Decomp616

/-- The product hypotheses in all five seed leaves have their actual paper instance. -/
theorem paper_product_instance : ∃ T : ℝ, 0 < T ∧
    HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T := by
  let f : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 1 else
    ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))
  let S : Set Nat.Primes := {p | 2 < (p : ℕ)}
  have hs : Function.mulSupport f ⊆ S := by
    intro p hp
    by_contra h
    have h2 : (p : ℕ) = 2 := by
      have hle := p.property.two_le
      change ¬ 2 < (p : ℕ) at h
      omega
    exact hp (by simp [f, h2])
  have hf : HasProd (f ∘ Subtype.val : S → ℝ) Decomp1544b.Ttwin :=
    (hasProd_subtype_iff_of_mulSupport_subset hs).mpr Decomp1544b.Ttwin_multipliable.hasProd
  let e : S ≃ {p : ℕ // p.Prime ∧ 2 < p} :=
    { toFun := fun p => ⟨p.val.val, p.val.property, p.property⟩
      invFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  refine ⟨Decomp1544b.Ttwin, lt_of_lt_of_le (by norm_num) Decomp1544b.one_le_Ttwin, ?_⟩
  have he : HasProd ((fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) ∘ e) Decomp1544b.Ttwin := by
    convert hf using 1
    ext p
    have hp : (p.val.val : ℕ) ≠ 2 := by have h := p.property; change 2 < p.val.val at h; omega
    simp [f, Function.comp_def, e, hp]
    rfl
  exact e.injective.hasProd_iff (by intro p hp; exact False.elim (hp (e.surjective p))) |>.mp he

/-- The exact sixth exponent cutoff has a concrete nonempty P0072 sieve instance. -/
theorem sixth_instance : (Finite616.sifted 10 (cutoff 10 6)).card = 4 := by
  rw [sifted_six]
  decide

/-- The relative lower coefficient predicate has a proved positive normalization instance. -/
theorem lower_instance : Lower 1 6 0 := lower_zero 1 6 (by norm_num)

/-- Equal exponent endpoints make every auxiliary prime band empty.
This instantiates the uniform auxiliary hypothesis without assuming an unproved bound. -/
theorem empty_auxiliary_band :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ p : ℕ, p.Prime → p.Coprime N → cutoff N 10 ≤ (p : ℝ) → (p : ℝ) < cutoff N 10 →
      childMass N p ≤ 2 * ((0 : ℝ) + δ) *
        M 1 N * (log N) ^ 2 / ((p : ℝ) * (log ((N : ℝ) / p)) ^ 2) := by
  intro δ hδ
  exact Eventually.of_forall (by intro N he p hp hpN hge hlt; exact False.elim (not_lt_of_ge hge hlt))

end LeanLab.AlmostPrimeSums.Instances616

/-
Transport of prime components to a common multiple of the source level.
Source: Pintz Part I pages 19 and 20, displays 7.9 to 7.14.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp247a

namespace LeanLab.BhowmikGrimmelt2026

/-- Each prime component level divides its source level.
Source: prime power decomposition in Pintz Part I page 19. -/
theorem compLevel_dvd443 (r p : ℕ) [NeZero r] : compLevel r p ∣ r := by
  by_cases hp : p.Prime
  · exact (Nat.Prime.pow_dvd_iff_le_factorization hp (NeZero.ne r)).mpr le_rfl
  · simp [compLevel, Nat.factorization_eq_zero_of_not_prime r hp]

/-- Lifting a character agrees with multiplying its lifted source components.
The equality is proved on units, where the component hypothesis applies.
Source: the component transport in the CRT expansion of Pintz Part I page 20. -/
theorem changeLevel_component_product443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r)
    (ψ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r p))
    (hψ : IsPrimeComponents χ ψ) (hd : r ∣ q) :
    DirichletCharacter.changeLevel hd χ =
      ∏ p ∈ r.primeFactors, DirichletCharacter.changeLevel ((compLevel_dvd443 r p).trans hd) (ψ p) := by
  classical
  apply MulChar.ext
  intro u
  let ev : DirichletCharacter ℂ q →* ℂ :=
    { toFun := fun η => η u
      map_one' := MulChar.one_apply_coe u
      map_mul' := fun a b => MulChar.mul_apply a b u }
  have he : (∏ p ∈ r.primeFactors,
      DirichletCharacter.changeLevel ((compLevel_dvd443 r p).trans hd) (ψ p)) u =
      ∏ p ∈ r.primeFactors,
        (DirichletCharacter.changeLevel ((compLevel_dvd443 r p).trans hd) (ψ p)) u :=
    map_prod ev _ _
  rw [he, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val]
  have hu : (u : ZMod q).val.Coprime r :=
    (ZMod.val_coe_unit_coprime u).of_dvd_right hd
  rw [hψ.2 _ hu]
  apply Finset.prod_congr rfl
  intro p hp
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.compLevel_dvd443
#print axioms LeanLab.BhowmikGrimmelt2026.changeLevel_component_product443

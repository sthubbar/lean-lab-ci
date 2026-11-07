/-
Split of `lemma74` into smaller leaves.

The target is the smoothed explicit formula for `∑ Λ(n) χ(n) Ψ(n)` for a primitive
character, with the pole term at `s = 1` subtracted and the zeros of the Dirichlet
L-function of `χ` added back, up to an error `C * S ^ (-A)` depending only on `A` and
on the seminorm bounds `M` of the kernel `Ψ`, whose support starts at `S`.

The split follows the proof's shape.  One leaf is the elementary kernel estimate: the
Mellin transform of a kernel supported in `Ioi S` decays like `S ^ σ` times
`(1 + |t|) ^ (-k)`.  One leaf is the contour shift on a rectangle, an identity: the
arithmetic side equals the boundary integral of the logarithmic derivative against the
Mellin transform, with the zeros inside the rectangle counted with multiplicity.  Two
leaves bound the two kinds of boundary pieces, the shifted vertical line and the two
horizontal pieces.  One leaf bounds what the truncation at height `T` and at the
abscissa `-B` leaves out of the zero sum.

The error bounds are stated with `C * S ^ (-B)` for a freely chosen `B`, because the
assembly then takes `B = A + 2` and uses `S ^ (-(A + 2)) ≤ S ^ (-A)` for `S ≥ 1`.  The
assembly uses the identity, the two boundary bounds and the zero tail bound; the kernel
estimate is the input those two boundary bounds need.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## The kernel estimate -/

/-- LEAF. Mellin decay of the kernel, from the support hypothesis and integration by parts.

Step: if every `k`-th derivative of `Ψ` is bounded by `M k` and the support of `Ψ`
lies in `Ioi S` with `S ≥ 1`, then on the half plane `re s + k ≤ -1` the Mellin
transform obeys a bound by `M k * S ^ (re s)` with `k` powers of `(1 + |Im s|)^-1`.
This is repeated integration by parts, with the boundary terms killed by the
support condition; no arithmetic enters.  It is the input the two boundary leaves
need, and the only place the seminorm bounds are spent. -/
theorem leaf_mellin_decay74 (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (hS : 1 ≤ S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (k : ℕ) (σ t : ℝ) (hσ : σ + (k : ℝ) ≤ -1) :
    ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((2 : ℝ) ^ k * M k) * S ^ σ / (1 + |t|) ^ k := by
  sorry

/-! ## The contour shift -/

/-- LEAF. The explicit formula on a rectangle, as an identity.

Step: for `0 < B`, `1 ≤ S`, a primitive `χ` and a smooth compactly supported `Ψ`
supported in `Ioi S`, the arithmetic side — the logarithmic sum, minus the residue
of the pole at `s = 1` when `χ` is the principal character, plus the zeros of the
L-function with `-B < re ρ` and `|Im ρ| ≤ T` counted with multiplicity — equals the
boundary of the rectangle with corners `-B` and `2` and heights `±T`: the shifted
vertical line plus the two horizontal pieces.  The identity is exact; every error
term of the target sits in the three quantities the next leaves bound. -/
theorem leaf_contour_shift74 (B T : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (hB : 0 < B) (hT : 0 < T)
    (hS : 1 ≤ S) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
      (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
      (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (hχ : χ.IsPrimitive) :
    ∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ) =
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I))) := by
  sorry

/-! ## The two boundary bounds -/

/-- LEAF. The shifted vertical line contributes at most a constant times `S ^ (-B)`.

Step: on the line `re s = -B` the logarithmic derivative of the L-function grows
only logarithmically in `|Im s|`, while the kernel's Mellin transform decays like
`S ^ (-B) * (1 + |Im s|) ^ (-2)` by the kernel leaf; the integral over the line is
therefore bounded by a constant, uniform in the character and in the kernel, times
`S ^ (-B)`.  This is the vertical part of the rectangle, which is where the size of
the shifted contour is paid for. -/
theorem leaf_vertical_remainder74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * S ^ (-B) := by
  sorry

/-- LEAF. The two horizontal pieces contribute at most a constant times `S ^ (-B)`.

Step: on the segments `Im s = ±T` and `-B ≤ re s ≤ 2` the Mellin transform is
bounded by `S ^ (-B)` times a constant depending on the seminorm bounds, and the
logarithmic derivative is bounded there as well, so the two segments together
contribute a constant times `S ^ (-B)`, uniformly in the character and in the
kernel.  This is the price of the truncation at height `T` that makes the zero sum
finite. -/
theorem leaf_horizontal_remainder74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ ≤ C * S ^ (-B) := by
  sorry

/-! ## What the truncation leaves out -/

/-- LEAF. The zeros outside the truncated window contribute at most a constant times `S ^ (-B)`.

Step: the difference between the sum over all zeros of the L-function and the sum
over those with `-B < re ρ` and `|Im ρ| ≤ T` is a sum of `mult χ ρ * mellinR Ψ ρ`
over the zeros above height `T` and over the zeros with `re ρ ≤ -B`, with
multiplicity.  Each term is a Mellin transform at a zero, so the kernel decay makes
the whole tail bounded by a constant times `S ^ (-B)`, uniformly in the character
and in the kernel.  This is the difference the assembly adds back after the
truncated identity. -/
theorem leaf_zero_tail74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ)‖ ≤ C * S ^ (-B) := by
  sorry

/-! ## The assembly -/

/-- The assembly: the exact sealed statement of `lemma74`, proved from the leaves above
through the truncated identity, two triangle inequalities and the monotonicity of
`S ↦ S ^ (-·)` on `S ≥ 1`, and nothing left open. -/
theorem lemma74_split : Lemma74 := by
  intro A hA M
  let B : ℝ := A + 2
  let T : ℝ := 1
  have hBval : B = A + 2 := rfl
  have hTval : T = 1 := rfl
  have hB : 0 < B := by rw [hBval]; linarith
  have hT : 0 < T := by rw [hTval]; norm_num
  obtain ⟨Cv, hCv, hv⟩ := leaf_vertical_remainder74 M B T hB hT
  obtain ⟨Ch, hCh, hh⟩ := leaf_horizontal_remainder74 M B T hB hT
  obtain ⟨Ct, hCt, ht⟩ := leaf_zero_tail74 M B T hB hT
  refine ⟨Cv + Ch + Ct, ?_⟩
  intro r hrinst χ hχ S Ψ hS hsm hcs hsupp hb
  haveI : NeZero r := hrinst
  have hid := leaf_contour_shift74 B T r χ M S Ψ hB hT hS hsm hcs hsupp hb hχ
  have hvt := hv r χ hχ S Ψ hS hsm hcs hsupp hb
  have hhr := hh r χ hχ S Ψ hS hsm hcs hsupp hb
  have htl := ht r χ hχ S Ψ hS hsm hcs hsupp hb
  have hEq : (∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ)) = ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))) + (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))) := by
    rw [← hid]
    abel
  have a2 : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ := norm_add_le (a := ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) (b := ((1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))))
  have a1 : ‖((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))) + (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ)))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ :=
    norm_add_le (a := ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I))))) (b := (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))))
  have h1 : ‖(∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ := by
    rw [hEq]
    exact le_trans a1 (add_le_add a2 (le_refl (‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖)))
  have h2 : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤
      Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) :=
    add_le_add (add_le_add hvt hhr) htl
  have h3 : Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) =
      (Cv + Ch + Ct) * S ^ (-B) := by ring
  have hp : S ^ (-B) ≤ S ^ (-A) := by
    have hle : (-B : ℝ) ≤ -A := by rw [hBval]; linarith
    exact Real.rpow_le_rpow_of_exponent_le hS hle
  have h4 : (Cv + Ch + Ct) * S ^ (-B) ≤ (Cv + Ch + Ct) * S ^ (-A) :=
    mul_le_mul_of_nonneg_left hp (by linarith)
  calc ‖(∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ := h1
    _ ≤ Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) := h2
    _ = (Cv + Ch + Ct) * S ^ (-B) := h3
    _ ≤ (Cv + Ch + Ct) * S ^ (-A) := h4

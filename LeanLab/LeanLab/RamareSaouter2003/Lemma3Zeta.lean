import Mathlib
import LeanLab.RamareSaouter2003.Lemma3Zeros
import LeanLab.PNTPort.ExplicitPsi1.Nontrivial
import LeanLab.PNTPort.ZetaZeros.Sym

/-!
# Ramaré-Saouter 2003, Lemma 3 for the nontrivial zeros of ζ

P0099, unit U-6762, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

The concrete zero family: `ZI = Σ ρ : Zall, Fin (m ρ)`, the nontrivial zeros of ζ each listed
with its multiplicity `m ρ = analyticOrderNatAt ζ ρ`, as in `PNTPort/ExplicitPsi1`; ordinate
`gZ i = Im ρ`, real part `bZ i = Re ρ`. `Zall_eq` of `PNTPort/ExplicitPsi1/Nontrivial.lean`
puts every such `ρ` in the open strip, so `0 ≤ bZ ≤ 1`. The functional equation symmetry is
`σ ⟨ρ, k⟩ = ⟨1 - ρ, k⟩`, well defined with multiplicity by `ZetaZeros.ord_one_sub`, PROVED in
the lab from Mathlib's functional equation; `|Im (1 - ρ)| = |Im ρ|` and `Re (1 - ρ) = 1 - Re ρ`.

* `RHUpTo T0`: every zero of ζ in the strip with `|Im ρ| ≤ T0` has `Re ρ = 1/2`. CITED, the
  verification of RH to height `T0`; the paper takes `T0 = 3.3 × 10^9`.
* `lemma3_zeta`: Lemma 3 of p. 15 for the true zero sum `ZsF gZ bZ`, PROVED CONDITIONAL ON
  `RHUpTo T0` and `Lemma1Count gZ`, Lemma 1 for the zeros of ζ.
* `theorem2At1e20_of_zeta`: Table 1 row one, PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
  `SchoenfeldPT 0.998697 1.001093`, `JLower15 NT (ZsF gZ bZ) 3.3e9`, `RHUpTo 3.3e9`,
  `Lemma1Count gZ` and `Lemma1Upper NT`.
-/

namespace LeanLab.RamareSaouter2003.L3Zeta

open Complex
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.RamareSaouter2003.L3Zeros
  LeanLab.RamareSaouter2003.Thm4JSplit LeanLab.RamareSaouter2003.Smooth

local notation "ζ" => riemannZeta

/-- The nontrivial zeros of ζ with multiplicity. -/
abbrev ZI := Σ ρ : Zall, Fin (analyticOrderNatAt ζ (ρ : ℂ))

/-- Ordinate. -/
noncomputable def gZ (i : ZI) : ℝ := ((i.1 : ℂ)).im

/-- Real part. -/
noncomputable def bZ (i : ZI) : ℝ := ((i.1 : ℂ)).re

/-- **RH verified to height `T0`.** CITED. -/
def RHUpTo (T0 : ℝ) : Prop :=
  ∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2

lemma mem_strip (ρ : Zall) : ζ (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
  have h : (ρ : ℂ) ∈ {ρ : ℂ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by rw [← Zall_eq]; exact ρ.2
  exact h

lemma one_sub_mem (ρ : Zall) : (1 - (ρ : ℂ)) ∈ Zall := by
  obtain ⟨hz, h0, h1⟩ := mem_strip ρ
  have h : (1 - (ρ : ℂ)) ∈ {ρ : ℂ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by
    refine ⟨LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hz, ?_, ?_⟩ <;> simp <;> linarith
  rw [← Zall_eq] at h
  exact h

lemma ord_eq (ρ : Zall) :
    analyticOrderNatAt ζ (1 - (ρ : ℂ)) = analyticOrderNatAt ζ (ρ : ℂ) := by
  obtain ⟨_, h0, h1⟩ := mem_strip ρ
  exact LeanLab.PNTPort.ZetaZeros.ord_one_sub h0 h1

/-- The functional equation symmetry `ρ ↦ 1 - ρ`, with multiplicity. -/
noncomputable def σZ (i : ZI) : ZI :=
  ⟨⟨1 - (i.1 : ℂ), one_sub_mem i.1⟩, Fin.cast (ord_eq i.1).symm i.2⟩

lemma σZ_injective : Function.Injective σZ := by
  rintro ⟨ρ, k⟩ ⟨ρ', k'⟩ h
  unfold σZ at h
  rw [Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hρ : ρ = ρ' := by
    apply Subtype.ext
    have := congrArg Subtype.val h1
    simp only at this
    linear_combination -this
  subst hρ
  have h3 : Fin.cast (ord_eq ρ).symm k = Fin.cast (ord_eq ρ).symm k' := eq_of_heq h2
  have h4 : k = k' := by
    apply Fin.ext
    have := congrArg Fin.val h3
    simpa using this
  rw [h4]

lemma gZ_σ (i : ZI) : |gZ (σZ i)| = |gZ i| := by
  simp [gZ, σZ, abs_neg]

lemma bZ_σ (i : ZI) : bZ (σZ i) = 1 - bZ i := by
  simp [bZ, σZ]

lemma bZ_mem (i : ZI) : 0 ≤ bZ i ∧ bZ i ≤ 1 := by
  obtain ⟨_, h0, h1⟩ := mem_strip i.1
  exact ⟨h0.le, h1.le⟩

lemma bZ_half {T0 : ℝ} (hRH : RHUpTo T0) (i : ZI) (h : |gZ i| ≤ T0) : bZ i = 1 / 2 := by
  obtain ⟨hz, h0, h1⟩ := mem_strip i.1
  exact hRH _ hz h0 h1 h

/-- **Lemma 3 of Ramaré-Saouter 2003, p. 15**, for the nontrivial zeros of ζ with multiplicity.
PROVED CONDITIONAL ON `RHUpTo T0` and `Lemma1Count gZ`. -/
theorem lemma3_zeta {T0 : ℝ} (hRH : RHUpTo T0) (hN : Lemma1Count gZ) :
    Lemma3Bound (ZsF gZ bZ) T0 :=
  lemma3_of hN σZ σZ_injective gZ_σ bZ_σ bZ_mem (bZ_half hRH)

/-- **Table 1 row one.** PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
`SchoenfeldPT 0.998697 1.001093`, `JLower15 NT (ZsF gZ bZ) 3.3e9`, `RHUpTo 3.3e9`,
`Lemma1Count gZ` and `Lemma1Upper NT`. -/
theorem theorem2At1e20_of_zeta (hMV : Thm4Parts.MVBrunTitchmarsh)
    (hS : Thm4Parts.SchoenfeldPT 0.998697 1.001093) {NT : ℝ → ℝ}
    (h15 : JLower15 NT (ZsF gZ bZ) 3300000000) (hRH : RHUpTo 3300000000)
    (hN : Lemma1Count gZ) (hU : Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  theorem2At1e20_of_split hMV hS h15 (lemma3_zeta hRH hN) hU

end LeanLab.RamareSaouter2003.L3Zeta

#print axioms LeanLab.RamareSaouter2003.L3Zeta.σZ_injective
#print axioms LeanLab.RamareSaouter2003.L3Zeta.lemma3_zeta
#print axioms LeanLab.RamareSaouter2003.L3Zeta.theorem2At1e20_of_zeta

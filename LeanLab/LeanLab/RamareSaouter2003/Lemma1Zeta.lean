import Mathlib
import LeanLab.RamareSaouter2003.Lemma3Zeta
import LeanLab.PNTPort.ExplicitPsi1.Residues

/-!
# Ramaré-Saouter 2003, Lemma 1 for the true zero counting function of ζ

P0099, unit U-6773, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

* `NZ t`: the true `N(t)`, the number of nontrivial zeros of ζ with `0 < Im ρ ≤ t`, counted
  with multiplicity, defined as the card of an explicit `Finset` of `ZI`. Finiteness is
  PROVED from `zeros_rect_finite` of `PNTPort/ExplicitPsi1/Residues.lean`.
* `Lemma1N`: Lemma 1 of p. 14 as printed, `|N(T) - M(T)| ≤ 0.67 log(T/2π)` for `T ≥ 10^3`,
  for this true `N`. CITED, Rosser 1941 Theorem 19; `Lemma1Rosser.lemma1_of_rosser` derives
  this exact form from `RosserN`.
* `lemma1Count_zeta`: `Lemma1Count gZ` of `Lemma3Zeros.lean`, counts with both signs of the
  ordinate over any finite set, PROVED CONDITIONAL ON `Lemma1N`. The negative ordinates are
  sent to positive ones by the functional equation symmetry `σZ`, `ρ ↦ 1 - ρ`, which keeps
  multiplicity by `ZetaZeros.ord_one_sub`, so the conjugate symmetry with multiplicity is not
  needed.
* `theorem2At1e20_of_N`: Table 1 row one, PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
  `SchoenfeldPT 0.998697 1.001093`, `JLower15 NZr (ZsF gZ bZ) 3.3e9`, `RHUpTo 3.3e9` and
  `Lemma1N`, with `NZr` the true `N` as a real function.
-/

namespace LeanLab.RamareSaouter2003.L1Zeta

open Complex Set Real
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.RamareSaouter2003.L3Zeros
  LeanLab.RamareSaouter2003.L3Zeta LeanLab.RamareSaouter2003.Thm4JSplit
  LeanLab.RamareSaouter2003.Smooth

local notation "ζ" => riemannZeta

/-- The zeros, with multiplicity, of ordinate in `(0, t]`, a finite set. PROVED. -/
lemma posSet_finite (t : ℝ) : {i : ZI | 0 < gZ i ∧ gZ i ≤ t}.Finite := by
  have hS : {ρ : Zall | (ρ : ℂ) ∈ Rectangle ⟨-1 / 2, -|t|⟩ ⟨1, |t|⟩ ∩ riemannZetaZeros}.Finite :=
    (zeros_rect_finite 1 |t|).preimage Subtype.val_injective.injOn
  have hsig := hS.sigma (t := fun ρ : Zall => (univ : Set (Fin (analyticOrderNatAt ζ (ρ : ℂ)))))
    (fun _ _ => Set.toFinite _)
  apply hsig.subset
  rintro ⟨ρ, k⟩ ⟨h0, h1⟩
  refine ⟨?_, mem_univ _⟩
  obtain ⟨hz, hr0, hr1⟩ := mem_strip ρ
  simp only [mem_ofPred_eq]
  refine ⟨(mem_rect (by norm_num) (abs_nonneg t)).mpr ⟨⟨by linarith, hr1.le⟩, ?_⟩, hz⟩
  simp only [gZ] at h0 h1
  constructor
  · linarith [abs_nonneg t]
  · exact h1.trans (le_abs_self t)

/-- The zeros with `0 < Im ρ ≤ t`, with multiplicity. -/
noncomputable def A (t : ℝ) : Finset ZI := (posSet_finite t).toFinset

lemma mem_A {t : ℝ} {i : ZI} : i ∈ A t ↔ 0 < gZ i ∧ gZ i ≤ t := by
  simp [A]

/-- **The true `N(t)`**, nontrivial zeros of ζ with `0 < Im ρ ≤ t`, with multiplicity. -/
noncomputable def NZ (t : ℝ) : ℕ := (A t).card

/-- `N` as a real function. -/
noncomputable def NZr (t : ℝ) : ℝ := (NZ t : ℝ)

/-- **Lemma 1 of Ramaré-Saouter 2003, p. 14**, as printed, for the true `N`. CITED. -/
def Lemma1N : Prop :=
  ∀ T : ℝ, 1000 ≤ T →
    |NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      0.67 * Real.log (T / (2 * π))

lemma gZ_σ_neg (i : ZI) : gZ (σZ i) = - gZ i := by
  simp [gZ, σZ]

/-- Counts over a finite set of the zeros with `T < Im ρ ≤ t` are at most `N(t) - N(T)`. -/
lemma card_pos_le {T t : ℝ} (hT : 0 ≤ T) (s : Finset ZI) :
    (s.filter (fun i => T < gZ i ∧ gZ i ≤ t)).card ≤ (A t \ A T).card := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_sdiff, mem_A, mem_A]
  refine ⟨⟨by linarith [hi.2.1], hi.2.2⟩, ?_⟩
  rintro ⟨_, h2⟩
  linarith [hi.2.1]

lemma A_mono {T t : ℝ} (h : T ≤ t) : A T ⊆ A t := by
  intro i hi
  rw [mem_A] at hi ⊢
  exact ⟨hi.1, hi.2.trans h⟩

/-- `Lemma1Count gZ` from Lemma 1 for the true `N`. PROVED CONDITIONAL ON `Lemma1N`. -/
theorem lemma1Count_zeta (h : Lemma1N) : Lemma1Count gZ := by
  intro T t hT hTt s
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set Fp := s.filter (fun i => T < gZ i ∧ gZ i ≤ t)
  set Fn := s.filter (fun i => T < -gZ i ∧ -gZ i ≤ t)
  have hsub : s.filter (fun i => T < |gZ i| ∧ |gZ i| ≤ t) ⊆ Fp ∪ Fn := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt 0 (gZ i) with hg | hg
    · left; rw [abs_of_nonneg hg] at hi; exact hi
    · right; rw [abs_of_neg hg] at hi; exact hi
  have hn : Fn.card ≤ (A t \ A T).card := by
    rw [← Finset.card_image_of_injective Fn σZ_injective]
    refine le_trans (Finset.card_le_card ?_) (card_pos_le hT0 (s.image σZ))
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_filter] at hi ⊢
    rw [gZ_σ_neg]
    exact ⟨Finset.mem_image_of_mem _ hi.1, hi.2⟩
  have hp : Fp.card ≤ (A t \ A T).card := card_pos_le hT0 s
  have hc : (s.filter (fun i => T < |gZ i| ∧ |gZ i| ≤ t)).card ≤ 2 * (A t \ A T).card := by
    calc _ ≤ (Fp ∪ Fn).card := Finset.card_le_card hsub
      _ ≤ Fp.card + Fn.card := Finset.card_union_le _ _
      _ ≤ 2 * (A t \ A T).card := by omega
  have hsd : (A t \ A T).card + (A T).card = (A t).card :=
    Finset.card_sdiff_add_card_eq_card (A_mono hTt)
  have hsdR : ((A t \ A T).card : ℝ) = NZr t - NZr T := by
    unfold NZr NZ; rw [← hsd]; push_cast; ring
  have ht := h t (by linarith)
  have hT1 := h T hT
  rw [abs_le] at ht hT1
  have hcR : ((s.filter (fun i => T < |gZ i| ∧ |gZ i| ≤ t)).card : ℝ) ≤
      2 * ((A t \ A T).card : ℝ) := by exact_mod_cast hc
  rw [hsdR] at hcR
  refine hcR.trans ?_
  unfold MN EN ℓ
  linarith [ht.2, hT1.1]

/-- **Table 1 row one.** PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
`SchoenfeldPT 0.998697 1.001093`, `JLower15 NZr (ZsF gZ bZ) 3.3e9`, `RHUpTo 3.3e9` and
`Lemma1N`, Lemma 1 for the true `N`. -/
theorem theorem2At1e20_of_N (hMV : Thm4Parts.MVBrunTitchmarsh)
    (hS : Thm4Parts.SchoenfeldPT 0.998697 1.001093)
    (h15 : JLower15 NZr (ZsF gZ bZ) 3300000000) (hRH : RHUpTo 3300000000)
    (h1 : Lemma1N) : Theorem2At1e20 :=
  theorem2At1e20_of_zeta hMV hS h15 hRH (lemma1Count_zeta h1)
    (fun T hT => by
      have := (abs_le.mp (h1 T hT)).2
      linarith)

end LeanLab.RamareSaouter2003.L1Zeta

#print axioms LeanLab.RamareSaouter2003.L1Zeta.posSet_finite
#print axioms LeanLab.RamareSaouter2003.L1Zeta.lemma1Count_zeta
#print axioms LeanLab.RamareSaouter2003.L1Zeta.theorem2At1e20_of_N

import LeanLab.ExceptionalSet.UpJ200.DQDecomp559bRoute
import LeanLab.ExceptionalSet.Prep1121SingSeries
import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Burst 2026-11-22 unit P1122-0127, REPAIR wiring of
`Decomp559b.pointwise_major_character_from_selected_cases`.
Source P0082, Brudern and Perelli 1998, Ann. Inst. Fourier 48, pages 358 to 364, Lemma 7,
doi 10.5802/aif.1621.

The assembly of `DQDecomp559bAssembly.pointwise_major_character_of_hyps` is copied here with
its four case leaves repointed to the wired forms below. Each wired leaf is the conditional
decision of its DQ file with every in-place input discharged by a proved theorem:

* page 362 case i, the singular series lower bound of display 11, by
  `Prep1121SingSeries.singularSeriesEvenLowerBP_split` and `singSeriesLowerHyp_split`;
* page 358 display 10, the real zero distance, by
  `Task672.landauRealZeroHyp_proved672` and `Task672.realZeroDistanceHyp_proved672`.

What is left are four named citation walls, one per case:
`DQLeafAbsentSelected.Lemma2NoExcBP` for case i, Montgomery and Vaughan through P0082 Lemma 2;
`DQLeafCoprimeSelected.BPLemma3CoprimeHyp` for case ii a, P0082 Lemma 3;
`DQLeafPrimeProductSelected.PrimeProductSelectedP0082` for case ii b, display 21;
`DQLeafNearZeroSelected.CaseIIdMajorLowerHyp` for case ii d.
No new definition and no admitted step. No existing statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero leaf_selected_real_zero
  selected_shape)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (Lemma2NoExcBP)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (BPLemma3CoprimeHyp)
open LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected (PrimeProductSelectedP0082)
open LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected (CaseIIdMajorLowerHyp)

/-- P0082 page 362 Lemma 7 case i. The exact type of `Decomp559b.leaf_absent_selected`.
CONDITIONAL ON `Lemma2NoExcBP` only; display 11 is discharged by `Prep1121SingSeries`. -/
theorem leaf_absent_selected_wired (hL : Lemma2NoExcBP) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
  LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.leaf_absent_selected_of_lemma2_only hL

/-- P0082 page 363 case ii a. The exact type of `Decomp559b.leaf_coprime_selected`.
CONDITIONAL ON `BPLemma3CoprimeHyp` only; display 11 is discharged by `Prep1121SingSeries`
and display 10 by `Task672.landauRealZeroHyp_proved672`. -/
theorem leaf_coprime_selected_wired (hL3 : BPLemma3CoprimeHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected :=
  LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.leaf_coprime_selected_of_two_hyps hL3
    LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672

/-- P0082 page 363 case ii b and display 21. The exact type of
`Decomp559b.leaf_prime_product_selected`. CONDITIONAL ON `PrimeProductSelectedP0082`. -/
theorem leaf_prime_product_selected_wired (H : PrimeProductSelectedP0082) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected :=
  LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.leaf_prime_product_selected_of_hyp H

/-- P0082 page 364 case ii d. The exact type of `Decomp559b.leaf_near_zero_selected`.
CONDITIONAL ON `CaseIIdMajorLowerHyp` only; display 10 is discharged by
`Task672.realZeroDistanceHyp_proved672`. -/
theorem leaf_near_zero_selected_wired (hII : CaseIIdMajorLowerHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected :=
  LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.leaf_near_zero_selected_of_hyps hII
    LeanLab.ExceptionalSet.Task672.realZeroDistanceHyp_proved672

/-- P0082 pages 362 to 364 Lemma 7. The statement of
`Decomp559b.pointwise_major_character_from_selected_cases`, by its proof with the four case
leaves replaced by the wired leaves above and the proved `leaf_selected_real_zero`.
CONDITIONAL ON the four named citation walls `Lemma2NoExcBP`, `BPLemma3CoprimeHyp`,
`PrimeProductSelectedP0082` and `CaseIIdMajorLowerHyp`; no admitted step. -/
theorem pointwise_major_character_wired
    (hL : Lemma2NoExcBP) (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            (r = 1 ∨ ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r),
              χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              let Y := (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)
              (r = 1 → c * F γ N ≤ Y) ∧
              (r ≠ 1 → Int.gcd (nu γ n + j) r = 1 → c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                  c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                  c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y) := by
  obtain ⟨a, hapos, hselect⟩ := leaf_selected_real_zero
  obtain ⟨δa, hδa, ha⟩ := leaf_absent_selected_wired hL γ h1 h2 a hapos
  obtain ⟨δb, hδb, hb⟩ := leaf_coprime_selected_wired hL3 γ h1 h2 a hapos
  obtain ⟨δd, hδd, hd⟩ := leaf_prime_product_selected_wired H γ h1 h2 a hapos
  obtain ⟨δe, hδe, he⟩ := leaf_near_zero_selected_wired hII γ h1 h2 a hapos
  refine ⟨min δa (min δb (min δd δe)), lt_min hδa (lt_min hδb (lt_min hδd hδe)), ?_⟩
  intro δ hδ hδsmall
  have hdeltas := lt_min_iff.mp hδsmall
  have hdeltas' := lt_min_iff.mp hdeltas.2
  have hdeltas'' := lt_min_iff.mp hdeltas'.2
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ hdeltas.1
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ hdeltas'.1
  obtain ⟨κd, hκd, hd⟩ := hd δ hδ hdeltas''.1
  obtain ⟨κe, hκe, he⟩ := he δ hδ hdeltas''.2
  refine ⟨min κa (min κb (min κd κe)), lt_min hκa (lt_min hκb (lt_min hκd hκe)), ?_⟩
  intro κ hκ hκsmall
  have hkappas := le_min_iff.mp hκsmall
  have hkappas' := le_min_iff.mp hkappas.2
  have hkappas'' := le_min_iff.mp hkappas'.2
  obtain ⟨ca, Aa, hca, hAa, Na, ha⟩ := ha κ hκ hkappas.1
  obtain ⟨cb, Ab, hcb, hAb, Nb, hb⟩ := hb κ hκ hkappas'.1
  obtain ⟨cd, Ad, hcd, hAd, Nd, hd⟩ := hd κ hκ hkappas''.1
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hkappas''.2
  let c := min ca (min cb (min cd ce))
  let A := Aa + Ab + Ad + Ae
  have hc : 0 < c := lt_min hca (lt_min hcb (lt_min hcd hce))
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp (hP.eventually_ge_atTop 2)
  refine ⟨c, A, hc, hA, max Np (max Na (max Nb (max Nd Ne))), ?_⟩
  intro N hN
  have hNs := max_le_iff.mp hN
  have hNs' := max_le_iff.mp hNs.2
  have hNs'' := max_le_iff.mp hNs'.2
  have hNs''' := max_le_iff.mp hNs''.2
  obtain ⟨r, hr, hrP, hs⟩ := hselect _ (hNp N hNs.1)
  refine ⟨r, hr, hrP, selected_shape a _ r hs, ?_⟩
  intro j hj n hn heven hm
  dsimp only
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hca' : c ≤ ca := min_le_left _ _
  have hcb' : c ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have hcd' : c ≤ cd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hce' : c ≤ ce := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAa' : Aa ≤ A := by dsimp [A]; linarith
  have hAb' : Ab ≤ A := by dsimp [A]; linarith
  have hAd' : Ad ≤ A := by dsimp [A]; linarith
  have hAe' : Ae ≤ A := by dsimp [A]; linarith
  have transfer (ci Ai w : ℝ) (hw : 0 ≤ w) (hci : c ≤ ci) (hAi : Ai ≤ A)
      (h : ci * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)) :
      c * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    have hleft := mul_le_mul_of_nonneg_right hci (mul_nonneg hX hw)
    have hright := mul_le_mul_of_nonneg_right hAi (mul_nonneg hX hD)
    nlinarith only [hleft, hright, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcase
    have hh := ha N hNs'.1 r hr hrP hs j hj n hn heven hm hcase
    simpa only [mul_one] using transfer ca Aa 1 (by norm_num) hca' hAa' (by simpa using hh)
  · intro hcase hgcd
    have hh := hb N hNs''.1 r hr hrP hs j hj n hn heven hm hcase hgcd
    simpa only [mul_one] using transfer cb Ab 1 (by norm_num) hcb' hAb' (by simpa using hh)
  · intro hgcd hprime
    have hh := hd N hNs'''.1 r hr hrP hs j hj n hn heven hm hgcd hprime
    simpa only [mul_one] using transfer cd Ad 1 (by norm_num) hcd' hAd' (by simpa using hh)
  · intro hgcd hprime hsmall
    exact transfer ce Ae _ (Real.rpow_nonneg (Real.exp_pos _).le _) hce' hAe'
      (he N hNs'''.2 r hr hrP hs j hj n hn heven hm hgcd hprime hsmall)

/-- Twin check: the wired theorem has exactly the type of
`Decomp559b.pointwise_major_character_from_selected_cases`. CONDITIONAL ON the same four
named citation walls. -/
theorem pointwise_major_character_wired_twin
    (hL : Lemma2NoExcBP) (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.pointwise_major_character_from_selected_cases :=
  pointwise_major_character_wired hL hL3 H hII

/-- The DQ5 named hypothesis `Decomp527a.PointwiseMajorCharacterDQ5`, the sealed statement
of `Decomp527a.leaf_pointwise_major_character`, from the four named citation walls.
CONDITIONAL ON `Lemma2NoExcBP`, `BPLemma3CoprimeHyp`, `PrimeProductSelectedP0082` and
`CaseIIdMajorLowerHyp`. -/
theorem pointwiseMajorCharacterDQ5_wired
    (hL : Lemma2NoExcBP) (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) :
    LeanLab.ExceptionalSet.UpJ200.Decomp527a.PointwiseMajorCharacterDQ5 :=
  fun γ h1 h2 => pointwise_major_character_wired hL hL3 H hII γ h1 h2

/-- P0082 pages 362 to 364 Lemma 7, the statement of `Decomp527a.pointwise_lower_from_cases`.
CONDITIONAL ON the same four named citation walls and on what
`Decomp527a.pointwise_lower_of_named_dq5` uses, reported by `#print axioms`. -/
theorem pointwise_lower_wired
    (hL : Lemma2NoExcBP) (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_from_cases :=
  LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_of_named_dq5
    (pointwiseMajorCharacterDQ5_wired hL hL3 H hII)

end LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire

#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_absent_selected_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_coprime_selected_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_prime_product_selected_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_near_zero_selected_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.pointwise_major_character_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.pointwise_major_character_wired_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.pointwiseMajorCharacterDQ5_wired
#print axioms LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.pointwise_lower_wired

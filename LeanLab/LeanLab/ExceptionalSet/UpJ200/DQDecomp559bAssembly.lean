import LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions

/-!
CITED WALL assembly for `Decomp559b.pointwise_major_character_from_selected_cases`, session
CLOUD-cited-decomp559b-p2, 2026-11-20. Source P0082, Brüdern and Perelli 1998,
Ann. Inst. Fourier 48, pages 358 to 364, Lemma 7.

The four case leaves of `Decomp559b` were each decided as NAMED HYPOTHESES on separate
branches. This file replays the proof of `pointwise_major_character_from_selected_cases`
with the four conditional `_of_hyps` theorems in place of the open leaves, and with the
proved `Decomp559b.leaf_selected_real_zero`. The result has exactly the type of the route
theorem. CONDITIONAL ON the eight named hypotheses

* `DQLeafAbsentSelected.Lemma2NoExcBP`, `DQLeafAbsentSelected.SingularSeriesEvenLowerBP`,
* `DQLeafCoprimeSelected.BPLemma3CoprimeHyp`, `DQLeafCoprimeSelected.SingSeriesLowerHyp`,
  `DQLeafCoprimeSelected.LandauRealZeroHyp`,
* `DQLeafPrimeProductSelected.PrimeProductSelectedP0082`,
* `DQLeafNearZeroSelected.CaseIIdMajorLowerHyp`, `DQLeafNearZeroSelected.RealZeroDistanceHyp`.

It also proves that the duplicate notions are equivalent: `LandauRealZeroHyp` and
`RealZeroDistanceHyp` imply each other, `singSeries` and `singularSeries` agree on naturals,
and `SingSeriesLowerHyp` and `SingularSeriesEvenLowerBP` imply each other. So the assembly
also holds from six named hypotheses, `pointwise_major_character_of_six_hyps`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero leaf_selected_real_zero
  selected_shape)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (Lemma2NoExcBP
  SingularSeriesEvenLowerBP singularSeries leaf_absent_selected_of_lemma2)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (BPLemma3CoprimeHyp
  SingSeriesLowerHyp LandauRealZeroHyp singSeries leaf_coprime_selected_of_hyps)
open LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected (PrimeProductSelectedP0082
  leaf_prime_product_selected_of_hyp)
open LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected (CaseIIdMajorLowerHyp
  RealZeroDistanceHyp leaf_near_zero_selected_of_hyps)

/-- P0082 pages 362 to 364 Lemma 7. The exact statement of
`Decomp559b.pointwise_major_character_from_selected_cases`, by the same proof with the four
case leaves replaced by their conditional decisions. CONDITIONAL ON the eight named
hypothesis arguments, six independent notions up to the equivalences below; no admitted step. -/
theorem pointwise_major_character_of_hyps
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (hS : SingSeriesLowerHyp) (hLa : LandauRealZeroHyp)
    (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp)
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
  obtain ⟨δa, hδa, ha⟩ := leaf_absent_selected_of_lemma2 hL hSa γ h1 h2 a hapos
  obtain ⟨δb, hδb, hb⟩ := leaf_coprime_selected_of_hyps hL3 hS hLa γ h1 h2 a hapos
  obtain ⟨δd, hδd, hd⟩ := leaf_prime_product_selected_of_hyp H γ h1 h2 a hapos
  obtain ⟨δe, hδe, he⟩ := leaf_near_zero_selected_of_hyps hII hZ γ h1 h2 a hapos
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

/-- Twin check: the assembled theorem has exactly the type of the route theorem
`Decomp559b.pointwise_major_character_from_selected_cases`. CONDITIONAL ON the same
named hypotheses. -/
theorem pointwise_major_character_twin
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (hS : SingSeriesLowerHyp) (hLa : LandauRealZeroHyp)
    (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.pointwise_major_character_from_selected_cases :=
  pointwise_major_character_of_hyps hL hSa hL3 hS hLa H hII hZ

/-! ## The duplicate notions across the four branches -/

/-- A nonprincipal character has modulus at least two. PROVED. -/
theorem two_le_of_ne_one (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hne : χ ≠ 1) :
    2 ≤ r := by
  have h0 : r ≠ 0 := NeZero.ne r
  by_contra h
  have hr : r = 1 := by omega
  subst hr
  exact hne (DirichletCharacter.level_one χ)

/-- P0082 display 10 in the two spellings: the coprime branch's `LandauRealZeroHyp`
implies the near zero branch's `RealZeroDistanceHyp`, with the same constant. PROVED. -/
theorem realZeroDistance_of_landau (h : LandauRealZeroHyp) : RealZeroDistanceHyp := by
  obtain ⟨c₃, hc₃, h⟩ := h
  refine ⟨c₃, hc₃, fun r hr χ hp hsq hne β _ hβ1 hz => ?_⟩
  have h2 : 2 ≤ r := two_le_of_ne_one r χ hne
  have hr1 : (1 : ℝ) < r := by exact_mod_cast h2
  have hlog : 0 < Real.log r := Real.log_pos hr1
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr (by linarith)
  have hb := h r hr χ β hp hsq hne hβ1 hz
  rw [div_le_iff₀ (by positivity)] at hb
  rw [← Real.sqrt_eq_rpow]
  linarith

/-- The converse: `RealZeroDistanceHyp` implies `LandauRealZeroHyp`, with the constant
`min c₀ (√2 (log 2)^2)`; for `β ≤ 0` the bound is trivial. PROVED. -/
theorem landau_of_realZeroDistance (h : RealZeroDistanceHyp) : LandauRealZeroHyp := by
  obtain ⟨c₀, hc₀, h⟩ := h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD2 : 0 < Real.sqrt 2 * Real.log 2 ^ 2 := by positivity
  refine ⟨min c₀ (Real.sqrt 2 * Real.log 2 ^ 2), lt_min hc₀ hD2,
    fun r hr χ β hp hsq hne hβ1 hz => ?_⟩
  have h2 : 2 ≤ r := two_le_of_ne_one r χ hne
  have h2' : (2 : ℝ) ≤ r := by exact_mod_cast h2
  have hlog2 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) h2'
  have hsqrt2 : Real.sqrt 2 ≤ Real.sqrt r := Real.sqrt_le_sqrt h2'
  have hDge : Real.sqrt 2 * Real.log 2 ^ 2 ≤ Real.sqrt r * Real.log r ^ 2 :=
    mul_le_mul hsqrt2 (pow_le_pow_left₀ hl2.le hlog2 2) (by positivity) (Real.sqrt_nonneg _)
  have hD : 0 < Real.sqrt r * Real.log r ^ 2 := lt_of_lt_of_le hD2 hDge
  rw [div_le_iff₀ hD]
  rcases le_or_gt β 0 with hβ | hβ
  · have : min c₀ (Real.sqrt 2 * Real.log 2 ^ 2) ≤ Real.sqrt r * Real.log r ^ 2 :=
      (min_le_right _ _).trans hDge
    nlinarith
  · have hb := h r hr χ hp hsq hne β hβ hβ1 hz
    rw [← Real.sqrt_eq_rpow] at hb
    have : min c₀ (Real.sqrt 2 * Real.log 2 ^ 2) ≤ c₀ := min_le_left _ _
    nlinarith

/-- `singSeries` of the coprime branch, on integers, and `singularSeries` of the absent
branch, on naturals, are the same product of P0082 display 11. PROVED. -/
theorem singSeries_natCast (m : ℕ) : singSeries (m : ℤ) = singularSeries m := by
  unfold singSeries singularSeries
  congr 1
  funext p
  simp only [Int.natCast_dvd_natCast]

/-- The two spellings of the bound `𝔖(m) ≫ m / φ(m)` for even `m` of P0082 page 362
imply each other, first direction. PROVED. -/
theorem singularSeriesEvenLower_of_singSeriesLower (h : SingSeriesLowerHyp) :
    SingularSeriesEvenLowerBP := by
  obtain ⟨c₀, hc₀, h⟩ := h
  refine ⟨c₀, hc₀, fun m hm he => ?_⟩
  have hh := h (m : ℤ) (by exact_mod_cast hm) ((Int.even_coe_nat m).mpr he)
  rwa [singSeries_natCast, Int.toNat_natCast] at hh

/-- Second direction. PROVED. -/
theorem singSeriesLower_of_singularSeriesEvenLower (h : SingularSeriesEvenLowerBP) :
    SingSeriesLowerHyp := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun m hm he => ?_⟩
  lift m to ℕ using (by omega)
  have hh := h m (by exact_mod_cast hm) ((Int.even_coe_nat m).mp he)
  rwa [singSeries_natCast, Int.toNat_natCast]

/-- The route theorem from six named hypotheses, using the equivalences
above to drop `SingSeriesLowerHyp` and `LandauRealZeroHyp`. CONDITIONAL ON
`Lemma2NoExcBP`, `SingularSeriesEvenLowerBP`, `BPLemma3CoprimeHyp`,
`PrimeProductSelectedP0082`, `CaseIIdMajorLowerHyp` and `RealZeroDistanceHyp`;
no admitted step. -/
theorem pointwise_major_character_of_six_hyps
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.pointwise_major_character_from_selected_cases :=
  pointwise_major_character_of_hyps hL hSa hL3
    (singSeriesLower_of_singularSeriesEvenLower hSa) (landau_of_realZeroDistance hZ) H hII hZ

end LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly

#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_major_character_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_major_character_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.two_le_of_ne_one
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.realZeroDistance_of_landau
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.landau_of_realZeroDistance
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.singSeries_natCast
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.singularSeriesEvenLower_of_singSeriesLower
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.singSeriesLower_of_singularSeriesEvenLower
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_major_character_of_six_hyps

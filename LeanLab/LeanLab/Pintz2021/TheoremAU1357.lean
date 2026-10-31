/-
Pin2 = J. Pintz, arXiv 1804.09084, Section 2: Theorem A, the explicit formula (2.10), with the
bound (2.11) on the generalized singular series, and Theorem B (2.17), stated as hypotheses.
Unit U-1357, PC run 20261021T0604Z-1697, track T2, paper P0054.

* `ZeroData K`: the generalized exceptional singularities `(ϱ_i, χ_i)` of (2.7), `i < K`, with
  `A(ϱ_i) = ±1` of (2.8), moduli `r_i`, and the generalized singular series `𝔖(χ_i, χ_j, m)`.
* `mainTerm`: the double sum of (2.10).
* `TheoremA_210`, `Hyp_211`: (2.10) and (2.11) on one block `m ∈ (Y/2, Y]`, `2 ∣ m`.
* `RemainingMain`: the lower bound for the main term on the classes with `q(ℛ') ≤ Y^ϑ`, the
  outcome of (2.18) to (2.41) of Pin2 in the case without a Siegel zero; a named hypothesis.
* `TheoremB_217`: Theorem B, (2.16) and (2.17), a named hypothesis.
* `classClause_of_theoremA`: PROVED from these hypotheses, the class clause of
  `Section3MajorInputLevels` with `κ = ϑ`.
* `majorLevels_of_pin2`: CONDITIONAL, `Section3MajorInputLevels ϑ ϑ ε`, so κ = ϑ.
No improvement on 0.72 is claimed. Binary Goldbach is OPEN. AI-written Lean code, Claude.
-/
import Mathlib
import LeanLab.Pintz2021.ExponentU1341

namespace LeanLab.Pintz2021.TheoremAU1357

open Real Finset Filter Topology MeasureTheory LeanLab.ExceptionalSet
open LeanLab.Pintz2021.Applications LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.Theorem3Prime LeanLab.Pintz2021.ExponentU1341

attribute [local instance] Classical.propDecidable

/-- The data of (2.7), (2.8): `K` generalized exceptional singularities `ϱ_i` with characters
of modulus `r_i`, the signs `A(ϱ_i)`, and the generalized singular series `𝔖(χ_i, χ_j, m)`. -/
structure ZeroData (K : ℕ) where
  A : Fin K → ℝ
  ρ : Fin K → ℂ
  r : Fin K → ℕ
  Sg : Fin K → Fin K → ℕ → ℂ

/-- The main term of (2.10):
`∑_i ∑_j A(ϱ_i) A(ϱ_j) 𝔖(χ_i,χ_j,m) Γ(ϱ_i)Γ(ϱ_j)/Γ(ϱ_i+ϱ_j) m^{ϱ_i+ϱ_j-1}`. -/
noncomputable def mainTerm {K : ℕ} (D : ZeroData K) (m : ℕ) : ℂ :=
  ∑ i, ∑ j, ((D.A i : ℂ) * D.A j) * D.Sg i j m *
    (Complex.Gamma (D.ρ i) * Complex.Gamma (D.ρ j) / Complex.Gamma (D.ρ i + D.ρ j)) *
    (m : ℂ) ^ (D.ρ i + D.ρ j - 1)

/-- (2.8): `A(ϱ) = ±1`, and the moduli of (2.7) lie in `[1, P]`. -/
def ZeroShape {K : ℕ} (D : ZeroData K) (P : ℝ) : Prop :=
  (∀ i, D.A i = 1 ∨ D.A i = -1) ∧ ∀ i, 1 ≤ D.r i ∧ (D.r i : ℝ) ≤ P

/-- Theorem A, display (2.10), on the block `(Y/2, Y]`, with the implied constant `Cerr`:
`‖R₁(m) - main(m)‖ ≤ Cerr (Y e^{-cH} + Y/√T + Y^{1-ε})` for even `m`. -/
def TheoremA_210 (R1 : ℕ → ℂ) (Y : ℕ) (ε c H T Cerr : ℝ) {K : ℕ} (D : ZeroData K) : Prop :=
  ∀ m ∈ Ioc (Y / 2) Y, Even m →
    ‖R1 m - mainTerm D m‖ ≤
      Cerr * ((Y : ℝ) * Real.exp (-(c * H)) + (Y : ℝ) / Real.sqrt T + (Y : ℝ) ^ (1 - ε))

/-- Display (2.11): `|𝔖(χ_i, χ_j, m)| ≤ 𝔖(m)`; for even `m` the `𝔖(m)` of Pin2 (2.9) is the
lab's `Sing m` of P0054 (2.4). -/
def Hyp_211 {K : ℕ} (D : ZeroData K) : Prop :=
  ∀ i j m, Even m → ‖D.Sg i j m‖ ≤ Sing m

/-- `q(ℛ'(m))`, the lcm of the moduli `r_i` dividing `C m`, as in (2.25) of Pin2. -/
def qOf {K : ℕ} (D : ZeroData K) (C m : ℕ) : ℕ :=
  ((univ : Finset (Fin K)).filter (fun i => D.r i ∣ C * m)).lcm D.r

/-- The named hypothesis on the remaining classes: when `q(ℛ'(m)) ≤ Y^ϑ` the main term is at
least `2δY`. Pin2 derives this, in the case without a Siegel zero, from (2.12), (2.13), (2.18)
to (2.21) and the zero density estimates; it is not proved here. -/
def RemainingMain {K : ℕ} (D : ZeroData K) (Y C : ℕ) (ϑ δ : ℝ) : Prop :=
  ∀ m ∈ Ioc (Y / 2) Y, Even m → ((qOf D C m : ℕ) : ℝ) ≤ (Y : ℝ) ^ ϑ →
    2 * δ * Y ≤ (mainTerm D m).re

/-- Theorem B, (2.16), (2.17), with the Siegel zero condition as a predicate `siegel X`:
if `X` is large and `siegel X` then `E(X) < X^{3/5+ε'}`. -/
def TheoremB_217 (siegel : ℕ → Prop) (ε' : ℝ) : Prop :=
  ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → siegel X → (E X : ℝ) < (X : ℝ) ^ (3 / 5 + ε')

/-- HELPER: the lcm of the `r_i` dividing `C m` divides `C m`. -/
theorem qOf_dvd {K : ℕ} (D : ZeroData K) (C m : ℕ) : qOf D C m ∣ C * m :=
  Finset.lcm_dvd fun i hi => (mem_filter.mp hi).2

/-- The classes `q(ℛ')` above `Y^ϑ`, one for each subset `ℛ'`. -/
noncomputable def bigClasses {K : ℕ} (D : ZeroData K) (Y : ℕ) (ϑ : ℝ) : Finset ℕ :=
  (((univ : Finset (Fin K)).powerset.filter
    (fun s => (Y : ℝ) ^ ϑ < ((s.lcm D.r : ℕ) : ℝ))).image fun s => s.lcm D.r)

/-- HELPER: at most `2^K` classes, the bound `C₂(ε) = 2^{K(ε)}` of Pin2. -/
theorem card_bigClasses_le {K : ℕ} (D : ZeroData K) (Y : ℕ) (ϑ : ℝ) :
    (bigClasses D Y ϑ).card ≤ 2 ^ K := by
  unfold bigClasses
  calc _ ≤ _ := card_image_le
    _ ≤ ((univ : Finset (Fin K)).powerset).card := card_filter_le _ _
    _ = 2 ^ K := by rw [card_powerset, card_univ, Fintype.card_fin]

/-- HELPER: every class in `bigClasses` is above `Y^ϑ`. -/
theorem bigClasses_ge {K : ℕ} (D : ZeroData K) (Y : ℕ) (ϑ : ℝ) :
    ∀ R0 ∈ bigClasses D Y ϑ, (Y : ℝ) ^ ϑ ≤ R0 := by
  intro R0 h
  unfold bigClasses at h
  obtain ⟨s, hs, rfl⟩ := mem_image.mp h
  exact (mem_filter.mp hs).2.le

/-- PROVED from the named hypotheses (2.10) and `RemainingMain`, on one block: every even
`m ∈ (Y/2, Y]` with `Re R₁(m) ≤ Y^{1-ε}` lies in a class `R0 ∣ C m` with `R0 > Y^ϑ`, among at
most `2^K` classes. The size condition `hY` holds for all large `Y`, `eventually_hY`. -/
theorem classClause_of_theoremA {K C Y : ℕ} {ϑ ε δ c H T Cerr : ℝ} (D : ZeroData K)
    (R1 : ℕ → ℂ) (hCerr : 0 ≤ Cerr) (hHT : Cerr * (Real.exp (-(c * H)) + 1 / Real.sqrt T) ≤ δ / 2)
    (hY : Cerr * (Y : ℝ) ^ (1 - ε) + (Y : ℝ) ^ (1 - ε) < δ * Y)
    (hA : TheoremA_210 R1 Y ε c H T Cerr D) (hR : RemainingMain D Y C ϑ δ) :
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ bigClasses D Y ϑ, R0 ∣ C * m) ∧
    (∀ R0 ∈ bigClasses D Y ϑ, (Y : ℝ) ^ ϑ ≤ R0) ∧ (bigClasses D Y ϑ).card ≤ 2 ^ K := by
  refine ⟨fun m hm he hle => ?_, bigClasses_ge D Y ϑ, card_bigClasses_le D Y ϑ⟩
  by_cases hq : ((qOf D C m : ℕ) : ℝ) ≤ (Y : ℝ) ^ ϑ
  · exfalso
    have hmain := hR m hm he hq
    have herr := hA m hm he
    have hre : (mainTerm D m).re - (R1 m).re ≤ ‖R1 m - mainTerm D m‖ := by
      have := Complex.abs_re_le_norm (R1 m - mainTerm D m)
      rw [Complex.sub_re] at this
      linarith [(abs_le.mp this).1]
    have hsplit : Cerr * ((Y : ℝ) * Real.exp (-(c * H)) + (Y : ℝ) / Real.sqrt T +
        (Y : ℝ) ^ (1 - ε)) = (Cerr * (Real.exp (-(c * H)) + 1 / Real.sqrt T)) * Y +
        Cerr * (Y : ℝ) ^ (1 - ε) := by ring
    have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
    have h1 : (Cerr * (Real.exp (-(c * H)) + 1 / Real.sqrt T)) * Y ≤ δ / 2 * Y :=
      mul_le_mul_of_nonneg_right hHT hY0
    have hδY : 0 ≤ δ * Y := by
      have := rpow_nonneg hY0 (1 - ε)
      nlinarith [mul_nonneg hCerr this]
    nlinarith
  · push Not at hq
    refine ⟨qOf D C m, ?_, qOf_dvd D C m⟩
    unfold bigClasses qOf
    exact mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hq⟩, rfl⟩

/-- HELPER: the size condition of `classClause_of_theoremA` holds for all large `Y`. -/
theorem eventually_hY {ε δ Cerr : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hCerr : 0 ≤ Cerr) :
    ∃ Y1 : ℕ, ∀ Y : ℕ, Y1 < Y → Cerr * (Y : ℝ) ^ (1 - ε) + (Y : ℝ) ^ (1 - ε) < δ * Y := by
  have ht : Tendsto (fun Y : ℕ => ((Y : ℝ)) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨Y1, hY1⟩ := eventually_atTop.mp (ht.eventually_gt_atTop ((Cerr + 1) / δ))
  refine ⟨Y1 + 1, fun Y hY => ?_⟩
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hbig := hY1 Y (by omega)
  have hp : 0 < (Y : ℝ) ^ (1 - ε) := rpow_pos_of_pos hYpos _
  have : Cerr + 1 < δ * (Y : ℝ) ^ ε := by
    rw [div_lt_iff₀ hδ] at hbig; linarith
  calc Cerr * (Y : ℝ) ^ (1 - ε) + (Y : ℝ) ^ (1 - ε) = (Cerr + 1) * (Y : ℝ) ^ (1 - ε) := by ring
    _ < (δ * (Y : ℝ) ^ ε) * (Y : ℝ) ^ (1 - ε) := mul_lt_mul_of_pos_right this hp
    _ = δ * Y := by
        rw [mul_assoc, ← rpow_add hYpos, add_sub_cancel, rpow_one]

/-- The Pin2 inputs on every large block, Siegel zero free: Lemma 1 at `P = Y^ϑ`, Theorem A
(2.10) with (2.11) and (2.14) `K ≤ Kmax`, the choice of `H`, `T` making `Cerr(e^{-cH} + T^{-1/2})`
at most `δ/2`, and `RemainingMain`. -/
def Pin2Inputs (ϑ ε : ℝ) : Prop :=
  ∃ (A δ c H T Cerr : ℝ) (C Kmax Y0 : ℕ), 0 ≤ A ∧ 0 < δ ∧ 0 ≤ Cerr ∧ 0 < C ∧
    Cerr * (Real.exp (-(c * H)) + 1 / Real.sqrt T) ≤ δ / 2 ∧
    ∀ Y : ℕ, Y0 < Y → ∃ (X1 : ℝ) (mi : Set ℝ) (K : ℕ) (D : ZeroData K) (P : ℝ),
      K ≤ Kmax ∧ MeasurableSet mi ∧ Lemma1On A X1 Y ((Y : ℝ) ^ ϑ) mi ∧
      (Y : ℝ) ^ (ϑ - ε) < P ∧ P < (Y : ℝ) ^ ϑ ∧ ZeroShape D P ∧
      TheoremA_210 (R1 (S X1 Y) mi) Y ε c H T Cerr D ∧ Hyp_211 D ∧ RemainingMain D Y C ϑ δ

/-- CONDITIONAL ON `Pin2Inputs ϑ ε`: the lab's `Section3MajorInputLevels ϑ κ ε` at `κ = ϑ`.
The κ obtained is exactly ϑ, the level `X^ϑ` above which Pin2 discards the classes. -/
theorem majorLevels_of_pin2 {ϑ ε : ℝ} (hε : 0 < ε) (h : Pin2Inputs ϑ ε) :
    Section3MajorInputLevels ϑ ϑ ε := by
  obtain ⟨A, δ, c, H, T, Cerr, C, Kmax, Y0, hA, hδ, hCerr, hC, hHT, hin⟩ := h
  obtain ⟨Y1, hY1⟩ := eventually_hY hε hδ hCerr
  refine ⟨A, C, 2 ^ Kmax, max Y0 Y1, hA, hC, fun Y hY => ?_⟩
  obtain ⟨X1, mi, K, D, P, hK, hmi, hL1, _, _, _, hTA, _, hRM⟩ :=
    hin Y (lt_of_le_of_lt (le_max_left _ _) hY)
  obtain ⟨hcl, hge, hcard⟩ := classClause_of_theoremA D (R1 (S X1 Y) mi) hCerr hHT
    (hY1 Y (lt_of_le_of_lt (le_max_right _ _) hY)) hTA hRM
  exact ⟨X1, mi, bigClasses D Y ϑ, hmi, hL1, hcl, hge,
    hcard.trans (Nat.pow_le_pow_right (by norm_num) hK)⟩

/-- CONDITIONAL ON `Pin2Inputs ϑ ε`, `ϑ ≤ 2/5`: `E(X) < X^α` for large `X` when
`1 - ϑ + 3ε < α`. With κ = ϑ the exponent is `1 - ϑ + 3ε`, never below `3/5`. -/
theorem exponent_of_pin2 {ϑ ε α : ℝ} (hε : 0 < ε) (hϑ : ϑ ≤ 2 / 5)
    (hα : 1 - ϑ + 3 * ε < α) (h : Pin2Inputs ϑ ε) : EventuallyBelow α :=
  exponent_of_majorLevels hε hϑ (by linarith) hα hα (majorLevels_of_pin2 hε h)

/-- CONDITIONAL ON `Pin2Inputs ϑ ε` with `0.28 + 3ε < ϑ ≤ 2/5`: Theorem 1 of Pin2 (1.9),
`E(X) < X^{0.72}`. -/
theorem theorem1_of_pin2 {ϑ ε : ℝ} (hε : 0 < ε) (hϑ : 0.28 + 3 * ε < ϑ) (hϑ2 : ϑ ≤ 2 / 5)
    (h : Pin2Inputs ϑ ε) : EventuallyBelow 0.72 :=
  exponent_of_pin2 hε hϑ2 (by linarith) h

/-- CONDITIONAL ON Theorem B: at the `X` with a Siegel zero, `E(X) < X^α` for every
`α ≥ 3/5 + ε'`, in particular at `α = 0.72` when `ε' ≤ 0.12`. -/
theorem siegel_case {siegel : ℕ → Prop} {ε' α : ℝ} (hα : 3 / 5 + ε' ≤ α)
    (hB : TheoremB_217 siegel ε') :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → siegel X → (E X : ℝ) < (X : ℝ) ^ α := by
  obtain ⟨X0, h⟩ := hB
  refine ⟨max X0 1, fun X hX hs => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (le_of_max_le_right hX)
  exact (h X (le_of_max_le_left hX) hs).trans_le (rpow_le_rpow_of_exponent_le hX1 hα)

/-! ### Vacuity tests -/

/-- The toy data: one zero `ϱ = 1`, `A = 1`, modulus `1`, `𝔖 = 2 C₀`. -/
noncomputable def toyData : ZeroData 1 where
  A := fun _ => 1
  ρ := fun _ => 1
  r := fun _ => 1
  Sg := fun _ _ _ => ((2 * C0 : ℝ) : ℂ)

/-- HELPER: the toy main term is `2 C₀ m`. -/
theorem mainTerm_toy (m : ℕ) : mainTerm toyData m = ((2 * C0 : ℝ) : ℂ) * m := by
  have h2 : Complex.Gamma (1 + 1) = 1 := by
    rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]
  have h2' : Complex.Gamma 2 = 1 := by rw [← one_add_one_eq_two, h2]
  simp [mainTerm, toyData, Complex.Gamma_one, h2, h2']

/-- Vacuity test: the hypotheses (2.8), (2.10), (2.11) and `RemainingMain` hold together for
`R₁ = 2 C₀ m` with the toy data, every `Y` and `ϑ`; so they are not contradictory on their
own. This says nothing about the `R₁` of the circle method. -/
theorem pin2Hyps_satisfiable (Y : ℕ) {ϑ ε c H T : ℝ} :
    ZeroShape toyData 1 ∧
    TheoremA_210 (fun m => ((2 * C0 : ℝ) : ℂ) * m) Y ε c H T 0 toyData ∧ Hyp_211 toyData ∧
    RemainingMain toyData Y 1 ϑ (C0 / 2) := by
  refine ⟨⟨fun _ => Or.inl rfl, fun _ => ⟨le_rfl, by simp [toyData]⟩⟩, ?_, ?_, ?_⟩
  · intro m _ _; simp [mainTerm_toy]
  · intro i j m _
    simp only [toyData, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [C0_pos])]
    exact two_C0_le_Sing' m
  · intro m hm _ _
    rw [mainTerm_toy]
    have hm2 : (Y : ℝ) ≤ 2 * m := by
      have := (mem_Ioc.mp hm).1
      have : Y ≤ 2 * m := by omega
      exact_mod_cast this
    have hre : (((2 * C0 : ℝ) : ℂ) * (m : ℂ)).re = 2 * C0 * m := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    nlinarith [C0_pos]

/-- Vacuity test for Theorem B: with no Siegel zero the hypothesis holds trivially. -/
theorem theoremB_satisfiable (ε' : ℝ) : TheoremB_217 (fun _ => False) ε' :=
  ⟨0, fun _ _ h => h.elim⟩

/-- Vacuity test for `Pin2Inputs` through its conclusion: binary Goldbach, which is OPEN,
implies the two level input at κ = ϑ, so the target of `majorLevels_of_pin2` is consistent. -/
theorem target_consistent (hBG : BinaryGoldbach) {ϑ ε : ℝ} (hε : 0 < ε) :
    Section3InputLevels ϑ ϑ ε :=
  levels_of_binaryGoldbach hBG hε

end LeanLab.Pintz2021.TheoremAU1357

#print axioms LeanLab.Pintz2021.TheoremAU1357.qOf_dvd
#print axioms LeanLab.Pintz2021.TheoremAU1357.card_bigClasses_le
#print axioms LeanLab.Pintz2021.TheoremAU1357.bigClasses_ge
#print axioms LeanLab.Pintz2021.TheoremAU1357.classClause_of_theoremA
#print axioms LeanLab.Pintz2021.TheoremAU1357.eventually_hY
#print axioms LeanLab.Pintz2021.TheoremAU1357.majorLevels_of_pin2
#print axioms LeanLab.Pintz2021.TheoremAU1357.exponent_of_pin2
#print axioms LeanLab.Pintz2021.TheoremAU1357.theorem1_of_pin2
#print axioms LeanLab.Pintz2021.TheoremAU1357.siegel_case
#print axioms LeanLab.Pintz2021.TheoremAU1357.mainTerm_toy
#print axioms LeanLab.Pintz2021.TheoremAU1357.pin2Hyps_satisfiable
#print axioms LeanLab.Pintz2021.TheoremAU1357.theoremB_satisfiable
#print axioms LeanLab.Pintz2021.TheoremAU1357.target_consistent

import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Lemma8Const

/-!
# Heath-Brown and Puchta 2002: the `C₂ ≤ 2.2141` input discharged from (41)

Lab proof, unit U-1277, PC run 20261020T2004Z-7678. AI wrote the Lean code. P0012, arXiv
math/0201299, Section 5, (35) and (41).

`AnalyticInputs` in `Assembly.lean` carries an abstract `C₂` with the field `C₂ ≤ 2.2141`.
Here `C₂` is the paper's `Σ_d k(d)/ε(d)` from `Lemma8Const.lean`, and the bound is supplied by
`C2_le_conditional`, which runs (41) at `M = 24` and gets `2.184`. Assembly.lean is unchanged.
CONDITIONAL: `theorem1_lemma8`, `theorem2_lemma8` ON the inputs of `theorem1_conditional` and
`theorem2_conditional` minus `C₂ ≤ 2.2141`, plus the three inputs of `C2_le_conditional`.
Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta.C2Discharge

open Filter LeanLab.Linnik LeanLab.HeathBrownPuchta.Assembly LeanLab.HeathBrownPuchta.Lemma8Const

/-- The three cited or lab inputs behind `C₂ ≤ 2.2141`; see `C2_le_conditional`. -/
structure C2Inputs : Prop where
  grouping : C2 = ∑' e : ℕ, kappaTrue (e + 1) / ((e : ℝ) + 1)
  mobius : ∀ e, 1 ≤ e → e ≤ 24 → kappaTrue e = (kappa e : ℝ)
  llw : ∀ n, 24 ≤ n → ∑ e ∈ Finset.range n, kappaTrue (e + 1) ≤ 2744 / 1000 * Real.log n

/-- `AnalyticInputs` with `C₂` fixed to the paper's constant and no `C₂` bound field. -/
structure InputsC2Free (K : ℕ) (lam θ E w : ℝ) where
  R : ℕ → ℝ
  maj : ℕ → ℝ
  mout : ℕ → ℝ
  minr : ℕ → ℝ
  X : ℕ → ℝ
  C0 : ℝ
  split : ∀ N, R N = maj N + mout N + minr N
  scale : ∃ c > 0, ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ≤ X N
  bound_C0 : 66 / 100 ≤ C0
  lemma7 : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N
  lemma9_out : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    |mout N| ≤ (C9 (78342 / 10000) C2 C0 w * lam ^ (K - 2) + ε) * X N
  lemma1_in : ∀ δ > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, |minr N| ≤ C * (N : ℝ) ^ (2 * θ - E + δ)

/-- The `C₂` field supplied by (41). -/
noncomputable def InputsC2Free.toInputs {K : ℕ} {lam θ E w : ℝ} (I : InputsC2Free K lam θ E w) (h : C2Inputs) :
    AnalyticInputs K lam θ E w where
  R := I.R
  maj := I.maj
  mout := I.mout
  minr := I.minr
  X := I.X
  C2 := C2
  C0 := I.C0
  split := I.split
  scale := I.scale
  bound_C2 := C2_le_conditional h.grouping h.mobius h.llw
  bound_C0 := I.bound_C0
  lemma7 := I.lemma7
  lemma9_out := I.lemma9_out
  lemma1_in := I.lemma1_in

/-- Theorem 1, `K = 13`, with `C₂` the paper's constant. CONDITIONAL ON `C2Inputs` and the inputs
of `theorem1_conditional` other than `C₂ ≤ 2.2141`. -/
theorem theorem1_lemma8 (h : C2Inputs) (E : ℝ) (hE : 109 / 154 < E)
    (I : ∀ w : ℝ, 0 < w → InputsC2Free 13 (863665 / 1000000) (263 / 308 + 3 * w) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 13 N) :
    AllLargeEven (LinnikExact 13) :=
  theorem1_conditional E hE (fun w hw => (I w hw).toInputs h) circle

/-- Theorem 2, `K = 7` on GRH, with `C₂` the paper's constant. CONDITIONAL ON `C2Inputs` and the
inputs of `theorem2_conditional` other than `C₂ ≤ 2.2141`. -/
theorem theorem2_lemma8 (h : C2Inputs) (E : ℝ) (hE : 1 / 2 < E)
    (I : ∀ w : ℝ, 0 < w → InputsC2Free 7 (722428 / 1000000) (3 / 4) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 7 N) :
    AllLargeEven (LinnikExact 7) :=
  theorem2_conditional E hE (fun w hw => (I w hw).toInputs h) circle

theorem C2_nonneg : 0 ≤ C2 :=
  tsum_nonneg fun d => div_nonneg (by exact_mod_cast k_nonneg d) (Nat.cast_nonneg _)

/-- Vacuity test: `InputsC2Free` has a model, as `inputs_consistent` does for `AnalyticInputs`. -/
noncomputable def c2free_consistent : InputsC2Free 13 (863665 / 1000000) (263 / 308) 1 0 where
  R N := 3 * N
  maj N := 3 * N
  mout _ := 0
  minr _ := 0
  X N := N
  C0 := 1
  split N := by ring
  scale := ⟨1, one_pos, Eventually.of_forall fun N => by simp⟩
  bound_C0 := by norm_num
  lemma7 ε hε := Eventually.of_forall fun N => by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  lemma9_out ε hε := Eventually.of_forall fun N => by
    simp only [abs_zero]
    have : (0 : ℝ) ≤ C9 (78342 / 10000) C2 1 0 * (863665 / 1000000) ^ (13 - 2) := by
      unfold C9
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      have := C2_nonneg
      positivity
    positivity
  lemma1_in δ hδ := ⟨0, Eventually.of_forall fun N => by simp⟩

end LeanLab.HeathBrownPuchta.C2Discharge

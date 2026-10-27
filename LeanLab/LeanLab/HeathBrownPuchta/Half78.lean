import LeanLab.HeathBrownPuchta.Assembly
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Heath-Brown and Puchta 2002 under a zero-free half-plane `Re s > 7/8`

Unit U-1336, T2 FRONTIER, PC run 20261021T0203Z-29730. AI wrote the Lean code. P0012,
arXiv math/0201299 v2, Section 6 and Section 7 (43), (44). Script `gen/half78.py`, output
`gen/half78.out`. Binary Goldbach is OPEN; nothing here is progress on it.

Question: if no Dirichlet `L`-function vanishes in `Re s > 7/8`, the unrefereed OpenAI claim
"The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8", file dated 2026-09-30, what
`K` does the HBP method give?

Where GRH enters HBP: only Section 6, Lemma 12 of Baker and Harman, giving the minor arc sup
bound `S(α) ≪ N^{3/4} log N` unless `q ≤ N^{1/4}`, so `θ = 3/4` and the Lemma 1 target
`E(λ) > 2θ - 1 = 1/2`. The major arcs `P = N^{45/154 - 4ϖ}`, Lemma 7's `2.7895`, Lemma 10's
`13.968` and Lemma 1's `E` are the same in both theorems.

The half-plane analogue of that step, MODEL: the explicit formula error per character is
`N^Θ (1 + |β| N)^{1/2}` up to logs; combined with Vaughan's bound for large `q` it gives
`θ(Θ) = (1 + Θ)/2`, which is `3/4` at `Θ = 1/2` and `15/16` at `Θ = 7/8`. Since
`15/16 > 263/308`, Vaughan's unconditional exponent with the zero density major arcs is
better, so the half-plane changes nothing: K = 13. The half-plane route alone needs
`E(λ) > 7/8`, reached at `λ = 0.952593` by (44) with `h = 16`, `ξ = 1.50166`, and then K = 36.
The pointwise route beats Vaughan only for `Θ < 109/154 ≈ 0.7078`, and gives K = 12 only for
`Θ < 0.68738`.

PROVED unconditional, real number facts: `thetaHalf_GRH`, `thetaHalf_78`, `exponent_78`,
`uncond_lt_78`, `thetaHalf_lt_uncond_iff`, `effective_78`, `crit36`, `crit35_fails`,
`k12_lambda_bound`, `halfPlane_one`, `halfPlane_mono`.
CONDITIONAL: `half78_K13` ON `HalfPlane (7/8)` and the inputs of `theorem1_conditional`; the
half-plane hypothesis is not used, which is the point. `half78_route_K36` ON `HalfPlane (7/8)`,
the half-plane sup bridge packaged as `AnalyticInputs 36 0.952593 (15/16) E ϖ`, `E > 7/8`, and
the circle identity.
-/

namespace LeanLab.HeathBrownPuchta.Half78

open LeanLab.Linnik LeanLab.HeathBrownPuchta.Assembly

/-- The zero-free half-plane hypothesis: no Dirichlet `L`-function, of any modulus, vanishes at
`s` with `Re s > Θ`, the pole of the principal character at `s = 1` excluded. `HalfPlane (1/2)`
is GRH; `HalfPlane (7/8)` is the OpenAI 2026-09-30 claim, unrefereed. -/
def HalfPlane (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), Θ < s.re → (χ ≠ 1 ∨ s ≠ 1) →
    DirichletCharacter.LFunction χ s ≠ 0

/-- Nonvacuity of the predicate: `HalfPlane 1` holds, from Mathlib's nonvanishing on `Re s ≥ 1`. -/
theorem halfPlane_one : HalfPlane 1 := by
  intro q _ χ s hs hχs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs.le

/-- A wider zero-free half-plane implies a narrower one. -/
theorem halfPlane_mono {Θ Θ' : ℝ} (h : Θ ≤ Θ') (hΘ : HalfPlane Θ) : HalfPlane Θ' :=
  fun q _ χ s hs hχs => hΘ q χ s (lt_of_le_of_lt h hs) hχs

/-- The minor arc sup exponent from a zero-free half-plane `Re s > Θ`, MODEL `(1 + Θ)/2`. -/
noncomputable def thetaHalf (Θ : ℝ) : ℝ := (1 + Θ) / 2

/-- Sanity: at `Θ = 1/2` the model gives the paper's GRH exponent `3/4`, Section 6. -/
theorem thetaHalf_GRH : thetaHalf (1 / 2) = 3 / 4 := by unfold thetaHalf; norm_num

/-- At `Θ = 7/8`: `θ = 15/16`. -/
theorem thetaHalf_78 : thetaHalf (7 / 8) = 15 / 16 := by unfold thetaHalf; norm_num

/-- The Lemma 1 target on the half-plane route: `2θ - 1 = 7/8`. -/
theorem exponent_78 : 2 * thetaHalf (7 / 8) - 1 = 7 / 8 := by unfold thetaHalf; norm_num

/-- Vaughan's unconditional exponent `263/308` beats the half-plane one `15/16`. -/
theorem uncond_lt_78 : (263 / 308 : ℝ) < thetaHalf (7 / 8) := by unfold thetaHalf; norm_num

/-- Break-even: the half-plane route beats Vaughan exactly when `Θ < 109/154`. -/
theorem thetaHalf_lt_uncond_iff (Θ : ℝ) : thetaHalf Θ < 263 / 308 ↔ Θ < 109 / 154 := by
  unfold thetaHalf; constructor <;> intro h <;> linarith

/-- The best available exponent under `HalfPlane (7/8)` is the unconditional one. -/
theorem effective_78 : min (263 / 308 : ℝ) (thetaHalf (7 / 8)) = 263 / 308 :=
  min_eq_left uncond_lt_78.le

/-- Section 6 criterion with the `ϖ` loss at `λ = 0.952593`, `K = 36`. -/
theorem crit36 : 13968 / 1000 * (952593 / 1000000 : ℝ) ^ (36 - 2) <
    27895 / 10000 * (1 - 3 * (1 / 100000)) := by norm_num

/-- At `λ = 0.952593` the criterion fails for `K = 35`, even without the `ϖ` loss. -/
theorem crit35_fails : ¬ (13968 / 1000 * (952593 / 1000000 : ℝ) ^ (35 - 2) < 27895 / 10000) := by
  norm_num

/-- `K = 12` needs `λ < 0.85122` by Section 6's criterion, whatever the route; by (44) with
`h = 16` that caps `E` at `0.68738`, below `109/154`, see `gen/half78.out`. -/
theorem k12_lambda_bound {lam : ℝ} (hl : 85122 / 100000 ≤ lam) :
    ¬ (13968 / 1000 * lam ^ (12 - 2) < 27895 / 10000) := by
  have h0 : (0 : ℝ) ≤ 85122 / 100000 := by norm_num
  have hp : (85122 / 100000 : ℝ) ^ 10 ≤ lam ^ 10 := pow_le_pow_left₀ h0 hl 10
  have : (27895 / 10000 : ℝ) ≤ 13968 / 1000 * (85122 / 100000) ^ 10 := by norm_num
  norm_num at hp ⊢
  nlinarith

/-- K = 13 under `HalfPlane (7/8)`. CONDITIONAL ON `HalfPlane (7/8)` and the inputs of
`theorem1_conditional`: Lemma 7, Lemma 9, Lemma 1 `E(0.863665) > 109/154` with Vaughan's
`θ = 263/308 + 3ϖ`, and the circle identity. The half-plane hypothesis is unused: it adds nothing
to the unconditional route. -/
theorem half78_K13 (_hHP : HalfPlane (7 / 8)) (E : ℝ) (hE : 109 / 154 < E)
    (I : ∀ w : ℝ, 0 < w → AnalyticInputs 13 (863665 / 1000000) (263 / 308 + 3 * w) E w)
    (circle : ∀ w (hw : 0 < w) N, 0 < (I w hw).R N → LinnikExact 13 N) :
    AllLargeEven (LinnikExact 13) :=
  theorem1_conditional E hE I circle

/-- The half-plane route alone: K = 36. CONDITIONAL ON `HalfPlane (7/8)`; the bridge, Baker and
Harman's Lemma 12 rerun with zeros up to `7/8`, giving `θ = 15/16`, packaged with Lemma 7 and
Lemma 9 as `AnalyticInputs 36 0.952593 (15/16) E ϖ` at `ϖ = 10⁻⁵`; Lemma 1 `E(0.952593) > 7/8`,
which (44) gives with `h = 16`, `ξ = 1.50166`, value 0.8750019 in `gen/half78.out`; and the
circle identity. -/
theorem half78_route_K36 (_hHP : HalfPlane (7 / 8)) (E : ℝ) (hE : 7 / 8 < E)
    (I : AnalyticInputs 36 (952593 / 1000000) (15 / 16) E (1 / 100000))
    (circle : ∀ N, 0 < I.R N → LinnikExact 36 N) :
    AllLargeEven (LinnikExact 36) := by
  refine allLarge_of_inputs I circle (by norm_num) le_rfl (by norm_num) ?_ crit36
  linarith

open Filter in
/-- Vacuity test for `half78_route_K36`: its analytic inputs have a model at `E = 1 > 7/8`,
`X = N`, `maj = 3N`, the minor pieces `0`. `HalfPlane (7/8)` itself is the unproved claim; its
predicate is nonvacuous by `halfPlane_one`. -/
def route36_consistent : AnalyticInputs 36 (952593 / 1000000) (15 / 16) 1 (1 / 100000) where
  R N := 3 * N
  maj N := 3 * N
  mout _ := 0
  minr _ := 0
  X N := N
  C2 := 2
  C0 := 1
  split N := by ring
  scale := ⟨1, one_pos, Eventually.of_forall fun N => by simp⟩
  bound_C2 := by norm_num
  bound_C0 := by norm_num
  lemma7 ε hε := Eventually.of_forall fun N => by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  lemma9_out ε hε := Eventually.of_forall fun N => by
    simp only [abs_zero]
    have : (0 : ℝ) ≤ C9 (78342 / 10000) 2 1 (1 / 100000) * (952593 / 1000000) ^ (36 - 2) := by
      unfold C9; have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
    positivity
  lemma1_in δ hδ := ⟨0, Eventually.of_forall fun N => by simp⟩

open Filter in
/-- The model meets every side condition of the K = 36 route. -/
theorem route36_positive : ∀ᶠ N : ℕ in atTop, 0 < route36_consistent.R N :=
  section6_positive route36_consistent (by norm_num) le_rfl (by norm_num) (by norm_num) crit36

end LeanLab.HeathBrownPuchta.Half78

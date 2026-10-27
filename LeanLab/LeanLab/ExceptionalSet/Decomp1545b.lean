/-
P0095 W. C. Lu 2010, Exceptional set of Goldbach number, J. Number Theory 130, 2359-2392.
Unit U-1545, run 20261026T0808Z-17522, ARCHITECT DECOMPOSE, track T1.

File b of three: Lemma 5 on p. 2367, the bound for the zero integral
  `|∫_a^b (td + v₁ + u₁)^{ρ₁-1} (N - td - d + v₂ + u₂)^{ρ₂-1} dt|
     ≤ 24 N d⁻¹ (ad - d - 1)^{β₁+β₂-2} (|γ₁| + |γ₂|)^{-1/2}`
for `0 ≤ v_j ≤ d`, `-1 ≤ u_j ≤ 0`, `ρ_j = β_j + iγ_j`, with `b = N/d - a` of p. 2360.
Lu's proof: the phase `f(x) = γ₁ log(xd + v₁ + u₁) + γ₂ log(N - xd - d + v₂ + u₂)` has
`|f'| ≥ (|γ₁| + |γ₂|) d / N` when `γ₁γ₂ ≤ 0`, giving (33) by Lemma 2, and
`|f''| ≥ N⁻² (|γ₁| + |γ₂|) d²` when `γ₁γ₂ ≥ 0`, giving (34) by Lemma 4; then "combining (33)
with (34) via integration by parts we get the lemma at once". This file writes that step out.

Two points the printed proof leaves implicit are made explicit here:
* when `γ₁γ₂ < 0`, `f'` is not monotone on `[a, b]` but changes monotonicity at most once,
  `phase2_two_signs`, so Lemma 2 is applied on two pieces and gives `4N/((|γ₁|+|γ₂|)d)`;
  this is at most `8N/((|γ₁|+|γ₂|)^{1/2} d)` once `|γ₁|+|γ₂| ≥ 1/4`, and below that the trivial
  bound `b - a ≤ N/d` suffices;
* the amplitude `(td+v₁+u₁)^{β₁-1} (N-td-d+v₂+u₂)^{β₂-1}` is not monotone either but changes
  monotonicity at most once, `amp1_two_signs`, so its total variation is at most twice its maximum,
  and integration by parts gives the factor `3 · 8 = 24` exactly as printed.

Lemma 2 and Lemma 4 themselves are PROVED in the lab, Lu2010FirstDerivative; the leaves
`osc_first_fixed` and `osc_second_any` restate them in the sign-free form used here.

All eighteen original leaves are proved. AB_bounds was already proved on main.
CODEX task143 proves the remaining seventeen leaves. The assemblies `phi_bound` and `lemma5`
are now unconditional. The original two-piece repairs above are preserved.
The helper `signOn_split_of_monotone` and the consequences `phi_first_two_piece`,
`lemma5_of_cutoff` and `integral_trivial_bound` are also proved.
Build and axiom evidence is in `build/codex-task143.log`.
AI wrote the Lean proof code for CODEX task143. Binary Goldbach is open.

AI wrote this Lean code, Claude, unit U-1545. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Lemma4
import LeanLab.ExceptionalSet.Lu2010FirstDerivative

namespace LeanLab.ExceptionalSet.Decomp1545b

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.Lu2010Lemma4 (osc norm_osc_le)

/-! ### The data of Lemma 5 -/

/-- The parameters `N, d, a, b, v₁, u₁, v₂, u₂` of Lemma 5. -/
structure Prm where
  N : ℝ
  d : ℝ
  a : ℝ
  b : ℝ
  v1 : ℝ
  u1 : ℝ
  v2 : ℝ
  u2 : ℝ

namespace Prm

/-- The hypotheses of Lemma 5: `d > 0`, `a ≤ b`, `bd + ad = N`, that is `b = N/d - a` of
p. 2360, `ad - d - 1 > 0`, `0 ≤ v_j ≤ d`, `-1 ≤ u_j ≤ 0`. -/
def Valid (p : Prm) : Prop :=
  0 < p.d ∧ p.a ≤ p.b ∧ p.b * p.d + p.a * p.d = p.N ∧ 0 < p.a * p.d - p.d - 1 ∧
    0 ≤ p.v1 ∧ p.v1 ≤ p.d ∧ -1 ≤ p.u1 ∧ p.u1 ≤ 0 ∧
    0 ≤ p.v2 ∧ p.v2 ≤ p.d ∧ -1 ≤ p.u2 ∧ p.u2 ≤ 0

/-- `td + v₁ + u₁`. -/
def A (p : Prm) (t : ℝ) : ℝ := t * p.d + p.v1 + p.u1

/-- `N - td - d + v₂ + u₂`. -/
def B (p : Prm) (t : ℝ) : ℝ := p.N - t * p.d - p.d + p.v2 + p.u2

/-- `ad - d - 1`, the lower bound of both bases. -/
def m (p : Prm) : ℝ := p.a * p.d - p.d - 1

/-- The phase `f(t) = γ₁ log A(t) + γ₂ log B(t)` of p. 2367. -/
noncomputable def phase (p : Prm) (γ1 γ2 t : ℝ) : ℝ :=
  γ1 * Real.log (p.A t) + γ2 * Real.log (p.B t)

/-- `f'(t) = γ₁ d / A(t) - γ₂ d / B(t)`, p. 2367. -/
noncomputable def phase1 (p : Prm) (γ1 γ2 t : ℝ) : ℝ :=
  γ1 * p.d / p.A t - γ2 * p.d / p.B t

/-- `f''(t) = -γ₁ d² / A(t)² - γ₂ d² / B(t)²`, p. 2367. -/
noncomputable def phase2 (p : Prm) (γ1 γ2 t : ℝ) : ℝ :=
  -(γ1 * p.d ^ 2 / p.A t ^ 2) - γ2 * p.d ^ 2 / p.B t ^ 2

/-- The amplitude `g(t) = A(t)^{β₁-1} B(t)^{β₂-1}`. -/
noncomputable def amp (p : Prm) (β1 β2 t : ℝ) : ℝ :=
  p.A t ^ (β1 - 1) * p.B t ^ (β2 - 1)

/-- `g'(t) = g(t) ((β₁-1) d / A(t) - (β₂-1) d / B(t))`. -/
noncomputable def amp1 (p : Prm) (β1 β2 t : ℝ) : ℝ :=
  p.amp β1 β2 t * ((β1 - 1) * p.d / p.A t - (β2 - 1) * p.d / p.B t)

end Prm

/-- Sign of `h` constant on a closed interval: `h ≥ 0` throughout or `h ≤ 0` throughout. -/
def SignOn (h : ℝ → ℝ) (s e : ℝ) : Prop :=
  (∀ x ∈ Icc s e, 0 ≤ h x) ∨ (∀ x ∈ Icc s e, h x ≤ 0)

theorem signOn_split_of_monotone {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : MonotoneOn f (Icc a b)) :
    ∃ c ∈ Icc a b, SignOn f a c ∧ SignOn f c b := by
  by_cases ha : 0 ≤ f a
  · have hpos : ∀ x ∈ Icc a b, 0 ≤ f x := fun x hx => ha.trans (hm ⟨le_rfl, hab⟩ hx hx.1)
    refine ⟨a, ⟨le_rfl, hab⟩, Or.inl ?_, Or.inl hpos⟩
    intro x hx
    exact hpos x ⟨hx.1, hx.2.trans hab⟩
  · by_cases hb : f b ≤ 0
    · have hneg : ∀ x ∈ Icc a b, f x ≤ 0 := fun x hx => (hm hx ⟨hab, le_rfl⟩ hx.2).trans hb
      refine ⟨a, ⟨le_rfl, hab⟩, Or.inr ?_, Or.inr hneg⟩
      intro x hx
      exact hneg x ⟨hx.1, hx.2.trans hab⟩
    · obtain ⟨c, hci, hfc⟩ := intermediate_value_Icc hab hc
        (show 0 ∈ Icc (f a) (f b) from ⟨(lt_of_not_ge ha).le, (lt_of_not_ge hb).le⟩)
      refine ⟨c, hci, Or.inr ?_, Or.inl ?_⟩
      · intro x hx
        calc f x ≤ f c := hm ⟨hx.1, hx.2.trans hci.2⟩ hci hx.2
          _ = 0 := hfc
      · intro x hx
        calc 0 = f c := hfc.symm
          _ ≤ f x := hm hci ⟨hci.1.trans hx.1, hx.2⟩ hx.1

/-! ### Leaves on the bases, the phase and the amplitude -/

/-- LEAF. Unit U-1545. P. 2367: for `a ≤ t ≤ b` both bases lie in `[ad - d - 1, N]`; the lower
bound uses `bd = N - ad`, `v_j ≥ 0`, `u_j ≥ -1`, the upper `ad ≥ d + 1`, `v_j ≤ d`, `u_j ≤ 0`. -/
theorem AB_bounds {p : Prm} (hp : p.Valid) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    p.m ≤ p.A t ∧ p.A t ≤ p.N ∧ p.m ≤ p.B t ∧ p.B t ≤ p.N := by
  obtain ⟨hd, hab, hN, hm, hv10, hv1d, hu10, hu11, hv20, hv2d, hu20, hu21⟩ := hp
  unfold Prm.A Prm.B Prm.m
  have h1 : p.a * p.d ≤ t * p.d := mul_le_mul_of_nonneg_right ht.1 hd.le
  have h2 : t * p.d ≤ p.b * p.d := mul_le_mul_of_nonneg_right ht.2 hd.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- LEAF. Unit U-1545. The integrand of Lemma 5 in amplitude and phase form: for `a ≤ t ≤ b`,
`A^{ρ₁-1} B^{ρ₂-1} = g(t) e^{i f(t)}` with `g = A^{β₁-1} B^{β₂-1}` and
`f = γ₁ log A + γ₂ log B`, since `A, B > 0`. -/
theorem integrand_eq {p : Prm} (hp : p.Valid) {t : ℝ} (ht : t ∈ Icc p.a p.b) (ρ1 ρ2 : ℂ) :
    ((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1) =
      (p.amp ρ1.re ρ2.re t : ℂ) * Complex.exp ((p.phase ρ1.im ρ2.im t : ℂ) * Complex.I) := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : 0 < p.A t := hm.trans_le hA
  have hB0 : 0 < p.B t := hm.trans_le hB
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA0.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hB0.ne')]
  simp only [Prm.amp, Prm.phase]
  rw [Real.rpow_def_of_pos hA0, Real.rpow_def_of_pos hB0,
    ← Complex.ofReal_log hA0.le, ← Complex.ofReal_log hB0.le]
  push_cast
  repeat rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- LEAF. Unit U-1545. `f' ` as printed on p. 2367 is the derivative of the phase on `[a, b]`. -/
theorem phase_hasDerivAt {p : Prm} (hp : p.Valid) (γ1 γ2 : ℝ) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    HasDerivAt (p.phase γ1 γ2) (p.phase1 γ1 γ2 t) t := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : p.A t ≠ 0 := (hm.trans_le hA).ne'
  have hB0 : p.B t ≠ 0 := (hm.trans_le hB).ne'
  have dA : HasDerivAt p.A p.d t := by
    convert (((hasDerivAt_id t).mul_const p.d).add_const p.v1).add_const p.u1 using 1 <;> first | rfl | simp
  have dB : HasDerivAt p.B (-p.d) t := by
    convert (((((hasDerivAt_id t).mul_const p.d).const_sub p.N).sub_const p.d).add_const p.v2).add_const p.u2 using 1 <;> first | rfl | simp
  convert ((dA.log hA0).const_mul γ1).add ((dB.log hB0).const_mul γ2) using 1
  · rfl
  · dsimp [Prm.phase1]
    ring

/-- LEAF. Unit U-1545. `f''` as printed on p. 2367 is the derivative of `f'` on `[a, b]`. -/
theorem phase1_hasDerivAt {p : Prm} (hp : p.Valid) (γ1 γ2 : ℝ) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    HasDerivAt (p.phase1 γ1 γ2) (p.phase2 γ1 γ2 t) t := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : p.A t ≠ 0 := (hm.trans_le hA).ne'
  have hB0 : p.B t ≠ 0 := (hm.trans_le hB).ne'
  have dA : HasDerivAt p.A p.d t := by
    convert (((hasDerivAt_id t).mul_const p.d).add_const p.v1).add_const p.u1 using 1 <;> first | rfl | simp
  have dB : HasDerivAt p.B (-p.d) t := by
    convert (((((hasDerivAt_id t).mul_const p.d).const_sub p.N).sub_const p.d).add_const p.v2).add_const p.u2 using 1 <;> first | rfl | simp
  convert ((hasDerivAt_const t (γ1 * p.d)).div dA hA0).sub
    ((hasDerivAt_const t (γ2 * p.d)).div dB hB0) using 1
  · rfl
  · dsimp [Prm.phase2]
    field_simp
    ring

/-- LEAF. Unit U-1545. `f''` is continuous on `[a, b]`. -/
theorem phase2_continuousOn {p : Prm} (hp : p.Valid) (γ1 γ2 : ℝ) :
    ContinuousOn (p.phase2 γ1 γ2) (Icc p.a p.b) := by
  intro t ht
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : p.A t ≠ 0 := (hm.trans_le hA).ne'
  have hB0 : p.B t ≠ 0 := (hm.trans_le hB).ne'
  have cA : ContinuousAt p.A t := by unfold Prm.A; fun_prop
  have cB : ContinuousAt p.B t := by unfold Prm.B; fun_prop
  exact (((continuousAt_const.div (cA.pow 2) (pow_ne_zero 2 hA0)).neg).sub
    (continuousAt_const.div (cB.pow 2) (pow_ne_zero 2 hB0))).continuousWithinAt

/-- LEAF. Unit U-1545. P. 2367: if `γ₁γ₂ ≤ 0` then `|f'(t)| ≥ (|γ₁| + |γ₂|) d / N` on `[a, b]`,
as both terms of `f'` have the same sign and `A, B ≤ N`. -/
theorem first_lower {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ} (hγ : γ1 * γ2 ≤ 0) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    (|γ1| + |γ2|) * p.d / p.N ≤ |p.phase1 γ1 γ2 t| := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, hAN, hB, hBN⟩ := AB_bounds hp ht
  have hA0 : 0 < p.A t := hm.trans_le hA
  have hB0 : 0 < p.B t := hm.trans_le hB
  have hd : 0 < p.d := hp.1
  have heq : |p.phase1 γ1 γ2 t| = |γ1| * p.d / p.A t + |γ2| * p.d / p.B t := by
    unfold Prm.phase1
    rcases mul_nonpos_iff.mp hγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonpos h2,
        abs_of_nonneg (sub_nonneg.mpr (le_trans
          (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h2 hd.le) hB0.le)
          (div_nonneg (mul_nonneg h1 hd.le) hA0.le)))]
      ring
    · rw [abs_of_nonpos h1, abs_of_nonneg h2,
        abs_of_nonpos (sub_nonpos.mpr (le_trans
          (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h1 hd.le) hA0.le)
          (div_nonneg (mul_nonneg h2 hd.le) hB0.le)))]
      ring
  rw [heq]
  calc (|γ1| + |γ2|) * p.d / p.N = |γ1| * p.d / p.N + |γ2| * p.d / p.N := by ring
    _ ≤ |γ1| * p.d / p.A t + |γ2| * p.d / p.B t :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hA0 hAN)
        (div_le_div_of_nonneg_left (by positivity) hB0 hBN)

/-- LEAF. Unit U-1545. P. 2367: if `γ₁, γ₂ ≥ 0` then `f''(t) ≤ -(|γ₁| + |γ₂|) d² / N²`. -/
theorem second_upper {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ} (h1 : 0 ≤ γ1) (h2 : 0 ≤ γ2) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    p.phase2 γ1 γ2 t ≤ -((|γ1| + |γ2|) * p.d ^ 2 / p.N ^ 2) := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, hAN, hB, hBN⟩ := AB_bounds hp ht
  have hA0 : 0 < p.A t := hm.trans_le hA
  have hB0 : 0 < p.B t := hm.trans_le hB
  have hN0 : 0 < p.N := hA0.trans_le hAN
  have hA2 : p.A t ^ 2 ≤ p.N ^ 2 := (sq_le_sq₀ hA0.le hN0.le).mpr hAN
  have hB2 : p.B t ^ 2 ≤ p.N ^ 2 := (sq_le_sq₀ hB0.le hN0.le).mpr hBN
  have ha := div_le_div_of_nonneg_left (mul_nonneg h1 (sq_nonneg p.d))
    (sq_pos_of_pos hA0) hA2
  have hb := div_le_div_of_nonneg_left (mul_nonneg h2 (sq_nonneg p.d))
    (sq_pos_of_pos hB0) hB2
  rw [abs_of_nonneg h1, abs_of_nonneg h2]
  unfold Prm.phase2
  calc -(γ1 * p.d ^ 2 / p.A t ^ 2) - γ2 * p.d ^ 2 / p.B t ^ 2
      ≤ -(γ1 * p.d ^ 2 / p.N ^ 2) - γ2 * p.d ^ 2 / p.N ^ 2 := by linarith
    _ = -((γ1 + γ2) * p.d ^ 2 / p.N ^ 2) := by ring

/-- LEAF. Unit U-1545. P. 2367: if `γ₁, γ₂ ≤ 0` then `f''(t) ≥ (|γ₁| + |γ₂|) d² / N²`. -/
theorem second_lower {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ} (h1 : γ1 ≤ 0) (h2 : γ2 ≤ 0) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    (|γ1| + |γ2|) * p.d ^ 2 / p.N ^ 2 ≤ p.phase2 γ1 γ2 t := by
  have H := second_upper hp (neg_nonneg.mpr h1) (neg_nonneg.mpr h2) ht
  simp only [abs_neg, Prm.phase2, neg_mul, neg_div, neg_neg] at H ⊢
  linarith

/-- LEAF. Unit U-1545. When `γ₁γ₂ ≤ 0`, `f'` changes monotonicity at most once on any
`[s, e] ⊆ [a, b]`: `A² B² f'' / d² = |γ₂| A² - |γ₁| B²` up to sign is monotone, as `A` increases
and `B` decreases, so some `x₀ ∈ [s, e]` splits `[s, e]` into two pieces on which `f''` has one
sign. This is the hypothesis "f' monotonic" of Lemma 2 used for (33). -/
theorem phase2_two_signs {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ} (hγ : γ1 * γ2 ≤ 0) {s e : ℝ}
    (hs : p.a ≤ s) (hse : s ≤ e) (he : e ≤ p.b) :
    ∃ x0 ∈ Icc s e, SignOn (p.phase2 γ1 γ2) s x0 ∧ SignOn (p.phase2 γ1 γ2) x0 e := by
  have hsub : Icc s e ⊆ Icc p.a p.b := Icc_subset_Icc hs he
  have hmono : ∀ c1 c2 : ℝ, 0 ≤ c1 → c2 ≤ 0 →
      MonotoneOn (p.phase2 c1 c2) (Icc p.a p.b) := by
    intro c1 c2 h1 h2 x hx y hy hxy
    have hm : 0 < p.m := hp.2.2.2.1
    have hd : 0 < p.d := hp.1
    obtain ⟨hAx, _, hBx, _⟩ := AB_bounds hp hx
    obtain ⟨hAy, _, hBy, _⟩ := AB_bounds hp hy
    have hAx0 : 0 < p.A x := hm.trans_le hAx
    have hAy0 : 0 < p.A y := hm.trans_le hAy
    have hBx0 : 0 < p.B x := hm.trans_le hBx
    have hBy0 : 0 < p.B y := hm.trans_le hBy
    have hAxy : p.A x ≤ p.A y := by
      unfold Prm.A
      linarith [mul_le_mul_of_nonneg_right hxy hd.le]
    have hByx : p.B y ≤ p.B x := by
      unfold Prm.B
      linarith [mul_le_mul_of_nonneg_right hxy hd.le]
    have hA2 := (sq_le_sq₀ hAx0.le hAy0.le).mpr hAxy
    have hB2 := (sq_le_sq₀ hBy0.le hBx0.le).mpr hByx
    have ha := div_le_div_of_nonneg_left (mul_nonneg h1 (sq_nonneg p.d))
      (sq_pos_of_pos hAx0) hA2
    have hb := div_le_div_of_nonneg_left (mul_nonneg (neg_nonneg.mpr h2) (sq_nonneg p.d))
      (sq_pos_of_pos hBy0) hB2
    simp only [neg_mul, neg_div] at hb
    unfold Prm.phase2
    linarith
  rcases mul_nonpos_iff.mp hγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact signOn_split_of_monotone hse ((phase2_continuousOn hp γ1 γ2).mono hsub)
      ((hmono γ1 γ2 h1 h2).mono hsub)
  · obtain ⟨x0, hx0, hl, hr⟩ := signOn_split_of_monotone hse
      ((phase2_continuousOn hp (-γ1) (-γ2)).mono hsub)
      ((hmono (-γ1) (-γ2) (neg_nonneg.mpr h1) (neg_nonpos.mpr h2)).mono hsub)
    have hneg {l r : ℝ} (h : SignOn (p.phase2 (-γ1) (-γ2)) l r) :
        SignOn (p.phase2 γ1 γ2) l r := by
      rcases h with h | h
      · right
        intro x hx
        have H := h x hx
        simp only [Prm.phase2, neg_mul, neg_div, neg_neg] at H ⊢
        linarith
      · left
        intro x hx
        have H := h x hx
        simp only [Prm.phase2, neg_mul, neg_div, neg_neg] at H ⊢
        linarith
    exact ⟨x0, hx0, hneg hl, hneg hr⟩

/-- LEAF. Unit U-1545. The amplitude is differentiable on `[a, b]` with derivative `g'`. -/
theorem amp_hasDerivAt {p : Prm} (hp : p.Valid) (β1 β2 : ℝ) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    HasDerivAt (p.amp β1 β2) (p.amp1 β1 β2 t) t := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : p.A t ≠ 0 := (hm.trans_le hA).ne'
  have hB0 : p.B t ≠ 0 := (hm.trans_le hB).ne'
  have dA : HasDerivAt p.A p.d t := by
    convert (((hasDerivAt_id t).mul_const p.d).add_const p.v1).add_const p.u1 using 1 <;> first | rfl | simp
  have dB : HasDerivAt p.B (-p.d) t := by
    convert (((((hasDerivAt_id t).mul_const p.d).const_sub p.N).sub_const p.d).add_const p.v2).add_const p.u2 using 1 <;> first | rfl | simp
  convert (dA.rpow_const (p := β1 - 1) (Or.inl hA0)).mul
    (dB.rpow_const (p := β2 - 1) (Or.inl hB0)) using 1
  · rfl
  · unfold Prm.amp1 Prm.amp
    rw [Real.rpow_sub_one hA0 (β1 - 1), Real.rpow_sub_one hB0 (β2 - 1)]
    ring

/-- LEAF. Unit U-1545. `g'` is continuous on `[a, b]`. -/
theorem amp1_continuousOn {p : Prm} (hp : p.Valid) (β1 β2 : ℝ) :
    ContinuousOn (p.amp1 β1 β2) (Icc p.a p.b) := by
  intro t ht
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : p.A t ≠ 0 := (hm.trans_le hA).ne'
  have hB0 : p.B t ≠ 0 := (hm.trans_le hB).ne'
  have cA : ContinuousAt p.A t := by unfold Prm.A; fun_prop
  have cB : ContinuousAt p.B t := by unfold Prm.B; fun_prop
  have cg : ContinuousAt (p.amp β1 β2) t :=
    (cA.rpow_const (Or.inl hA0)).mul (cB.rpow_const (Or.inl hB0))
  exact (cg.mul ((continuousAt_const.div cA hA0).sub
    (continuousAt_const.div cB hB0))).continuousWithinAt

/-- LEAF. Unit U-1545. For `β₁, β₂ ≤ 1` the amplitude changes monotonicity at most once on
`[a, b]`: `g'/g = d ((1-β₂) A - (1-β₁) B)/(AB)` and the numerator is increasing. -/
theorem amp1_two_signs {p : Prm} (hp : p.Valid) {β1 β2 : ℝ} (h1 : β1 ≤ 1) (h2 : β2 ≤ 1) :
    ∃ x0 ∈ Icc p.a p.b, SignOn (p.amp1 β1 β2) p.a x0 ∧ SignOn (p.amp1 β1 β2) x0 p.b := by
  let h : ℝ → ℝ := fun t => (1 - β2) * p.A t - (1 - β1) * p.B t
  have hab : p.a ≤ p.b := hp.2.1
  have hc : ContinuousOn h (Icc p.a p.b) := by dsimp [h, Prm.A, Prm.B]; fun_prop
  have hmono : MonotoneOn h (Icc p.a p.b) := by
    intro x hx y hy hxy
    have hd : 0 < p.d := hp.1
    have hA : p.A x ≤ p.A y := by unfold Prm.A; linarith [mul_le_mul_of_nonneg_right hxy hd.le]
    have hB : p.B y ≤ p.B x := by unfold Prm.B; linarith [mul_le_mul_of_nonneg_right hxy hd.le]
    dsimp [h]
    exact sub_le_sub (mul_le_mul_of_nonneg_left hA (by linarith))
      (mul_le_mul_of_nonneg_left hB (by linarith))
  obtain ⟨x0, hx0, hl, hr⟩ := signOn_split_of_monotone hab hc hmono
  have hmul {l r : ℝ} (hsub : Icc l r ⊆ Icc p.a p.b) (hsign : SignOn h l r) :
      SignOn (p.amp1 β1 β2) l r := by
    have heq (x : ℝ) (hx : x ∈ Icc l r) : p.amp1 β1 β2 x =
        (p.amp β1 β2 x * p.d / (p.A x * p.B x)) * h x := by
      have hm : 0 < p.m := hp.2.2.2.1
      obtain ⟨hA, _, hB, _⟩ := AB_bounds hp (hsub hx)
      have hA0 : p.A x ≠ 0 := (hm.trans_le hA).ne'
      have hB0 : p.B x ≠ 0 := (hm.trans_le hB).ne'
      dsimp [Prm.amp1, h]
      field_simp
      ring
    have hfac (x : ℝ) (hx : x ∈ Icc l r) :
        0 ≤ p.amp β1 β2 x * p.d / (p.A x * p.B x) := by
      have hm : 0 < p.m := hp.2.2.2.1
      obtain ⟨hA, _, hB, _⟩ := AB_bounds hp (hsub hx)
      have hA0 : 0 < p.A x := hm.trans_le hA
      have hB0 : 0 < p.B x := hm.trans_le hB
      have hd : 0 < p.d := hp.1
      unfold Prm.amp
      positivity
    rcases hsign with hpos | hneg
    · left; intro x hx; rw [heq x hx]; exact mul_nonneg (hfac x hx) (hpos x hx)
    · right; intro x hx; rw [heq x hx]; exact mul_nonpos_of_nonneg_of_nonpos (hfac x hx) (hneg x hx)
  exact ⟨x0, hx0, hmul (Icc_subset_Icc_right hx0.2) hl,
    hmul (Icc_subset_Icc_left hx0.1) hr⟩

/-- LEAF. Unit U-1545. P. 2367: for `β₁, β₂ ≤ 1` and `a ≤ t ≤ b`,
`0 ≤ g(t) ≤ (ad - d - 1)^{β₁+β₂-2}`, from `AB_bounds` and nonpositive exponents. -/
theorem amp_bounds {p : Prm} (hp : p.Valid) {β1 β2 : ℝ} (h1 : β1 ≤ 1) (h2 : β2 ≤ 1) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    0 ≤ p.amp β1 β2 t ∧ p.amp β1 β2 t ≤ p.m ^ (β1 + β2 - 2) := by
  have hm : 0 < p.m := hp.2.2.2.1
  obtain ⟨hA, _, hB, _⟩ := AB_bounds hp ht
  have hA0 : 0 < p.A t := hm.trans_le hA
  have hB0 : 0 < p.B t := hm.trans_le hB
  refine ⟨mul_nonneg (Real.rpow_nonneg hA0.le _) (Real.rpow_nonneg hB0.le _), ?_⟩
  calc p.amp β1 β2 t
      ≤ p.m ^ (β1 - 1) * p.m ^ (β2 - 1) :=
        mul_le_mul (Real.rpow_le_rpow_of_nonpos hm hA (by linarith))
          (Real.rpow_le_rpow_of_nonpos hm hB (by linarith))
          (Real.rpow_nonneg hB0.le _) (Real.rpow_nonneg hm.le _)
    _ = p.m ^ (β1 + β2 - 2) := by rw [← Real.rpow_add hm]; congr 1; ring

/-! ### Generic leaves on oscillatory integrals -/

/-- LEAF. Unit U-1545. Lemma 2 of p. 2364 in sign-free form, with constant 2 per piece: if
`|f'| ≥ y > 0` on `[a, b]` and `f''` has one sign there, then `|∫_a^b e^{if}| ≤ 2/y`. Follows
from the PROVED `first_derivative_positive`, `first_derivative_negative` and `norm_osc_neg` of
Lu2010FirstDerivative, with the intermediate value theorem fixing the sign of `f'`. -/
theorem osc_first_fixed {f fp fpp : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (hy : 0 < y)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Icc a b, HasDerivAt fp (fpp x) x)
    (hc : ContinuousOn fpp (Icc a b))
    (hp : ∀ x ∈ Icc a b, y ≤ |fp x|) (hpp : SignOn fpp a b) :
    ‖osc f a b‖ ≤ 2 / y := by
  have hfpc : ContinuousOn fp (Icc a b) := fun x hx => (hfp x hx).continuousAt.continuousWithinAt
  have hnz (x : ℝ) (hx : x ∈ Icc a b) : fp x ≠ 0 := by
    intro hz
    have H := hp x hx
    rw [hz, abs_zero] at H
    linarith
  have hsign : (∀ x ∈ Icc a b, 0 ≤ fp x) ∨ (∀ x ∈ Icc a b, fp x ≤ 0) := by
    by_cases ha : 0 ≤ fp a
    · left
      intro x hx
      by_contra hn
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hx.1
        (hfpc.mono (Icc_subset_Icc_right hx.2))
        (show 0 ∈ Icc (fp x) (fp a) from ⟨(lt_of_not_ge hn).le, ha⟩)
      exact hnz z ⟨hz.1, hz.2.trans hx.2⟩ hfz
    · right
      intro x hx
      by_contra hn
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hx.1
        (hfpc.mono (Icc_subset_Icc_right hx.2))
        (show 0 ∈ Icc (fp a) (fp x) from ⟨(lt_of_not_ge ha).le, (lt_of_not_ge hn).le⟩)
      exact hnz z ⟨hz.1, hz.2.trans hx.2⟩ hfz
  have hbound : (∀ x ∈ Icc a b, y ≤ fp x) ∨ (∀ x ∈ Icc a b, fp x ≤ -y) := by
    rcases hsign with hpos | hneg
    · left; intro x hx; simpa [abs_of_nonneg (hpos x hx)] using hp x hx
    · right; intro x hx
      have H := hp x hx
      rw [abs_of_nonpos (hneg x hx)] at H
      linarith
  rcases hpp with hpp | hpp
  · rcases hbound with hpos | hneg
    · exact LeanLab.ExceptionalSet.Lu2010FirstDerivative.first_derivative_positive hab hy hf hfp hc hpos hpp
    · exact LeanLab.ExceptionalSet.Lu2010FirstDerivative.first_derivative_negative hab hy hf hfp hc hneg hpp
  · rw [← LeanLab.ExceptionalSet.Lu2010FirstDerivative.norm_osc_neg f a b]
    have hfn : ∀ x ∈ Icc a b, HasDerivAt (fun t => -f t) (-fp x) x := fun x hx => (hf x hx).neg
    have hfpn : ∀ x ∈ Icc a b, HasDerivAt (fun t => -fp t) (-fpp x) x := fun x hx => (hfp x hx).neg
    have hppn : ∀ x ∈ Icc a b, 0 ≤ -fpp x := fun x hx => neg_nonneg.mpr (hpp x hx)
    rcases hbound with hpos | hneg
    · exact LeanLab.ExceptionalSet.Lu2010FirstDerivative.first_derivative_negative hab hy hfn hfpn hc.neg
        (fun x hx => by linarith [hpos x hx]) hppn
    · exact LeanLab.ExceptionalSet.Lu2010FirstDerivative.first_derivative_positive hab hy hfn hfpn hc.neg
        (fun x hx => by linarith [hneg x hx]) hppn

/-- LEAF. Unit U-1545. Lemma 4 of p. 2366 in sign-free form: if `f'' ≥ y` or `f'' ≤ -y` on
`[a, b]`, `y > 0`, then `|∫_a^b e^{if}| ≤ 8/√y`. Follows from the PROVED
`second_derivative_positive` and `norm_osc_neg` of Lu2010FirstDerivative. -/
theorem osc_second_any {f fp fpp : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (hy : 0 < y)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Icc a b, HasDerivAt fp (fpp x) x)
    (hc : ContinuousOn fpp (Icc a b))
    (hpp : (∀ x ∈ Icc a b, y ≤ fpp x) ∨ (∀ x ∈ Icc a b, fpp x ≤ -y)) :
    ‖osc f a b‖ ≤ 8 / Real.sqrt y := by
  open LeanLab.ExceptionalSet.Lu2010FirstDerivative in
  rcases hpp with hpp | hpp
  · exact second_derivative_positive hab hy hf hfp hc hpp
  · rw [← norm_osc_neg f a b]
    exact second_derivative_positive hab hy (fun x hx => (hf x hx).neg)
      (fun x hx => (hfp x hx).neg) hc.neg (fun x hx => by linarith [hpp x hx])

/-- LEAF. Unit U-1545. Additivity: for `f` continuous on `[a, b]` and `a ≤ m ≤ b`,
`∫_a^b e^{if} = ∫_a^m e^{if} + ∫_m^b e^{if}`. -/
theorem osc_add {f : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    osc f a b = osc f a m + osc f m b := by
  have hc : ContinuousOn (fun x => Complex.exp ((f x : ℂ) * Complex.I)) (Icc a b) := by
    fun_prop
  have hi : IntervalIntegrable (fun x => Complex.exp ((f x : ℂ) * Complex.I)) volume a b := hc.intervalIntegrable_of_Icc (ham.trans hmb)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (by simp only [uIcc_of_le ham, uIcc_of_le (ham.trans hmb)]; exact Icc_subset_Icc_right hmb))
    (hi.mono_set (by simp only [uIcc_of_le hmb, uIcc_of_le (ham.trans hmb)]; exact Icc_subset_Icc_left ham))).symm

/-- LEAF. Unit U-1545. Integration by parts, "via integration by parts" on p. 2367: if `g` is
`C¹` on `[a, b]`, `f` continuous there and `|∫_a^t e^{if}| ≤ M` for all `t ∈ [a, b]`, then
`|∫_a^b g e^{if}| ≤ (|g(b)| + ∫_a^b |g'|) M`. -/
theorem ibp_bound {f g g' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hM : ∀ t ∈ Icc a b, ‖osc f a t‖ ≤ M) :
    ‖∫ t in a..b, (g t : ℂ) * Complex.exp ((f t : ℂ) * Complex.I)‖ ≤
      (|g b| + ∫ t in a..b, |g' t|) * M := by
  let U : ℝ → ℂ := fun t => Complex.exp ((f t : ℂ) * Complex.I)
  let V : ℝ → ℂ := fun t => ∫ x in a..t, U x
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc a b) := by dsimp [U]; fun_prop
  have hUi : IntervalIntegrable U volume a b := hUc.intervalIntegrable_of_Icc hab
  have hVc : ContinuousOn V (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hUi (show a ∈ uIcc a b from left_mem_uIcc))
  have hVd : ∀ t ∈ Ioo a b, HasDerivAt V (U t) t := by
    intro t ht
    have hi : IntervalIntegrable U volume a t := hUi.mono_set
      (by simp only [uIcc_of_le ht.1.le, uIcc_of_le hab]; exact Icc_subset_Icc_right ht.2.le)
    exact intervalIntegral.integral_hasDerivAt_right hi
      ((hUc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hUc.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have hGc : ContinuousOn (fun t => (g t : ℂ)) (Icc a b) := by fun_prop
  have hGpc : ContinuousOn (fun t => (g' t : ℂ)) (Icc a b) := by fun_prop
  have hIBP : (∫ t in a..b, (g t : ℂ) * U t) =
      (g b : ℂ) * V b - (g a : ℂ) * V a - ∫ t in a..b, (g' t : ℂ) * V t := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · simpa only [uIcc_of_le hab] using hGc
    · simpa only [uIcc_of_le hab] using hVc
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
      exact (hg t (Ioo_subset_Icc_self ht')).ofReal_comp
    · intro t ht
      exact hVd t (by simpa only [min_eq_left hab, max_eq_right hab] using ht)
    · exact hGpc.intervalIntegrable_of_Icc hab
    · exact hUi
  have hVa : V a = 0 := by simp [V]
  have hend : ‖(g b : ℂ) * V b‖ ≤ |g b| * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM b ⟨hab, le_rfl⟩) (abs_nonneg _)
  have htail : ‖∫ t in a..b, (g' t : ℂ) * V t‖ ≤ (∫ t in a..b, |g' t|) * M := by
    calc ‖∫ t in a..b, (g' t : ℂ) * V t‖
        ≤ ∫ t in a..b, ‖(g' t : ℂ) * V t‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, |g' t| * M := by
        apply intervalIntegral.integral_mono_on hab
          ((hGpc.mul hVc).norm.intervalIntegrable_of_Icc hab)
          ((hg'.abs.mul continuousOn_const).intervalIntegrable_of_Icc hab)
        intro t ht
        change ‖(g' t : ℂ) * V t‖ ≤ |g' t| * M
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg _)
      _ = (∫ t in a..b, |g' t|) * M := by rw [intervalIntegral.integral_mul_const]
  change ‖∫ t in a..b, (g t : ℂ) * U t‖ ≤ _
  rw [hIBP, hVa, mul_zero, sub_zero]
  calc ‖(g b : ℂ) * V b - ∫ t in a..b, (g' t : ℂ) * V t‖
      ≤ ‖(g b : ℂ) * V b‖ + ‖∫ t in a..b, (g' t : ℂ) * V t‖ := norm_sub_le _ _
    _ ≤ |g b| * M + (∫ t in a..b, |g' t|) * M := add_le_add hend htail
    _ = (|g b| + ∫ t in a..b, |g' t|) * M := by ring

/-- LEAF. Unit U-1545. Total variation of a function that changes monotonicity at most once:
if `g` is `C¹` on `[a, b]`, `a ≤ x₀ ≤ b`, `g'` has one sign on `[a, x₀]` and on `[x₀, b]`, and
`0 ≤ g ≤ G` on `[a, b]`, then `∫_a^b |g'| ≤ 2G`. -/
theorem variation_two_piece {g g' : ℝ → ℝ} {a x0 b G : ℝ} (hax : a ≤ x0) (hxb : x0 ≤ b)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc a b))
    (h1 : SignOn g' a x0) (h2 : SignOn g' x0 b)
    (hG : ∀ t ∈ Icc a b, 0 ≤ g t ∧ g t ≤ G) :
    ∫ t in a..b, |g' t| ≤ 2 * G := by
  have hpiece {s e : ℝ} (hs : a ≤ s) (hse : s ≤ e) (he : e ≤ b)
      (hsgn : SignOn g' s e) : ∫ t in s..e, |g' t| ≤ G := by
    have hsub : Icc s e ⊆ Icc a b := Icc_subset_Icc hs he
    have hc := hg'.mono hsub
    have hFTC : ∫ t in s..e, g' t = g e - g s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hg x (hsub (by simpa only [uIcc_of_le hse] using hx)))
        (hc.intervalIntegrable_of_Icc hse)
    have hGs := hG s (hsub ⟨le_rfl, hse⟩)
    have hGe := hG e (hsub ⟨hse, le_rfl⟩)
    rcases hsgn with hpos | hneg
    · have heq : ∫ t in s..e, |g' t| = ∫ t in s..e, g' t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact abs_of_nonneg (hpos t (by simpa only [uIcc_of_le hse] using ht))
      rw [heq, hFTC]
      linarith
    · have heq : ∫ t in s..e, |g' t| = -(∫ t in s..e, g' t) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        exact abs_of_nonpos (hneg t (by simpa only [uIcc_of_le hse] using ht))
      rw [heq, hFTC]
      linarith
  have hab : a ≤ b := hax.trans hxb
  have hi : IntervalIntegrable (fun t => |g' t|) volume a b := hg'.abs.intervalIntegrable_of_Icc hab
  have his : IntervalIntegrable (fun t => |g' t|) volume a x0 :=
    hi.mono_set (by simp only [uIcc_of_le hax, uIcc_of_le hab]; exact Icc_subset_Icc_right hxb)
  have hie : IntervalIntegrable (fun t => |g' t|) volume x0 b :=
    hi.mono_set (by simp only [uIcc_of_le hxb, uIcc_of_le hab]; exact Icc_subset_Icc_left hax)
  rw [← intervalIntegral.integral_add_adjacent_intervals his hie]
  linarith [hpiece le_rfl hax hxb h1, hpiece hax hxb le_rfl h2]

/-! ### Assemblies from the proved leaves above -/

theorem Prm.Valid.d_pos {p : Prm} (hp : p.Valid) : 0 < p.d := hp.1
theorem Prm.Valid.a_le_b {p : Prm} (hp : p.Valid) : p.a ≤ p.b := hp.2.1
theorem Prm.Valid.m_pos {p : Prm} (hp : p.Valid) : 0 < p.m := hp.2.2.2.1

theorem Prm.Valid.N_pos {p : Prm} (hp : p.Valid) : 0 < p.N := by
  obtain ⟨hd, hab, hbd, hm, _⟩ := hp
  nlinarith [mul_le_mul_of_nonneg_right hab hd.le]

/-- `b ≤ N/d` and `a > 0`. -/
theorem Prm.Valid.b_le {p : Prm} (hp : p.Valid) : 0 < p.a ∧ p.b ≤ p.N / p.d := by
  obtain ⟨hd, _, hbd, hm, _⟩ := hp
  have ha : 0 < p.a := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨ha, ?_⟩
  rw [le_div_iff₀ hd]
  nlinarith

/-- ASSEMBLY, (33) and (34) combined, from the proved leaves `AB_bounds`, `phase_hasDerivAt`,
`phase1_hasDerivAt`, `phase2_continuousOn`, `first_lower`, `second_upper`, `second_lower`,
`phase2_two_signs`, `osc_first_fixed`, `osc_second_any`, `osc_add`: for `|γ₁| + |γ₂| > 0` and
`a ≤ t ≤ b`, `|∫_a^t e^{if}| ≤ 8N / (d (|γ₁|+|γ₂|)^{1/2})`. -/
theorem phi_bound {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ} (hG : 0 < |γ1| + |γ2|) {t : ℝ}
    (ht : t ∈ Icc p.a p.b) :
    ‖osc (p.phase γ1 γ2) p.a t‖ ≤ 8 * p.N / (p.d * Real.sqrt (|γ1| + |γ2|)) := by
  set G := |γ1| + |γ2| with hGdef
  have hd := hp.d_pos
  have hN := hp.N_pos
  have hsG : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  have hsub : ∀ {s e : ℝ}, p.a ≤ s → e ≤ t → Icc s e ⊆ Icc p.a p.b := by
    intro s e hs he x hx
    exact ⟨le_trans hs hx.1, le_trans (le_trans hx.2 he) ht.2⟩
  have hder : ∀ {s e : ℝ}, p.a ≤ s → e ≤ t →
      (∀ x ∈ Icc s e, HasDerivAt (p.phase γ1 γ2) (p.phase1 γ1 γ2 x) x) ∧
      (∀ x ∈ Icc s e, HasDerivAt (p.phase1 γ1 γ2) (p.phase2 γ1 γ2 x) x) ∧
      ContinuousOn (p.phase2 γ1 γ2) (Icc s e) := by
    intro s e hs he
    exact ⟨fun x hx => phase_hasDerivAt hp γ1 γ2 (hsub hs he hx),
      fun x hx => phase1_hasDerivAt hp γ1 γ2 (hsub hs he hx),
      (phase2_continuousOn hp γ1 γ2).mono (hsub hs he)⟩
  -- the second derivative case
  have hsecond : (0 ≤ γ1 ∧ 0 ≤ γ2) ∨ (γ1 ≤ 0 ∧ γ2 ≤ 0) →
      ‖osc (p.phase γ1 γ2) p.a t‖ ≤ 8 * p.N / (p.d * Real.sqrt G) := by
    intro hcase
    set r := Real.sqrt G * p.d / p.N with hr
    have hr0 : 0 < r := by positivity
    have hr2 : r ^ 2 = G * p.d ^ 2 / p.N ^ 2 := by
      rw [hr, div_pow, mul_pow, Real.sq_sqrt hG.le]
    obtain ⟨h1, h2, h3⟩ := hder (s := p.a) (e := t) le_rfl le_rfl
    have hpp : (∀ x ∈ Icc p.a t, r ^ 2 ≤ p.phase2 γ1 γ2 x) ∨
        (∀ x ∈ Icc p.a t, p.phase2 γ1 γ2 x ≤ -r ^ 2) := by
      rcases hcase with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · right; intro x hx; rw [hr2]; exact second_upper hp g1 g2 (hsub le_rfl le_rfl hx)
      · left; intro x hx; rw [hr2]; exact second_lower hp g1 g2 (hsub le_rfl le_rfl hx)
    have h := osc_second_any ht.1 (by positivity) h1 h2 h3 hpp
    rw [Real.sqrt_sq hr0.le] at h
    calc ‖osc (p.phase γ1 γ2) p.a t‖ ≤ 8 / r := h
      _ = 8 * p.N / (p.d * Real.sqrt G) := by rw [hr]; field_simp
  -- the first derivative case
  have hfirst : γ1 * γ2 ≤ 0 →
      ‖osc (p.phase γ1 γ2) p.a t‖ ≤ 8 * p.N / (p.d * Real.sqrt G) := by
    intro hγ
    by_cases hG4 : 1 / 4 ≤ G
    · obtain ⟨x0, hx0, hs1, hs2⟩ := phase2_two_signs hp hγ le_rfl ht.1 ht.2
      set y := G * p.d / p.N with hy
      have hy0 : 0 < y := by positivity
      have hlow : ∀ x ∈ Icc p.a t, y ≤ |p.phase1 γ1 γ2 x| := fun x hx =>
        first_lower hp hγ (hsub le_rfl le_rfl hx)
      obtain ⟨d1, d2, d3⟩ := hder (s := p.a) (e := x0) le_rfl hx0.2
      obtain ⟨e1, e2, e3⟩ := hder (s := x0) (e := t) hx0.1 le_rfl
      have hI1 := osc_first_fixed hx0.1 hy0 d1 d2 d3
        (fun x hx => hlow x ⟨hx.1, le_trans hx.2 hx0.2⟩) hs1
      have hI2 := osc_first_fixed hx0.2 hy0 e1 e2 e3
        (fun x hx => hlow x ⟨le_trans hx0.1 hx.1, hx.2⟩) hs2
      have hcont : ContinuousOn (p.phase γ1 γ2) (Icc p.a t) := fun x hx =>
        (phase_hasDerivAt hp γ1 γ2 (hsub le_rfl le_rfl hx)).continuousAt.continuousWithinAt
      rw [osc_add hx0.1 hx0.2 hcont]
      have hsq : 1 / 2 ≤ Real.sqrt G := by
        have : Real.sqrt (1 / 4) = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [← this]; exact Real.sqrt_le_sqrt hG4
      have hGs : G = Real.sqrt G * Real.sqrt G := (Real.mul_self_sqrt hG.le).symm
      calc ‖osc (p.phase γ1 γ2) p.a x0 + osc (p.phase γ1 γ2) x0 t‖
          ≤ ‖osc (p.phase γ1 γ2) p.a x0‖ + ‖osc (p.phase γ1 γ2) x0 t‖ := norm_add_le _ _
        _ ≤ 2 / y + 2 / y := add_le_add hI1 hI2
        _ = 4 * p.N / (p.d * Real.sqrt G) / Real.sqrt G := by
            rw [div_div, mul_assoc, ← hGs, hy]; field_simp; ring
        _ ≤ 4 * p.N / (p.d * Real.sqrt G) / (1 / 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
        _ = 8 * p.N / (p.d * Real.sqrt G) := by ring
    · push Not at hG4
      have hsq : Real.sqrt G ≤ 1 := by
        rw [Real.sqrt_le_one]; linarith
      obtain ⟨ha, hb⟩ := hp.b_le
      have h1 : ‖osc (p.phase γ1 γ2) p.a t‖ ≤ |t - p.a| := norm_osc_le _ _ _
      have h2 : |t - p.a| ≤ p.N / p.d := by
        rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
      have h3 : p.N / p.d ≤ 8 * p.N / (p.d * Real.sqrt G) := by
        rw [div_le_div_iff₀ hd (by positivity)]
        nlinarith [mul_pos hN hd]
      linarith
  rcases le_total 0 γ1 with g1 | g1 <;> rcases le_total 0 γ2 with g2 | g2
  · exact hsecond (Or.inl ⟨g1, g2⟩)
  · exact hfirst (mul_nonpos_of_nonneg_of_nonpos g1 g2)
  · exact hfirst (mul_nonpos_of_nonpos_of_nonneg g1 g2)
  · exact hsecond (Or.inr ⟨g1, g2⟩)

/-- ASSEMBLY. Lemma 5, p. 2367, as printed, from the proved leaves of this file through
`phi_bound`, `integrand_eq`, `ibp_bound`, `amp_hasDerivAt`, `amp1_continuousOn`,
`amp1_two_signs`, `variation_two_piece`, `amp_bounds`: for `β₁, β₂ ≤ 1` and
`|γ₁| + |γ₂| > 0`,
`|∫_a^b A^{ρ₁-1} B^{ρ₂-1} dt| ≤ 24 N d⁻¹ (ad - d - 1)^{β₁+β₂-2} (|γ₁| + |γ₂|)^{-1/2}`. -/
theorem lemma5 {p : Prm} (hp : p.Valid) (ρ1 ρ2 : ℂ) (h1 : ρ1.re ≤ 1) (h2 : ρ2.re ≤ 1)
    (hG : 0 < |ρ1.im| + |ρ2.im|) :
    ‖∫ t in p.a..p.b, ((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
      24 * p.N * p.d⁻¹ * p.m ^ (ρ1.re + ρ2.re - 2) * (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) := by
  have hab := hp.a_le_b
  have hd := hp.d_pos
  have hN := hp.N_pos
  set G := |ρ1.im| + |ρ2.im| with hGdef
  set Mb := 8 * p.N / (p.d * Real.sqrt G) with hMb
  set E := p.m ^ (ρ1.re + ρ2.re - 2) with hE
  have hcongr : ∫ t in p.a..p.b, ((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1) =
      ∫ t in p.a..p.b, (p.amp ρ1.re ρ2.re t : ℂ) *
        Complex.exp ((p.phase ρ1.im ρ2.im t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact integrand_eq hp ht ρ1 ρ2
  have hcont : ContinuousOn (p.phase ρ1.im ρ2.im) (Icc p.a p.b) := fun x hx =>
    (phase_hasDerivAt hp ρ1.im ρ2.im hx).continuousAt.continuousWithinAt
  have hibp := ibp_bound hab (fun t ht => amp_hasDerivAt hp ρ1.re ρ2.re ht)
    (amp1_continuousOn hp ρ1.re ρ2.re) hcont (fun t ht => phi_bound hp hG ht)
  obtain ⟨x0, hx0, hs1, hs2⟩ := amp1_two_signs hp h1 h2
  have hvar := variation_two_piece hx0.1 hx0.2 (fun t ht => amp_hasDerivAt hp ρ1.re ρ2.re ht)
    (amp1_continuousOn hp ρ1.re ρ2.re) hs1 hs2 (fun t ht => amp_bounds hp h1 h2 ht)
  have hgb := amp_bounds hp h1 h2 (t := p.b) ⟨hab, le_rfl⟩
  have hMb0 : 0 ≤ Mb := by
    have : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
    positivity
  have hsum : |p.amp ρ1.re ρ2.re p.b| + ∫ t in p.a..p.b, |p.amp1 ρ1.re ρ2.re t| ≤ 3 * E := by
    rw [abs_of_nonneg hgb.1]; linarith [hgb.2]
  have hpow : G ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt G := by
    rw [Real.rpow_neg hG.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hcongr]
  calc _ ≤ (|p.amp ρ1.re ρ2.re p.b| + ∫ t in p.a..p.b, |p.amp1 ρ1.re ρ2.re t|) * Mb := hibp
    _ ≤ 3 * E * Mb := mul_le_mul_of_nonneg_right hsum hMb0
    _ = 24 * p.N * p.d⁻¹ * E * G ^ (-(1 / 2) : ℝ) := by
        rw [hpow, hMb]
        have : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
        field_simp
        ring

theorem phi_first_two_piece {p : Prm} (hp : p.Valid) {γ1 γ2 : ℝ}
    (hγ : γ1 * γ2 ≤ 0) (hG : 0 < |γ1| + |γ2|) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    ‖osc (p.phase γ1 γ2) p.a t‖ ≤ 4 * p.N / (p.d * (|γ1| + |γ2|)) := by
  have hd := hp.d_pos
  have hN := hp.N_pos
  obtain ⟨x0, hx0, hleft, hright⟩ := phase2_two_signs hp hγ le_rfl ht.1 ht.2
  let y : ℝ := (|γ1| + |γ2|) * p.d / p.N
  have hy : 0 < y := by dsimp [y]; positivity
  have hs1 : Icc p.a x0 ⊆ Icc p.a p.b := Icc_subset_Icc le_rfl (hx0.2.trans ht.2)
  have hs2 : Icc x0 t ⊆ Icc p.a p.b := Icc_subset_Icc hx0.1 ht.2
  have hi1 := osc_first_fixed hx0.1 hy
    (fun x hx => phase_hasDerivAt hp γ1 γ2 (hs1 hx))
    (fun x hx => phase1_hasDerivAt hp γ1 γ2 (hs1 hx))
    ((phase2_continuousOn hp γ1 γ2).mono hs1)
    (fun x hx => first_lower hp hγ (hs1 hx)) hleft
  have hi2 := osc_first_fixed hx0.2 hy
    (fun x hx => phase_hasDerivAt hp γ1 γ2 (hs2 hx))
    (fun x hx => phase1_hasDerivAt hp γ1 γ2 (hs2 hx))
    ((phase2_continuousOn hp γ1 γ2).mono hs2)
    (fun x hx => first_lower hp hγ (hs2 hx)) hright
  have hc : ContinuousOn (p.phase γ1 γ2) (Icc p.a t) := fun x hx =>
    (phase_hasDerivAt hp γ1 γ2 ⟨hx.1, hx.2.trans ht.2⟩).continuousAt.continuousWithinAt
  rw [osc_add hx0.1 hx0.2 hc]
  calc ‖osc (p.phase γ1 γ2) p.a x0 + osc (p.phase γ1 γ2) x0 t‖
      ≤ ‖osc (p.phase γ1 γ2) p.a x0‖ + ‖osc (p.phase γ1 γ2) x0 t‖ := norm_add_le _ _
    _ ≤ 2 / y + 2 / y := add_le_add hi1 hi2
    _ = 4 * p.N / (p.d * (|γ1| + |γ2|)) := by dsimp [y]; field_simp; ring

theorem lemma5_of_cutoff {p : Prm} (hp : p.Valid) (ρ1 ρ2 : ℂ) (h1 : ρ1.re ≤ 1) (h2 : ρ2.re ≤ 1)
    {M : ℝ} (hM : 0 < M) (hMG : M ≤ |ρ1.im| + |ρ2.im|) :
    ‖∫ t in p.a..p.b, ((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
      24 * p.N * p.d⁻¹ * p.m ^ (ρ1.re + ρ2.re - 2) * M ^ (-(1 / 2) : ℝ) := by
  have hG : 0 < |ρ1.im| + |ρ2.im| := hM.trans_le hMG
  have hpow : (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) ≤ M ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hM hMG (by norm_num)
  have hd := hp.d_pos
  have hN := hp.N_pos
  have hm := hp.m_pos
  exact (lemma5 hp ρ1 ρ2 h1 h2 hG).trans (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem integral_trivial_bound {p : Prm} (hp : p.Valid) (ρ1 ρ2 : ℂ)
    (h1 : ρ1.re ≤ 1) (h2 : ρ2.re ≤ 1) :
    ‖∫ t in p.a..p.b, ((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
      (p.b - p.a) * p.m ^ (ρ1.re + ρ2.re - 2) := by
  have hab := hp.a_le_b
  have hfun : ∀ t ∈ uIoc p.a p.b,
      ‖((p.A t : ℝ) : ℂ) ^ (ρ1 - 1) * ((p.B t : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
        p.m ^ (ρ1.re + ρ2.re - 2) := by
    intro t ht
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Icc p.a p.b := ⟨ht.1.le, ht.2⟩
    have hg := amp_bounds hp h1 h2 ht'
    rw [integrand_eq hp ht' ρ1 ρ2, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hg.1, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hg.2
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hfun
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact hi.trans_eq (mul_comm _ _)

/-! ### Vacuity instance, PROVED -/

/-- `Valid` holds at `N = 100`, `d = 1`, `a = 10`, `b = 90`, `v_j = u_j = 0`. -/
theorem vacuity_valid : (⟨100, 1, 10, 90, 0, 0, 0, 0⟩ : Prm).Valid := by
  unfold Prm.Valid
  norm_num

theorem vacuity_phase_requires_split :
    let p : Prm := ⟨100, 1, 10, 90, 0, 0, 0, 0⟩
    p.Valid ∧ ¬MonotoneOn (p.phase1 1 (-1)) (Icc p.a p.b) ∧
      ¬AntitoneOn (p.phase1 1 (-1)) (Icc p.a p.b) := by
  dsimp only
  refine ⟨vacuity_valid, ?_, ?_⟩
  · intro h
    have H := h (a := 10) (b := 50) (by norm_num) (by norm_num) (by norm_num)
    norm_num [Prm.phase1, Prm.A, Prm.B] at H
  · intro h
    have H := h (a := 50) (b := 90) (by norm_num) (by norm_num) (by norm_num)
    norm_num [Prm.phase1, Prm.A, Prm.B] at H

theorem vacuity_amp_requires_split :
    let p : Prm := ⟨100, 1, 10, 90, 0, 0, 0, 0⟩
    p.Valid ∧ ¬MonotoneOn (p.amp 0 0) (Icc p.a p.b) ∧
      ¬AntitoneOn (p.amp 0 0) (Icc p.a p.b) := by
  dsimp only
  refine ⟨vacuity_valid, ?_, ?_⟩
  · intro h
    have H := h (a := 10) (b := 50) (by norm_num) (by norm_num) (by norm_num)
    norm_num [Prm.amp, Prm.A, Prm.B, Real.rpow_neg_one] at H
  · intro h
    have H := h (a := 50) (b := 90) (by norm_num) (by norm_num) (by norm_num)
    norm_num [Prm.amp, Prm.A, Prm.B, Real.rpow_neg_one] at H

theorem vacuity_trivial_bound_sharp :
    let p : Prm := ⟨100, 1, 10, 90, 0, 0, 0, 0⟩
    p.Valid ∧
      ‖∫ t in p.a..p.b, ((p.A t : ℝ) : ℂ) ^ ((1 : ℂ) - 1) *
        ((p.B t : ℝ) : ℂ) ^ ((1 : ℂ) - 1)‖ =
        (p.b - p.a) * p.m ^ ((1 : ℝ) + 1 - 2) := by
  dsimp only
  refine ⟨vacuity_valid, ?_⟩
  norm_num

end LeanLab.ExceptionalSet.Decomp1545b

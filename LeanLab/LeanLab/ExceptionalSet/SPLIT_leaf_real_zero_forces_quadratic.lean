import LeanLab.ExceptionalSet.SPLIT_leaf_selected_real_zero

/-!
Splitting the quadratic character step of `SPLIT_leaf_selected_real_zero`.

The imported statement fixes one positive width and then, for every range,
either a strip free of primitive zeros or one real quadratic character whose
zero is the only one in that strip. The step cut here is its middle leaf: a real
zero of a primitive `L` function just below one forces the character to be a
nontrivial real quadratic one.

Three smaller steps build it. The strip of the stated width lies inside `(0, 1)`,
so a zero in it is a positive real number below one. At such a point the
principal character has no zero, because a primitive principal character has
level one and the `L` function there is the Riemann zeta function, which is
negative on `(0, 1)`. Away from the principal character a real zero below one is
the exceptional zero of the lab zero free region: either it sits at distance at
least a fixed multiple of `1 / log` of the level from one, which the strip
forbids for a small enough width, or its character is real.

No new definition is introduced here, and the assembly closes the cut statement
from the three steps.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Real Finset Filter
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.PNTPort.DirichletZF

/-- LEAF: the strip lies inside `(0, 1)`. For a width at most `1 / 4` the lower
edge `1 - a / Real.log P` of the strip is positive, because `1 / 4 < log 2` and
`log 2 ≤ log P`, so every point of the strip is a positive real number. -/
theorem leaf_strip_lower_edge_pos :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ β : ℝ, 1 - a / Real.log P ≤ β → β < 1 → 0 < β := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 2, by linarith, ?_⟩
  intro P hP β hβ hβ1
  have hlogmono : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hratio : Real.log 2 / 2 / Real.log P ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog]
    linarith
  linarith

/-- A local nonvanishing statement for the Riemann zeta function at one, coming
from the simple pole: `(s - 1) * ζ s` tends to the nonzero residue `1`, so on a
small punctured ball around one `ζ` does not vanish. -/
private lemma exists_delta_riemannZeta_ne_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s ≠ 1 → dist s 1 < δ → riemannZeta s ≠ 0 := by
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.tendsto_nhdsWithin_nhds.1 riemannZeta_residue_one (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun s hs hdist hzero => ?_⟩
  have h := hδ' hs hdist
  rw [hzero, mul_zero] at h
  simp [Complex.dist_eq] at h
  norm_num at h

/-- LEAF: the principal character has no zero in the strip. A primitive
principal character of level `q` has `q = 1`, and there the `L` function is the
Riemann zeta function, which does not vanish at a positive real point below
one. -/
theorem leaf_principal_no_strip_zero :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive → χ = 1 →
          ∀ β : ℝ, 0 < β → 1 - a / Real.log P ≤ β → β < 1 →
            χ.LFunction β ≠ 0 := by
  obtain ⟨δ, hδ, hζ⟩ := exists_delta_riemannZeta_ne_zero
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min δ 1 * Real.log 2 / 2, by positivity, ?_⟩
  intro P hP q hq χ h1q hqP hprim hχ1 β hβ hβlow hβ1
  -- primitivity of the principal character forces level one
  have hq1 : q = 1 := by
    have h : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).1 hprim
    rw [hχ1, DirichletCharacter.conductor_one] at h
    exact h.symm
  subst hq1
  -- the character is now the one at level one, where `LFunction` is `riemannZeta`
  rw [DirichletCharacter.LFunction_modOne_eq]
  refine hζ (β : ℂ) ?_ ?_
  · intro h
    have hβeq : β = 1 := by exact_mod_cast h
    linarith
  · have hlogmono : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    have hlog : 0 < Real.log P := Real.log_pos (by linarith)
    have hdist : dist (β : ℂ) 1 = 1 - β := by
      rw [Complex.dist_eq]
      have hsub : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hratio : min δ 1 * Real.log 2 / 2 / Real.log P ≤ min δ 1 / 2 := by
      rw [div_le_iff₀ hlog]
      have hmul := mul_le_mul_of_nonneg_left hlogmono (le_of_lt (lt_min hδ one_pos))
      linarith
    have hminle : min δ 1 ≤ δ := min_le_left _ _
    have hone : min δ 1 ≤ 1 := min_le_right _ _
    rw [hdist]
    have hstep : 1 - β ≤ min δ 1 / 2 := by linarith
    linarith

/-! ### The scale of the strip against the lab zero free region

`Bt N 0 = 6 * Z * N`, so for `q ≤ P` the box `1 - c / log (Bt q 0) ≤ ·` of
`zero_free_region_real` is wider than the strip `1 - a / log P ≤ ·` once
`a ≤ c / (2 K)` with `K = log (6 Z) / log 2 + 2`. Bookkeeping, as in the
imported file, restated so the leaf depends only on the region statement. -/

private lemma mz_log_sixZ_nonneg : 0 ≤ Real.log (6 * Z) :=
  Real.log_nonneg (by have := one_le_Z; linarith)

private lemma mz_K_pos : 0 < Real.log (6 * Z) / Real.log 2 + 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 := mz_log_sixZ_nonneg
  have : 0 ≤ Real.log (6 * Z) / Real.log 2 := div_nonneg h0 h2.le
  linarith

private lemma mz_bt_zero_eq (N : ℕ) : Bt N 0 = (6 * Z) * N := by
  unfold Bt
  simp
  ring

private lemma mz_log_bt_zero_le {q : ℕ} [NeZero q] {P : ℝ} (hP : 2 ≤ P)
    (hqP : (q : ℝ) ≤ P) :
    Real.log (Bt q 0) ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlogP0 : 0 < Real.log P := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hL := mz_log_sixZ_nonneg
  have h6Z : (0 : ℝ) < 6 * Z := by have := one_le_Z; linarith
  rw [mz_bt_zero_eq, Real.log_mul h6Z.ne' hq0.ne']
  have h1 : Real.log (6 * Z) ≤ Real.log (6 * Z) / Real.log 2 * Real.log P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogP hL
  have h2 : Real.log (q : ℝ) ≤ Real.log P := Real.log_le_log hq0 hqP
  have hexp : (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P
      = Real.log (6 * Z) / Real.log 2 * Real.log P + 2 * Real.log P := by ring
  linarith

private lemma mz_one_sub_lt_box {c : ℝ} (hc : 0 < c) {q : ℕ} [NeZero q] {P β a : ℝ}
    (hP : 2 ≤ P) (hqP : (q : ℝ) ≤ P) (ha0 : 0 ≤ a)
    (ha : a ≤ c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)))
    (hβ : 1 - a / Real.log P ≤ β) :
    1 - c / Real.log (Bt q 0) < β := by
  have hKpos := mz_K_pos
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogBt1 : 1 ≤ Real.log (Bt q 0) := one_le_log_Bt 0
  have hlogBt : 0 < Real.log (Bt q 0) := by linarith
  have hmono : Real.log (Bt q 0)
      ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := mz_log_bt_zero_le hP hqP
  have haK : a * (Real.log (6 * Z) / Real.log 2 + 2) ≤ c / 2 := by
    have h := mul_le_mul_of_nonneg_right ha (le_of_lt hKpos)
    have he : (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)))
        * (Real.log (6 * Z) / Real.log 2 + 2) = c / 2 := by
      rw [div_mul_eq_mul_div, mul_comm c, mul_comm (2 : ℝ)]
      exact mul_div_mul_left c 2 hKpos.ne'
    linarith
  have h1 : a * Real.log (Bt q 0)
      ≤ a * ((Real.log (6 * Z) / Real.log 2 + 2) * Real.log P) :=
    mul_le_mul_of_nonneg_left hmono ha0
  have h2 : a * ((Real.log (6 * Z) / Real.log 2 + 2) * Real.log P)
      = (a * (Real.log (6 * Z) / Real.log 2 + 2)) * Real.log P := by ring
  have h3 : (a * (Real.log (6 * Z) / Real.log 2 + 2)) * Real.log P
      ≤ (c / 2) * Real.log P := mul_le_mul_of_nonneg_right haK (le_of_lt hlogP)
  have h4 : a * Real.log (Bt q 0) ≤ (c / 2) * Real.log P := by
    rw [h2] at h1
    linarith
  have hkey : a * Real.log (Bt q 0) < c * Real.log P := by nlinarith
  have hdiv : a / Real.log P < c / Real.log (Bt q 0) := by
    rw [div_lt_div_iff₀ hlogP hlogBt]
    exact hkey
  linarith

/-- LEAF: a non-principal character with a real zero in the strip is real
quadratic. The lab zero free region puts such a zero either at distance at least
a fixed multiple of `1 / log` of the level from one, which a small enough width
forbids, or else at the single exceptional zero, whose character is real. -/
theorem leaf_nonprincipal_strip_forces_quadratic :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive → χ ≠ 1 →
          ∀ β : ℝ, 0 < β → 1 - a / Real.log P ≤ β → β < 1 →
            χ.LFunction β = 0 → χ ^ 2 = 1 := by
  obtain ⟨c, c', hc, hc', H⟩ := zero_free_region_real
  have hKpos := mz_K_pos
  have hden : 0 < 2 * (Real.log (6 * Z) / Real.log 2 + 2) := by linarith
  refine ⟨min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4),
    lt_min (div_pos hc hden) (by norm_num), ?_⟩
  intro P hP q hq χ h1q hqP hprim hχ1 β hβ hβlow hβ1 hzero
  haveI : NeZero q := hq
  have ha0 : 0 ≤ min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4) :=
    le_of_lt (lt_min (div_pos hc hden) (by norm_num))
  have haK : min (c / (2 * (Real.log (6 * Z) / Real.log 2 + 2))) (1 / 4)
      ≤ c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)) := min_le_left _ _
  have hbox := mz_one_sub_lt_box hc hP hqP ha0 haK hβlow
  have hres := (H q χ hχ1).1 (β : ℂ) hzero
  rcases hres with hleft | hright
  · rw [Complex.ofReal_re, Complex.ofReal_im] at hleft
    linarith
  · exact hright.2.2.1

/-- The quadratic character step of the imported file, closed from the three
leaves above: one positive width, and every primitive character with a real zero
that close to one is a nontrivial real quadratic character. -/
theorem leaf_real_zero_forces_quadratic_split :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
          (∃ β : ℝ, 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0) →
            χ ^ 2 = 1 ∧ χ ≠ 1 := by
  obtain ⟨a₁, ha₁, hpos⟩ := leaf_strip_lower_edge_pos
  obtain ⟨a₂, ha₂, hprin⟩ := leaf_principal_no_strip_zero
  obtain ⟨a₃, ha₃, hquad⟩ := leaf_nonprincipal_strip_forces_quadratic
  refine ⟨min a₁ (min a₂ a₃), lt_min ha₁ (lt_min ha₂ ha₃), ?_⟩
  intro P hP q hq χ h1q hqP hprim
  rintro ⟨β, hβ, hβ1, hβ0⟩
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hle₁ : min a₁ (min a₂ a₃) ≤ a₁ := min_le_left _ _
  have hle₂ : min a₁ (min a₂ a₃) ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : min a₁ (min a₂ a₃) ≤ a₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hmono : ∀ a' : ℝ, min a₁ (min a₂ a₃) ≤ a' → 1 - a' / Real.log P ≤ β := by
    intro a' ha'
    have h := div_le_div_of_nonneg_right ha' hlog.le
    linarith
  have hβpos : 0 < β := hpos P hP β (hmono a₁ hle₁) hβ1
  by_cases h1 : χ = 1
  · exact absurd hβ0
      (hprin P hP q hq χ h1q hqP hprim h1 β hβpos (hmono a₂ hle₂) hβ1)
  · refine ⟨?_, h1⟩
    by_contra h2
    exact h2 (hquad P hP q hq χ h1q hqP hprim h1 β hβpos (hmono a₃ hle₃) hβ1 hβ0)

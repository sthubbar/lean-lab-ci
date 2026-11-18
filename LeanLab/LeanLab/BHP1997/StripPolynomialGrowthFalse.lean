/-
FALSIFY unit BHP1997/SPLIT_leaf_strip_convexity_interpolation.

`leaf_strip_polynomial_growth` in
LeanLab.BHP1997.SPLIT_leaf_strip_convexity_interpolation is FALSE as stated. Its statement
quantifies over every modulus `q >= 1` and every character `chi` of modulus `q`, with no
exclusion of the principal character. At `x = 2`, `q = 1` the only character is trivial and
Mathlib's `DirichletCharacter.LFunction` is `riemannZeta`
(`DirichletCharacter.LFunction_modOne_eq`). The real points `s = 1 + eps` with
`0 < eps < 1 / log 2` lie in the closed strip `1 / 2 <= Re s <= 1 + 1 / log 2` and have
`Im s = 0`, so the claimed bound there reads `|zeta(1 + eps)| <= C * 1 ^ k = C`. But
`(s - 1) * zeta(s) -> 1` as `s -> 1` (`riemannZeta_residue_one`), so
`eps * |zeta(1 + eps)| -> 1` while `eps * C -> 0`. Contradiction.

The statement below is the universal closure of the statement of
`leaf_strip_polynomial_growth`, copied verbatim, under a negation. This file imports only
Mathlib, so the refutation does not depend on any sorry of the lab.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace LeanLab.BHP1997.DecompC165a.Contour230

open Complex Filter Set
open scoped Topology

/-- The real path `eps |-> 1 + eps`, `eps > 0`, tends to `1` inside the punctured
neighbourhood of `1` in the complex plane. Standard. -/
theorem tendsto_one_add_ofReal_nhdsNE :
    Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (((1 + 0 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
    have h1 : (((1 + 0 : ℝ)) : ℂ) = 1 := by simp
    rw [h1] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    intro hmem
    have h2 : ((1 + ε : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by simpa using hmem
    have h3 : 1 + ε = 1 := Complex.ofReal_injective h2
    linarith

/-- `leaf_strip_polynomial_growth` is FALSE: its universal closure, with the statement
copied verbatim, is refuted at `x = 2`, `q = 1`, where the L-function is the Riemann zeta
function and is unbounded on the real points `1 + eps` of the strip, by the pole at
`s = 1` with residue `1` (`riemannZeta_residue_one`). -/
theorem leaf_strip_polynomial_growth_false :
    ¬ (∀ (x : ℝ) (_hx : 2 ≤ x) (q : ℕ) [NeZero q] (_hq : 1 ≤ q)
        (_hqx : (q : ℝ) ≤ x) (χ : DirichletCharacter ℂ q),
        ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
          ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 + 1 / Real.log x →
            ‖χ.LFunction s‖ ≤ C * (|s.im| + 1) ^ k) := by
  intro h
  obtain ⟨C, k, hC, _hk, hb⟩ :=
    h 2 le_rfl 1 le_rfl (by norm_num) (1 : DirichletCharacter ℂ 1)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (0 : ℝ) < 1 / Real.log 2 := one_div_pos.mpr hlog
  -- residue one along the real path
  have hres : Tendsto (fun ε : ℝ => ‖(((1 + ε : ℝ) : ℂ) - 1) * riemannZeta ((1 + ε : ℝ) : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖(1 : ℂ)‖) :=
    (riemannZeta_residue_one.comp tendsto_one_add_ofReal_nhdsNE).norm
  -- the claimed bound forces the same quantity below `eps * C`
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖(((1 + ε : ℝ) : ℂ) - 1) * riemannZeta ((1 + ε : ℝ) : ℂ)‖ ≤ ε * C := by
    filter_upwards [Ioo_mem_nhdsGT hinv] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have hre : (((1 + ε : ℝ) : ℂ)).re = 1 + ε := Complex.ofReal_re _
    have him : (((1 + ε : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
    have hbound := hb ((1 + ε : ℝ) : ℂ) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [DirichletCharacter.LFunction_modOne_eq, him] at hbound
    have hone : C * (|(0 : ℝ)| + 1) ^ k = C := by simp
    rw [hone] at hbound
    have hsub : (((1 + ε : ℝ) : ℂ) - 1) = ((ε : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    exact mul_le_mul_of_nonneg_left hbound hε0.le
  have h0 : Tendsto (fun ε : ℝ => ε * C) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => ε * C) (𝓝 (0 : ℝ)) (𝓝 (0 * C)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hfin : ‖(1 : ℂ)‖ ≤ 0 := le_of_tendsto_of_tendsto hres h0 hle
  rw [norm_one] at hfin
  linarith

-- Axiom audit driver.
#print axioms tendsto_one_add_ofReal_nhdsNE
#print axioms leaf_strip_polynomial_growth_false

end LeanLab.BHP1997.DecompC165a.Contour230

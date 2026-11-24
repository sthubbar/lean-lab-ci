import LeanLab.ChenDoubleSieve.Decomp587i

/-!
Split of `r2j16_short` from `LeanLab.ChenDoubleSieve.Decomp587i`.
Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30. Source: https://arxiv.org/abs/0705.1652.
The window two to seven halves for phi is cut at 421 / 200 and 221 / 100.
Above 221 / 100 the kernel argument is at least 13 / 10 on the whole box, so a uniform cap
78 / 100 on Buchstab's function and the exact reciprocal polynomial moment close it;
that glue is proved here. The cap and the two low windows are the LEAFs.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587.SplitR2J16
open Wu04Functional

/-- LEAF: Buchstab function cap, Wu 2004 Lemma 2.10 page 9 with the numerical values of
omega used for Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30. For u at least 13 / 10 one has omega u at most
78 / 100; numerically the last crossing of this level is below 13 / 10 and omega tends to
exp of minus gamma, about 0.5615. Class MEDIUM. -/
theorem omega_cap {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (13 / 10 : ℝ) ≤ u) :
    ω u ≤ (78 / 100 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30, numerical maximisation of the Buchstab
integral, low window phi between 2 and 421 / 200. Class HARD. -/
theorem window_low {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (421 / 200 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤ ((42971 / 500000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30, numerical maximisation of the Buchstab
integral, middle window phi between 421 / 200 and 221 / 100. Class HARD. -/
theorem window_mid {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (421 / 200 : ℝ) ≤ φ) (hφtop : φ ≤ (221 / 100 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤ ((42971 / 500000000) : ℝ) := by
  sorry

/-- A corner bound puts the kernel argument above `A` on the whole box.
Wu 2004 page 26, derived corner arithmetic. -/
theorem argument_ge {d : ℕ} (k : Fin d) {lo hi : Fin d → ℚ} {φ P A : ℝ}
    (hA : 0 ≤ A) (hlo : ∀ j, 0 < lo j) (hφ : P ≤ φ)
    (hcorner : A * (hi k : ℝ) + ∑ j, (hi j : ℝ) ≤ P)
    {x : Fin d → ℝ} (hx : x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) :
    A ≤ (φ - ∑ j, x j) / x k := by
  have hxk : (0 : ℝ) < x k := by
    have h : (0 : ℝ) < (lo k : ℝ) := by exact_mod_cast hlo k
    exact h.trans_le (hx.2 k).1
  exact Task562.argument_ge_of_box (k := k) (a := A) (P := P)
    (lo := fun j => (lo j : ℝ)) (hi := fun j => (hi j : ℝ))
    hA ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩ hxk hφ hcorner

/-- The reciprocal certificate with an arbitrary cap `C` valid from `A ≥ 1` on.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
theorem cell_integral_cap {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (N : ℕ) (lo hi : Fin (n + 2) → ℚ) {φ A C : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hcap : ∀ u : ℝ, A ≤ u → ω u ≤ C)
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j)
    (harg : ∀ x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      A ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    buchstabIntegral ω n (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ ≤
      C * ∫ x in domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
        cellPoly N ⟨n, by omega⟩ lo hi x := by
  have hl (j : Fin (n + 2)) : (0 : ℝ) < lo j := by exact_mod_cast hlo j
  have hf := kernel_integrable_above_one hω (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ hl
    (fun x hx => hA.trans (harg x hx))
  have hm := setIntegral_mono_on hf
    ((cellPoly_integrable N ⟨n, by omega⟩ lo hi).const_mul C)
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hl j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (hcap _ (harg x hx)) hd.le
      calc
        _ ≤ C / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = C * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_le_cellPoly N _ lo hi hlo hle hx) hC)
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

/-- The window phi at least 221 / 100, CONDITIONAL ON the LEAF `omega_cap`.
Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30. -/
theorem window_high {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (221 / 100 : ℝ) ≤ φ) :
    buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤ ((42971 / 500000000) : ℝ) := by
  have h := cell_integral_cap hω (n := 2) 4 r2j16_lo r2j16_hi (A := (13 / 10 : ℝ)) (C := (78 / 100 : ℝ))
    (by norm_num) (by norm_num) (fun u hu => omega_cap hω hu)
    (by intro j; fin_cases j <;> norm_num [r2j16_lo])
    (by intro j; fin_cases j <;> norm_num [r2j16_lo, r2j16_hi])
    (fun x hx => argument_ge (d := 4) (2 : Fin 4) (lo := r2j16_lo) (hi := r2j16_hi)
      (A := (13 / 10 : ℝ)) (P := (221 / 100 : ℝ)) (by norm_num)
      (by intro j; fin_cases j <;> norm_num [r2j16_lo]) hφ
      (by norm_num [r2j16_hi, Fin.sum_univ_four]) hx)
  change buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤
    (78 / 100 : ℝ) * (∫ x in domain (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)),
      cellPoly 4 (2 : Fin 4) r2j16_lo r2j16_hi x) at h
  rw [r2j16_integral] at h
  exact h.trans (by norm_num)

/-- Exactly the parent statement `r2j16_short`, PROVED from the LEAFs
`omega_cap`, `window_low` and `window_mid`. CONDITIONAL ON those LEAFs.
Wu 2004 Lemma 5.2 page 26, D2,16, Table 1 row 3 page 30. -/
theorem r2j16_short_of_leaves {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r2j16_lo j : ℝ)) (fun j => (r2j16_hi j : ℝ)) φ ≤ ((42971 / 500000000) : ℝ) := by
  rcases le_total φ (421 / 200 : ℝ) with h1 | h1
  · exact window_low hω hz hφ h1
  rcases le_total φ (221 / 100 : ℝ) with h2 | h2
  · exact window_mid hω hz h1 h2
  · exact window_high hω h2

end LeanLab.ChenDoubleSieve.Task587.SplitR2J16

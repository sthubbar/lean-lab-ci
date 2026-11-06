import LeanLab.LPZ2007.ZeroFamily373

/-!
Jutila 1977, Theorem 1, pages 46 and 51 to 54.
DOI https://doi.org/10.7146/math.scand.a-11701.
The distinct zero version suffices for the input quoted on P0045 page 5.
The two analytic leaves separate local zero extraction from the density estimate
for separated zeros. The final theorem has exactly type JutilaBound.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Decomp407a

open Real Filter

/-- P0045 pages 4 and 5, display 8, and Jutila page 51, the bounded modulus case.
For bounded modulus and height the exceptional strip eventually contains no zeros.
This follows from finiteness and the strict inequality Re rho less than one. -/
theorem bounded_moduli_empty (H T M : ℝ) :
    ∃ X0 : ℝ, ∀ X P : ℝ, X0 ≤ X → P ≤ M → EZero X H T P = ∅ := by
  let S := EZero (Real.exp 1) 1 T M
  have hfinite : S.Finite := ZeroFamily373.EZero_finite _ _ _ _
  have hlim : Tendsto (fun X : ℝ => H / Real.log X) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hgap : ∀ᶠ X : ℝ in atTop, ∀ z ∈ S, H / Real.log X < 1 - z.2.2.re := by
    apply hfinite.eventually_all.2
    intro z hz
    have hlt := ZeroFamily373.primitive_zero_re_lt_one hz.1 z.2.1 hz.2.2.1 hz.2.2.2.1
    exact hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - z.2.2.re))
  have hsmall : ∀ᶠ X : ℝ in atTop, H / Real.log X < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 (hgap.and hsmall)
  refine ⟨X0, fun X P hX hP => Set.eq_empty_iff_forall_notMem.2 ?_⟩
  intro z hz
  obtain ⟨hg, hs⟩ := hX0 X hX
  have hzS : z ∈ S := by
    refine ⟨hz.1, hz.2.1.trans hP, hz.2.2.1, hz.2.2.2.1, ?_, hz.2.2.2.2.2⟩
    simp only [Real.log_exp, div_one, sub_self]
    linarith [hz.2.2.2.2.1]
  have := hg z hzS
  linarith [hz.2.2.2.2.1]

/-- LEAF. Jutila 1977 page 51, Lemma 8 and the selection in display 3.1.
One selected zero per height cell and parity gives a separated primitive family.
The local zero count costs at most a constant times H plus one.
Distinct zeros are counted here, so this is weaker than the multiplicity version.
The height spacing is reciprocal log of P squared times T. -/
theorem separated_extraction :
    ∃ C : ℝ, 0 < C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∃ s : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ s, z ∈ EZero X H T P) ∧
          (∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ →
              1 / Real.log (P ^ 2 * T) ≤ |z.2.2.im - w.2.2.im|) ∧
          ((EZero X H T P).ncard : ℝ) ≤ C * (H + 1) * s.card := by
  sorry

/-- LEAF. Jutila 1977 pages 52 to 54, displays 3.2 to 3.7 and the proof of 1.8.
The pseudcharacter detector and the integrated Halasz kernel bound the selected
primitive family. Epsilon one half in display 1.8 gives the exponent fifteen quarters
after P at most sqrt X and T at most P. Separation is only within each character.
This leaf does not assert the count for the full unseparated zero family. -/
theorem separated_density :
    ∃ C : ℝ, 0 < C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∀ s : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ s, z ∈ EZero X H T P) →
          (∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ →
              1 / Real.log (P ^ 2 * T) ≤ |z.2.2.im - w.2.2.im|) →
          (s.card : ℝ) ≤ C * Real.exp ((15 / 4 : ℝ) * H) := by
  sorry

/-- Jutila page 51, the loss from extracting separated zeros is absorbed
by the slack between fifteen quarters H and four H in P0045 page 5. -/
theorem extraction_loss_le {H : ℝ} (hH : 0 ≤ H) :
    (H + 1) * Real.exp ((15 / 4 : ℝ) * H) ≤ 4 * Real.exp (4 * H) := by
  have h := Real.add_one_le_exp (H / 4)
  have hlinear : H + 1 ≤ 4 * Real.exp (H / 4) := by linarith
  calc
    _ ≤ (4 * Real.exp (H / 4)) * Real.exp ((15 / 4 : ℝ) * H) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
    _ = 4 * Real.exp (4 * H) := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring

/-- The cited JutilaBound assembled from the two smaller analytic leaves.
This is CONDITIONAL ON separated_extraction and separated_density. -/
theorem jutila_decomposed : JutilaBound := by
  obtain ⟨Ce, hCe, he⟩ := separated_extraction
  obtain ⟨Cd, hCd, hd⟩ := separated_density
  refine ⟨4 * Ce * Cd, ?_⟩
  intro H T hH hT
  obtain ⟨Xe, he⟩ := he H T hH hT
  obtain ⟨Xd, hd⟩ := hd H T hH hT
  obtain ⟨Xb, hb⟩ := bounded_moduli_empty H T 2
  refine ⟨max Xe (max Xd Xb), ?_⟩
  intro X P hX hTP hPX
  refine ⟨ZeroFamily373.EZero_finite X H T P, ?_⟩
  by_cases hP : 2 ≤ P
  · obtain ⟨s, hs, hsep, hcard⟩ := he X P ((le_max_left _ _).trans hX) hP hTP hPX
    have hbound := hd X P ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
      hP hTP hPX s hs hsep
    calc
      ((EZero X H T P).ncard : ℝ) ≤ Ce * (H + 1) * s.card := hcard
      _ ≤ Ce * (H + 1) * (Cd * Real.exp ((15 / 4 : ℝ) * H)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Ce * Cd * ((H + 1) * Real.exp ((15 / 4 : ℝ) * H)) := by ring
      _ ≤ Ce * Cd * (4 * Real.exp (4 * H)) :=
        mul_le_mul_of_nonneg_left (extraction_loss_le (by linarith)) (by positivity)
      _ = 4 * Ce * Cd * Real.exp (4 * H) := by ring
  · rw [hb X P ((le_max_right _ _).trans ((le_max_right _ _).trans hX)) (le_of_not_ge hP),
      Set.ncard_empty, Nat.cast_zero]
    positivity

end LeanLab.LPZ2007.Decomp407a

#print axioms LeanLab.LPZ2007.Decomp407a.bounded_moduli_empty
#print axioms LeanLab.LPZ2007.Decomp407a.separated_extraction
#print axioms LeanLab.LPZ2007.Decomp407a.separated_density
#print axioms LeanLab.LPZ2007.Decomp407a.extraction_loss_le
#print axioms LeanLab.LPZ2007.Decomp407a.jutila_decomposed

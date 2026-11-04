import LeanLab.DERZ1997.Decomp1529b2
import LeanLab.DERZ1997.Character266
import LeanLab.DERZ1997.Cover266
import LeanLab.DERZ1997.Saouter266

/-!
Concrete instances for CODEX task266.
The finite-set and cutoff examples need no cited analytic input.
The separated-height example is labeled conditional on the existing zero-free leaf.
AI wrote the Lean code. Goldbach is open.
-/
open Complex
open LeanLab.DERZ1997.Decomp1529b2 LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Decomp1529a
open LeanLab.DERZ1997.Character266

example : ‖(2 : ℂ) * (2 : ℂ) ^ ((1 / 2 : ℂ) + 3 * I) /
    ((1 / 2 : ℂ) + 3 * I)‖ ≤ (2 : ℝ) * 2 / 3 := by
  apply zero_term_height266 (by norm_num) (by norm_num)
  · norm_num
  · norm_num

example : ({(1 / 2 : ℂ) + 3 * I} : Finset ℂ).Nonempty := ⟨(1 / 2 : ℂ) + 3 * I, by simp⟩
example :
    ‖(∑ ρ ∈ ({(1 / 2 : ℂ) + 3 * I, (1 / 2 : ℂ) + 4 * I} : Finset ℂ),
      ((1 : ℕ) : ℂ) * ((2 : ℝ) : ℂ) ^ ρ / ρ) -
      ∑ ρ ∈ ({(1 / 2 : ℂ) + 3 * I} : Finset ℂ), ((1 : ℕ) : ℂ) * ((2 : ℝ) : ℂ) ^ ρ / ρ‖ ≤
    (∑ _ρ ∈ ({(1 / 2 : ℂ) + 3 * I, (1 / 2 : ℂ) + 4 * I} : Finset ℂ) \
      {(1 / 2 : ℂ) + 3 * I}, ((1 : ℕ) : ℝ)) * 2 / 3 := by
  classical
  refine finite_height_transfer266 (x := 2) (T := 3) (by norm_num) (by norm_num)
    {(1 / 2 : ℂ) + 3 * I} {(1 / 2 : ℂ) + 3 * I, (1 / 2 : ℂ) + 4 * I}
    (by simp) (fun _ => 1) ?_ ?_
  · intro ρ hρ
    have hmem := (Finset.mem_sdiff.mp hρ).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> norm_num
  · intro ρ hρ
    have hmem := (Finset.mem_sdiff.mp hρ).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> norm_num

example : |(2 : ℝ) + 1 / 2 - 4| ≤ (3 / 2 : ℝ) * |(11 / 4 : ℝ) - 4| :=
  distant_integer_compare266 2 4 (by norm_num) (by norm_num) (by decide) (by decide)

example : (∑ n ∈ Finset.range 6, if n = 2 ∨ n = 3 then (0 : ℝ) else 1 / |(11 / 4 : ℝ) - n|) ≤
    12 * Real.log (11 / 4 : ℝ) := by
  have hh := distant_recip_sum266 (by norm_num : (2 : ℝ) ≤ 11 / 4)
  norm_num only [show ⌊(11 / 4 : ℝ)⌋₊ = 2 by norm_num] at hh
  exact hh

example : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * ((11 / 4 : ℝ) / n) ^
      (1 + 1 / Real.log (11 / 4 : ℝ)) * min 1 (1 / ((2 : ℝ) * |Real.log ((11 / 4 : ℝ) / n)|)) ≤
    432 * ((11 / 4 : ℝ) * Real.log (11 / 4 : ℝ) ^ 2 / 2) + 32 * Real.log (11 / 4 : ℝ) :=
  perron_tail_arbitrary266 (by norm_num) (by norm_num)

example : ‖(Chebyshev.psi (11 / 4 : ℝ) : ℂ) -
    perronPsi (11 / 4 : ℝ) (1 + 1 / Real.log (11 / 4 : ℝ)) 2‖ ≤
      432 * ((11 / 4 : ℝ) * Real.log (11 / 4 : ℝ) ^ 2 / 2 + Real.log (11 / 4 : ℝ)) := by
  apply perron_error_arbitrary266 (by norm_num) (by norm_num)
  intro n hn
  have hh : (n : ℝ) * 4 = 11 := by linarith
  have hh' : n * 4 = 11 := by exact_mod_cast hh
  omega

example : ∃ hfT : (zetaZeros 3).Finite, ∃ hfU : (zetaZeros 3).Finite,
    ∃ hfW : (zetaZerosWindow 3).Finite,
      (∑ ρ ∈ hfU.toFinset \ hfT.toFinset, (zetaMult ρ : ℝ)) ≤
        2 * ∑ ρ ∈ hfW.toFinset, (zetaMult ρ : ℝ) := by
  classical
  have hw : (zetaZerosWindow 3).Finite := by
    apply (zetaZeros_finite 4).subset
    intro ρ hρ
    refine ⟨hρ.1, hρ.2.1, hρ.2.2.1, ?_⟩
    rw [abs_of_pos (by linarith [hρ.2.2.2.1])]
    linarith [hρ.2.2.2.2]
  refine ⟨zetaZeros_finite 3, zetaZeros_finite 3, hw, ?_⟩
  exact zeta_band_mass266 (by norm_num) (by norm_num) _ _ _

example : ∃ hf : (zetaZeros 3).Finite, ∃ hw : (zetaZerosWindow 3).Finite,
    ‖(∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (2 : ℂ) ^ ρ / ρ) -
      ∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
        2 * (∑ ρ ∈ hw.toFinset, (zetaMult ρ : ℝ)) * 2 / 3 := by
  classical
  have hw : (zetaZerosWindow 3).Finite := by
    apply (zetaZeros_finite 4).subset
    intro ρ hρ
    refine ⟨hρ.1, hρ.2.1, hρ.2.2.1, ?_⟩
    rw [abs_of_pos (by linarith [hρ.2.2.2.1])]
    linarith [hρ.2.2.2.2]
  refine ⟨zetaZeros_finite 3, hw, ?_⟩
  simpa only [Complex.ofReal_ofNat] using zeta_height_transfer266 (x := 2) (T := 3) (U := 3)
    (B := ∑ ρ ∈ hw.toFinset, (zetaMult ρ : ℝ))
    (by norm_num) (by norm_num) le_rfl (by norm_num) _ _ hw le_rfl

/-- CONDITIONAL ON the existing cited zero-free-height leaf for this concrete separation witness. -/
example : ∃ C : ℝ, ‖(Chebyshev.psi (11 / 2 : ℝ) : ℂ) - (11 / 2 : ℝ) +
    ∑ ρ ∈ (zetaZeros_finite 5).toFinset, (zetaMult ρ : ℂ) * ((11 / 2 : ℝ) : ℂ) ^ ρ / ρ‖ ≤
      C * ((11 / 2 : ℝ) * Real.log (11 / 2 : ℝ) ^ 2 / 5 + Real.log (11 / 2 : ℝ)) := by
  obtain ⟨C, hC⟩ := explicit_formula_noninteger_good266
  refine ⟨C, hC (11 / 2) 5 (by norm_num) (by norm_num) (by norm_num) ?_ ?_ _⟩
  · intro n hn
    have hh : (n : ℝ) * 2 = 11 := by linarith
    have hh' : n * 2 = 11 := by exact_mod_cast hh
    omega
  · intro ρ hρ
    rw [zetaZeros_eq_empty (by norm_num : (5 : ℝ) + 1 < 14)] at hρ
    exact False.elim hρ

/-- CONDITIONAL ON the existing cited zero-free-height leaf for this concrete separation witness. -/
example : ∃ C : ℝ, ‖(Chebyshev.psi 5 : ℂ) - 5 +
    ∑ ρ ∈ (zetaZeros_finite 5).toFinset, (zetaMult ρ : ℂ) * (5 : ℂ) ^ ρ / ρ‖ ≤
      C * (5 * Real.log 5 ^ 2 / 5 + Real.log 5) := by
  obtain ⟨C, hC⟩ := explicit_formula_good266
  refine ⟨C, hC 5 5 (by norm_num) (by norm_num) le_rfl ?_ _⟩
  intro ρ hρ
  rw [zetaZeros_eq_empty (by norm_num : (5 : ℝ) + 1 < 14)] at hρ
  exact False.elim hρ

example : (2 : ℝ) ^ (1 / 8 : ℝ) * Real.log 2 * 1 ≤ 4 * (Real.sqrt 2 + 1 ^ 2) :=
  left_edge_budget266 (by norm_num) (by norm_num)

/-- The nonprincipal premise has a concrete modulus-three instance. -/
example : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  refine ⟨e.symm (-1), ?_⟩
  intro he
  have hh := congrArg e he
  simp only [MulEquiv.apply_symm_apply, map_one] at hh
  have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh
  exact (by decide : (-1 : ZMod 3) ≠ 1) hc

example (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    residue (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (2 : ℂ) ^ s / s) 2 =
        -(analyticOrderNatAt (DirichletCharacter.LFunction χ) 2 : ℂ) * (2 : ℂ) ^ (2 : ℂ) / 2 := by
  simpa only [Complex.ofReal_ofNat] using character_perron_residue266 χ hχ
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℂ) ≠ 0)

example (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    ∃ hf : (Rectangle (⟨2, -1⟩ : ℂ) ⟨3, 1⟩ ∩ {s : ℂ | DirichletCharacter.LFunction χ s = 0}).Finite,
      RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (2 : ℂ) ^ s / s) ⟨2, -1⟩ ⟨3, 1⟩ =
          -(∑ ρ ∈ hf.toFinset, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
            (2 : ℂ) ^ ρ / ρ) := by
  have hre {z : ℂ} (hz : z ∈ Rectangle (⟨2, -1⟩ : ℂ) ⟨3, 1⟩) : (2 : ℝ) ≤ z.re := by
    change z.re ∈ Set.uIcc (2 : ℝ) 3 ∧ z.im ∈ Set.uIcc (-1 : ℝ) 1 at hz
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at hz
    exact hz.1.1
  have heq : Rectangle (⟨2, -1⟩ : ℂ) ⟨3, 1⟩ ∩ {s : ℂ | DirichletCharacter.LFunction χ s = 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by linarith [hre hz.1]) hz.2
  have hf : (Rectangle (⟨2, -1⟩ : ℂ) ⟨3, 1⟩ ∩ {s : ℂ | DirichletCharacter.LFunction χ s = 0}).Finite := by
    rw [heq]
    exact Set.finite_empty
  refine ⟨hf, ?_⟩
  simpa only [Complex.ofReal_ofNat] using character_rectangle266 χ hχ
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) < 3) (by norm_num : (0 : ℝ) < 1) hf
    (fun z hz => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by linarith [hre (rectangleBorder_subset_rectangle _ _ hz)]))

/-- This concrete contour witness is conditional on GRH alone. -/
example (hG : LeanLab.DERZ1997.GRH) (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    ∃ T ∈ Set.Icc (1 : ℝ) 2, ∃ hf : (LZeros χ T).Finite,
      RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (2 : ℂ) ^ s / s) ⟨1 / 8, -T⟩ ⟨2, T⟩ =
          -(∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (2 : ℂ) ^ ρ / ρ) := by
  classical
  let hz := LZeros_finite χ 2
  let G := hz.toFinset.image (fun ρ : ℂ => |ρ.im|)
  obtain ⟨T, hTI, hfar⟩ := LeanLab.PNTPort.ZetaZeros.exists_far G 1
  have hT0 : 0 < T := by linarith [hTI.1]
  have hT2 : T ≤ 2 := by linarith [hTI.2]
  have hbd : ∀ z ∈ RectangleBorder (⟨1 / 8, -T⟩ : ℂ) ⟨2, T⟩,
      DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hborder hzero
    have hrect := rectangleBorder_subset_rectangle _ _ hborder
    change z.re ∈ Set.uIcc (1 / 8 : ℝ) 2 ∧ z.im ∈ Set.uIcc (-T) T at hrect
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 2),
      Set.uIcc_of_le (show -T ≤ T by linarith)] at hrect
    have hre : 0 < z.re := by linarith [hrect.1.1]
    have hre1 : z.re < 1 := by
      by_contra hn
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hzero
    have hline := hG 3 χ z hzero hre hre1
    have hheight : |z.im| = T := by
      have hcases : z.im = -T ∨ z.re = 1 / 8 ∨ z.im = T ∨ z.re = 2 := by
        simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at hborder
        rcases hborder with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      rcases hcases with h | h | h | h
      · simp only [h, abs_neg, abs_of_pos hT0]
      · linarith
      · simp only [h, abs_of_pos hT0]
      · linarith
    have hmem : T ∈ G := by
      apply Finset.mem_image.mpr
      refine ⟨z, hz.mem_toFinset.mpr ⟨hzero, hre, hre1, ?_⟩, hheight⟩
      rw [hheight]
      exact hT2
    have hh := hfar T hmem
    simp only [sub_self, abs_zero] at hh
    have hp : (0 : ℝ) < 1 / (2 * ((G.card : ℝ) + 1)) := by positivity
    linarith
  refine ⟨T, ⟨hTI.1, hT2⟩, LZeros_finite χ T, ?_⟩
  simpa only [Complex.ofReal_ofNat] using character_contour_GRH266 hG χ hχ
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2) hT0 hbd (LZeros_finite χ T)

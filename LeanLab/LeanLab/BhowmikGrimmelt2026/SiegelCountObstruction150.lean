/-
Obstruction to the leaf `siegel_count150` of SPLIT_mv_siegel150.lean, P0029 page 20.
The leaf is not proved here and its statement is not changed. This file proves that the
statement of the leaf, taken as a hypothesis, forces the dyadic exceptional count `Edy X`
to be at most a constant times `log X + 2` for every `X ≥ 2`, with no Siegel zero needed.
The reason: `SiegelZero R r χ β` has no lower bound on `β` beyond `1 - 1 / log R`, so for
`R = X ^ ϑ` just above one the trivial zero `β = -2` of the Riemann zeta function, with the
character of modulus one, is a Siegel zero of level `R` in the sense of the definition.
Such a bound is far beyond every known exceptional set estimate, so the leaf as stated is
out of reach. Standard mathematics only: the trivial zeros of zeta and `Λ(n) ≤ log n`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- The trivial zero `-2` of zeta, with the character of modulus one, satisfies the lab
definition `SiegelZero` at every level `R` with `0 < log R < 1 / 3`. -/
theorem siegelZero_trivial_zero150 {R : ℝ} (hR1 : 1 ≤ R) (hlog0 : 0 < Real.log R)
    (hlog : Real.log R < 1 / 3) :
    SiegelZero R 1 (1 : DirichletCharacter ℂ 1) (-2) := by
  refine ⟨DirichletCharacter.isPrimitive_one_level_one, ?_, by simpa using hR1, ?_,
    by norm_num, ?_⟩
  · intro a
    have ha : a = 1 := Subsingleton.elim a 1
    rw [ha, map_one]
    simp
  · have h3 : 3 < 1 / Real.log R := by
      rw [lt_div_iff₀ hlog0]
      linarith
    linarith
  · rw [DirichletCharacter.LFunction_modOne_eq]
    have h := riemannZeta_neg_two_mul_nat_add_one 0
    have he : ((-2 : ℝ) : ℂ) = -2 * (((0 : ℕ) : ℂ) + 1) := by push_cast; ring
    rw [he]
    exact h

/-- A pointwise bound `M` on `[1, N]` bounds `intervalMax N R f` by `M` when `R ≤ N`. -/
theorem intervalMax_le_of_norm_le150 (N : ℕ) (R M : ℝ) (f : ℕ → ℂ) (hM : 0 ≤ M)
    (hNR : 1 ≤ (N : ℝ) / R) (hf : ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖f n‖ ≤ M) :
    intervalMax N R f ≤ M := by
  unfold intervalMax
  refine Real.iSup_le (fun x => Real.iSup_le (fun y => Real.iSup_le (fun hxy => ?_) hM) hM) hM
  obtain ⟨hx1, hxy', hyN⟩ := hxy
  have hden : 0 < (y - x) + (N : ℝ) / R := by linarith
  rw [div_le_iff₀ hden]
  have hy0 : 0 ≤ y := by linarith
  have hcard : ((Finset.Icc ⌈x⌉₊ ⌊y⌋₊).card : ℝ) ≤ y - x + 1 := by
    rw [Nat.card_Icc]
    have hxa : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hby : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    by_cases h : ⌈x⌉₊ ≤ ⌊y⌋₊ + 1
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · have h0 : ⌊y⌋₊ + 1 - ⌈x⌉₊ = 0 := by omega
      rw [h0]
      simp
      linarith
  calc ‖∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, f n‖
      ≤ ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, M := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        rw [Finset.mem_Icc] at hn
        have hc : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.mpr (by linarith)
        have hfl : ⌊y⌋₊ ≤ N := by
          have := Nat.floor_le_floor hyN
          rwa [Nat.floor_natCast] at this
        exact hf n (le_trans hc hn.1) (le_trans hn.2 hfl)
    _ = ((Finset.Icc ⌈x⌉₊ ⌊y⌋₊).card : ℝ) * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (y - x + 1) * M := mul_le_mul_of_nonneg_right hcard hM
    _ ≤ M * ((y - x) + (N : ℝ) / R) := by nlinarith

/-- The twisted von Mangoldt term with two corrections of norm at most one is at most
`log N + 2` in norm on `[1, N]`, by `Λ(n) ≤ log n`. -/
theorem norm_twisted_term_le150 (N : ℕ) {r : ℕ} (χ : DirichletCharacter ℂ r) (a b : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ N) :
    ‖(vonMangoldt n : ℂ) * χ n - a + b‖ ≤ Real.log N + 2 := by
  have hΛ : ‖(vonMangoldt n : ℂ)‖ ≤ Real.log N := by
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    refine le_trans vonMangoldt_le_log ?_
    exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast hn)
  have hχ : ‖χ (n : ZMod r)‖ ≤ 1 := χ.norm_le_one _
  have hprod : ‖(vonMangoldt n : ℂ) * χ n‖ ≤ Real.log N := by
    rw [norm_mul]
    calc ‖(vonMangoldt n : ℂ)‖ * ‖χ (n : ZMod r)‖ ≤ ‖(vonMangoldt n : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hχ (norm_nonneg _)
      _ ≤ Real.log N := by linarith
  calc ‖(vonMangoldt n : ℂ) * χ n - a + b‖
      ≤ ‖(vonMangoldt n : ℂ) * χ n - a‖ + ‖b‖ := norm_add_le _ _
    _ ≤ ‖(vonMangoldt n : ℂ) * χ n‖ + ‖a‖ + ‖b‖ := by
        linarith [norm_sub_le ((vonMangoldt n : ℂ) * χ n) a]
    _ ≤ Real.log N + 2 := by linarith

/-- When `⌊R⌋₊ = 1` the primitive character sum has only the modulus one terms. -/
theorem primSum_le_of_floor_one150 (R M : ℝ)
    (F : ∀ r : ℕ, [NeZero r] → DirichletCharacter ℂ r → ℝ) (hfl : ⌊R⌋₊ = 1) (hM : 0 ≤ M)
    (hF : ∀ χ : DirichletCharacter ℂ (0 + 1), F (0 + 1) χ ≤ M) :
    primSum R F ≤ (Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ) * M := by
  unfold primSum
  rw [hfl, Finset.sum_range_one]
  calc ∑ χ : DirichletCharacter ℂ (0 + 1), (if χ.IsPrimitive then F (0 + 1) χ else 0)
      ≤ ∑ _χ : DirichletCharacter ℂ (0 + 1), M := by
        refine Finset.sum_le_sum (fun χ _ => ?_)
        split_ifs
        · exact hF χ
        · exact hM
    _ = (Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ) * M := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- OBSTRUCTION. The statement of the leaf `siegel_count150`, taken as a hypothesis, gives
`Edy X ≤ C' (log X + 2)` for every `X ≥ 2`, unconditionally. The exceptional set would then
be of polylogarithmic size, which is far beyond what is known; with the prime number theorem
in place of `Λ(n) ≤ log n` the same route gives `Edy X = 0` for large `X`. -/
theorem siegel_count150_statement_forces_log_bound
    (hleaf : ∃ C : ℝ, 0 < C ∧
      ∀ (X ϑ : ℝ), 2 ≤ X → 0 < ϑ → ϑ < 1 / 5 →
        ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
          SiegelZero (X ^ ϑ) r₀ χ₀ β →
          (Edy X : ℝ) ≤ C * primSum (X ^ ϑ) (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀))
                    ((n : ℂ) ^ ((β : ℂ) - 1)) 0))) :
    ∃ C' : ℝ, ∀ X : ℝ, 2 ≤ X → (Edy X : ℝ) ≤ C' * (Real.log X + 2) := by
  obtain ⟨C, hC, h⟩ := hleaf
  refine ⟨C * (Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ), ?_⟩
  intro X hX
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set ϑ : ℝ := 1 / (10 * (1 + Real.log X)) with hϑdef
  have hden : 0 < 10 * (1 + Real.log X) := by linarith
  have hϑ : 0 < ϑ := one_div_pos.mpr hden
  have hϑ5 : ϑ < 1 / 5 := by
    rw [hϑdef, div_lt_div_iff₀ hden (by norm_num)]
    linarith
  have hlogR : Real.log (X ^ ϑ) = ϑ * Real.log X := Real.log_rpow hXpos ϑ
  have hlogR0 : 0 < Real.log (X ^ ϑ) := by
    rw [hlogR]
    exact mul_pos hϑ hlogX
  have hlogR10 : Real.log (X ^ ϑ) < 1 / 10 := by
    rw [hlogR, hϑdef, one_div_mul_eq_div, div_lt_div_iff₀ hden (by norm_num)]
    linarith
  have hR1 : 1 ≤ X ^ ϑ := Real.one_le_rpow (by linarith) (le_of_lt hϑ)
  have hRpos : 0 < X ^ ϑ := by linarith
  have hR2 : X ^ ϑ < 2 := by
    have hl2 : Real.log (X ^ ϑ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact (Real.log_lt_log_iff hRpos (by norm_num)).mp hl2
  have hfl : ⌊X ^ ϑ⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (le_of_lt hRpos)]
    constructor
    · simpa using hR1
    · norm_num
      linarith
  have hS : SiegelZero (X ^ ϑ) 1 (1 : DirichletCharacter ℂ 1) (-2) :=
    siegelZero_trivial_zero150 hR1 hlogR0 (by linarith)
  have hmain := h X ϑ hX hϑ hϑ5 1 (1 : DirichletCharacter ℂ 1) (-2) hS
  have hN2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    have h2 : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
    exact_mod_cast h2
  have hNX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (le_of_lt hXpos)
  have hlogN : Real.log ⌊X⌋₊ ≤ Real.log X := Real.log_le_log (by linarith) hNX
  have hlogN0 : 0 ≤ Real.log ⌊X⌋₊ := Real.log_nonneg (by linarith)
  have hNR : 1 ≤ (⌊X⌋₊ : ℝ) / X ^ ϑ := by
    rw [le_div_iff₀ hRpos]
    linarith
  have hM : 0 ≤ Real.log ⌊X⌋₊ + 2 := by linarith
  have hps := primSum_le_of_floor_one150 (X ^ ϑ) (Real.log ⌊X⌋₊ + 2)
    (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
      (fun n => (vonMangoldt n : ℂ) * χ n -
          @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
        @ite ℂ (r = 1 ∧ HEq χ (1 : DirichletCharacter ℂ 1))
          (Classical.propDecidable (r = 1 ∧ HEq χ (1 : DirichletCharacter ℂ 1)))
          ((n : ℂ) ^ ((((-2 : ℝ)) : ℂ) - 1)) 0)) hfl hM (by
      intro χ
      refine intervalMax_le_of_norm_le150 _ _ _ _ hM hNR (fun n h1 hn => ?_)
      refine norm_twisted_term_le150 ⌊X⌋₊ χ _ _ ?_ ?_ n h1 hn
      · split_ifs <;> simp
      · split_ifs
        · rw [Complex.norm_natCast_cpow_of_pos (by omega)]
          refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h1) ?_
          simp
          norm_num
        · simp)
  calc (Edy X : ℝ) ≤ C * _ := hmain
    _ ≤ C * ((Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ) * (Real.log ⌊X⌋₊ + 2)) :=
        mul_le_mul_of_nonneg_left hps (le_of_lt hC)
    _ ≤ C * ((Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ) * (Real.log X + 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
        exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = C * (Fintype.card (DirichletCharacter ℂ (0 + 1)) : ℝ) * (Real.log X + 2) := by ring

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.siegelZero_trivial_zero150
#print axioms LeanLab.BhowmikGrimmelt2026.intervalMax_le_of_norm_le150
#print axioms LeanLab.BhowmikGrimmelt2026.siegel_count150_statement_forces_log_bound

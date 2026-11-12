import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b
import LeanLab.PNTPort.DirichletZF.RealZero

/-!
The nonreal zero step behind P0045 page 5 and Corollary 4.2 on page 6.
Reuse the proved classical region from DirichletZF and the proved zeta region.
The primitive principal character has modulus one.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Real Complex
open LeanLab.PNTPort.DirichletZF

noncomputable section

/-- P0045 page 5, display 8, change of logarithmic scale in the classical region.
The auxiliary factor in Bt is absorbed in one absolute positive constant. -/
theorem log_Bt_comparison484 :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 1 ≤ r → ∀ t : ℝ,
      Real.log (Bt r t) ≤ K * Real.log ((r : ℝ) * (|t| + 2)) := by
  have hZ : 0 < Z := Z_pos
  let B : ℝ := 3 * Z
  have hB : 1 ≤ B := by dsimp [B]; linarith [one_le_Z]
  have hB0 : 0 < B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log B / Real.log 2, by positivity, ?_⟩
  intro r hr t
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  let A : ℝ := (r : ℝ) * (|t| + 2)
  have hA2 : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg hr0.le (abs_nonneg t)]
  have hA0 : 0 < A := by linarith
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hA2
  have hBt : Bt r t ≤ B * A := by
    dsimp [Bt, B, A]
    nlinarith [show 0 ≤ (r : ℝ) * |t| * Z by positivity]
  have hBt0 : 0 < Bt r t := by dsimp [Bt]; positivity
  have hscale : Real.log B ≤ Real.log B / Real.log 2 * Real.log A := by
    have hm := mul_le_mul_of_nonneg_left hlogA (div_nonneg hlB hl2.le)
    simpa [div_mul_cancel₀ _ hl2.ne'] using hm
  calc Real.log (Bt r t) ≤ Real.log (B * A) := Real.log_le_log hBt0 hBt
    _ = Real.log B + Real.log A := Real.log_mul hB0.ne' hA0.ne'
    _ ≤ (1 + Real.log B / Real.log 2) * Real.log A := by nlinarith

/-- P0045 page 5 before Lemma 4.1, nonreal zeros of nonprincipal characters.
The only exceptional zero in the proved classical region is real. -/
theorem nonprincipal_nonreal_gap484 :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ ≠ 1 → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨c, c', hc, _, hreg⟩ := zero_free_region_real
  obtain ⟨K, hK, hcomp⟩ := log_Bt_comparison484
  refine ⟨c / K, div_pos hc hK, ?_⟩
  intro r hr χ hχ ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hzero : DirichletCharacter.LFunction χ ρ = 0 := by simpa [Lfun481, hr0] using hρ
  have hgap : c / Real.log (Bt r ρ.im) ≤ 1 - ρ.re := by
    rcases (hreg r χ hχ).1 ρ hzero with h | h
    · linarith
    · exact (him h.2.2.2).elim
  have hlogBt : 0 < Real.log (Bt r ρ.im) := by linarith [one_le_log_Bt (N := r) ρ.im]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 < (r : ℝ) * (|ρ.im| + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)]
  have hlogA : 0 < Real.log ((r : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA
  apply le_trans _ hgap
  rw [div_div, div_le_div_iff₀ (mul_pos hK hlogA) hlogBt]
  exact mul_le_mul_of_nonneg_left (hcomp r hr ρ.im) hc.le

/-- P0045 page 5, the primitive principal case of the nonreal zero region.
The compact low height strip and the classical zeta region cover all heights. -/
theorem zeta_gap484 :
    ∃ b : ℝ, 0 < b ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      b / Real.log (|ρ.im| + 2) ≤ 1 - ρ.re := by
  obtain ⟨σ, hσ, hbox⟩ := ZetaNoZerosInBox 3
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  have hσgap : 0 < 1 - σ := sub_pos.mpr hσ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min ((1 - σ) * Real.log 2) A, lt_min (by positivity) hA.1, ?_⟩
  intro ρ hρ
  have hre : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρ
  have hrepr : (ρ.re : ℂ) + (ρ.im : ℂ) * I = ρ := by
    simpa [mul_comm] using ρ.re_add_im
  have hlog : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
  by_cases ht : |ρ.im| ≤ 3
  · have hs : ρ.re < σ := by
      by_contra h
      exact hbox ρ.im ht ρ.re (le_of_not_gt h) (by rwa [hrepr])
    have hlogs : Real.log 2 ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
    rw [div_le_iff₀ hlog]
    calc min ((1 - σ) * Real.log 2) A ≤ (1 - σ) * Real.log 2 := min_le_left _ _
      _ ≤ (1 - σ) * Real.log (|ρ.im| + 2) := mul_le_mul_of_nonneg_left hlogs (by linarith)
      _ ≤ (1 - ρ.re) * Real.log (|ρ.im| + 2) := by nlinarith
  · have ht3 : 3 < |ρ.im| := lt_of_not_ge ht
    have hzero : riemannZeta ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = 0 := by rwa [hrepr]
    have hleft : ρ.re < 1 - A / Real.log |ρ.im| := by
      by_contra hn
      have he := hlarge ρ.re ρ.im ht3 ⟨by simpa using le_of_not_gt hn, hre⟩
      exact he hzero
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hlogs : Real.log |ρ.im| ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    calc min ((1 - σ) * Real.log 2) A / Real.log (|ρ.im| + 2)
        ≤ A / Real.log (|ρ.im| + 2) := div_le_div_of_nonneg_right (min_le_right _ _) hlog.le
      _ ≤ A / Real.log |ρ.im| := div_le_div_of_nonneg_left hA.1.le hlogt hlogs
      _ ≤ 1 - ρ.re := by linarith

/-- P0045 pages 5 and 6, the classical gap for primitive characters at nonreal zeros.
Primitivity reduces the principal case to zeta at modulus one. -/
theorem primitive_nonreal_gap484 :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨b₁, hb₁, hnon⟩ := nonprincipal_nonreal_gap484
  obtain ⟨b₂, hb₂, hzeta⟩ := zeta_gap484
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
  intro r hr χ hprim ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log ((r : ℝ) * (|ρ.im| + 2)) :=
    Real.log_nonneg (by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)])
  by_cases hχ : χ = 1
  · have hrone : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hζ : riemannZeta ρ = 0 := by
      simpa [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq] using hρ
    have he := hzeta ρ hζ
    simp only [Nat.cast_one, one_mul] at hlog ⊢
    exact (div_le_div_of_nonneg_right (min_le_right _ _) hlog).trans he
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hlog).trans (hnon r hr χ hχ ρ hρ him)

end
end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.log_Bt_comparison484
#print axioms LeanLab.LPZ2007.nonprincipal_nonreal_gap484
#print axioms LeanLab.LPZ2007.zeta_gap484
#print axioms LeanLab.LPZ2007.primitive_nonreal_gap484

import LeanLab.PNTPort.DirichletZF.Siegel

/-!
# The zero-free region with Siegel's bound for the exceptional zero

Lab proof, unit U-5173. AI wrote this file. Known mathematics, no cited input, the form used in
the proof of Siegel-Walfisz, Davenport chapter 22.

`zero_free_siegel`: for every `ε > 0` there is `c > 0` such that for every `N ≥ 1`, every
non-principal Dirichlet character `χ` mod `N` and every zero `β + iγ` of `L(s, χ)`,

  `β ≤ 1 - min(c / log B(γ), c N^{-ε})`,  `B(γ) = 2NZ(|γ| + 3)`.

The exceptional zero, real and of a real character by `zero_free_region_real`, is bounded by
`siegel_zero` after lifting `χ` to modulus `8N`. Ineffective through Siegel's theorem.
-/

namespace LeanLab.PNTPort.DirichletZF

open Complex

theorem zero_free_siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - min (c / Real.log (Bt N ρ.im)) (c * (N : ℝ) ^ (-ε)) := by
  intro ε hε
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  obtain ⟨cs, hcs, hsz⟩ := siegel_zero ε hε
  have h8 : (0 : ℝ) < (8 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) _
  set C := min c (cs * (8 : ℝ) ^ (-ε)) with hC
  have hCpos : 0 < C := lt_min hc (by positivity)
  refine ⟨C, hCpos, fun N _ χ hχ ρ hρ ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hLp : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
  rcases (hreg N χ hχ).1 ρ hρ with h | ⟨-, -, hsq, him⟩
  · have : C / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N ρ.im) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLp.le
    have := min_le_left (C / Real.log (Bt N ρ.im)) (C * (N : ℝ) ^ (-ε))
    linarith
  · -- the exceptional zero: real, of a real character
    have hρr : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hβ1 : ρ.re ≤ 1 := by
      by_contra hcc; push Not at hcc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcc.le hρ
    set M := 8 * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
    have hd : N ∣ M := Dvd.intro_left 8 rfl
    have hz : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ) ρ.re = 0 := by
      rw [L_lift hd hχ, ← hρr, hρ, zero_mul]
    have hM8 : 8 ≤ M := by have := Nat.pos_of_ne_zero (NeZero.ne N); omega
    have hb := hsz M hM8 _ (lift_ne_one hd hχ) (lift_sq hd hsq) ρ.re hβ1 hz
    have hMr : ((M : ℕ) : ℝ) = 8 * N := by simp [M]
    rw [hMr, Real.mul_rpow (by norm_num) hN0.le] at hb
    have h1 : C * (N : ℝ) ^ (-ε) ≤ cs * ((8 : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hN0.le _)
    have := min_le_right (C / Real.log (Bt N ρ.im)) (C * (N : ℝ) ^ (-ε))
    linarith

/-- The exceptional zero is simple: a zero `ρ` of a non-principal `L(s, χ)` in the box
`β ≥ 1 - c₀/log B(0)`, `|γ| ≤ c₀/log B(0)` of `page_count` has order exactly one. -/
theorem exceptional_simple : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      1 - c₀ / Real.log (Bt N 0) ≤ ρ.re → |ρ.im| ≤ c₀ / Real.log (Bt N 0) →
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 := by
  obtain ⟨c, hc, hc31, h⟩ := page_count
  refine ⟨c, hc, fun N _ χ hχ ρ hρ hb hg ↦ ?_⟩
  have hL1 : 1 ≤ Real.log (Bt N 0) := one_le_log_Bt 0
  have hη : c / Real.log (Bt N 0) ≤ 1 / 31 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmem := mem_Tset_of_box hχ hη hρ hb hg
  have hf : fShift χ 0 (ρ - 3 / 2) = 0 := (mem_Tset.mp hmem).2
  have hord1 := one_le_order hχ 0 hf
  have hle : analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) ≤ 1 := by
    have hin : ρ - 3 / 2 ∈ (Tset hχ 0).filter (fun ρ ↦ 1 - c / Real.log (Bt N 0) ≤ ρ.re + 3 / 2 ∧
        |ρ.im| ≤ c / Real.log (Bt N 0)) := by
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_, ?_⟩
      · simp; linarith
      · simpa using hg
    have := Finset.single_le_sum (f := fun ρ ↦ analyticOrderNatAt (fShift χ 0) ρ)
      (fun _ _ ↦ Nat.zero_le _) hin
    exact this.trans (h N χ hχ)
  have htr : analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
    have e : fShift χ 0 = fun z ↦ DirichletCharacter.LFunction χ (z + 3 / 2) := by
      funext z; simp [fShift]
    rw [e, analyticOrderNatAt_fun_comp_add_right, sub_add_cancel]
  omega

end LeanLab.PNTPort.DirichletZF

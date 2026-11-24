/-
Case split for `short_interval_mean_decay_exceptional` of LeanLab/Linnik/Decomp486c.lean.
This file adds new declarations only: the parent keeps its sorry, and the existing range
split in SPLIT_short_interval_mean_decay_exceptional.lean is left untouched.

Source: Gallagher 1975 Invent. Math. 29 p.131 display 14 and the paragraph after it, with
"the method of [10, Section 7]", Gallagher 1970 Invent. Math. 11 p.336 to 337 display 27.

The parent is stated for every real zero gamma of the exceptional character in the fixed
strip. Two cases.
1. gamma is the largest real zero in the strip: the proved
   `ExplicitFormula.mean_decay_exceptional_max`.
2. a larger real zero exists: by the Deuring-Heilbronn leaf every zero of the exceptional
   character is left of 1 - delta / log T, by Page subsingleton every other primitive
   character up to T has no zero in the strip, so the proved
   `ExplicitFormula.mean_decay_nonexceptional` applies at width min delta exceptionalStrip;
   the exceptional character's summand differs only by the main polynomial of gamma,
   handled by Minkowski and the main window leaf.
No new leaf: the result is CONDITIONAL ON `leaf_deuring_heilbronn_other_zero` and
`leaf_exceptional_main_window` of SPLIT_leaf_nonmaximal_exceptional_summand_decay.lean.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.SPLIT_leaf_nonmaximal_exceptional_summand_decay

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- The parent statement `short_interval_mean_decay_exceptional` of
LeanLab/Linnik/Decomp486c.lean, same statement text, by the case split on whether gamma is
the largest real zero in the strip. CONDITIONAL ON `leaf_deuring_heilbronn_other_zero` and
`leaf_exceptional_main_window`. The parent theorem is neither used nor restated. -/
theorem short_interval_mean_decay_exceptional_case_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨cm, Cm, θm, hcm, hCm, hθm, hθm2, hmax⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_exceptional_max
  obtain ⟨δ, T₀, hδ, hDH⟩ := leaf_deuring_heilbronn_other_zero
  have hb0 : 0 < min δ exceptionalStrip := lt_min hδ exceptionalStrip_pos
  obtain ⟨cn, Cn, θn, hcn, hCn, hθn, hθn2, hnon⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_nonexceptional (min δ exceptionalStrip) hb0
  obtain ⟨ce, Ce, θe, hce, hCe, hθe, hθe2, hE⟩ := leaf_exceptional_main_window δ hδ
  refine ⟨min cm (min cn ce), Cm + (Cn + Ce), min θm (min θn θe),
    lt_min hcm (lt_min hcn hce), by linarith, lt_min hθm (lt_min hθn hθe),
    (min_le_left _ _).trans hθm2, fun θ hθ hθle => ?_⟩
  have hθm' : θ ≤ θm := hθle.trans (min_le_left _ _)
  have hθn' : θ ≤ θn := hθle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθe' : θ ≤ θe := hθle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N₁, hN₁⟩ := hmax θ hθ hθm'
  obtain ⟨N₂, hN₂⟩ := hnon θ hθ hθn'
  obtain ⟨N₃, hN₃⟩ := hE θ hθ hθe'
  have hev : ∀ᶠ N : ℕ in atTop, max T₀ 2 ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₁ N₂) (max N₃ (max N₄ 2)), ?_⟩
  rintro N hN ⟨q, χ⟩ hx hxP γ hz hlo hlt
  dsimp only at hxP hz ⊢
  have hN1' : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3' : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN4' : N₄ ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN2 : 2 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  set P := (N : ℝ) ^ θ with hPdef
  have hPm : max T₀ 2 ≤ P := hN₄ N hN4'
  have hP2 : 2 ≤ P := (le_max_right T₀ 2).trans hPm
  have hP1 : 1 ≤ P := by linarith
  have hPT : P ≤ P ^ 5 := le_self_pow₀ hP1 (by norm_num)
  have hT₀ : T₀ ≤ P ^ 5 := (le_max_left T₀ 2).trans (hPm.trans hPT)
  have hT2 : 2 ≤ P ^ 5 := hP2.trans hPT
  have hlogT : 0 < Real.log (P ^ 5) := Real.log_pos (by linarith)
  have hqT : (q : ℝ) + 1 ≤ P ^ 5 := by
    have h : ((q + 1 : ℕ) : ℝ) ≤ P := hxP
    push_cast at h
    linarith
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  have hexp : ∀ c' : ℝ, min cm (min cn ce) ≤ c' →
      Real.exp (-c' / θ) ≤ Real.exp (-(min cm (min cn ce)) / θ) := fun c' h =>
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hcm' : min cm (min cn ce) ≤ cm := min_le_left _ _
  have hcn' : min cm (min cn ce) ≤ cn := (min_le_right _ _).trans (min_le_left _ _)
  have hce' : min cm (min cn ce) ≤ ce := (min_le_right _ _).trans (min_le_right _ _)
  have hE0 : 0 ≤ Real.exp (-(min cm (min cn ce)) / θ) := (Real.exp_pos _).le
  by_cases hm : ∀ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 →
      1 - exceptionalStrip / Real.log (P ^ 5) ≤ γ' → γ' < 1 → γ' ≤ γ
  · -- case 1: gamma is the largest real zero in the strip
    have h := hN₁ N hN1' ⟨q, χ⟩ hx hxP γ hz hlo hlt hm
    refine le_trans h ?_
    have h1 : Cm * Real.exp (-cm / θ) ≤ (Cm + (Cn + Ce)) * Real.exp (-(min cm (min cn ce)) / θ) :=
      mul_le_mul (by linarith) (hexp cm hcm') (Real.exp_pos _).le (by linarith)
    exact mul_le_mul_of_nonneg_right h1 hs
  · -- case 2: a larger real zero exists
    push_neg at hm
    obtain ⟨γ', hz', hlo', hlt', hγγ'⟩ := hm
    have hne : ((γ' : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
      intro h
      have := Complex.ofReal_inj.mp h
      linarith
    have hγ'gap : γ' < 1 - δ / Real.log (P ^ 5) := by
      have h := hDH (P ^ 5) hT₀ q χ hx.2.1 hqT (γ' : ℂ) (γ : ℂ) hz' hz hne
        (by simp only [Complex.ofReal_im, abs_zero]; positivity)
        (by simp only [Complex.ofReal_im, abs_zero]; positivity)
        (by simpa only [Complex.ofReal_re] using hlo)
      simpa only [Complex.ofReal_re] using h
    have hγgap : γ < 1 - δ / Real.log (P ^ 5) := hγγ'.trans hγ'gap
    have hgapχ : ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ P ^ 5 →
        ρ.re < 1 - δ / Real.log (P ^ 5) := by
      intro ρ hρ him
      by_cases hργ : ρ = (γ : ℂ)
      · subst hργ
        simpa only [Complex.ofReal_re] using hγgap
      · exact hDH (P ^ 5) hT₀ q χ hx.2.1 hqT ρ (γ : ℂ) hρ hz hργ him
          (by simp only [Complex.ofReal_im, abs_zero]; positivity)
          (by simpa only [Complex.ofReal_re] using hlo)
    have hδb : 1 - δ / Real.log (P ^ 5) ≤ 1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
      have := div_le_div_of_nonneg_right (min_le_left δ exceptionalStrip) hlogT.le
      linarith
    have hesb : 1 - exceptionalStrip / Real.log (P ^ 5) ≤
        1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
      have := div_le_div_of_nonneg_right (min_le_right δ exceptionalStrip) hlogT.le
      linarith
    have hsub := Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton
    have hbs : exceptionalStrip ≤ Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hgap : ∀ k < ⌊P⌋₊, ∀ ψ : DirichletCharacter ℂ (k + 1), ψ.IsPrimitive →
        ∀ ρ : ℂ, ψ.LFunction ρ = 0 → |ρ.im| ≤ P ^ 5 →
          ρ.re < 1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
      intro k hk ψ hψ ρ hρ him
      by_cases hkx : (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩
      · obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hkx
        obtain rfl := eq_of_heq hh
        exact (hgapχ ρ hρ him).trans_le hδb
      · by_contra hge
        push_neg at hge
        have hkP : ((k + 1 : ℕ) : ℝ) ≤ P :=
          (Nat.le_floor_iff (by linarith)).mp (Nat.succ_le_of_lt hk)
        have hmem : (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
            excSet exceptionalStrip (P ^ 5) := by
          refine ⟨?_, hψ, ρ, hρ, hesb.trans hge, him⟩
          push_cast at hkP
          show (k : ℝ) + 1 ≤ P ^ 5
          linarith
        exact hkx (hsub.2 (P ^ 5) hT2 (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hmem)
          (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hx))
    have hn := hN₂ N hN2' hgap
    have he := hN₃ N hN3' γ hγgap
    set L := gallagherLength N θ with hL
    set H := Real.pi / (2 * (L : ℝ)) *
      Real.sqrt (∑ m ∈ range (N + 1 + L),
        ‖LeanLab.PNTPort.Gallagher.win
          (fun m : ℕ => if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0)
          (N + 1) L m‖ ^ 2) with hHdef
    have hH0 : 0 ≤ H := by positivity
    have hpi : 0 ≤ Real.pi / (2 * (L : ℝ)) := by positivity
    have hpt : ∀ k ∈ range ⌊P⌋₊,
        ∀ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
          Real.pi / (2 * (L : ℝ)) *
              Real.sqrt (∑ m ∈ range (N + 1 + L),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ (q + 1) γ) (N + 1) L m‖ ^ 2)
            ≤ Real.pi / (2 * (L : ℝ)) *
              Real.sqrt (∑ m ∈ range (N + 1 + L),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1) L m‖ ^ 2) +
              (if (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩ then H else 0) := by
      intro k hk ψ hψ
      by_cases hkx : (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩
      · rw [ite_cond_eq_true _ _ (eq_true hkx)]
        obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hkx
        obtain rfl := eq_of_heq hh
        rw [nmx_correctedCoefficient_split ψ γ hz]
        simp_rw [nmx_win_add]
        refine (mul_le_mul_of_nonneg_left (nmx_sqrt_sum_norm_add_sq_le _ _ _) hpi).trans ?_
        rw [mul_add]
      · rw [ite_cond_eq_false _ _ (eq_false hkx), add_zero]
        rw [show correctedCoefficient ψ (q + 1) γ = correctedCoefficient ψ 0 0 from
          correctedCoefficient_eq_unexceptional hT2 ⟨q, χ⟩ hx k ψ (mem_filter.mp hψ).2 hkx γ hlo]
    have hJ : ∑ k ∈ range ⌊P⌋₊,
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
          (if (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩ then H else 0) ≤ H := by
      rw [Finset.sum_sigma' (range ⌊P⌋₊)
        (fun k => (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive))
        (fun k ψ => if (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩ then H else 0)]
      simp only [Sigma.eta]
      rw [Finset.sum_ite_eq']
      split_ifs <;> linarith
    calc _ ≤ ∑ k ∈ range ⌊P⌋₊,
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
            (Real.pi / (2 * (L : ℝ)) *
              Real.sqrt (∑ m ∈ range (N + 1 + L),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1) L m‖ ^ 2) +
              (if (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩ then H else 0)) :=
          sum_le_sum fun k hk => sum_le_sum fun ψ hψ => hpt k hk ψ hψ
      _ = ∑ k ∈ range ⌊P⌋₊,
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
            Real.pi / (2 * (L : ℝ)) *
              Real.sqrt (∑ m ∈ range (N + 1 + L),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1) L m‖ ^ 2) +
          ∑ k ∈ range ⌊P⌋₊,
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
            (if (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩ then H else 0) := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun k _ => sum_add_distrib
      _ ≤ Cn * Real.exp (-cn / θ) * (Real.sqrt N / Real.log N) +
          Ce * Real.exp (-ce / θ) * (Real.sqrt N / Real.log N) :=
          add_le_add hn (hJ.trans he)
      _ ≤ (Cm + (Cn + Ce)) * Real.exp (-(min cm (min cn ce)) / θ) *
          (Real.sqrt N / Real.log N) := by
          have h1 := mul_le_mul_of_nonneg_left (hexp cn hcn') hCn.le
          have h2 := mul_le_mul_of_nonneg_left (hexp ce hce') hCe.le
          have h3 : 0 ≤ Cm * Real.exp (-(min cm (min cn ce)) / θ) := by positivity
          have h4 : Cn * Real.exp (-cn / θ) + Ce * Real.exp (-ce / θ) ≤
              (Cm + (Cn + Ce)) * Real.exp (-(min cm (min cn ce)) / θ) := by nlinarith
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right h4 hs

end LeanLab.Linnik.Decomp486c

#print axioms LeanLab.Linnik.Decomp486c.short_interval_mean_decay_exceptional_case_split

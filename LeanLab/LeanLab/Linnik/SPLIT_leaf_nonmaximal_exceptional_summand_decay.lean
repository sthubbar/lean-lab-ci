/-
Split unit for `leaf_nonmaximal_exceptional_summand_decay` of
LeanLab/Linnik/Decomp498a.lean. This file adds new declarations only: no existing
statement is edited, and the parent keeps its sorry.

Source: Gallagher 1975 Invent. Math. 29 p.131 display 14 and the paragraph after it,
"it follows by the method of [10, Section 7]", where [10] is Gallagher 1970 Invent. Math. 11
329-339, and there p.336 to 337 display 27, the Deuring-Heilbronn widening of the zero free
region 26 in the presence of an exceptional zero.

Route. In the nonmaximal case the character has two real zeros gamma < gamma' in the lab's
fixed strip of width exceptionalStrip. Display 27 of Gallagher 1970 forces every zero of
that character other than a zero in the strip to lie left of 1 - delta / log T, for a fixed
delta depending on the strip width. Then
1. the corrected coefficient splits as the uncorrected coefficient plus the exceptional main
   coefficient of gamma, because gamma is a zero;
2. the uncorrected single summand is bounded as in the nonexceptional case of display 14;
3. the exceptional main coefficient of gamma, with gamma left of 1 - delta / log T, has a
   window norm with the same exponential saving;
4. Minkowski's inequality on the window norm adds the two bounds.
Steps 1 and 4 and the case analysis are proved here; the three LEAF theorems carry the rest.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp498a

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- LEAF: Deuring-Heilbronn repulsion, Gallagher 1970 Invent. Math. 11 p.336 to 337 display 27.
Class: HARD.
Display 27 widens the zero free region 26 and is cited by Gallagher 1975 p.131 after display 14 as
"the method of [10, Section 7]" and "an even stronger bound". If a primitive L function of
conductor at most T has a zero in the rectangle of width exceptionalStrip over log T and
height T, then every other zero in that height range lies left of 1 - delta over log T, for
a fixed positive delta depending only on the strip width. In the source: a zero right of
1 - delta / log T with delta small is the exceptional zero 1 - delta of display 26, and
display 27 then pushes every other zero left of 1 - c2 log of e c1 over delta log T, which is
left of the strip once delta is small. -/
theorem leaf_deuring_heilbronn_other_zero :
    ∃ δ T₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)), χ.IsPrimitive → (q : ℝ) + 1 ≤ T →
        ∀ ρ₁ ρ₂ : ℂ, χ.LFunction ρ₁ = 0 → χ.LFunction ρ₂ = 0 → ρ₁ ≠ ρ₂ →
          |ρ₁.im| ≤ T → |ρ₂.im| ≤ T → 1 - exceptionalStrip / Real.log T ≤ ρ₂.re →
          ρ₁.re < 1 - δ / Real.log T := by
  sorry

/-- LEAF: single summand of the nonexceptional case, Gallagher 1975 p.131 display 14.
Class: MEDIUM.
Gallagher 1975 Invent. Math. 29 p.131 display 14. For a primitive character of conductor at most P = N^θ carrying a real zero in the fixed
strip at height T = P^5, and with no zero right of 1 - delta / log T up to height T, the
uncorrected single summand of display 14 is at most C exp of minus c over theta times
sqrt N over log N. Intended proof: by `Decomp1532b.page_subsingleton` at the strip width,
no other primitive character of conductor at most T has a zero in the strip, so the gap
hypothesis of `ExplicitFormula.mean_decay_nonexceptional` holds at width min delta
exceptionalStrip for every conductor at most P; take the single summand of that proved sum. -/
theorem leaf_single_summand_nonexceptional (δ : ℝ) (hδ : 0 < δ) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ →
          (∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 →
            ρ.re < 1 - δ / Real.log (((N : ℝ) ^ θ) ^ 5)) →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ 0 0) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-- LEAF: window bound for the main polynomial T tilde, Gallagher 1975 p.131 after display 14.
Class: MEDIUM.
Gallagher 1975 Invent. Math. 29 p.131, the bound on T tilde of a real zero with the saving of
display 14. If gamma lies left of 1 - delta / log T with
T = P^5 and P = N^θ, the Gallagher window norm of the coefficients m^(gamma - 1) / log m,
1 < m, is at most C exp of minus c over theta times sqrt N over log N. Elementary: windows
inside m at least sqrt N have terms at most exp of minus delta over 10 theta, and the
windows meeting m below sqrt N number at most sqrt N + L and cost N^(-θ/2) log N relatively. -/
theorem leaf_exceptional_main_window (δ : ℝ) (hδ : 0 < δ) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ γ : ℝ, γ < 1 - δ / Real.log (((N : ℝ) ^ θ) ^ 5) →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win
                  (fun m : ℕ => if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0)
                  (N + 1) (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-! ### Proved helpers -/

/-- Minkowski's inequality for a finite sum of squared complex norms. -/
lemma nmx_sqrt_sum_norm_add_sq_le (s : Finset ℕ) (a b : ℕ → ℂ) :
    Real.sqrt (∑ m ∈ s, ‖a m + b m‖ ^ 2) ≤
      Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2) := by
  have hA : 0 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hB : 0 ≤ ∑ m ∈ s, ‖b m‖ ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hcs : (∑ m ∈ s, ‖a m‖ * ‖b m‖) ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * ∑ m ∈ s, ‖b m‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq s _ _
  have hcs' : ∑ m ∈ s, ‖a m‖ * ‖b m‖ ≤
      Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) * Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2) := by
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  have hpt : ∑ m ∈ s, ‖a m + b m‖ ^ 2 ≤
      ∑ m ∈ s, ‖a m‖ ^ 2 + 2 * ∑ m ∈ s, ‖a m‖ * ‖b m‖ + ∑ m ∈ s, ‖b m‖ ^ 2 := by
    calc ∑ m ∈ s, ‖a m + b m‖ ^ 2
        ≤ ∑ m ∈ s, (‖a m‖ ^ 2 + 2 * (‖a m‖ * ‖b m‖) + ‖b m‖ ^ 2) := by
          apply sum_le_sum
          intro m _
          have h := norm_add_le (a m) (b m)
          have h0 := norm_nonneg (a m + b m)
          nlinarith [norm_nonneg (a m), norm_nonneg (b m)]
      _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have hsq : ∑ m ∈ s, ‖a m‖ ^ 2 + 2 * ∑ m ∈ s, ‖a m‖ * ‖b m‖ + ∑ m ∈ s, ‖b m‖ ^ 2 ≤
      (Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2)) ^ 2 := by
    have e1 := Real.sq_sqrt hA
    have e2 := Real.sq_sqrt hB
    nlinarith
  calc Real.sqrt (∑ m ∈ s, ‖a m + b m‖ ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt (hpt.trans hsq)
    _ = _ := Real.sqrt_sq (by positivity)

/-- The Gallagher window is additive in the coefficient sequence. -/
lemma nmx_win_add (f g : ℕ → ℂ) (N L m : ℕ) :
    LeanLab.PNTPort.Gallagher.win (fun n => f n + g n) N L m =
      LeanLab.PNTPort.Gallagher.win f N L m + LeanLab.PNTPort.Gallagher.win g N L m := by
  unfold LeanLab.PNTPort.Gallagher.win
  rw [sum_add_distrib]

/-- Gallagher 1975 p.131: at a zero gamma, the corrected coefficient at conductor q + 1 is
the uncorrected coefficient plus the exceptional main coefficient of gamma. -/
lemma nmx_correctedCoefficient_split {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (γ : ℝ) (hz : χ.LFunction (γ : ℂ) = 0) :
    correctedCoefficient χ (q + 1) γ = fun m => correctedCoefficient χ 0 0 m +
      (if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0) := by
  funext m
  unfold correctedCoefficient
  have h0 : ¬ (q + 1 = 0 ∧ χ.LFunction ((0 : ℝ) : ℂ) = 0) := fun h => Nat.succ_ne_zero q h.1
  rw [_root_.if_pos (show q + 1 = q + 1 ∧ χ.LFunction (γ : ℂ) = 0 from ⟨rfl, hz⟩),
    _root_.if_neg h0, add_zero]

/-- Adding two exponentially decaying bounds at a common rate. -/
lemma nmx_add_two_exponential_bounds {E₁ E₂ c c₁ c₂ C₁ C₂ θ s : ℝ} (hθ : 0 < θ)
    (hs : 0 ≤ s) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂)
    (h₁ : E₁ ≤ C₁ * Real.exp (-c₁ / θ) * s)
    (h₂ : E₂ ≤ C₂ * Real.exp (-c₂ / θ) * s) :
    E₁ + E₂ ≤ (C₁ + C₂) * Real.exp (-c / θ) * s := by
  have hexp₁ : Real.exp (-c₁ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hexp₂ : Real.exp (-c₂ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have h₁' : E₁ ≤ C₁ * Real.exp (-c / θ) * s :=
    h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₁ hC₁) hs)
  have h₂' : E₂ ≤ C₂ * Real.exp (-c / θ) * s :=
    h₂.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₂ hC₂) hs)
  have hsplit : C₁ * Real.exp (-c / θ) * s + C₂ * Real.exp (-c / θ) * s
      = (C₁ + C₂) * Real.exp (-c / θ) * s := by ring
  linarith

/-! ### Assembly -/

/-- The parent statement `leaf_nonmaximal_exceptional_summand_decay` of
LeanLab/Linnik/Decomp498a.lean, same statement text, proved from the three leaves above.
The parent theorem is neither used nor restated as a hypothesis. -/
theorem leaf_nonmaximal_exceptional_summand_decay_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          (∃ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' ∧ γ' < 1 ∧ γ < γ') →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  obtain ⟨δ, T₀, hδ, hDH⟩ := leaf_deuring_heilbronn_other_zero
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hB⟩ := leaf_single_summand_nonexceptional δ hδ
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hE⟩ := leaf_exceptional_main_window δ hδ
  refine ⟨min c₁ c₂, C₁ + C₂, min θ₁ θ₂, lt_min hc₁ hc₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hB θ hθ (hθle.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hE θ hθ (hθle.trans (min_le_right _ _))
  have hev : ∀ᶠ N : ℕ in atTop, max T₀ 2 ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN q χ γ hp hq hz hlo hlt hmore => ?_⟩
  have hN1' : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3' : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set P := (N : ℝ) ^ θ with hPdef
  have hPm : max T₀ 2 ≤ P := hN₃ N hN3'
  have hP1 : 1 ≤ P := by linarith [le_max_right T₀ 2]
  have hPT : P ≤ P ^ 5 := le_self_pow₀ hP1 (by norm_num)
  have hT₀ : T₀ ≤ P ^ 5 := (le_max_left T₀ 2).trans (hPm.trans hPT)
  have hqT : (q : ℝ) + 1 ≤ P ^ 5 := hq.trans hPT
  obtain ⟨γ', hz', hlo', hlt', hγγ'⟩ := hmore
  have hne : ((γ' : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
    intro h
    have := Complex.ofReal_inj.mp h
    linarith
  have hγ'gap : γ' < 1 - δ / Real.log (P ^ 5) := by
    have h := hDH (P ^ 5) hT₀ q χ hp hqT (γ' : ℂ) (γ : ℂ) hz' hz hne
      (by simp only [Complex.ofReal_im, abs_zero]; positivity)
      (by simp only [Complex.ofReal_im, abs_zero]; positivity)
      (by simpa only [Complex.ofReal_re] using hlo)
    simpa only [Complex.ofReal_re] using h
  have hγgap : γ < 1 - δ / Real.log (P ^ 5) := hγγ'.trans hγ'gap
  have hgap : ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ P ^ 5 →
      ρ.re < 1 - δ / Real.log (P ^ 5) := by
    intro ρ hρ him
    by_cases hργ : ρ = (γ : ℂ)
    · subst hργ
      simpa only [Complex.ofReal_re] using hγgap
    · exact hDH (P ^ 5) hT₀ q χ hp hqT ρ (γ : ℂ) hρ hz hργ him
        (by simp only [Complex.ofReal_im, abs_zero]; positivity)
        (by simpa only [Complex.ofReal_re] using hlo)
  have hb₁ := hN₁ N hN1' q χ γ hp hq hz hlo hgap
  have hb₂ := hN₂ N hN2' γ hγgap
  rw [nmx_correctedCoefficient_split χ γ hz]
  simp_rw [nmx_win_add]
  have hpi : 0 ≤ Real.pi / (2 * (gallagherLength N θ : ℝ)) := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  refine (mul_le_mul_of_nonneg_left (nmx_sqrt_sum_norm_add_sq_le _ _ _) hpi).trans ?_
  rw [mul_add]
  exact nmx_add_two_exponential_bounds hθ hs hC₁.le hC₂.le (min_le_left _ _)
    (min_le_right _ _) hb₁ hb₂

end LeanLab.Linnik.Decomp486c

#print axioms LeanLab.Linnik.Decomp486c.leaf_nonmaximal_exceptional_summand_decay_split

/-
P0068 Zhan 1991, the LEAF `innerBound_leaf_ps` of PartialSum1122d.lean, page 264 the display
after "The inner integral above can be estimated by Lemma 1" and page 265 first display, split
into three cited LEAF steps: the Fubini identity, the Lemma 1 bound of the inner `u` integral,
and the finiteness of the weighted `t` integral. The final triangle inequality is PROVED here.
AI-written Lean code, Claude, unit S8-31 of burst-20261124. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PartialSum1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- The inner `u` integral of page 264, `∫_{N-A}^{N} u^{s-1} e(λu) du` with `s = 1/2 + it`. -/
def innerJ_ib (N : ℕ) (A lam t : ℝ) : ℂ :=
  ∫ u in ((N : ℝ) - A)..N, (u : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I - 1) * ee (lam * u)

/-- LEAF: page 264, the display after "The inner integral above can be estimated by Lemma 1":
`∂_u Vline = (1/2π) ∫ F(s) u^{s-1} dt` on `Re s = 1/2`, and Fubini over `t ∈ [-T, T]`,
`u ∈ [N-A, N]`, giving `∫ ∂_u Vline(u) e(λu) du = (1/2π) ∫_{-T}^{T} F(1/2+it) J(t) dt`.
Class MEDIUM. -/
theorem fubini_leaf_ib : ∃ N₀ : ℝ, ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 1 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    ∫ u in ((N : ℝ) - A)..N, deriv (fun v => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)
      = (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
          Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) * innerJ_ib N A lam t := by
  sorry

/-- LEAF: page 264 to page 265 first display, Lemma 1 applied to
`∫_{N-A}^N u^{-1/2} e(t log u / 2π + λu) du` with `G = u^{-1/2} ≤ 2 N^{-1/2}` and
`F' = t/(2πu) + λ`, on the at most two pieces where `G/F'` is monotone, and the trivial bound
`A (N-A)^{-1/2}` otherwise: `|J(t)| ≪ N^{-1/2} min(A, N / min_u |t + 2πλu|)`. Class MEDIUM. -/
theorem inner_lemma1_leaf_ib (h1 : Lemma1) : ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T → ∀ t : ℝ, -T ≤ t → t ≤ T →
    ‖innerJ_ib N A lam t‖ ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) * wt38 N A lam t := by
  sorry

/-- LEAF: page 265 first display, the `t` integral on the right is finite: the weight `wt38`
is bounded by `A` and measurable in `t`, and `F(1/2+it)` is continuous. Class EASY. -/
theorem weight_integrable_leaf_ib {q : ℕ} (N : ℕ) (A lam T : ℝ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ) (hT : 1 ≤ T) :
    IntervalIntegrable (fun t => wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖)
      MeasureTheory.volume (-T) T := by
  have hF : Continuous (fun t : ℝ => Fprod Nv χ (1 / 2 + t * Complex.I)) := by
    unfold Fprod fj
    refine continuous_finsetProd _ (fun j _ => continuous_finsetSum _ (fun n hn => ?_))
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    refine continuous_const.mul ?_
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg.const_cpow
      (Or.inl hn0)
  set m : ℝ → ℝ := fun t => sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N)
    with hm_def
  have hm_nonneg : ∀ t, 0 ≤ m t := fun t =>
    Real.sInf_nonneg (by rintro _ ⟨u, -, rfl⟩; exact abs_nonneg _)
  have hm_cont : Continuous m := by
    by_cases hne : (Set.Icc ((N : ℝ) - A) N).Nonempty
    · refine (LipschitzWith.of_le_add (fun x y => ?_)).continuous
      have hbdd : BddBelow ((fun u => |y + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
        ⟨0, by rintro _ ⟨u, -, rfl⟩; exact abs_nonneg _⟩
      have : m x - dist x y ≤ m y := by
        refine le_csInf (hne.image _) ?_
        rintro _ ⟨u, hu, rfl⟩
        have hbx : BddBelow ((fun u => |x + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
          ⟨0, by rintro _ ⟨u, -, rfl⟩; exact abs_nonneg _⟩
        have h1 : m x ≤ |x + 2 * π * lam * u| := csInf_le hbx ⟨u, hu, rfl⟩
        have h2 : |x + 2 * π * lam * u| ≤ |y + 2 * π * lam * u| + dist x y := by
          rw [Real.dist_eq]
          calc |x + 2 * π * lam * u| = |(y + 2 * π * lam * u) + (x - y)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have : m = fun _ => 0 := by
        funext t; simp only [hm_def, hne, Set.image_empty, Real.sInf_empty]
      rw [this]; exact continuous_const
  have hw : (fun t => wt38 N A lam t) = fun t => if m t = 0 then A else min A (N / m t) := by
    funext t; simp only [wt38, hm_def]
  have hmeas : Measurable (fun t => wt38 N A lam t) := by
    rw [hw]
    exact Measurable.ite (measurableSet_eq_fun hm_cont.measurable measurable_const)
      measurable_const (measurable_const.min (measurable_const.div hm_cont.measurable))
  have hbdd : ∀ t, ‖wt38 N A lam t‖ ≤ |A| := by
    intro t
    rw [show wt38 N A lam t = if m t = 0 then A else min A (N / m t) from congrFun hw t,
      Real.norm_eq_abs]
    split_ifs with h0
    · exact le_rfl
    · have hx : 0 ≤ (N : ℝ) / m t := div_nonneg (Nat.cast_nonneg _) (hm_nonneg t)
      rw [abs_le]
      constructor
      · exact le_min (neg_abs_le A) (le_trans (neg_nonpos.mpr (abs_nonneg A)) hx)
      · exact le_trans (min_le_left _ _) (le_abs_self A)
  have hg := hF.norm.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
  exact ⟨hg.1.bdd_mul hmeas.aestronglyMeasurable (MeasureTheory.ae_of_all _ hbdd),
    hg.2.bdd_mul hmeas.aestronglyMeasurable (MeasureTheory.ae_of_all _ hbdd)⟩

/-- PROVED from the three LEAFs: `InnerBound_ps`, page 265 first display. -/
theorem innerBound_of_leaves_ib (h1 : Lemma1) : InnerBound_ps := by
  obtain ⟨N₁, hF⟩ := fubini_leaf_ib
  obtain ⟨K, N₂, hK, hJ⟩ := inner_lemma1_leaf_ib h1
  refine ⟨K / (2 * π), max N₁ N₂, by positivity, ?_⟩
  intro N A lam T q χ Nv hN hA1 hA2 hT
  have hTT : -T ≤ T := by linarith
  rw [hF N A lam T q χ Nv (le_trans (le_max_left _ _) hN) hA1 hA2 hT]
  have hs : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + t * Complex.I) = 1 / 2 + t * Complex.I := by
    intro t; push_cast; ring
  have hbound : ‖∫ t in (-T)..T, Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
      innerJ_ib N A lam t‖ ≤ ∫ t in (-T)..T, K * (N : ℝ) ^ (-(1 / 2) : ℝ) *
        (wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hTT ?_
      ((weight_integrable_leaf_ib N A lam T χ Nv hT).const_mul _)
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [norm_mul, hs]
    have := hJ N A lam T (le_trans (le_max_right _ _) hN) hA1 hA2 hT t ht.1.le ht.2
    calc ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ * ‖innerJ_ib N A lam t‖
        ≤ ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * wt38 N A lam t) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hR : ∫ t in (-T)..T, K * (N : ℝ) ^ (-(1 / 2) : ℝ) *
        (wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖)
      = K * (N : ℝ) ^ (-(1 / 2) : ℝ) * ∫ t in Set.Icc (-T) T,
        wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hTT,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hR] at hbound
  rw [norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one]
    simp [abs_of_pos Real.pi_pos]
  rw [hc]
  calc 1 / (2 * π) * ‖∫ t in (-T)..T, Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
        innerJ_ib N A lam t‖
      ≤ 1 / (2 * π) * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * ∫ t in Set.Icc (-T) T,
          wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- `innerBound_leaf_ps` of PartialSum1122d.lean, from the three LEAFs above. -/
theorem innerBound_split_ib (h1 : Lemma1) : InnerBound_ps := innerBound_of_leaves_ib h1

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.innerBound_of_leaves_ib

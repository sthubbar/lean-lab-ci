/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364.

ROUTE BURST session 9, 2026-11-12. The right end block for `clip_average_proved`, PROVED:

* `right_end_sum`: the moving sums ending at `b`, summed over the right end block, are at most
  `3 ∫_0^h W(u) du + 2 K₀ (log 2N + 1)²`, as the regions `b ≤ x + u < b + 1` are disjoint.
* `pair_bound`: for one pair `a`, `b`, the square integral of the clipped window sum is at most
  `W(h)` plus the left end at `a` plus the right end at `b`, off the integers.
* `clip_average_proved`: the average over the end blocks.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Clip3

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

/-- The window integral over the unit window `b ≤ x + u < b + 1` is `|S(x, b - x)|²`. PROVED. -/
theorem Fm_unit_window (x : ℝ) (b : ℕ) :
    (∫ u in Ico ((b : ℝ) - x) (b - x + 1), Fm χ x u) = Fm χ x (b - x) := by
  have hc : ∀ u ∈ Ico ((b : ℝ) - x) (b - x + 1), Fm χ x u = Fm χ x (b - x) := by
    intro u hu
    simp only [Fm]
    rw [movingSum_right_const χ (b := b) (by linarith [hu.1]) (by linarith [hu.2])]
  rw [setIntegral_congr_fun measurableSet_Ico hc, setIntegral_const, measureReal_def,
    Real.volume_Ico, show (b : ℝ) - x + 1 - (b - x) = 1 by ring, ENNReal.ofReal_one,
    ENNReal.toReal_one, one_smul]

/-- The pointwise bound behind the right end block. PROVED. -/
theorem right_pointwise {N K0 : ℕ} {h : ℝ} (hJ : ∀ b ∈ Bset N K0,
      Ioo ((b : ℝ) - h + 1) b ⊆ Ioo (N : ℝ) (2 * N)) (hN : (0 : ℝ) ≤ N) (hhN : h ≤ N) (x : ℝ) :
    ∑ b ∈ Bset N K0, (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => Fm χ x (b - x)) x ≤
      (Ioo (N : ℝ) (2 * N)).indicator (Phi χ h) x := by
  classical
  by_cases hx : x ∈ Ioo (N : ℝ) (2 * N)
  · rw [indicator_of_mem hx]
    set B' := (Bset N K0).filter (fun b : ℕ => x ∈ Ioo ((b : ℝ) - h + 1) b) with hB'
    have e1 : ∑ b ∈ Bset N K0, (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => Fm χ x (b - x)) x =
        ∑ b ∈ B', ∫ u in Ico ((b : ℝ) - x) (b - x + 1), Fm χ x u := by
      rw [hB', Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : x ∈ Ioo ((b : ℝ) - h + 1) b
      · rw [indicator_of_mem hb, if_pos hb, Fm_unit_window]
      · rw [indicator_of_notMem hb, if_neg hb]
    rw [e1]
    have hdisj : Set.Pairwise (↑B' : Set ℕ)
        (Function.onFun Disjoint fun b : ℕ => Ico ((b : ℝ) - x) (b - x + 1)) := by
      intro b _ b' _ hbb
      refine Set.disjoint_left.mpr fun u hu hu' => hbb ?_
      have h1 : (b : ℝ) < b' + 1 := by linarith [hu.1, hu'.2]
      have h2 : (b' : ℝ) < b + 1 := by linarith [hu'.1, hu.2]
      have h1' : b < b' + 1 := by exact_mod_cast h1
      have h2' : b' < b + 1 := by exact_mod_cast h2
      omega
    have hsub : (⋃ b ∈ B', Ico ((b : ℝ) - x) (b - x + 1)) ⊆ Ioc 0 h := by
      intro u hu
      simp only [mem_iUnion] at hu
      obtain ⟨b, hb, hub⟩ := hu
      have hxb := (Finset.mem_filter.mp hb).2
      exact ⟨by linarith [hub.1, hxb.2], by linarith [hub.2, hxb.1]⟩
    have hint : IntegrableOn (fun u => Fm χ x u) (Ioc 0 h) :=
      Fm_int_u χ measurableSet_Ioc measure_Ioc_lt_top.ne (R := 4 * N)
        fun u hu => by linarith [hx.2, hu.2]
    rw [← integral_biUnion_finset _ (fun b _ => measurableSet_Ico) hdisj
      (fun b hb => hint.mono_set (fun u hu => hsub (by
        simp only [mem_iUnion]; exact ⟨b, hb, hu⟩)))]
    exact setIntegral_mono_set hint (Eventually.of_forall fun u => Fm_nonneg χ x u)
      (Eventually.of_forall hsub)
  · rw [indicator_of_notMem hx]
    refine le_of_eq (Finset.sum_eq_zero fun b hb => ?_)
    exact indicator_of_notMem (fun h' => hx (hJ b hb h')) _

/-- **The right end block**: `Σ_b ∫_{b-h}^{b} |S(x, b - x)|² dx ≤ 3 ∫_0^h W(u) du +
2 K₀ (log 2N + 1)²`. PROVED. -/
theorem right_end_sum {N K0 : ℕ} (hN : 64 ≤ N) (hK4 : 4 * K0 ≤ N) {h : ℝ}
    (h2 : 2 ≤ h) (h8 : 8 * h ≤ N) :
    (∑ b ∈ Bset N K0, ∫ x in ((b : ℝ) - h)..b, Fm χ x (b - x)) ≤
      3 * (∫ u in Ioc 0 h, windowMean N χ u) + 2 * K0 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have hbB : ∀ b ∈ Bset N K0, b ≤ 2 * N ∧ (2 * N : ℝ) - K0 < b := by
    intro b hb
    have hb' := Finset.mem_Ioc.mp hb
    refine ⟨hb'.2, ?_⟩
    have : 2 * N - K0 < b := hb'.1
    have h3 : ((2 * N - K0 : ℕ) : ℝ) < b := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h3
    push_cast at h3
    linarith
  have hone : ∀ b ∈ Bset N K0, (∫ x in ((b : ℝ) - h)..b, Fm χ x (b - x)) ≤
      3 * (∫ x in ((b : ℝ) - h + 1)..b, Fm χ x (b - x)) + 2 * β ^ 2 := by
    intro b hb
    obtain ⟨hb2, hb1⟩ := hbB b hb
    exact right_end_one χ (by omega) hb2 h2 (by linarith)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_Bset N K0 (by omega),
    nsmul_eq_mul]
  have hJ : ∀ b ∈ Bset N K0, Ioo ((b : ℝ) - h + 1) b ⊆ Ioo (N : ℝ) (2 * N) := by
    intro b hb x hx
    obtain ⟨hb2, hb1⟩ := hbB b hb
    have hb2' : (b : ℝ) ≤ 2 * N := by exact_mod_cast hb2
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hGint : ∀ b ∈ Bset N K0, Integrable ((Ioo ((b : ℝ) - h + 1) b).indicator
      (fun x => Fm χ x (b - x))) := by
    intro b hb
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    refine intOn_bdd (Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop))
      measurableSet_Ioo measure_Ioo_lt_top.ne (SR χ b ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (by linarith)
  have hPhiJ : IntegrableOn (Phi χ h) (Ioo (N : ℝ) (2 * N)) :=
    Phi_intOn χ measurableSet_Ioo measure_Ioo_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hkey : (∑ b ∈ Bset N K0, ∫ x in ((b : ℝ) - h + 1)..b, Fm χ x (b - x)) ≤
      ∫ u in Ioc 0 h, windowMean N χ u := by
    have e1 : ∀ b ∈ Bset N K0, (∫ x in ((b : ℝ) - h + 1)..b, Fm χ x (b - x)) =
        ∫ x, (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => Fm χ x (b - x)) x := by
      intro b hb
      obtain ⟨hb2, hb1⟩ := hbB b hb
      rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
        integral_indicator measurableSet_Ioo]
    rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ hGint]
    calc (∫ x, ∑ b ∈ Bset N K0, (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => Fm χ x (b - x)) x)
        ≤ ∫ x, (Ioo (N : ℝ) (2 * N)).indicator (Phi χ h) x :=
          integral_mono (integrable_finsetSum _ hGint)
            (hPhiJ.integrable_indicator measurableSet_Ioo)
            (fun x => right_pointwise χ hJ (by linarith) (by linarith) x)
      _ = ∫ x in Ioo (N : ℝ) (2 * N), Phi χ h x := integral_indicator measurableSet_Ioo
      _ ≤ _ := swap_le χ N measurableSet_Ioo (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (by linarith)
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  nlinarith

#print axioms Fm_unit_window
#print axioms right_pointwise
#print axioms right_end_sum

end
end LeanLab.PerelliPintz1992.Burst9

/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364.

ROUTE BURST session 9, 2026-11-12. The end averaging of the clipped window sum, first stated as a
leaf `clip_average` in `Burst9Leaves.lean`, PROVED here as `clip_average_proved` with the same
statement and `C₁ = 6`:

* `pair_bound`: for one pair `a`, `b` of the end blocks, the square integral of Gallagher's
  clipped window sum is at most `W(h)` plus the left end at `a` plus the right end at `b`; the
  clipped sum is the moving sum from `a`, at `x`, or ending at `b`, off the integers.
* `clip_average_proved`: the average over the end blocks, from `left_end_sum` and
  `right_end_sum`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Clip4

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem Fm_const_measurable (c : ℝ) (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun x : ℝ => Fm χ c (g x)) := by
  have h1 : Measurable (fun x : ℝ => (c, g x)) := measurable_const.prodMk hg
  have h2 := (Fm_measurable χ).comp h1
  exact h2

/-- **One pair of end points**: `∫ |Σ_{x < n ≤ x + h, a ≤ n ≤ b} c_n|² dx ≤ W(h) +
∫_0^h |S(a, u)|² du + ∫_{b-h}^{b} |S(x, b - x)|² dx`. PROVED. -/
theorem pair_bound {N K0 : ℕ} (hN : 64 ≤ N) (hK4 : 4 * K0 ≤ N) {h : ℝ} (h2 : 2 ≤ h)
    (h8 : 8 * h ≤ N) {a b : ℕ} (ha : a ∈ Aset N K0) (hb : b ∈ Bset N K0) :
    (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤
      windowMean N χ h + (∫ u in (0 : ℝ)..h, Fm χ a u) +
        (∫ x in ((b : ℝ) - h)..b, Fm χ x (b - x)) := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  have haN : (N : ℝ) ≤ a := by exact_mod_cast ha'.1
  have haK : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast ha'.2
  have hb2 : (b : ℝ) ≤ 2 * N := by exact_mod_cast hb'.2
  have hbK : (2 * N : ℝ) - K0 < b := by
    have : 2 * N - K0 < b := hb'.1
    have h3 : ((2 * N - K0 : ℕ) : ℝ) < b := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h3
    push_cast at h3
    linarith
  have hab : (a : ℝ) + h ≤ b := by linarith
  set f1 : ℝ → ℝ := fun x => Fm χ a (x + h - a) with hf1
  set f2 : ℝ → ℝ := fun x => Fm χ x h with hf2
  set f3 : ℝ → ℝ := fun x => Fm χ x (b - x) with hf3
  set g : ℝ → ℝ := fun x => (Ico ((a : ℝ) - h) a).indicator f1 x +
    (Icc (a : ℝ) (b - h)).indicator f2 x + (Ioo ((b : ℝ) - h) b).indicator f3 x with hg
  have i1 : IntegrableOn f1 (Ico ((a : ℝ) - h) a) := by
    refine intOn_bdd (Fm_const_measurable χ a (fun x => x + h - a) (by fun_prop))
      measurableSet_Ico measure_Ico_lt_top.ne (SR χ (4 * N) ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (by linarith [hx.2])
  have i2 : IntegrableOn f2 (Ioc ((N : ℝ) / 2) (3 * N)) :=
    Fm_int_x χ measurableSet_Ioc measure_Ioc_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hsub2 : Icc (a : ℝ) (b - h) ⊆ Ioc ((N : ℝ) / 2) (3 * N) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have i3 : IntegrableOn f3 (Ioo ((b : ℝ) - h) b) := by
    refine intOn_bdd (Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop))
      measurableSet_Ioo measure_Ioo_lt_top.ne (SR χ (4 * N) ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (by linarith)
  have I1 := i1.integrable_indicator measurableSet_Ico
  have I2 := (i2.mono_set hsub2).integrable_indicator measurableSet_Icc
  have I3 := i3.integrable_indicator measurableSet_Ioo
  -- the a.e. pointwise bound off the integers
  have hnull : volume (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero volume
  have hae : ∀ᵐ x ∂volume, x ∉ Set.range (fun n : ℕ => (n : ℝ)) :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  have hpt : ∀ᵐ x ∂volume, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 ≤ g x := by
    filter_upwards [hae] with x hx
    have hxn : ∀ n : ℕ, x ≠ n := fun n h' => hx ⟨n, h'.symm⟩
    have n1 : 0 ≤ (Ico ((a : ℝ) - h) a).indicator f1 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    have n2 : 0 ≤ (Icc (a : ℝ) (b - h)).indicator f2 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    have n3 : 0 ≤ (Ioo ((b : ℝ) - h) b).indicator f3 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    simp only [hg]
    rcases lt_or_ge x ((a : ℝ) - h) with hx1 | hx1
    · rw [clip_eq_zero χ (Or.inl hx1), norm_zero]; nlinarith
    rcases lt_or_ge x a with hx2 | hx2
    · have e : (Ico ((a : ℝ) - h) a).indicator f1 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Ico ((a : ℝ) - h) a from ⟨hx1, hx2⟩), clip_eq_left χ hab hx1 hx2]; rfl
      linarith
    rcases le_or_gt (x + h) b with hx3 | hx3
    · have e : (Icc (a : ℝ) (b - h)).indicator f2 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Icc (a : ℝ) (b - h) from ⟨hx2, by linarith⟩), clip_eq_mid χ (by linarith) hx2 hx3 hxn]; rfl
      linarith
    rcases lt_or_ge x b with hx4 | hx4
    · have e : (Ioo ((b : ℝ) - h) b).indicator f3 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Ioo ((b : ℝ) - h) b from ⟨by linarith, hx4⟩), clip_eq_right χ (by linarith) hx4 hx2 hxn]; rfl
      linarith
    · rw [clip_eq_zero χ (Or.inr hx4), norm_zero]; nlinarith
  have hmono := integral_mono_ae (Burst9G.cwinSum_sq_integrable _ _ h (by linarith))
    ((I1.add I2).add I3) hpt
  refine hmono.trans ?_
  show (∫ x, g x) ≤ windowMean N χ h + (∫ u in (0 : ℝ)..h, Fm χ a u) +
    intervalIntegral f3 ((b : ℝ) - h) b volume
  have e1 : (∫ x, g x) = (∫ x in Ico ((a : ℝ) - h) a, f1 x) + (∫ x in Icc (a : ℝ) (b - h), f2 x) +
      (∫ x in Ioo ((b : ℝ) - h) b, f3 x) := by
    have J12 : Integrable (fun x => (Ico ((a : ℝ) - h) a).indicator f1 x +
        (Icc (a : ℝ) (b - h)).indicator f2 x) := I1.add I2
    show (∫ x, ((Ico ((a : ℝ) - h) a).indicator f1 x + (Icc (a : ℝ) (b - h)).indicator f2 x) +
      (Ioo ((b : ℝ) - h) b).indicator f3 x) = _
    rw [integral_add J12 I3, integral_add I1 I2, integral_indicator measurableSet_Ico,
      integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioo]
  have e2 : (∫ x in Ico ((a : ℝ) - h) a, f1 x) = ∫ u in (0 : ℝ)..h, Fm χ a u := by
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith)]
    have : ∀ x, x + h - (a : ℝ) = x + (h - a) := fun x => by ring
    simp only [hf1, this]
    rw [intervalIntegral.integral_comp_add_right (fun u => Fm χ a u) (h - (a : ℝ))]
    congr 1 <;> ring
  have e3 : (∫ x in Ioo ((b : ℝ) - h) b, f3 x) = intervalIntegral f3 ((b : ℝ) - h) b volume := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have e4 : (∫ x in Icc (a : ℝ) (b - h), f2 x) ≤ windowMean N χ h :=
    setIntegral_mono_set i2 (Eventually.of_forall fun x => Fm_nonneg χ _ _)
      (Eventually.of_forall hsub2)
  have h1 := e1
  have h2 := e2
  have h3 := e3
  have h4 := e4
  linarith

/-- **The end averaging of the clipped window sum, PROVED**, with `C₁ = 6`: the route of
`Decomp1624.reduction27A` and the second term of `Decomp1624.WA`, for display 27, p. 364. -/
theorem clip_average_proved :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ N K0 : ℕ, 64 ≤ N → 1 ≤ K0 → 4 * K0 ≤ N →
      ∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (h : ℝ), 2 ≤ h → 8 * h ≤ N →
        (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ Aset N K0, ∑ b ∈ Bset N K0,
            (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤
          C₁ * (windowMean N χ h + (1 / (K0 : ℝ)) * (∫ u in Ioc (0 : ℝ) h, windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2) := by
  refine ⟨6, by norm_num, fun N K0 hN hK1 hK4 q χ h h2 h8 => ?_⟩
  set W := windowMean N χ h with hW
  set V := ∫ u in Ioc (0 : ℝ) h, windowMean N χ u with hV
  set β := Real.log (2 * N) + 1 with hβ
  set L : ℕ → ℝ := fun a => ∫ u in (0 : ℝ)..h, Fm χ a u with hL
  set R : ℕ → ℝ := fun b => ∫ x in ((b : ℝ) - h)..b, Fm χ x (b - x) with hR
  have hK0 : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hW0 : 0 ≤ W := setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have hp : ∀ a ∈ Aset N K0, ∀ b ∈ Bset N K0,
      (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤ W + L a + R b :=
    fun a ha b hb => pair_bound χ hN hK4 h2 h8 ha hb
  have hsum := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hp a ha b hb
  have e : (∑ a ∈ Aset N K0, ∑ b ∈ Bset N K0, (W + L a + R b)) =
      (K0 : ℝ) * K0 * W + K0 * (∑ a ∈ Aset N K0, L a) + K0 * ∑ b ∈ Bset N K0, R b := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_Aset, card_Bset N K0 (by omega),
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  rw [e] at hsum
  have hLs : (∑ a ∈ Aset N K0, L a) ≤ 3 * V + 2 * K0 * β ^ 2 := left_end_sum χ hN hK1 hK4 h2 h8
  have hRs : (∑ b ∈ Bset N K0, R b) ≤ 3 * V + 2 * K0 * β ^ 2 := right_end_sum χ hN hK4 h2 h8
  have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hK2]
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  have key : (K0 : ℝ) * K0 * W + K0 * (∑ a ∈ Aset N K0, L a) + K0 * ∑ b ∈ Bset N K0, R b ≤
      6 * (W + (1 / (K0 : ℝ)) * V + β ^ 2) * (K0 : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hLs hK0.le
    have h2 := mul_le_mul_of_nonneg_left hRs hK0.le
    have e2 : 6 * (W + (1 / (K0 : ℝ)) * V + β ^ 2) * (K0 : ℝ) ^ 2 =
        6 * K0 * K0 * W + 6 * K0 * V + 6 * K0 * K0 * β ^ 2 := by
      field_simp
    rw [e2]
    have h3 : 0 ≤ (K0 : ℝ) * K0 * W := by positivity
    have h4 : 0 ≤ (K0 : ℝ) * K0 * β ^ 2 := by positivity
    nlinarith
  linarith

#print axioms Fm_const_measurable
#print axioms pair_bound
#print axioms clip_average_proved

end
end LeanLab.PerelliPintz1992.Burst9

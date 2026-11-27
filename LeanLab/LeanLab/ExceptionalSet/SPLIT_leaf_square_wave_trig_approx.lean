import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_fourier_large_translate

/-!
Split of `U1539.leaf_square_wave_trig_approx`, burst-20261124 unit S6-10b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into its two analytic ingredients:

* `leaf_smoothed_square_wave_series`, MEDIUM: the square wave `(-1) ^ ⌊x⌋` smoothed at scale
  `Δ` has an absolutely convergent Fourier series in the frequencies `h / 2` with
  `c_h ≪ min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, and equals `(-1) ^ ⌊x⌋` at distance at least `Δ`
  from the integers.
* `leaf_square_wave_weight_sums`, EASY: the weight `min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))` sums to
  `≪ 1 + log (1 / Δ)` over `|h| ≤ H` and to `≪ Δ ^ (-1) H ^ (-1)` over any finite set of `|h| > H`.

`leaf_square_wave_trig_approx_of_split` proves the parent statement verbatim from them.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539

/-- The coefficient weight of display (40) for the square wave: `1` at `h = 0`, else
`min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`. -/
noncomputable def sqW (Δ : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 1 else min (1 / |(h : ℝ)|) (1 / (Δ * (h : ℝ) ^ 2))

/-- LEAF: P0082 page 370 display (40), the Fourier series of the smoothed square wave. Class
MEDIUM. For `0 < Δ ≤ 1 / 4` the square wave `(-1) ^ ⌊x⌋` convolved with a kernel of width `Δ`,
for example the trapezoid with ramps of width `2 Δ` around the integers, has coefficients `c_h`
in the frequencies `h / 2` with `|c_h| ≤ C min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, its Fourier
series converges to it at every `x`, and it equals `(-1) ^ ⌊x⌋` when `Δ ≤ {x} ≤ 1 - Δ`. -/
theorem leaf_smoothed_square_wave_series :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, ∃ T : ℂ,
          (Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ → T = (-1 : ℂ) ^ ⌊x⌋) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) T := by
  sorry

private theorem sqW_nonneg_sw {Δ : ℝ} (hΔ : 0 < Δ) (h : ℤ) : 0 ≤ sqW Δ h := by
  unfold sqW
  split_ifs
  · exact zero_le_one
  · exact le_min (by positivity) (by positivity)

private theorem sqW_neg_sw (Δ : ℝ) (h : ℤ) : sqW Δ (-h) = sqW Δ h := by
  unfold sqW
  simp only [neg_eq_zero, Int.cast_neg, abs_neg, neg_sq]

private theorem sqW_natAbs_sw (Δ : ℝ) (h : ℤ) : sqW Δ h = sqW Δ (h.natAbs : ℤ) := by
  rcases Int.natAbs_eq h with hh | hh
  · rw [← hh]
  · conv_lhs => rw [hh]
    exact sqW_neg_sw Δ _

private theorem sqW_nat_le_inv_sw {Δ : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    sqW Δ (n : ℤ) ≤ 1 / (n : ℝ) := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold sqW
  rw [if_neg hn0]
  refine (min_le_left _ _).trans (le_of_eq ?_)
  push_cast
  rw [abs_of_nonneg (Nat.cast_nonneg n)]

private theorem sqW_nat_le_sq_sw {Δ : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    sqW Δ (n : ℤ) ≤ 1 / Δ * ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold sqW
  rw [if_neg hn0]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  push_cast
  rw [one_div, one_div, mul_inv]

/-- Proved: folding a sum over nonzero integers onto absolute values. -/
private theorem sum_sqW_le_two_mul_sw {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset ℤ) (T : Finset ℕ)
    (hT : ∀ h ∈ S, h.natAbs ∈ T) :
    (∑ h ∈ S, sqW Δ h) ≤ 2 * ∑ n ∈ T, sqW Δ (n : ℤ) := by
  have hpiece : ∀ p : ℤ → Prop, [DecidablePred p] → (∀ a ∈ S, ∀ b ∈ S, p a → p b →
      a.natAbs = b.natAbs → a = b) →
      (∑ h ∈ S.filter p, sqW Δ h) ≤ ∑ n ∈ T, sqW Δ (n : ℤ) := by
    intro p _ hinj
    calc (∑ h ∈ S.filter p, sqW Δ h)
        = ∑ h ∈ S.filter p, sqW Δ (h.natAbs : ℤ) :=
          Finset.sum_congr rfl (fun h _ => sqW_natAbs_sw Δ h)
      _ = ∑ n ∈ (S.filter p).image Int.natAbs, sqW Δ (n : ℤ) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
          exact hinj a ha.1 b hb.1 ha.2 hb.2 hab
      _ ≤ ∑ n ∈ T, sqW Δ (n : ℤ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sqW_nonneg_sw hΔ _)
          intro n hn
          obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hn
          exact hT h (Finset.mem_filter.1 hh).1
  rw [← Finset.sum_filter_add_sum_filter_not S (fun h : ℤ => 0 ≤ h), two_mul]
  refine add_le_add (hpiece _ ?_) (hpiece _ ?_)
  · intro a _ b _ ha hb hab; omega
  · intro a _ b _ ha hb hab; omega

/-- PROVED, formerly LEAF EASY: the two elementary sums of the weight `sqW`. Class EASY. For `0 < Δ ≤ 1 / 4` and
`H ≥ 1`, the sum over `|h| ≤ H` is at most `C (1 + log (1 / Δ))`, splitting at `|h| = 1 / Δ`,
and the sum over any finite set of integers disjoint from `[-H, H]` is at most `C / (Δ H)`. -/
theorem leaf_square_wave_weight_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, sqW Δ h) ≤ C * (1 + Real.log (1 / Δ)) ∧
      ∀ S : Finset ℤ, Disjoint S (Finset.Icc (-(H : ℤ)) H) →
        (∑ h ∈ S, sqW Δ h) ≤ C / (Δ * H) := by
  refine ⟨7, by norm_num, fun Δ hΔ hΔ4 H hH => ⟨?_, fun S hS => ?_⟩⟩
  · -- the sum over `|h| ≤ H`
    have hinvΔ : (4 : ℝ) ≤ 1 / Δ := by rw [le_div_iff₀ hΔ]; linarith
    have hlogpos : 0 ≤ Real.log (1 / Δ) := Real.log_nonneg (by linarith)
    set K : ℕ := ⌊1 / Δ⌋₊ with hKdef
    have hK1 : (K : ℝ) ≤ 1 / Δ := Nat.floor_le (by linarith)
    have hK2 : 1 / Δ < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have hKpos : 1 ≤ K := by
      have : (1 : ℝ) < (K : ℝ) + 1 := by linarith
      have : (0 : ℝ) < K := by linarith
      exact_mod_cast this
    have hKreal : (1 : ℝ) / Δ ≤ 2 * K := by linarith
    -- the positive half
    have hhalf : (∑ n ∈ Finset.Icc 1 H, sqW Δ (n : ℤ)) ≤ 3 + Real.log (1 / Δ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 H) (fun n => n ≤ K)]
      have h1 : (∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), sqW Δ (n : ℤ))
          ≤ 1 + Real.log (1 / Δ) := by
        calc (∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), sqW Δ (n : ℤ))
            ≤ ∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), 1 / (n : ℝ) := by
              refine Finset.sum_le_sum (fun n hn => sqW_nat_le_inv_sw n ?_)
              exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
          _ ≤ ∑ n ∈ Finset.Icc 1 K, 1 / (n : ℝ) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
              intro n hn
              obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
              exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn1).1, hn2⟩
          _ = (harmonic K : ℝ) := by
              rw [harmonic_eq_sum_Icc]; push_cast; simp only [one_div]
          _ ≤ 1 + Real.log K := harmonic_le_one_add_log K
          _ ≤ 1 + Real.log (1 / Δ) := by
              have : (0 : ℝ) < K := by exact_mod_cast hKpos
              linarith [Real.log_le_log this hK1]
      have h2 : (∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), sqW Δ (n : ℤ)) ≤ 2 := by
        calc (∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), sqW Δ (n : ℤ))
            ≤ ∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), 1 / Δ * ((n : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum (fun n hn => sqW_nat_le_sq_sw n ?_)
              exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
          _ ≤ ∑ n ∈ Finset.Ioc K (max K H), 1 / Δ * ((n : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
              intro n hn
              obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
              have := (Finset.mem_Icc.1 hn1).2
              exact Finset.mem_Ioc.2 ⟨by omega, le_max_of_le_right this⟩
          _ = 1 / Δ * ∑ n ∈ Finset.Ioc K (max K H), ((n : ℝ) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ 1 / Δ * ((K : ℝ)⁻¹ - ((max K H : ℕ) : ℝ)⁻¹) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
          _ ≤ 1 / Δ * (K : ℝ)⁻¹ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : (0 : ℝ) ≤ ((max K H : ℕ) : ℝ)⁻¹ := by positivity
              linarith
          _ ≤ 2 := by
              have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
              rw [← div_eq_mul_inv, div_le_iff₀ hKr]
              linarith
      linarith
    have hzero : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    rw [← Finset.add_sum_erase _ _ hzero]
    have hs0 : sqW Δ 0 = 1 := by simp [sqW]
    rw [hs0]
    have hrest := sum_sqW_le_two_mul_sw hΔ ((Finset.Icc (-(H : ℤ)) H).erase 0)
      (Finset.Icc 1 H) (by
        intro h hh
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hh
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hmem
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    nlinarith
  · -- the tail over `|h| > H`
    set M : ℕ := max H (S.sup Int.natAbs) with hMdef
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hfold := sum_sqW_le_two_mul_sw hΔ S (Finset.Ioc H M) (by
        intro h hh
        have hnot : h ∉ Finset.Icc (-(H : ℤ)) H := Finset.disjoint_left.1 hS hh
        rw [Finset.mem_Icc] at hnot
        refine Finset.mem_Ioc.2 ⟨by omega, ?_⟩
        exact le_max_of_le_right (Finset.le_sup (f := Int.natAbs) hh))
    have htail : (∑ n ∈ Finset.Ioc H M, sqW Δ (n : ℤ)) ≤ 1 / Δ * (H : ℝ)⁻¹ := by
      calc (∑ n ∈ Finset.Ioc H M, sqW Δ (n : ℤ))
          ≤ ∑ n ∈ Finset.Ioc H M, 1 / Δ * ((n : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum (fun n hn => sqW_nat_le_sq_sw n ?_)
            have := (Finset.mem_Ioc.1 hn).1; omega
        _ = 1 / Δ * ∑ n ∈ Finset.Ioc H M, ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ 1 / Δ * ((H : ℝ)⁻¹ - (M : ℝ)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
        _ ≤ 1 / Δ * (H : ℝ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
            linarith
    have heq : 1 / Δ * (H : ℝ)⁻¹ = 1 / (Δ * H) := by field_simp
    have hpos : 0 < 1 / (Δ * H) := by positivity
    have h7 : 7 / (Δ * H) = 7 * (1 / (Δ * H)) := by ring
    rw [h7]
    nlinarith

private theorem eC_norm_sw (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Proved: the tail of a convergent series past a finite set `I` is bounded by any bound on
the norms over finite sets disjoint from `I`. -/
theorem norm_sub_partial_le_of_hasSum_sw {g : ℤ → ℂ} {T : ℂ} (hg : HasSum g T) (I : Finset ℤ)
    (B : ℝ) (hB : ∀ S : Finset ℤ, Disjoint S I → (∑ h ∈ S, ‖g h‖) ≤ B) :
    ‖T - ∑ h ∈ I, g h‖ ≤ B := by
  have ht : Filter.Tendsto (fun s : Finset ℤ => ‖(∑ h ∈ s, g h) - ∑ h ∈ I, g h‖)
      Filter.atTop (nhds ‖T - ∑ h ∈ I, g h‖) :=
    ((hg.sub_const (∑ h ∈ I, g h))).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with s hs
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  exact (norm_sum_le _ _).trans (hB _ Finset.sdiff_disjoint)

/-- Proved: `leaf_square_wave_trig_approx` verbatim, CONDITIONAL ON
`leaf_smoothed_square_wave_series` and `leaf_square_wave_weight_sums`. -/
theorem leaf_square_wave_trig_approx_of_split :
    ∃ A : ℝ, 0 < A ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ A * (1 + Real.log (1 / Δ)) ∧
        ∀ x : ℝ, Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊x⌋ - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖
            ≤ A / (Δ * H) := by
  obtain ⟨C1, hC1, hser⟩ := leaf_smoothed_square_wave_series
  obtain ⟨C2, hC2, hsum⟩ := leaf_square_wave_weight_sums
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun Δ hΔ hΔ4 H hH => ?_⟩
  obtain ⟨c, hc, hx⟩ := hser Δ hΔ hΔ4
  obtain ⟨hs1, hs2⟩ := hsum Δ hΔ hΔ4 H hH
  refine ⟨c, ?_, fun x hx1 hx2 => ?_⟩
  · calc (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖)
        ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, C1 * sqW Δ h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, sqW Δ h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 * (1 + Real.log (1 / Δ))) := mul_le_mul_of_nonneg_left hs1 hC1.le
      _ = C1 * C2 * (1 + Real.log (1 / Δ)) := by ring
  obtain ⟨T, hTeq, hTs⟩ := hx x
  rw [← hTeq hx1 hx2]
  refine norm_sub_partial_le_of_hasSum_sw hTs _ _ (fun S hS => ?_)
  calc (∑ h ∈ S, ‖c h * eC ((h : ℝ) / 2 * x)‖)
      = ∑ h ∈ S, ‖c h‖ := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [norm_mul, eC_norm_sw, mul_one]
    _ ≤ ∑ h ∈ S, C1 * sqW Δ h := Finset.sum_le_sum (fun h _ => hc h)
    _ = C1 * ∑ h ∈ S, sqW Δ h := by rw [Finset.mul_sum]
    _ ≤ C1 * (C2 / (Δ * H)) := mul_le_mul_of_nonneg_left (hs2 S hS) hC1.le
    _ = C1 * C2 / (Δ * H) := by ring

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_square_wave_weight_sums

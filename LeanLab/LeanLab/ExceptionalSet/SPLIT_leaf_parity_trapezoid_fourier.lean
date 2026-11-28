import LeanLab.ExceptionalSet.SPLIT_feed1122_parity_removal_core

/-!
Split of `Feed1122ParityCore.leaf_parity_trapezoid_fourier`, burst-20261124 unit S6-02b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into its two analytic ingredients:

* `leaf_trapezoid_fourier_series`, MEDIUM: the trapezoid function of ramp width `2 A` has an
  absolutely convergent Fourier series in the frequencies `h / 2` with
  `c_h ≪ min(1, A ^ (-1) h ^ (-2))`, its value lies in `[0, 1]` and equals the indicator of
  `⌊x⌋` even off the ramps.
* `leaf_trapezoid_weight_sums`, EASY: the weight `min(1, A ^ (-1) h ^ (-2))` sums to
  `≪ A ^ (-1 / 2)` over `|h| ≤ H` and to `≪ A ^ (-1) H ^ (-1)` over any finite set of `|h| > H`.

`leaf_parity_trapezoid_fourier_of_split` proves the parent statement verbatim from them.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

/-- The coefficient weight of display (40): `1` at `h = 0`, else `min(1, A ^ (-1) h ^ (-2))`. -/
noncomputable def trapW (A : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 1 else min 1 (1 / (A * (h : ℝ) ^ 2))

/-- LEAF: P0082 page 370 display (40), the Fourier series of the trapezoid. Class MEDIUM.
For `0 < A ≤ 1 / 4` the period two trapezoid, one on `[k + A, k + 1 - A]` for `k` even, zero
there for `k` odd, linear on the ramps of width `2 A` around the integers, has coefficients
`c_h` in the frequencies `h / 2` with `|c_h| ≤ C min(1, A ^ (-1) h ^ (-2))`, the series
converges to it at every `x`, its value lies in `[0, 1]`, and off the ramps it is the
indicator of `⌊x⌋` even. Poisson summation, or integration by parts twice. -/
theorem leaf_trapezoid_fourier_series :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * trapW A h) ∧
        ∀ x : ℝ, ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 ∧
          (A ≤ Int.fract x → Int.fract x ≤ 1 - A → (T : ℂ) = if Even ⌊x⌋ then 1 else 0) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) (T : ℂ) := by
  sorry

private theorem trapW_nonneg_tw {A : ℝ} (hA : 0 < A) (h : ℤ) : 0 ≤ trapW A h := by
  unfold trapW
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

private theorem trapW_natAbs_tw (A : ℝ) (h : ℤ) : trapW A h = trapW A (h.natAbs : ℤ) := by
  rcases Int.natAbs_eq h with hh | hh
  · rw [← hh]
  · conv_lhs => rw [hh]
    unfold trapW
    simp only [neg_eq_zero, Int.cast_neg, neg_sq]

private theorem trapW_nat_le_one_tw {A : ℝ} (n : ℕ) : trapW A (n : ℤ) ≤ 1 := by
  unfold trapW
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem trapW_nat_le_sq_tw {A : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    trapW A (n : ℤ) ≤ 1 / A * ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold trapW
  rw [if_neg hn0]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  push_cast
  rw [one_div, one_div, mul_inv]

/-- Proved: folding a sum over nonzero integers onto absolute values. -/
private theorem sum_trapW_le_two_mul_tw {A : ℝ} (hA : 0 < A) (S : Finset ℤ) (T : Finset ℕ)
    (hT : ∀ h ∈ S, h.natAbs ∈ T) :
    (∑ h ∈ S, trapW A h) ≤ 2 * ∑ n ∈ T, trapW A (n : ℤ) := by
  have hpiece : ∀ p : ℤ → Prop, [DecidablePred p] → (∀ a ∈ S, ∀ b ∈ S, p a → p b →
      a.natAbs = b.natAbs → a = b) →
      (∑ h ∈ S.filter p, trapW A h) ≤ ∑ n ∈ T, trapW A (n : ℤ) := by
    intro p _ hinj
    calc (∑ h ∈ S.filter p, trapW A h)
        = ∑ h ∈ S.filter p, trapW A (h.natAbs : ℤ) :=
          Finset.sum_congr rfl (fun h _ => trapW_natAbs_tw A h)
      _ = ∑ n ∈ (S.filter p).image Int.natAbs, trapW A (n : ℤ) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
          exact hinj a ha.1 b hb.1 ha.2 hb.2 hab
      _ ≤ ∑ n ∈ T, trapW A (n : ℤ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => trapW_nonneg_tw hA _)
          intro n hn
          obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hn
          exact hT h (Finset.mem_filter.1 hh).1
  rw [← Finset.sum_filter_add_sum_filter_not S (fun h : ℤ => 0 ≤ h), two_mul]
  refine add_le_add (hpiece _ ?_) (hpiece _ ?_)
  · intro a _ b _ ha hb hab; omega
  · intro a _ b _ ha hb hab; omega

/-- PROVED, formerly LEAF EASY: the two elementary sums of the weight `trapW`. Class EASY. For `0 < A ≤ 1 / 4` and
`H ≥ 1`, the sum over `|h| ≤ H` is at most `C A ^ (-1 / 2)`, and the sum over any finite set
of integers disjoint from `[-H, H]` is at most `C / (A H)`, by comparison with `∫ t ^ (-2)`. -/
theorem leaf_trapezoid_weight_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, trapW A h) ≤ C * A ^ (-(1 / 2 : ℝ)) ∧
      ∀ S : Finset ℤ, Disjoint S (Finset.Icc (-(H : ℤ)) H) →
        (∑ h ∈ S, trapW A h) ≤ C / (A * H) := by
  refine ⟨7, by norm_num, fun A hA hA4 H hH => ⟨?_, fun S hS => ?_⟩⟩
  · set s : ℝ := A ^ (-(1 / 2 : ℝ)) with hsdef
    have hs0 : 0 < s := Real.rpow_pos_of_pos hA _
    have hs2 : s ^ 2 = 1 / A := by
      rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
      norm_num
      rw [Real.rpow_neg_one]
    have hsge : 2 ≤ s := by
      have h4 : (4 : ℝ) ≤ s ^ 2 := by rw [hs2, le_div_iff₀ hA]; linarith
      nlinarith
    set K : ℕ := ⌊s⌋₊ with hKdef
    have hK1 : (K : ℝ) ≤ s := Nat.floor_le hs0.le
    have hK2 : s < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have hKreal : s ≤ 2 * K := by linarith
    have hKpos : 1 ≤ K := by
      have : (0 : ℝ) < K := by linarith
      exact_mod_cast this
    have hhalf : (∑ n ∈ Finset.Icc 1 H, trapW A (n : ℤ)) ≤ 3 * s := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 H) (fun n => n ≤ K)]
      have h1 : (∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), trapW A (n : ℤ)) ≤ s := by
        calc (∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), trapW A (n : ℤ))
            ≤ ∑ n ∈ (Finset.Icc 1 H).filter (fun n => n ≤ K), (1 : ℝ) :=
              Finset.sum_le_sum (fun n _ => trapW_nat_le_one_tw n)
          _ ≤ ∑ n ∈ Finset.Icc 1 K, (1 : ℝ) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => zero_le_one)
              intro n hn
              obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
              exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn1).1, hn2⟩
          _ = K := by simp
          _ ≤ s := hK1
      have h2 : (∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), trapW A (n : ℤ))
          ≤ 2 * s := by
        calc (∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), trapW A (n : ℤ))
            ≤ ∑ n ∈ (Finset.Icc 1 H).filter (fun n => ¬ n ≤ K), 1 / A * ((n : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum (fun n hn => trapW_nat_le_sq_tw n ?_)
              exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
          _ ≤ ∑ n ∈ Finset.Ioc K (max K H), 1 / A * ((n : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
              intro n hn
              obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
              have := (Finset.mem_Icc.1 hn1).2
              exact Finset.mem_Ioc.2 ⟨by omega, le_max_of_le_right this⟩
          _ = 1 / A * ∑ n ∈ Finset.Ioc K (max K H), ((n : ℝ) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ 1 / A * ((K : ℝ)⁻¹ - ((max K H : ℕ) : ℝ)⁻¹) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
          _ ≤ 1 / A * (K : ℝ)⁻¹ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : (0 : ℝ) ≤ ((max K H : ℕ) : ℝ)⁻¹ := by positivity
              linarith
          _ ≤ 2 * s := by
              have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
              rw [← hs2, ← div_eq_mul_inv, div_le_iff₀ hKr]
              nlinarith
      linarith
    have hzero : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    rw [← Finset.add_sum_erase _ _ hzero]
    have hs0' : trapW A 0 = 1 := by simp [trapW]
    rw [hs0']
    have hrest := sum_trapW_le_two_mul_tw hA ((Finset.Icc (-(H : ℤ)) H).erase 0)
      (Finset.Icc 1 H) (by
        intro h hh
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hh
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hmem
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    linarith
  · set M : ℕ := max H (S.sup Int.natAbs) with hMdef
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hfold := sum_trapW_le_two_mul_tw hA S (Finset.Ioc H M) (by
        intro h hh
        have hnot : h ∉ Finset.Icc (-(H : ℤ)) H := Finset.disjoint_left.1 hS hh
        rw [Finset.mem_Icc] at hnot
        refine Finset.mem_Ioc.2 ⟨by omega, ?_⟩
        exact le_max_of_le_right (Finset.le_sup (f := Int.natAbs) hh))
    have htail : (∑ n ∈ Finset.Ioc H M, trapW A (n : ℤ)) ≤ 1 / A * (H : ℝ)⁻¹ := by
      calc (∑ n ∈ Finset.Ioc H M, trapW A (n : ℤ))
          ≤ ∑ n ∈ Finset.Ioc H M, 1 / A * ((n : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum (fun n hn => trapW_nat_le_sq_tw n ?_)
            have := (Finset.mem_Ioc.1 hn).1; omega
        _ = 1 / A * ∑ n ∈ Finset.Ioc H M, ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ 1 / A * ((H : ℝ)⁻¹ - (M : ℝ)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
        _ ≤ 1 / A * (H : ℝ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
            linarith
    have heq : 1 / A * (H : ℝ)⁻¹ = 1 / (A * H) := by field_simp
    have hpos : 0 < 1 / (A * H) := by positivity
    have h7 : 7 / (A * H) = 7 * (1 / (A * H)) := by ring
    rw [h7]
    nlinarith

/-- Proved: the tail of a convergent series past a finite set `I` is bounded by any bound on
the norms over finite sets disjoint from `I`. -/
theorem norm_sub_partial_le_of_hasSum {g : ℤ → ℂ} {T : ℂ} (hg : HasSum g T) (I : Finset ℤ)
    (B : ℝ) (hB : ∀ S : Finset ℤ, Disjoint S I → (∑ h ∈ S, ‖g h‖) ≤ B) :
    ‖T - ∑ h ∈ I, g h‖ ≤ B := by
  have ht : Filter.Tendsto (fun s : Finset ℤ => ‖(∑ h ∈ s, g h) - ∑ h ∈ I, g h‖)
      Filter.atTop (nhds ‖T - ∑ h ∈ I, g h‖) :=
    ((hg.sub_const (∑ h ∈ I, g h))).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with s hs
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  exact (norm_sum_le _ _).trans (hB _ Finset.sdiff_disjoint)

/-- Proved: `leaf_parity_trapezoid_fourier` verbatim, CONDITIONAL ON
`leaf_trapezoid_fourier_series` and `leaf_trapezoid_weight_sums`. -/
theorem leaf_parity_trapezoid_fourier_of_split :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ C * A ^ (-(1 / 2 : ℝ)) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖ ≤
            (if A ≤ Int.fract x ∧ Int.fract x ≤ 1 - A then C / (A * H)
              else 2 + C / (A * H)) := by
  obtain ⟨C1, hC1, hser⟩ := leaf_trapezoid_fourier_series
  obtain ⟨C2, hC2, hsum⟩ := leaf_trapezoid_weight_sums
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun A hA hA4 H hH => ?_⟩
  obtain ⟨c, hc, hx⟩ := hser A hA hA4
  obtain ⟨hs1, hs2⟩ := hsum A hA hA4 H hH
  refine ⟨c, ?_, fun x => ?_⟩
  · calc (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖)
        ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, C1 * trapW A h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, trapW A h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 * A ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hs1 hC1.le
      _ = C1 * C2 * A ^ (-(1 / 2 : ℝ)) := by ring
  obtain ⟨T, hT0, hT1, hTeq, hTs⟩ := hx x
  have htail : ‖(T : ℂ) - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖ ≤
      C1 * C2 / (A * H) := by
    refine norm_sub_partial_le_of_hasSum hTs _ _ (fun S hS => ?_)
    calc (∑ h ∈ S, ‖c h * eC ((h : ℝ) / 2 * x)‖)
        = ∑ h ∈ S, ‖c h‖ := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [norm_mul, eC_norm, mul_one]
      _ ≤ ∑ h ∈ S, C1 * trapW A h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ S, trapW A h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 / (A * H)) := mul_le_mul_of_nonneg_left (hs2 S hS) hC1.le
      _ = C1 * C2 / (A * H) := by ring
  have hsplit : (if Even ⌊x⌋ then (1 : ℂ) else 0) -
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x) =
      ((if Even ⌊x⌋ then (1 : ℂ) else 0) - (T : ℂ)) +
      ((T : ℂ) - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)) := by ring
  by_cases hoff : A ≤ Int.fract x ∧ Int.fract x ≤ 1 - A
  · rw [if_pos hoff, hsplit, ← hTeq hoff.1 hoff.2, sub_self, zero_add]
    exact htail
  · rw [if_neg hoff, hsplit]
    refine (norm_add_le _ _).trans ?_
    have hind : ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) - (T : ℂ)‖ ≤ 2 := by
      split_ifs
      · rw [show (1 : ℂ) - (T : ℂ) = ((1 - T : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      · rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
    linarith

end LeanLab.ExceptionalSet.Feed1122ParityCore

#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.leaf_trapezoid_weight_sums

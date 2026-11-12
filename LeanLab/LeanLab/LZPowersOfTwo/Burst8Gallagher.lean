/-
ROUTE BURST session 8, part 2 of the LZPowersOfTwo split: Gallagher's lemma, P0079 page 8,
Lemma 6, proved in a form sufficient for the J3 estimate of page 9.
Paper: P0079 A. Languasco and A. Zaccagnini, arXiv 0811.3663v2, 2 Apr 2009.
Source of the lemma: P. X. Gallagher, "A large sieve density estimate near σ = 1",
Invent. Math. 11 (1970), Lemma 1, as cited on page 8 of P0079.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

Gallagher's argument, made finite: for real coefficients `a_n` on a finite set,
`∫ |∑ a_n e(nα)|^2 K_h(α) dα = ∫ |∑_{x < n ≤ x + h} a_n|^2 dx`, since both sides equal
`∑_{m,n} a_m a_n max(0, h - |m - n|)`, with `K_h(α) = (sin(π h α)/(π α))^2`. As
`K_h(α) ≥ (2h/π)^2` for `|α| ≤ 1/(2h)`, this gives
`∫_{-Y}^{Y} |∑ a_n e(nα)|^2 dα ≤ π^2 Y^2 ∫ |∑_{x < n ≤ x + 1/(2Y)} a_n|^2 dx`.
-/
import LeanLab.LZPowersOfTwo.Burst8Major
import LeanLab.LZPowersOfTwo.PrimeMoment353

open Real Finset MeasureTheory Filter Asymptotics
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

open LeanLab.LZPowersOfTwo

/-- The window `{x : x < n ≤ x + h} = [n - h, n)`. -/
def win (h : ℝ) (n : ℕ) : Set ℝ := Set.Ico ((n : ℝ) - h) n

/-- Gallagher's window sum `C(x) = ∑_{x < n ≤ x + h} a_n`. -/
def winSum (T : Finset ℕ) (a : ℕ → ℝ) (h x : ℝ) : ℝ :=
  ∑ n ∈ T, (win h n).indicator (fun _ => a n) x

/-- The overlap of two windows has length `max(0, h - |m - n|)`. -/
theorem win_inter_p2 (h : ℝ) (hh : 0 < h) (m n : ℕ) :
    volume.real (win h m ∩ win h n) = max 0 (h - |(m : ℝ) - n|) := by
  unfold win
  rw [Set.Ico_inter_Ico, measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal', max_comm]
  congr 1
  rcases le_total (m : ℝ) n with hmn | hmn
  · rw [max_eq_right (by linarith), min_eq_left hmn, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), min_eq_right hmn, abs_of_nonneg (by linarith)]; ring

/-- The square of a window sum is the double sum over overlapping windows. -/
theorem winSum_sq_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h x : ℝ) :
    winSum T a h x ^ 2 =
      ∑ m ∈ T, ∑ n ∈ T, (win h m ∩ win h n).indicator (fun _ => a m * a n) x := by
  unfold winSum
  rw [sq, sum_mul_sum]
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  by_cases hm : x ∈ win h m <;> by_cases hn : x ∈ win h n <;>
    simp [hm, hn, Set.indicator_of_mem, Set.indicator_of_notMem]

theorem winSum_sq_integral_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x => winSum T a h x ^ 2) ∧
    (∫ x : ℝ, winSum T a h x ^ 2) =
      ∑ m ∈ T, ∑ n ∈ T, a m * a n * max 0 (h - |(m : ℝ) - n|) := by
  have hmeas : ∀ m n : ℕ, MeasurableSet (win h m ∩ win h n) := fun m n =>
    measurableSet_Ico.inter measurableSet_Ico
  have hfin : ∀ m n : ℕ, volume (win h m ∩ win h n) ≠ ⊤ := fun m n =>
    ((measure_mono Set.inter_subset_left).trans_lt measure_Ico_lt_top).ne
  have hint : ∀ m n : ℕ, Integrable ((win h m ∩ win h n).indicator (fun _ => a m * a n)) :=
    fun m n => (integrable_indicator_iff (hmeas m n)).mpr
      (integrableOn_const (hfin m n))
  simp_rw [winSum_sq_p2]
  constructor
  · exact integrable_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hint m n))
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hint m n))]
  apply sum_congr rfl; intro m _
  rw [integral_finsetSum _ (fun n _ => hint m n)]
  apply sum_congr rfl; intro n _
  rw [integral_indicator_const _ (hmeas m n), win_inter_p2 h hh, smul_eq_mul]
  ring

/-- The exponential sum `∑ a_n e(nα)`. -/
def expSum (T : Finset ℕ) (a : ℕ → ℝ) (α : ℝ) : ℂ :=
  ∑ n ∈ T, (a n : ℂ) * character293 ((n : ℝ) * α)

theorem expSum_sq_p2 (T : Finset ℕ) (a : ℕ → ℝ) (α : ℝ) :
    ((‖expSum T a α‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ T, ∑ n ∈ T, ((a m * a n : ℝ) : ℂ) * character293 (((m : ℝ) - n) * α) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold expSum
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [sum_mul_sum]
  apply sum_congr rfl; intro m _
  apply sum_congr rfl; intro n _
  rw [← character_neg353, show ((m : ℝ) - n) * α = (m : ℝ) * α + -((n : ℝ) * α) by ring,
    character_add293]
  push_cast
  ring

/-- Gallagher's identity: `∫ |∑ a_n e(nα)|^2 K_h = ∫ C(x)^2 dx`. PROVED. -/
theorem gallagher_identity_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h : ℝ) (hh : 0 < h) :
    (∫ α : ℝ, ‖expSum T a α‖ ^ 2 * kernel293 h α) = ∫ x : ℝ, winSum T a h x ^ 2 := by
  rw [(winSum_sq_integral_p2 T a h hh).2]
  let w : ℕ × ℕ → ℂ := fun x => ((a x.1 * a x.2 : ℝ) : ℂ)
  let φ : ℕ × ℕ → ℝ := fun x => (x.1 : ℝ) - x.2
  have key : ∀ α : ℝ, (((‖expSum T a α‖ ^ 2 * kernel293 h α : ℝ)) : ℂ) =
      (∑ x ∈ T ×ˢ T, w x * character293 (φ x * α)) * (kernel293 h α : ℂ) := by
    intro α
    rw [Complex.ofReal_mul, expSum_sq_p2]
    simp only [w, φ, sum_product]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [finite_kernel_integral293 (T ×ˢ T) w φ h hh]
  simp only [w, φ, sum_product]
  push_cast
  rfl

/-- `sinc t ≥ 2/π` for `|t| ≤ π/2` (Jordan's inequality). -/
theorem sinc_ge_p2 (t : ℝ) (ht : |t| ≤ π / 2) : 2 / π ≤ Real.sinc t := by
  rcases eq_or_ne t 0 with h0 | h0
  · rw [h0, Real.sinc_zero, div_le_one pi_pos]; linarith [pi_gt_three]
  rw [Real.sinc_of_ne_zero h0]
  have key : ∀ u : ℝ, 0 < u → u ≤ π / 2 → 2 / π ≤ sin u / u := by
    intro u hu hu'
    rw [le_div_iff₀ hu]
    exact Real.mul_le_sin hu.le hu'
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have := key (-t) (by linarith) (by rw [abs_of_neg hn] at ht; linarith)
    rwa [Real.sin_neg, neg_div_neg_eq] at this
  · exact key t hp (by rwa [abs_of_pos hp] at ht)

/-- `K_h(α) ≥ (2h/π)^2` for `|α| ≤ 1/(2h)`. -/
theorem kernel_ge_p2 (h α : ℝ) (hh : 0 < h) (hα : |α| ≤ 1 / (2 * h)) :
    (2 * h / π) ^ 2 ≤ kernel293 h α := by
  unfold kernel293
  have ht : |π * h * α| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < π * h)]
    calc π * h * |α| ≤ π * h * (1 / (2 * h)) := by gcongr
      _ = π / 2 := by field_simp
  have hs := sinc_ge_p2 _ ht
  have h1 : 2 * h / π ≤ h * Real.sinc (π * h * α) := by
    calc 2 * h / π = h * (2 / π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hh.le
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- Gallagher's lemma [5, Lemma 1], finite form: for `0 < Y`,
`∫_{-Y}^{Y} |∑ a_n e(nα)|^2 dα ≤ π^2 Y^2 ∫ |∑_{x < n ≤ x + 1/(2Y)} a_n|^2 dx`. PROVED. -/
theorem gallagher_p2 (T : Finset ℕ) (a : ℕ → ℝ) (Y : ℝ) (hY : 0 < Y) :
    (∫ α in (-Y)..Y, ‖expSum T a α‖ ^ 2) ≤
      π ^ 2 * Y ^ 2 * ∫ x : ℝ, winSum T a (1 / (2 * Y)) x ^ 2 := by
  set h := 1 / (2 * Y) with hh_def
  have hh : 0 < h := by positivity
  have hc : Continuous (fun α => ‖expSum T a α‖ ^ 2) := by
    unfold expSum character293; fun_prop
  have hK : Integrable (fun α => ‖expSum T a α‖ ^ 2 * kernel293 h α) := by
    let P := ∑ n ∈ T, |a n|
    apply (kernel_integrable293 h).bdd_mul (c := P ^ 2) hc.aestronglyMeasurable
    apply Eventually.of_forall; intro α
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    unfold expSum
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply sum_congr rfl; intro n _
    rw [norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hYh : Y = 1 / (2 * h) := by rw [hh_def]; field_simp
  have hpt : ∀ α ∈ Set.Icc (-Y) Y, ‖expSum T a α‖ ^ 2 ≤
      (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) := by
    intro α hα
    have hα' : |α| ≤ 1 / (2 * h) := by rw [← hYh]; exact abs_le.mpr hα
    have hk := kernel_ge_p2 h α hh hα'
    have e : (π / (2 * h)) ^ 2 * (2 * h / π) ^ 2 = 1 := by field_simp
    have hn : 0 ≤ ‖expSum T a α‖ ^ 2 := sq_nonneg _
    calc ‖expSum T a α‖ ^ 2 = (π / (2 * h)) ^ 2 * (2 * h / π) ^ 2 * ‖expSum T a α‖ ^ 2 := by
          rw [e, one_mul]
      _ ≤ (π / (2 * h)) ^ 2 * kernel293 h α * ‖expSum T a α‖ ^ 2 := by gcongr
      _ = _ := by ring
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  calc (∫ α in Set.Icc (-Y) Y, ‖expSum T a α‖ ^ 2)
      ≤ ∫ α in Set.Icc (-Y) Y, (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) :=
        setIntegral_mono_on (hc.integrableOn_Icc) (hK.const_mul _).integrableOn
          measurableSet_Icc hpt
    _ ≤ ∫ α : ℝ, (π / (2 * h)) ^ 2 * (‖expSum T a α‖ ^ 2 * kernel293 h α) :=
        setIntegral_le_integral (hK.const_mul _) (Eventually.of_forall (fun α =>
          mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (kernel_nonneg293 h α))))
    _ = (π / (2 * h)) ^ 2 * ∫ α : ℝ, ‖expSum T a α‖ ^ 2 * kernel293 h α := integral_const_mul _ _
    _ = π ^ 2 * Y ^ 2 * ∫ x : ℝ, winSum T a h x ^ 2 := by
        rw [gallagher_identity_p2 T a h hh, hYh]; field_simp

/-! ### Gallagher's lemma for `S - U`, P0079 page 8, Lemma 6 in the form used on page 9 -/

/-- The integers `εX ≤ n ≤ X` of `U`. -/
abbrev boxN (ε X : ℝ) : Finset ℕ := (range (⌊X⌋₊ + 1)).filter (fun n : ℕ => ε * X ≤ (n : ℝ))

/-- The coefficients of `S - U`: `log n` on primes, minus one. -/
def suCoeff (n : ℕ) : ℝ := (if n.Prime then log n else 0) - 1

/-- `S(α) - U(α) = ∑_{εX ≤ n ≤ X} (Λ'(n) - 1) e(nα)`. PROVED. -/
theorem su_eq_expSum_p2 (ε X α : ℝ) :
    primeSum293 ε X α - discretePrime396 ε X α = expSum (boxN ε X) suCoeff α := by
  have hS : primeSum293 ε X α =
      ∑ n ∈ boxN ε X, (((if n.Prime then log n else 0 : ℝ)) : ℂ) * character293 ((n : ℝ) * α) := by
    unfold primeSum293
    have hset : (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)) =
        (boxN ε X).filter (fun n : ℕ => n.Prime) := by
      ext n; simp only [mem_filter]; tauto
    rw [hset, sum_filter]
    apply sum_congr rfl; intro n _
    split_ifs <;> simp
  rw [hS]
  unfold discretePrime396 expSum suCoeff
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro n _
  push_cast
  ring

/-- `|Λ'(n) - 1| ≤ log X + 1` for `n ≤ X`. -/
theorem suCoeff_abs_le_p2 (X : ℝ) (n : ℕ) (hX : 1 ≤ X) (hn : (n : ℝ) ≤ X) :
    |suCoeff n| ≤ log X + 1 := by
  unfold suCoeff
  have hl : 0 ≤ log X := log_nonneg hX
  have hln : log (n : ℝ) ≤ log X := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0, hl]
    · exact log_le_log (by exact_mod_cast hpos) hn
  have hln0 : 0 ≤ log (n : ℝ) := Real.log_natCast_nonneg n
  split_ifs
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- The window sum over `boxN` as a sum over the integers in the window. -/
theorem winSum_eq_filter_p2 (T : Finset ℕ) (a : ℕ → ℝ) (h x : ℝ) :
    winSum T a h x = ∑ n ∈ T.filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + h), a n := by
  unfold winSum
  rw [sum_filter]
  apply sum_congr rfl; intro n _
  have : x ∈ win h n ↔ x < n ∧ (n : ℝ) ≤ x + h := by
    unfold win; rw [Set.mem_Ico]; constructor <;> intro H <;> constructor <;> linarith [H.1, H.2]
  by_cases hx : x ∈ win h n
  · rw [Set.indicator_of_mem hx, if_pos (this.mp hx)]
  · rw [Set.indicator_of_notMem hx, if_neg (fun H => hx (this.mpr H))]

/-- The window integers lie in `(⌊x⌋, ⌊x + h⌋]`. -/
theorem window_subset_p2 (ε X h x : ℝ) (hεX : 0 < ε * X) :
    (boxN ε X).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + h) ⊆ Ioc ⌊x⌋₊ ⌊x + h⌋₊ := by
  intro n hn
  simp only [mem_filter, mem_range] at hn
  rw [mem_Ioc]
  have hn1 : (0 : ℝ) < n := lt_of_lt_of_le hεX hn.1.2
  constructor
  · rcases le_or_gt 0 x with hx | hx
    · exact (Nat.floor_lt hx).mpr hn.2.1
    · rw [Nat.floor_of_nonpos hx.le]; exact_mod_cast hn1
  · exact Nat.le_floor hn.2.2

/-- At most `h + 1` integers lie in a window of length `h`. -/
theorem window_card_p2 (h x : ℝ) (hh : 0 < h) :
    ((Ioc ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) ≤ h + 1 := by
  rw [Nat.card_Ioc]
  have hmono : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hmono]
  have h1 := Nat.lt_floor_add_one x
  rcases le_or_gt 0 (x + h) with hxh | hxh
  · have h2 := Nat.floor_le hxh
    rcases le_or_gt 0 x with hx | hx
    · linarith
    · rw [Nat.floor_of_nonpos hx.le]; push_cast; linarith
  · rw [Nat.floor_of_nonpos hxh.le]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊x⌋₊]

/-- P0079 page 8, display (31) and Lemma 6: pointwise bound for the window sum of `S - U`.
Inside `[εX, X - h]` it is `θ(x+h) - θ(x) - h` up to one; on the two boundary strips it is at
most `(h + 1)(log X + 1)`; elsewhere it vanishes. PROVED. -/
theorem winSum_su_bound_p2 (ε X h x : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hX : 1 ≤ X)
    (hh : 0 < h) :
    winSum (boxN ε X) suCoeff h x ^ 2 ≤
      2 * (Set.Icc (ε * X) X).indicator
          (fun x => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2) x +
        2 * (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x +
        (Set.Ico (ε * X - h) (ε * X) ∪ Set.Ioo (X - h) X).indicator
          (fun _ => ((h + 1) * (log X + 1)) ^ 2) x := by
  have hεX : 0 < ε * X := by positivity
  have hX0 : 0 ≤ X := by linarith
  have hlogX : 0 ≤ log X := log_nonneg hX
  rw [winSum_eq_filter_p2]
  set F := (boxN ε X).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + h)
  have hI1 : 0 ≤ (Set.Icc (ε * X) X).indicator
      (fun x => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2) x :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hI2 : 0 ≤ (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hI3 : 0 ≤ (Set.Ico (ε * X - h) (ε * X) ∪ Set.Ioo (X - h) X).indicator
      (fun _ => ((h + 1) * (log X + 1)) ^ 2) x :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  -- the empty cases
  by_cases hout : x < ε * X - h ∨ X ≤ x
  · have hF : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      simp only [F, mem_filter, mem_range] at hn
      have hnX : (n : ℝ) ≤ X := by
        have := Nat.floor_le hX0
        have h2 : (n : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hn.1.1
        linarith
      rcases hout with h1 | h1 <;> linarith [hn.1.2, hn.2.1, hn.2.2]
    rw [hF, sum_empty]
    nlinarith
  push_neg at hout
  by_cases hbd : x < ε * X ∨ X - h < x
  · -- boundary strips
    have hmem : x ∈ Set.Ico (ε * X - h) (ε * X) ∪ Set.Ioo (X - h) X := by
      rcases hbd with h1 | h1
      · left; exact ⟨hout.1, h1⟩
      · right; exact ⟨h1, hout.2⟩
    rw [Set.indicator_of_mem hmem]
    have hb : |∑ n ∈ F, suCoeff n| ≤ (h + 1) * (log X + 1) := by
      calc |∑ n ∈ F, suCoeff n| ≤ ∑ n ∈ F, |suCoeff n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ F, (log X + 1) := by
            apply sum_le_sum; intro n hn
            simp only [F, mem_filter, mem_range] at hn
            apply suCoeff_abs_le_p2 X n hX
            have := Nat.floor_le hX0
            have h2 : (n : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hn.1.1
            linarith
        _ = F.card * (log X + 1) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (h + 1) * (log X + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact (Nat.cast_le.mpr (card_le_card (window_subset_p2 ε X h x hεX))).trans
              (window_card_p2 h x hh)
    have : (∑ n ∈ F, suCoeff n) ^ 2 ≤ ((h + 1) * (log X + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    linarith
  push_neg at hbd
  -- the interior `εX ≤ x ≤ X - h`
  have hx0 : 0 ≤ x := by linarith
  have hmem : x ∈ Set.Icc (ε * X) X := ⟨hbd.1, by linarith⟩
  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  have hF : F = Ioc ⌊x⌋₊ ⌊x + h⌋₊ := by
    apply Finset.Subset.antisymm (window_subset_p2 ε X h x hεX)
    intro n hn
    rw [mem_Ioc] at hn
    have h1 : x < n := (Nat.floor_lt hx0).mp hn.1
    have h2 : (n : ℝ) ≤ x + h := (Nat.le_floor_iff (by linarith)).mp hn.2
    simp only [F, mem_filter, mem_range]
    refine ⟨⟨Nat.lt_succ_iff.mpr (Nat.le_floor (by linarith)), by linarith⟩, h1, h2⟩
  have hmono : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have htheta : Chebyshev.theta (x + h) - Chebyshev.theta x =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, (if n.Prime then log (n : ℝ) else 0) := by
    have e : ∀ y : ℝ, Chebyshev.theta y =
        ∑ n ∈ Ioc 0 ⌊y⌋₊, (if n.Prime then log (n : ℝ) else 0) := by
      intro y; unfold Chebyshev.theta; rw [sum_filter]
    rw [e, e, ← sum_Ioc_consecutive _ (Nat.zero_le _) hmono]
    ring
  have hsum : ∑ n ∈ F, suCoeff n =
      (Chebyshev.theta (x + h) - Chebyshev.theta x - h) +
        (h - ((⌊x + h⌋₊ : ℝ) - ⌊x⌋₊)) := by
    rw [hF, htheta]
    unfold suCoeff
    rw [sum_sub_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hmono]
    ring
  have hE : |h - ((⌊x + h⌋₊ : ℝ) - ⌊x⌋₊)| ≤ 1 := by
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one x
    have h3 := Nat.floor_le (show 0 ≤ x + h by linarith)
    have h4 := Nat.lt_floor_add_one (x + h)
    rw [abs_le]; constructor <;> linarith
  rw [hsum]
  have hE2 : (h - ((⌊x + h⌋₊ : ℝ) - ⌊x⌋₊)) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (h - ((⌊x + h⌋₊ : ℝ) - ⌊x⌋₊))]
  nlinarith [sq_nonneg ((Chebyshev.theta (x + h) - Chebyshev.theta x - h) -
    (h - ((⌊x + h⌋₊ : ℝ) - ⌊x⌋₊)))]

/-- Measurability of the Selberg integrand, from the monotonicity of `θ`. -/
theorem selberg_integrand_measurable_p2 (h : ℝ) :
    Measurable (fun x : ℝ => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2) := by
  have hm : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  exact (((hm.comp (measurable_id.add_const h)).sub hm).sub_const h).pow_const 2

/-- P0079 page 8, Lemma 6 in the form proved here: for `X ≥ 1` and `Y > 0`, with
`h = 1/(2Y)`, `∫_{-Y}^{Y} |S - U|^2 ≤ π^2 Y^2 (2 J(X, h) + 2X + 2h ((h+1)(log X + 1))^2)`.
This has `(log X)^2 / Y` where the printed Lemma 6 has `log X / Y`, and `J(X, 1/(2Y))` in place
of `J(X, 1/Y)`; both are harmless for page 9. PROVED. -/
theorem gallagher_su_p2 (ε X Y : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hX : 1 ≤ X) (hY : 0 < Y) :
    (∫ α in (-Y)..Y, ‖primeSum293 ε X α - discretePrime396 ε X α‖ ^ 2) ≤
      π ^ 2 * Y ^ 2 * (2 * selbergJ ε X (1 / (2 * Y)) + 2 * X +
        2 * (1 / (2 * Y)) * (((1 / (2 * Y)) + 1) * (log X + 1)) ^ 2) := by
  set h := 1 / (2 * Y) with hh_def
  have hh : 0 < h := by positivity
  have hεX : ε * X ≤ X := by nlinarith
  simp_rw [su_eq_expSum_p2]
  refine (gallagher_p2 (boxN ε X) suCoeff Y hY).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set g := fun x : ℝ => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2
  set c := ((h + 1) * (log X + 1)) ^ 2
  set Bd := Set.Ico (ε * X - h) (ε * X) ∪ Set.Ioo (X - h) X
  have hBd : MeasurableSet Bd := measurableSet_Ico.union measurableSet_Ioo
  have hBdf : volume Bd < ⊤ :=
    (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨measure_Ico_lt_top, measure_Ioo_lt_top⟩)
  have hgI : IntegrableOn g (Set.Icc (ε * X) X) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (selberg_integrand_measurable_p2 h).aestronglyMeasurable
      ((2 * Chebyshev.theta (X + h) + h) ^ 2)
    rw [ae_restrict_iff' measurableSet_Icc]
    apply Eventually.of_forall
    intro x hx
    have t1 := Chebyshev.theta_nonneg x
    have t2 := Chebyshev.theta_nonneg (x + h)
    have t3 : Chebyshev.theta (x + h) ≤ Chebyshev.theta (X + h) :=
      Chebyshev.theta_mono (by linarith [hx.2])
    have t4 : Chebyshev.theta x ≤ Chebyshev.theta (X + h) :=
      Chebyshev.theta_mono (by linarith [hx.2])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (abs_nonneg _) _ 2 |>.trans' (le_of_eq (sq_abs _).symm)
    rw [abs_le]; constructor <;> linarith
  have i1 : Integrable ((Set.Icc (ε * X) X).indicator g) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hgI
  have i2 : Integrable ((Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have i3 : Integrable (Bd.indicator (fun _ => c)) :=
    (integrable_indicator_iff hBd).mpr (integrableOn_const hBdf.ne)
  have hW := (winSum_sq_integral_p2 (boxN ε X) suCoeff h hh).1
  calc (∫ x : ℝ, winSum (boxN ε X) suCoeff h x ^ 2)
      ≤ ∫ x : ℝ, (2 * (Set.Icc (ε * X) X).indicator g x +
          2 * (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x + Bd.indicator (fun _ => c) x) :=
        integral_mono hW (((i1.const_mul 2).add (i2.const_mul 2)).add i3)
          (fun x => winSum_su_bound_p2 ε X h x hε hε' hX hh)
    _ = 2 * (∫ x : ℝ, (Set.Icc (ε * X) X).indicator g x) +
          2 * (∫ x : ℝ, (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x) +
          ∫ x : ℝ, Bd.indicator (fun _ => c) x := by
        rw [integral_add (f := fun x => 2 * (Set.Icc (ε * X) X).indicator g x +
            2 * (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x)
            (g := fun x => Bd.indicator (fun _ => c) x) ((i1.const_mul 2).add (i2.const_mul 2)) i3,
          integral_add (f := fun x => 2 * (Set.Icc (ε * X) X).indicator g x)
            (g := fun x => 2 * (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x)
            (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 2 * selbergJ ε X h + 2 * X + 2 * h * c := by
        have e1 : (∫ x : ℝ, (Set.Icc (ε * X) X).indicator g x) = selbergJ ε X h := by
          rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hεX]
          rfl
        have e2 : (∫ x : ℝ, (Set.Icc (ε * X) X).indicator (fun _ => (1 : ℝ)) x) ≤ X := by
          rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
            Real.volume_real_Icc_of_le hεX]
          nlinarith
        have e3 : (∫ x : ℝ, Bd.indicator (fun _ => c) x) ≤ 2 * h * c := by
          rw [integral_indicator_const _ hBd, smul_eq_mul]
          have hv : volume.real Bd ≤ 2 * h := by
            have := measureReal_union_le (μ := volume) (Set.Ico (ε * X - h) (ε * X))
              (Set.Ioo (X - h) X)
            rw [Real.volume_real_Ico_of_le (by linarith),
              Real.volume_real_Ioo_of_le (by linarith)] at this
            linarith
          have hc : 0 ≤ c := sq_nonneg _
          nlinarith
        linarith

set_option maxHeartbeats 1600000 in
/-- P0079 page 9, the J3 estimate: the exact statement of the leaf
`prime_integer_l2_small418`, now from Gallagher's lemma as proved here, `gallagher_su_p2`,
and Lemma 7 with `A = 3`, `Y = |λ| P / X`, `P = X^{1/3}`.
CONDITIONAL ON `saffari_vaughan_lemma7_p2` alone; this proof has no sorry of its own. -/
theorem prime_integer_l2_small_p3 (ε l : ℝ) (hl : l ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      (∫ α in major293 X,
        ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) ≤ δ * X / log X := by
  obtain ⟨B, hB, C', hC', H7⟩ := saffari_vaughan_lemma7_p2 ε hε hε' 3 (by norm_num)
  intro δ hδ
  obtain ⟨a, ha_def⟩ : ∃ a, a = |l| := ⟨_, rfl⟩
  have ha : 0 < a := ha_def ▸ abs_pos.mpr hl
  -- the small quantity
  obtain ⟨K, hK⟩ : ∃ K, K = a⁻¹ * π ^ 2 * (C' / 18 + 6 * a ^ 2 + 108 / a) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = δ / K := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  -- asymptotics in `t = X^{1/3}`
  have hlog3 : Tendsto (fun t : ℝ => log t ^ 3 / t) atTop (nhds 0) := by
    simpa using (isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
  have hlog1 : Tendsto (fun t : ℝ => log t ^ 1 / t) atTop (nhds 0) := by
    simpa using (isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
  have hinvlog : Tendsto (fun t : ℝ => (log t ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp tendsto_log_atTop)
  have hB' : (fun t : ℝ => log t ^ B) =o[atTop] (fun t : ℝ => t ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop B one_pos
  have hBt := hB'.bound (c := (2 * a * 3 ^ B)⁻¹) (by positivity)
  have ht : ∀ᶠ t : ℝ in atTop,
      log t ^ 3 / t ≤ e ∧ log t ^ 1 / t ≤ e ∧ (log t ^ 2)⁻¹ ≤ e ∧ 1 ≤ log t ∧
      2 * a ≤ t ^ 2 ∧ 1 ≤ a * t ∧ ‖log t ^ B‖ ≤ (2 * a * 3 ^ B)⁻¹ * ‖t ^ (1 : ℝ)‖ := by
    filter_upwards [hlog3.eventually (eventually_le_nhds he0),
      hlog1.eventually (eventually_le_nhds he0),
      hinvlog.eventually (eventually_le_nhds he0),
      tendsto_log_atTop.eventually (eventually_ge_atTop 1),
      (tendsto_pow_atTop (n := 2) (by norm_num)).eventually (eventually_ge_atTop (2 * a)),
      eventually_ge_atTop (1 / a), hBt] with t h1 h2 h3 h4 h5 h6 h7
    refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
    rwa [div_le_iff₀ ha, mul_comm] at h6
  have hcube : Tendsto (fun X : ℝ => X ^ ((1 : ℝ) / 3)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [H7, hcube.eventually ht, eventually_ge_atTop (1 : ℝ)] with
    X h7 htX hX1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := htX
  set t := X ^ ((1 : ℝ) / 3) with htdef
  have hX0 : 0 < X := by linarith
  have ht0 : 0 < t := by positivity
  have hXt : X = t ^ 3 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hlogX : log X = 3 * log t := by rw [hXt, Real.log_pow]; norm_num
  have hlt : 0 < log t := by linarith
  have h16 : X ^ ((1 : ℝ) / 6) ≤ t := by
    rw [htdef]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  clear_value t
  have ht1 : 1 ≤ t := by
    by_contra h; push_neg at h
    have := Real.log_nonpos ht0.le h.le; linarith
  have hR : X ^ ((1 : ℝ) / 3) / X = 1 / t ^ 2 := by
    rw [← htdef, hXt]; field_simp
  obtain ⟨Y, hY⟩ : ∃ Y, Y = a / t ^ 2 := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hsub : (∫ α in major293 X,
      ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) =
      a⁻¹ * ∫ β in (-Y)..Y, ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2 := by
    have := symm_subst_p2 (fun β => ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2) l
      (X ^ ((1 : ℝ) / 3) / X) hl (by positivity)
    rw [hR] at this
    unfold major293
    rw [hR, this, hY, ← ha_def]
    congr 2 <;> ring
  -- Gallagher, proved
  have G := gallagher_su_p2 ε X Y hε hε' hX1 hY0
  -- Lemma 7 at `h = 1/(2Y) = t^2/(2a)`
  obtain ⟨h, hh⟩ : ∃ h, h = 1 / (2 * Y) := ⟨_, rfl⟩
  rw [← hh] at G
  have hhv : h = t ^ 2 / (2 * a) := by rw [hh, hY]; field_simp
  have hh1 : 1 ≤ h := by rw [hhv, le_div_iff₀ (by positivity)]; linarith
  have hlogB : (log X) ^ B = 3 ^ B * (log t) ^ B := by
    rw [hlogX, Real.mul_rpow (by norm_num) hlt.le]
  have h7' : (log t) ^ B ≤ (2 * a * 3 ^ B)⁻¹ * t := by
    have := t7
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg hlt.le _), Real.rpow_one,
      Real.norm_of_nonneg ht0.le] at this
  have hlow : X ^ ((1 : ℝ) / 6) * (log X) ^ B ≤ h := by
    rw [hhv, hlogB]
    have hp : 0 ≤ 3 ^ B * (log t) ^ B := by positivity
    have h3B : 0 < (3 : ℝ) ^ B := by positivity
    calc X ^ ((1 : ℝ) / 6) * (3 ^ B * log t ^ B) ≤ t * (3 ^ B * ((2 * a * 3 ^ B)⁻¹ * t)) := by
          apply mul_le_mul h16 (mul_le_mul_of_nonneg_left h7' h3B.le) hp ht0.le
      _ = t ^ 2 / (2 * a) := by field_simp
  have hup : h ≤ X := by
    rw [hhv, hXt, div_le_iff₀ (by positivity)]; nlinarith
  have L7 := h7 h hlow hup
  have hYh : Y * h = 1 / 2 := by rw [hh]; field_simp
  have hJ : Y ^ 2 * (2 * selbergJ ε X h) ≤ C' * t ^ 3 / (54 * log t ^ 3) := by
    have hl3 : (log X) ^ (3 : ℝ) = 27 * log t ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hlogX]; ring
    rw [hl3] at L7
    have hY2' : 0 ≤ 2 * Y ^ 2 := by positivity
    calc Y ^ 2 * (2 * selbergJ ε X h) = 2 * Y ^ 2 * selbergJ ε X h := by ring
      _ ≤ 2 * Y ^ 2 * (C' * h ^ 2 * X / (27 * log t ^ 3)) :=
          mul_le_mul_of_nonneg_left L7 hY2'
      _ = 2 * C' * (Y * h) ^ 2 * X / (27 * log t ^ 3) := by ring
      _ = C' * t ^ 3 / (54 * log t ^ 3) := by rw [hYh, hXt]; field_simp; ring
  have hT2 : Y ^ 2 * (2 * X) = 2 * a ^ 2 / t := by rw [hY, hXt]; field_simp
  have hT3 : Y ^ 2 * (2 * h * ((h + 1) * (log X + 1)) ^ 2) ≤
      36 * t ^ 2 * log t ^ 2 / a := by
    have e1 : h + 1 ≤ 2 * h := by linarith
    have e2 : log X + 1 ≤ 6 * log t := by rw [hlogX]; linarith
    have hlX : 0 ≤ log X := by rw [hlogX]; linarith
    have e3 : ((h + 1) * (log X + 1)) ^ 2 ≤ (2 * h * (6 * log t)) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith))
      exact mul_le_mul e1 e2 (by linarith) (by linarith)
    calc Y ^ 2 * (2 * h * ((h + 1) * (log X + 1)) ^ 2)
        ≤ Y ^ 2 * (2 * h * (2 * h * (6 * log t)) ^ 2) := by gcongr
      _ = 288 * (Y * h) ^ 2 * h * log t ^ 2 := by ring
      _ = 36 * t ^ 2 * log t ^ 2 / a := by rw [hYh, hhv]; field_simp; ring
  rw [hsub]
  have hint : (∫ β in (-Y)..Y, ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2) ≤
      π ^ 2 * (C' * t ^ 3 / (54 * log t ^ 3) + 2 * a ^ 2 / t + 36 * t ^ 2 * log t ^ 2 / a) := by
    refine G.trans ?_
    have e : π ^ 2 * Y ^ 2 * (2 * selbergJ ε X h + 2 * X + 2 * h * ((h + 1) * (log X + 1)) ^ 2) =
        π ^ 2 * (Y ^ 2 * (2 * selbergJ ε X h) + Y ^ 2 * (2 * X) +
          Y ^ 2 * (2 * h * ((h + 1) * (log X + 1)) ^ 2)) := by ring
    rw [e, hT2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hfin : a⁻¹ * (π ^ 2 * (C' * t ^ 3 / (54 * log t ^ 3) + 2 * a ^ 2 / t +
      36 * t ^ 2 * log t ^ 2 / a)) ≤ δ * X / log X := by
    rw [hlogX, hXt]
    have hlt3 : 0 < 3 * log t := by positivity
    rw [le_div_iff₀ hlt3]
    have key : a⁻¹ * π ^ 2 * (C' / 18 * (log t ^ 2)⁻¹ + 6 * a ^ 2 * (log t ^ 1 / t) +
        108 / a * (log t ^ 3 / t)) ≤ δ := by
      have hb1 : C' / 18 * (log t ^ 2)⁻¹ ≤ C' / 18 * e :=
        mul_le_mul_of_nonneg_left t3 (by positivity)
      have hb2 : 6 * a ^ 2 * (log t ^ 1 / t) ≤ 6 * a ^ 2 * e :=
        mul_le_mul_of_nonneg_left t2 (by positivity)
      have hb3 : 108 / a * (log t ^ 3 / t) ≤ 108 / a * e :=
        mul_le_mul_of_nonneg_left t1 (by positivity)
      have hsum : C' / 18 * (log t ^ 2)⁻¹ + 6 * a ^ 2 * (log t ^ 1 / t) +
          108 / a * (log t ^ 3 / t) ≤ (C' / 18 + 6 * a ^ 2 + 108 / a) * e := by linarith
      have hp : 0 ≤ a⁻¹ * π ^ 2 := by positivity
      calc _ ≤ a⁻¹ * π ^ 2 * ((C' / 18 + 6 * a ^ 2 + 108 / a) * e) :=
            mul_le_mul_of_nonneg_left hsum hp
        _ = (K - 1) * e := by rw [hK]; ring
        _ ≤ K * e := by nlinarith
        _ = δ := by rw [he]; field_simp [hK0.ne']
    have hlog4 : log t ^ 1 / t ^ 4 ≤ log t ^ 1 / t := by
      apply div_le_div_of_nonneg_left (by positivity) ht0
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have expand : a⁻¹ * (π ^ 2 * (C' * t ^ 3 / (54 * log t ^ 3) + 2 * a ^ 2 / t +
        36 * t ^ 2 * log t ^ 2 / a)) * (3 * log t) =
        t ^ 3 * (a⁻¹ * π ^ 2 * (C' / 18 * (log t ^ 2)⁻¹ + 6 * a ^ 2 * (log t ^ 1 / t ^ 4) +
          108 / a * (log t ^ 3 / t))) := by
      have h1 : a ≠ 0 := ha.ne'
      have h2 : t ≠ 0 := ht0.ne'
      have h3 : log t ≠ 0 := hlt.ne'
      field_simp
      ring
    rw [expand]
    have hp : 0 ≤ a⁻¹ * π ^ 2 := by positivity
    have : a⁻¹ * π ^ 2 * (C' / 18 * (log t ^ 2)⁻¹ + 6 * a ^ 2 * (log t ^ 1 / t ^ 4) +
        108 / a * (log t ^ 3 / t)) ≤ δ := by
      refine le_trans ?_ key
      apply mul_le_mul_of_nonneg_left _ hp
      have := mul_le_mul_of_nonneg_left hlog4 (show (0 : ℝ) ≤ 6 * a ^ 2 by positivity)
      linarith
    calc t ^ 3 * (a⁻¹ * π ^ 2 * (C' / 18 * (log t ^ 2)⁻¹ + 6 * a ^ 2 * (log t ^ 1 / t ^ 4) +
          108 / a * (log t ^ 3 / t))) ≤ t ^ 3 * δ :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ * t ^ 3 := by ring
  calc a⁻¹ * ∫ β in (-Y)..Y, ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2
      ≤ a⁻¹ * (π ^ 2 * (C' * t ^ 3 / (54 * log t ^ 3) + 2 * a ^ 2 / t +
          36 * t ^ 2 * log t ^ 2 / a)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ δ * X / log X := hfin

end LeanLab.LZPowersOfTwo.Burst8P2

import LeanLab.Zhan1991.SingIntegral1122

/-!
P0068 Zhan 1991, page 271, the tail of the singular integral, `SingIntTail` of
SingIntegral1122.lean, the LEAF `singIntTail_leaf`.

Route: for `0 < |λ| ≤ 1/2` the geometric sum gives `|Σ e(nλ)| ≤ 1/|sin πλ| ≤ 1/(2|λ|)`.
Instead of Abel summation, `1/log n` is replaced by `1/log(N/3)` on the window, at a cost of
`12 U²/N` in total, so `|v(λ)| ≤ 1/(|λ| L) + 12 U²/N`. Then `|Re v³ e(-Nλ)| ≤ |v|³`, and the
integral over `L⁴/U ≤ |λ| ≤ 1/2` is at most `4 U² L⁻¹¹ + 4·1728 U⁶ N⁻³ ≪ U² L⁻⁴`.
`singIntTail_proof` is PROVED, no sorry. burst-20261122 1122d. AI wrote the Lean code.
Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real

noncomputable section

theorem sitail_ee_nat_mul (n : ℕ) (x : ℝ) : ee ((n : ℝ) * x) = ee x ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem sitail_norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem sitail_norm_ee_sub_one (x : ℝ) : ‖ee x - 1‖ = |2 * Real.sin (π * x)| := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = Complex.I * ((2 * π * x : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  congr 2; ring_nf

theorem sitail_sin_lower {x : ℝ} (hx : 0 < |x|) (hx2 : |x| ≤ 1 / 2) :
    2 * |x| ≤ |Real.sin (π * x)| := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ≤ Real.sin (π * y) := by
    intro y hy hy2
    have h := Real.mul_le_sin (x := π * y) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * y) = 2 * y := by field_simp
    linarith
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx2 ⊢
    exact (key x h hx2).trans (le_abs_self _)
  · rw [abs_of_neg h] at hx2 ⊢
    have := key (-x) (by linarith) hx2
    rw [show π * x = -(π * -x) by ring, Real.sin_neg, abs_neg]
    exact this.trans (le_abs_self _)

theorem sitail_geom (a b : ℕ) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, ee ((n : ℝ) * lam)‖ ≤ 1 / (2 * |lam|) := by
  have hpos : 0 < 1 / (2 * |lam|) := by positivity
  by_cases hab : a ≤ b + 1
  · simp_rw [sitail_ee_nat_mul]
    rw [← Finset.Ico_add_one_right_eq_Icc]
    have hg := geom_sum_Ico_mul (ee lam) hab
    have h1 : ‖(∑ i ∈ Finset.Ico a (b + 1), ee lam ^ i)‖ * ‖ee lam - 1‖ ≤ 2 := by
      rw [← norm_mul, hg]
      calc ‖ee lam ^ (b + 1) - ee lam ^ a‖ ≤ ‖ee lam ^ (b + 1)‖ + ‖ee lam ^ a‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_pow, sitail_norm_ee]; norm_num
    rw [sitail_norm_ee_sub_one] at h1
    have hs := sitail_sin_lower hl hl2
    have h2 : 4 * |lam| ≤ |2 * Real.sin (π * lam)| := by rw [abs_mul]; norm_num; linarith
    have hS := norm_nonneg (∑ i ∈ Finset.Ico a (b + 1), ee lam ^ i)
    rw [div_eq_mul_inv, one_mul, ← one_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [Finset.Icc_eq_empty (by omega)]; simp only [Finset.sum_empty, norm_zero]; exact hpos.le

/-- The window bound: `n` in the window of `vSum` lies within `U` of `N/3`. -/
theorem sitail_window {N : ℕ} {U : ℝ} (hU : 0 ≤ U) {n : ℕ}
    (hn : n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊) :
    (N : ℝ) / 3 - U ≤ n ∧ (n : ℝ) ≤ (N : ℝ) / 3 + U := by
  rw [Finset.mem_Icc] at hn
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hn.1)
  · exact (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by positivity))

theorem sitail_card (N : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    ((Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊).card : ℝ) ≤ 2 * U + 1 := by
  rw [Nat.card_Icc]
  set a := ⌈(N : ℝ) / 3 - U⌉₊
  set b := ⌊(N : ℝ) / 3 + U⌋₊
  have ha : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
  have hb : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by positivity)
  by_cases h : a ≤ b + 1
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [show b + 1 - a = 0 by omega]; simp; linarith

theorem sitail_one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have := Real.exp_one_lt_d9
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith)

theorem sitail_log_diff {x y D : ℝ} (hD : 0 < D) (hx : D ≤ x) (hy : D ≤ y) :
    |Real.log y - Real.log x| ≤ |y - x| / D := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : Real.log y - Real.log x ≤ (y - x) / x := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [sub_div, div_self hx0.ne']; exact this
  have h2 : Real.log x - Real.log y ≤ (x - y) / y := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [sub_div, div_self hy0.ne']; exact this
  have h3 : (y - x) / x ≤ |y - x| / D := by
    rcases le_or_gt 0 (y - x) with h | h
    · rw [abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hD hx
    · exact (div_neg_of_neg_of_pos h hx0).le.trans (by positivity)
  have h4 : (x - y) / y ≤ |y - x| / D := by
    rcases le_or_gt 0 (x - y) with h | h
    · rw [abs_sub_comm, abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hD hy
    · exact (div_neg_of_neg_of_pos h hy0).le.trans (by positivity)
  rw [abs_le]; constructor <;> linarith

/-- Pointwise bound `|v(λ)| ≤ 1/(|λ| L) + 12 U²/N`, page 271. -/
theorem sitail_vSum_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
    (hUN : 12 * U ≤ N) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
    ‖vSum N U lam‖ ≤ 1 / (|lam| * Real.log N) + 12 * U ^ 2 / N := by
  set L0 := Real.log ((N : ℝ) / 3)
  have hL0 : 1 ≤ L0 := sitail_one_le_log (by linarith)
  have hL : 2 * L0 ≥ Real.log N := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    norm_num
    nlinarith
  unfold vSum
  set S := Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊
  have hsplit : (∑ n ∈ S, ee ((n : ℝ) * lam) / (Real.log n : ℂ)) =
      (∑ n ∈ S, ee ((n : ℝ) * lam)) / (L0 : ℂ) +
        ∑ n ∈ S, ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  rw [hsplit]
  have hterm : ∀ n ∈ S, ‖ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ)‖ ≤
      4 * U / N := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := sitail_window (by linarith) hn
    rw [norm_mul, sitail_norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hn3 : (N : ℝ) / 4 ≤ n := by linarith
    have hln : 1 ≤ Real.log n := sitail_one_le_log (by linarith)
    have hd := sitail_log_diff (D := (N : ℝ) / 4) (by positivity) hn3
      (show (N : ℝ) / 4 ≤ (N : ℝ) / 3 by linarith)
    have hd2 : |(N : ℝ) / 3 - n| ≤ U := by rw [abs_le]; constructor <;> linarith
    have hd3 : |L0 - Real.log n| ≤ 4 * U / N := by
      refine hd.trans ?_
      rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    have : |1 / Real.log n - 1 / L0| ≤ |L0 - Real.log n| := by
      rw [div_sub_div _ _ (by linarith) (by linarith), abs_div, one_mul, mul_one,
        abs_of_pos (by positivity : 0 < Real.log n * L0)]
      exact div_le_self (abs_nonneg _) (by nlinarith)
    linarith
  have hsum := norm_sum_le_of_le S hterm
  have hcard := sitail_card N (show (0 : ℝ) ≤ U by linarith)
  have hgeo := sitail_geom ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊ hl hl2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  calc _ ≤ ‖(∑ n ∈ S, ee ((n : ℝ) * lam)) / (L0 : ℂ)‖ +
        ‖∑ n ∈ S, ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / (|lam| * Real.log N) + 12 * U ^ 2 / N := by
      gcongr
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        calc _ ≤ 1 / (2 * |lam|) / L0 := by gcongr
          _ ≤ _ := by
            rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
            nlinarith
      · refine hsum.trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        calc (S.card : ℝ) * (4 * U / N) ≤ (2 * U + 1) * (4 * U / N) := by gcongr
          _ ≤ 12 * U ^ 2 / N := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; nlinarith

theorem sitail_integrand_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
    (hUN : 12 * U ≤ N) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
    ‖singIntegrand N U lam‖ ≤
      4 * (1 / Real.log N) ^ 3 * (1 / |lam| ^ 3) + 4 * (12 * U ^ 2 / N) ^ 3 := by
  have hv := sitail_vSum_bound hN hU hUN hl hl2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  unfold singIntegrand
  rw [norm_mul, norm_pow, sitail_norm_ee, mul_one]
  set a := 1 / (|lam| * Real.log N)
  set b := 12 * U ^ 2 / N
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have h3 : ‖vSum N U lam‖ ^ 3 ≤ (a + b) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hv 3
  have h4 : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
  have h5 : a ^ 3 = (1 / Real.log N) ^ 3 * (1 / |lam| ^ 3) := by
    simp only [a]; ring
  rw [h5] at h4
  linarith

/-- Both tails, for a general cut `w`, page 271. -/
theorem sitail_tail_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
    (hUN : 12 * U ≤ N) {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 2) :
    |(∫ lam in (-(1 / 2 : ℝ))..(-w), singIntegrand N U lam).re +
      (∫ lam in w..(1 / 2), singIntegrand N U lam).re| ≤
      4 * (1 / Real.log N) ^ 3 / w ^ 2 + 4 * (12 * U ^ 2 / N) ^ 3 := by
  set A := (1 / Real.log N) ^ 3
  set B := (12 * U ^ 2 / N) ^ 3
  have hA : 0 ≤ A := by
    have : 0 < Real.log N := Real.log_pos (by linarith)
    positivity
  have hB : 0 ≤ B := by positivity
  set f := singIntegrand N U
  set g : ℝ → ℝ := fun x => 4 * A * x ^ (-3 : ℤ) + 4 * B
  have hpt : ∀ x ∈ Set.Ioc w (1 / 2), ‖f x‖ ≤ g x ∧ ‖f (-x)‖ ≤ g x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hz : x ^ (-3 : ℤ) = 1 / |x| ^ 3 := by
      rw [abs_of_pos hx0, zpow_neg, one_div]; norm_cast
    have e1 : 0 < |x| := by rw [abs_of_pos hx0]; exact hx0
    have e2 : |x| ≤ 1 / 2 := by rw [abs_of_pos hx0]; exact hx.2
    have e3 : 0 < |-x| := by rw [abs_neg]; exact e1
    have e4 : |-x| ≤ 1 / 2 := by rw [abs_neg]; exact e2
    have b1 := sitail_integrand_bound hN hU hUN e1 e2
    have b2 := sitail_integrand_bound hN hU hUN e3 e4
    rw [abs_neg] at b2
    simp only [g, hz]
    constructor
    · linarith
    · linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc w (1 / 2) := by
    rw [Set.uIcc_of_le hw]; intro h; linarith [h.1]
  have hzi : IntervalIntegrable (fun x : ℝ => x ^ (-3 : ℤ)) MeasureTheory.volume w (1 / 2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
  have hgi : IntervalIntegrable g MeasureTheory.volume w (1 / 2) :=
    (hzi.const_mul (4 * A)).add intervalIntegrable_const
  have h1 : ‖∫ x in w..(1 / 2), f x‖ ≤ ∫ x in w..(1 / 2), g x :=
    intervalIntegral.norm_integral_le_of_norm_le hw
      (Filter.Eventually.of_forall fun x hx => (hpt x hx).1) hgi
  have h2 : ‖∫ x in (-(1 / 2 : ℝ))..(-w), f x‖ ≤ ∫ x in w..(1 / 2), g x := by
    rw [← intervalIntegral.integral_comp_neg (a := w) (b := 1 / 2) (f := f)]
    exact intervalIntegral.norm_integral_le_of_norm_le hw
      (Filter.Eventually.of_forall fun x hx => (hpt x hx).2) hgi
  have hz : ∫ x in w..(1 / 2), x ^ (-3 : ℤ) = (1 / w ^ 2 - 4) / 2 := by
    rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩), show ((-3 : ℤ) + 1) = -2 by norm_num,
      zpow_neg, zpow_neg, zpow_two, zpow_two]
    push_cast
    field_simp
    try ring
  have hgv : ∫ x in w..(1 / 2), g x ≤ 2 * A / w ^ 2 + 2 * B := by
    simp only [g]
    rw [intervalIntegral.integral_add (hzi.const_mul (4 * A)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hz, intervalIntegral.integral_const, smul_eq_mul]
    have : 0 < w ^ 2 := by positivity
    have e : 4 * A * ((1 / w ^ 2 - 4) / 2) = 2 * A / w ^ 2 - 8 * A := by
      field_simp; try ring
    rw [e]
    nlinarith
  have hre : ∀ z : ℂ, |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm
  calc _ ≤ |(∫ lam in (-(1 / 2 : ℝ))..(-w), f lam).re| + |(∫ lam in w..(1 / 2), f lam).re| :=
        abs_add_le _ _
    _ ≤ ‖∫ lam in (-(1 / 2 : ℝ))..(-w), f lam‖ + ‖∫ lam in w..(1 / 2), f lam‖ :=
        add_le_add (hre _) (hre _)
    _ ≤ 2 * (2 * A / w ^ 2 + 2 * B) := by linarith
    _ = 4 * A / w ^ 2 + 4 * B := by ring

theorem sitail_eventually (r s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 1 ≤ x → Real.log x ^ r ≤ ε * x ^ s := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ((isLittleO_log_rpow_rpow_atTop r hs).bound hε)
  refine ⟨X, fun x hx h1 => ?_⟩
  have := hX x hx
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg h1) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at this

/-- Page 271, the tail of the singular integral `L⁴/U ≤ |λ| ≤ 1/2` is `O(U² L⁻⁴)`. PROVED. -/
theorem singIntTail_proof : SingIntTail := by
  intro c hc
  obtain ⟨X1, hX1⟩ := sitail_eventually (4 * c + 4) (1 / 2) 1 (by norm_num) one_pos
  obtain ⟨X2, hX2⟩ := sitail_eventually c (3 / 8) (1 / 12) (by norm_num) (by norm_num)
  obtain ⟨X3, hX3⟩ := sitail_eventually 4 (5 / 8) (1 / 2) (by norm_num) (by norm_num)
  refine ⟨4 + 4 * 1728, max (max X1 X2) (max X3 12), fun N hN => ?_⟩
  set x : ℝ := (N : ℝ)
  have hx12 : 12 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have h1 := hX1 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) hx1
  have h2 := hX2 x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hx1
  have h3 := hX3 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN) hx1
  rw [one_mul] at h1
  set L := Real.log x
  have hL1 : 1 ≤ L := sitail_one_le_log (by linarith)
  have hL0 : 0 < L := by linarith
  have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc.le
  have hx58 : 1 ≤ x ^ (5 / 8 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  set U := x ^ (5 / 8 : ℝ) * L ^ c
  have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le hx58 hLc
  have hU0 : 0 < U := by linarith
  have hxx : x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hUN : 12 * U ≤ x := by
    have : 12 * U = x ^ (5 / 8 : ℝ) * (12 * L ^ c) := by simp only [U]; ring
    rw [this]
    calc x ^ (5 / 8 : ℝ) * (12 * L ^ c) ≤ x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) := by
          gcongr; linarith
      _ = x := hxx
  have hL4 : L ^ (4 : ℝ) = L ^ 4 := by exact_mod_cast Real.rpow_natCast L 4
  have hLm4 : L ^ (-4 : ℝ) = (L ^ 4)⁻¹ := by rw [Real.rpow_neg hL0.le, hL4]
  have hw0 : 0 < L ^ (4 : ℝ) / U := by positivity
  have hw : L ^ (4 : ℝ) / U ≤ 1 / 2 := by
    rw [div_le_iff₀ hU0]
    have : x ^ (5 / 8 : ℝ) ≤ U := le_mul_of_one_le_right (by positivity) hLc
    linarith
  refine (sitail_tail_bound hx12 hU1 hUN hw0 hw).trans ?_
  rw [hLm4, hL4]
  -- first term
  have t1 : 4 * (1 / L) ^ 3 / (L ^ 4 / U) ^ 2 ≤ 4 * U ^ 2 * (L ^ 4)⁻¹ := by
    have e : 4 * (1 / L) ^ 3 / (L ^ 4 / U) ^ 2 = 4 * U ^ 2 * (L ^ 4)⁻¹ * (L ^ 7)⁻¹ := by
      field_simp
    rw [e]
    have : (L ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have : 0 ≤ 4 * U ^ 2 * (L ^ 4)⁻¹ := by positivity
    nlinarith
  -- second term
  have hU4 : U ^ 4 * L ^ 4 ≤ x ^ 3 := by
    have e1 : (x ^ (5 / 8 : ℝ)) ^ 4 = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (x ^ (5 / 8 : ℝ)) 4, ← Real.rpow_mul hx0.le]; norm_num
    have e2 : (L ^ c) ^ 4 * L ^ 4 = L ^ (4 * c + 4) := by
      rw [← Real.rpow_natCast (L ^ c) 4, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 4,
        ← Real.rpow_add hL0]
      congr 1; push_cast; ring
    have e3 : x ^ (5 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ 3 := by
      rw [← Real.rpow_add hx0]; norm_num
    have : U ^ 4 * L ^ 4 = x ^ (5 / 2 : ℝ) * L ^ (4 * c + 4) := by
      simp only [U]; rw [mul_pow, e1, mul_assoc, e2]
    rw [this, ← e3]
    gcongr
  have t2 : 4 * (12 * U ^ 2 / x) ^ 3 ≤ 4 * 1728 * U ^ 2 * (L ^ 4)⁻¹ := by
    have e : 4 * (12 * U ^ 2 / x) ^ 3 = 4 * 1728 * U ^ 2 * (U ^ 4 / x ^ 3) := by
      field_simp; try ring
    rw [e]
    have : U ^ 4 / x ^ 3 ≤ (L ^ 4)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      calc U ^ 4 = U ^ 4 * L ^ 4 * (L ^ 4)⁻¹ := by field_simp
        _ ≤ x ^ 3 * (L ^ 4)⁻¹ := by gcongr
        _ = _ := by ring
    have : 0 ≤ 4 * 1728 * U ^ 2 := by positivity
    nlinarith
  have : (4 + 4 * 1728 : ℝ) * U ^ 2 * (L ^ 4)⁻¹ =
      4 * U ^ 2 * (L ^ 4)⁻¹ + 4 * 1728 * U ^ 2 * (L ^ 4)⁻¹ := by ring
  rw [this]
  linarith

end

end LeanLab.Zhan1991

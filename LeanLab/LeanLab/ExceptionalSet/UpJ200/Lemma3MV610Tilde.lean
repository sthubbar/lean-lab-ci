import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral

/-!
# P0015 display (6.1̃0), page 364: the arc integrals of `T̃²` and `T T̃`

Burst burst-20261122, step mv610_tilde, run by a Claude cloud session S112.

Source P0015, Montgomery and Vaughan 1975, page 364, display (6.1̃0). By partial summation
`T̃(η) ≪ ‖η‖⁻¹`, since the coefficients `k^{β̃-1}` lie in `(0,1]` and decrease for `β̃ ≤ 1`;
with `T(η) ≪ ‖η‖⁻¹` from (6.10), the integrals of `|T̃|²` and `|T T̃|` over
`1/qQ ≤ |η| ≤ 1/2` are `≪ qQ`, and by periodicity the full integral over `[0,1]` equals the one
over `[-1/2,1/2]`.

* PROVED `mv_610_tilde_sq_proved`, twin of `Lemma3MV617Integral.mv_610_tilde_sq`.
* PROVED `mv_610_tilde_cross_proved`, twin of `Lemma3MV617Integral.mv_610_tilde_cross`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV610Tilde

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (T)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral

/-- Partial summation, as used on page 364 for (6.1̃0): if `f` is nonnegative and decreasing and
every initial partial sum of `g` has norm at most `M`, then `‖Σ_{i<n} f i g i‖ ≤ f 0 M`. PROVED. -/
theorem abel_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (M : ℝ) (n : ℕ)
    (hf0 : ∀ i, 0 ≤ f i) (hfa : ∀ i, f (i + 1) ≤ f i)
    (hG : ∀ m, ‖∑ i ∈ range m, g i‖ ≤ M) :
    ‖∑ i ∈ range n, (f i : ℂ) * g i‖ ≤ f 0 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hG 0)
  have hsm : ∀ i, (f i : ℂ) * g i = f i • g i := fun i => by rw [Complex.real_smul]
  simp_rw [hsm]
  rw [Finset.sum_range_by_parts]
  have h1 : ∀ i ∈ range (n - 1),
      ‖(f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤ (f i - f (i + 1)) * M := by
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hfa i])]
    have := hG (i + 1)
    have : 0 ≤ -(f (i + 1) - f i) := by linarith [hfa i]
    nlinarith
  calc _ ≤ ‖f (n - 1) • ∑ i ∈ range n, g i‖ +
        ‖∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ := norm_sub_le _ _
    _ ≤ f (n - 1) * M + ∑ i ∈ range (n - 1), (f i - f (i + 1)) * M := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
          exact mul_le_mul_of_nonneg_left (hG n) (hf0 _)
        · exact (norm_sum_le _ _).trans (sum_le_sum h1)
    _ = f 0 * M := by
        rw [← Finset.sum_mul, Finset.sum_range_sub' f (n - 1)]; ring

/-- `T(η) ≪ ‖η‖⁻¹` for any range of summation, P0015 (6.10). PROVED. -/
theorem T_sum_bound (A B : ℕ) (η : ℝ) (h0 : 0 < |η|) (h1 : |η| ≤ 1 / 2) :
    ‖∑ m ∈ Ioc A B, eC (η * m)‖ ≤ 1 / (2 * |η|) := by
  rcases le_or_gt A B with hAB | hAB
  · exact Lemma2MV.arc611_T_bound A B hAB η h0 h1
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]; positivity

/-- P0015 page 364, partial summation: `T̃(η) ≪ ‖η‖⁻¹`, precisely `|T̃(η)| ≤ 1/(2|η|)` for
`β̃ ≤ 1`. PROVED. -/
theorem Ttilde_bound (β P X η : ℝ) (hβ : β ≤ 1) (h0 : 0 < |η|) (h1 : |η| ≤ 1 / 2) :
    ‖Ttilde β P X η‖ ≤ 1 / (2 * |η|) := by
  set A := ⌊P⌋₊
  set B := ⌊X⌋₊
  have hI : Ioc A B = Ico (A + 1) (B + 1) := by ext; simp
  unfold Ttilde
  rw [norm_neg, hI, Finset.sum_Ico_eq_sum_range]
  set f : ℕ → ℝ := fun i => ((A + 1 + i : ℕ) : ℝ) ^ (β - 1) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (by positivity) _
  have hfa : ∀ i, f (i + 1) ≤ f i := by
    intro i
    simp only [hf]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  have hG : ∀ m, ‖∑ i ∈ range m, eC (η * ((A + 1 + i : ℕ) : ℝ))‖ ≤ 1 / (2 * |η|) := by
    intro m
    have e : ∑ i ∈ range m, eC (η * ((A + 1 + i : ℕ) : ℝ)) = ∑ k ∈ Ioc A (A + m), eC (η * k) := by
      rw [show Ioc A (A + m) = Ico (A + 1) (A + m + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
        show A + m + 1 - (A + 1) = m by omega]
    rw [e]; exact T_sum_bound A (A + m) η h0 h1
  have key := abel_bound f (fun i => eC (η * ((A + 1 + i : ℕ) : ℝ))) (1 / (2 * |η|))
    (B + 1 - (A + 1)) hf0 hfa hG
  have hf1 : f 0 ≤ 1 := by
    simp only [hf]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by push_cast; linarith) (by linarith)
  calc _ = ‖∑ i ∈ range (B + 1 - (A + 1)), (f i : ℂ) * eC (η * ((A + 1 + i : ℕ) : ℝ))‖ := rfl
    _ ≤ f 0 * (1 / (2 * |η|)) := key
    _ ≤ 1 * (1 / (2 * |η|)) := by gcongr
    _ = _ := one_mul _

/-- `|e(x)| = 1`. PROVED. -/
theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [show (2 * π * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `e(x + m) = e(x)` for integers `m`. PROVED. -/
theorem eC_add_int (x : ℝ) (m : ℤ) : eC (x + m) = eC x := by
  unfold eC
  rw [show (2 * π * Complex.I * ((x + m : ℝ) : ℂ)) =
    2 * π * Complex.I * (x : ℂ) + m * (2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The frequencies are integers, so `η ↦ e(ηk)` has period one. PROVED. -/
theorem eC_mul_nat_periodic (k : ℕ) (η : ℝ) : eC ((η + 1) * k) = eC (η * k) := by
  rw [show (η + 1) * (k : ℝ) = η * k + ((k : ℤ) : ℝ) by push_cast; ring, eC_add_int]

theorem eC_neg_periodic (n : ℕ) (η : ℝ) : eC (-((η + 1) * n)) = eC (-(η * n)) := by
  rw [show -((η + 1) * (n : ℝ)) = -(η * n) + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, eC_add_int]

theorem Ttilde_periodic (β P X : ℝ) : Function.Periodic (Ttilde β P X) 1 := by
  intro η; unfold Ttilde; simp_rw [eC_mul_nat_periodic]

theorem T_periodic (P X : ℝ) : Function.Periodic (T P X) 1 := by
  intro η; unfold T; simp_rw [eC_mul_nat_periodic]

theorem cont_Ttilde (β P X : ℝ) : Continuous (Ttilde β P X) := by
  unfold Ttilde
  exact (continuous_finsetSum _ fun j _ => continuous_const.mul (cont_eC _)).neg

theorem cont_T (P X : ℝ) : Continuous (T P X) := by
  unfold T
  exact continuous_finsetSum _ fun j _ => cont_eC _

theorem cont_eCn (n : ℕ) : Continuous fun η : ℝ => eC (-(η * n)) := by
  unfold eC; fun_prop

/-- Periodicity: the integral over `[0,1]` equals the integral over `[-1/2,1/2]`. PROVED. -/
theorem int01_eq_half (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    ∫ η in (0 : ℝ)..1, f η = ∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η := by
  have := hf.intervalIntegral_add_eq 0 (-(1 / 2))
  rw [zero_add] at this
  rw [this]; norm_num

/-- P0015 (6.10) and (6.1̃0), page 364: an integrand bounded by `‖η‖⁻²/4` on `0 < |η| ≤ 1/2`
has arc integral over `|η| ≤ r` within `r⁻¹/2` of its integral over `[-1/2,1/2]`. PROVED. -/
theorem arc_tail_generic (f : ℝ → ℂ) (hfc : Continuous f)
    (hb : ∀ η : ℝ, 0 < |η| → |η| ≤ 1 / 2 → ‖f η‖ ≤ 1 / 4 * η ^ (-2 : ℤ))
    (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 1 / 2) :
    ‖(∫ η in (-r)..r, f η) - ∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η‖ ≤ 1 / 2 * r⁻¹ := by
  have hii : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hfc.intervalIntegrable a b
  have hsplit : (∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η) =
      (∫ η in (-(1 / 2) : ℝ)..(-r), f η) + (∫ η in (-r)..r, f η) + ∫ η in r..(1 / 2), f η := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have tail : ∀ a b : ℝ, a ≤ b → (0 : ℝ) ∉ Set.uIcc a b →
      (∀ η ∈ Set.Ioc a b, 0 < |η| ∧ |η| ≤ 1 / 2) →
      ‖∫ η in a..b, f η‖ ≤ 1 / 4 * (a⁻¹ - b⁻¹) := by
    intro a b hab h0 hη
    have hg : IntervalIntegrable (fun η : ℝ => 1 / 4 * η ^ (-2 : ℤ)) MeasureTheory.volume a b :=
      (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul _
    refine (intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun η hm => hb η (hη η hm).1 (hη η hm).2) hg).trans
      (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
    norm_num
    ring
  have hL := tail (-(1 / 2)) (-r) (by linarith)
    (by rw [Set.uIcc_of_le (by linarith)]; intro h; simp only [Set.mem_Icc] at h; linarith)
    (by
      intro η hm; simp only [Set.mem_Ioc] at hm
      rw [abs_of_neg (by linarith)]; constructor <;> linarith)
  have hR := tail r (1 / 2) hr
    (by rw [Set.uIcc_of_le hr]; intro h; simp only [Set.mem_Icc] at h; linarith)
    (by
      intro η hm; simp only [Set.mem_Ioc] at hm
      rw [abs_of_pos (by linarith)]; constructor <;> linarith)
  have hmid : (∫ η in (-r)..r, f η) - ∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η =
      -((∫ η in (-(1 / 2) : ℝ)..(-r), f η) + ∫ η in r..(1 / 2), f η) := by
    rw [hsplit]; ring
  rw [hmid, norm_neg]
  calc _ ≤ ‖∫ η in (-(1 / 2) : ℝ)..(-r), f η‖ + ‖∫ η in r..(1 / 2), f η‖ := norm_add_le _ _
    _ ≤ 1 / 4 * ((-(1 / 2))⁻¹ - (-r)⁻¹) + 1 / 4 * (r⁻¹ - (1 / 2)⁻¹) := by gcongr
    _ ≤ _ := by rw [inv_neg, inv_neg]; norm_num; linarith

/-- The square of the bound `1/(2|η|)`. PROVED. -/
theorem sq_bound (η : ℝ) (h0 : 0 < |η|) : 1 / (2 * |η|) * (1 / (2 * |η|)) = 1 / 4 * η ^ (-2 : ℤ) := by
  rw [zpow_neg, zpow_two, ← abs_mul_self η, abs_mul]
  have : |η| ≠ 0 := h0.ne'
  field_simp
  ring

/-- The size of the arc: for `X ≥ 36`, `θ < 6/100` and `q ≥ 1`, `0 < P/(qX) ≤ 1/2`. PROVED. -/
theorem arc_radius (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 6 / 100) (X : ℝ) (hX : 36 ≤ X)
    (q : ℕ) (hq : 1 ≤ q) : 0 < X ^ θ / (q * X) ∧ X ^ θ / (q * X) ≤ 1 / 2 := by
  set P := X ^ θ with hP
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hX1 (by linarith)
  have hP4 : P ^ 4 ≤ X := by
    rw [hP, ← Real.rpow_mul_natCast hX0.le]
    calc X ^ (θ * ((4 : ℕ) : ℝ)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by push_cast; linarith)
      _ = X := Real.rpow_one X
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP2 : 6 * P ^ 2 ≤ X := by nlinarith [sq_nonneg (6 * P ^ 2 - X), sq_nonneg (6 * P ^ 2 + X)]
  have h2 : 2 * P ≤ X := by nlinarith
  have h3 : X ≤ q * X := by nlinarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]; linarith

/-- The common final step of both displays. PROVED. -/
theorem arc_final (F : ℝ → ℂ) (hFc : Continuous F) (hFp : Function.Periodic F 1)
    (hb : ∀ η : ℝ, 0 < |η| → |η| ≤ 1 / 2 → ‖F η‖ ≤ 1 / 4 * η ^ (-2 : ℤ))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 6 / 100) (X : ℝ) (hX : 36 ≤ X) (q : ℕ) (hq : 1 ≤ q) :
    ‖(∫ η in (-(X ^ θ / (q * X)))..(X ^ θ / (q * X)), F η) - ∫ η in (0 : ℝ)..1, F η‖ ≤
      1 * q * (X / X ^ θ) := by
  obtain ⟨hr0, hr⟩ := arc_radius θ hθ0 hθ1 X hX q hq
  rw [int01_eq_half F hFp]
  refine (arc_tail_generic F hFc hb _ hr0 hr).trans ?_
  have h0 : 0 ≤ (q : ℝ) * X / X ^ θ := by have : (0 : ℝ) < X := by linarith
                                          positivity
  have e : (1 : ℝ) * q * (X / X ^ θ) = q * X / X ^ θ := by ring
  rw [inv_div, e]; linarith

/-- P0015 display (6.1̃0), first integral, the exact type of
`Lemma3MV617Integral.mv_610_tilde_sq`. PROVED. -/
theorem mv_610_tilde_sq_proved : type_of% @Lemma3MV617Integral.mv_610_tilde_sq := by
  refine ⟨1, one_pos, fun θ hθ0 hθ1 => ⟨36, fun X hX β hβ q hq _ n _ _ => ?_⟩⟩
  set F : ℝ → ℂ := fun η => Ttilde β (X ^ θ) X η ^ 2 * eC (-(η * n)) with hF
  have hFc : Continuous F := ((cont_Ttilde _ _ _).pow 2).mul (cont_eCn n)
  have hFp : Function.Periodic F 1 := by
    intro η; simp only [hF]; rw [Ttilde_periodic β (X ^ θ) X η, eC_neg_periodic]
  have hb : ∀ η : ℝ, 0 < |η| → |η| ≤ 1 / 2 → ‖F η‖ ≤ 1 / 4 * η ^ (-2 : ℤ) := by
    intro η h0 h1
    simp only [hF]
    rw [norm_mul, norm_eC, mul_one, norm_pow, sq, ← sq_bound η h0]
    have := Ttilde_bound β (X ^ θ) X η hβ h0 h1
    exact mul_le_mul this this (norm_nonneg _) (by positivity)
  exact arc_final F hFc hFp hb θ hθ0 hθ1 X hX q hq

/-- P0015 display (6.1̃0), second integral, the exact type of
`Lemma3MV617Integral.mv_610_tilde_cross`. PROVED. -/
theorem mv_610_tilde_cross_proved : type_of% @Lemma3MV617Integral.mv_610_tilde_cross := by
  refine ⟨1, one_pos, fun θ hθ0 hθ1 => ⟨36, fun X hX β hβ q hq _ n _ _ => ?_⟩⟩
  set F : ℝ → ℂ := fun η => T (X ^ θ) X η * Ttilde β (X ^ θ) X η * eC (-(η * n)) with hF
  have hFc : Continuous F := ((cont_T _ _).mul (cont_Ttilde _ _ _)).mul (cont_eCn n)
  have hFp : Function.Periodic F 1 := by
    intro η; simp only [hF]
    rw [T_periodic (X ^ θ) X η, Ttilde_periodic β (X ^ θ) X η, eC_neg_periodic]
  have hb : ∀ η : ℝ, 0 < |η| → |η| ≤ 1 / 2 → ‖F η‖ ≤ 1 / 4 * η ^ (-2 : ℤ) := by
    intro η h0 h1
    simp only [hF]
    rw [norm_mul, norm_eC, mul_one, norm_mul, ← sq_bound η h0]
    have h2 := Ttilde_bound β (X ^ θ) X η hβ h0 h1
    have h3 : ‖T (X ^ θ) X η‖ ≤ 1 / (2 * |η|) := by
      unfold T; exact T_sum_bound _ _ η h0 h1
    exact mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
  exact arc_final F hFc hFp hb θ hθ0 hθ1 X hX q hq

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV610Tilde

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV610Tilde.mv_610_tilde_sq_proved
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV610Tilde.mv_610_tilde_cross_proved

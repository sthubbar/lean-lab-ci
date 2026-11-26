import Mathlib
import LeanLab.ExceptionalSet.State1539Data264

/-!
# P0015 displays 6.10 and 6.11, the main term of one major arc

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, 353-370, page 363, displays 6.10 and 6.11.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MV

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

/-- P0015 page 363, display 6.10: the additive character is a homomorphism. -/
theorem arc611_eC_add (a b : ℝ) : eC a * eC b = eC (a + b) := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- P0015 page 363, display 6.11: over one period the character integrates to the indicator
of zero. -/
theorem arc611_int_eC (k : ℤ) :
    ∫ η in (-(1 / 2) : ℝ)..(1 / 2), eC (η * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]; norm_num
  · have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [Complex.I_ne_zero, hpi, this]
    have hfun : (fun η : ℝ => eC (η * k)) =
        fun η : ℝ => Complex.exp ((2 * π * Complex.I * k) * η) := by
      funext η; unfold eC; congr 1; push_cast; ring
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * k * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * k * ((-(1 / 2) : ℝ) : ℂ)) *
          Complex.exp (k * (2 * π * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I]; simp

/-- P0015 page 363: the integrand of 6.10 is continuous. -/
theorem arc611_cont_eC (c : ℝ) : Continuous fun η : ℝ => eC (η * c) := by
  unfold eC; fun_prop


/-- P0015 page 363: the square of `T` times `e(-nη)` expands into a double sum of characters. -/
theorem arc611_expand (S : Finset ℕ) (n : ℕ) (η : ℝ) :
    (∑ m ∈ S, eC (η * m)) ^ 2 * eC (-(η * n)) =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, eC (η * (((m₁ : ℤ) + m₂ - n : ℤ) : ℝ)) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [arc611_eC_add, arc611_eC_add]; congr 1; push_cast; ring

/-- P0015 page 363: the count of representations `m₁ + m₂ = n` with `A < mᵢ ≤ B`. -/
theorem arc611_card (A B n : ℕ) (hn : n ≤ B) :
    #((Ioc A B ×ˢ Ioc A B).filter (fun x : ℕ × ℕ => x.1 + x.2 = n)) = n - A - A - 1 := by
  rw [← Nat.card_Ioo A (n - A)]
  refine Finset.card_nbij' (fun x => x.1) (fun m => (m, n - m)) ?_ ?_ ?_ ?_
  · intro x hx; simp only [coe_filter, mem_product, mem_Ioc, Set.mem_ofPred_eq] at hx
    simp only [coe_Ioo, Set.mem_Ioo]; omega
  · intro m hm; simp only [coe_Ioo, Set.mem_Ioo] at hm
    simp only [coe_filter, mem_product, mem_Ioc, Set.mem_ofPred_eq]; omega
  · intro x hx; simp only [coe_filter, mem_product, mem_Ioc, Set.mem_ofPred_eq] at hx
    ext <;> simp; omega
  · intro m hm; simp

/-- P0015 display 6.11, page 363: the integral over a full period counts the representations. -/
theorem arc611_period (A B n : ℕ) (hn : n ≤ B) :
    ∫ η in (-(1 / 2) : ℝ)..(1 / 2), (∑ m ∈ Ioc A B, eC (η * m)) ^ 2 * eC (-(η * n)) =
      ((n - A - A - 1 : ℕ) : ℂ) := by
  simp_rw [arc611_expand]
  rw [intervalIntegral.integral_finsetSum]
  swap; · intro i _; exact (continuous_finsetSum _ fun j _ => arc611_cont_eC _).intervalIntegrable _ _
  have : ∀ m₁ ∈ Ioc A B, (∫ η in (-(1 / 2) : ℝ)..(1 / 2),
      ∑ m₂ ∈ Ioc A B, eC (η * (((m₁ : ℤ) + m₂ - n : ℤ) : ℝ))) =
        ∑ m₂ ∈ Ioc A B, if m₁ + m₂ = n then (1 : ℂ) else 0 := by
    intro m₁ _
    rw [intervalIntegral.integral_finsetSum]
    swap; · intro j _; exact (arc611_cont_eC _).intervalIntegrable _ _
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [arc611_int_eC]
    congr 1; apply propext; omega
  rw [Finset.sum_congr rfl this, ← Finset.sum_product', Finset.sum_boole, arc611_card A B n hn]


/-- P0015 page 363, the bound `|e(η) - 1| ≥ 4|η|` for `|η| ≤ 1/2` used for 6.10. -/
theorem arc611_sub_one (η : ℝ) (h1 : |η| ≤ 1 / 2) : 4 * |η| ≤ ‖eC η - 1‖ := by
  have he : eC η = Complex.exp (Complex.I * ((2 * π * η : ℝ) : ℂ)) := by
    unfold eC; congr 1; push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpi := Real.pi_pos
  have key : 2 * |η| ≤ |Real.sin (2 * π * η / 2)| := by
    rw [show 2 * π * η / 2 = π * η by ring]
    rcases le_or_gt 0 η with h | h
    · rw [abs_of_nonneg h] at h1 ⊢
      have := Real.mul_le_sin (x := π * η) (by positivity) (by nlinarith)
      have e : 2 / π * (π * η) = 2 * η := by field_simp
      rw [e] at this; rw [abs_of_nonneg (by linarith)]; exact this
    · rw [abs_of_neg h] at h1 ⊢
      have := Real.mul_le_sin (x := π * -η) (by nlinarith) (by nlinarith)
      have e : 2 / π * (π * -η) = 2 * -η := by field_simp
      rw [e] at this
      rw [show π * η = -(π * -η) by ring, Real.sin_neg, abs_neg, abs_of_nonneg (by linarith)]
      exact this
  have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [this]; linarith

/-- P0015 display 6.10, page 363: `T(η) ≪ ‖η‖⁻¹`, precisely `|T(η)| ≤ 1/(2|η|)`. -/
theorem arc611_T_bound (A B : ℕ) (hAB : A ≤ B) (η : ℝ) (h0 : 0 < |η|) (h1 : |η| ≤ 1 / 2) :
    ‖∑ m ∈ Ioc A B, eC (η * m)‖ ≤ 1 / (2 * |η|) := by
  set z := eC η with hz
  have hpow : ∀ m : ℕ, eC (η * m) = z ^ m := by
    intro m; rw [hz]; unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz1 : ‖z‖ = 1 := by
    rw [hz]; unfold eC
    rw [show (2 * π * Complex.I * (η : ℂ)) = ((2 * π * η : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsub := arc611_sub_one η h1
  have hpos : 0 < ‖z - 1‖ := by linarith
  have hne : z ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  have hI : Ioc A B = Ico (A + 1) (B + 1) := by ext; simp
  simp_rw [hpow]
  rw [hI, geom_sum_Ico hne (by omega), norm_div]
  have hnum : ‖z ^ (B + 1) - z ^ (A + 1)‖ ≤ 2 := by
    calc _ ≤ ‖z ^ (B + 1)‖ + ‖z ^ (A + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hz1]; norm_num
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith


/-- P0015 display 6.10, page 363: the square of the bound `T(η) ≪ ‖η‖⁻¹` on the integrand. -/
theorem arc611_pointwise (A B n : ℕ) (hAB : A ≤ B) (η : ℝ) (h0 : 0 < |η|) (h1 : |η| ≤ 1 / 2) :
    ‖(∑ m ∈ Ioc A B, eC (η * m)) ^ 2 * eC (-(η * n))‖ ≤ 1 / 4 * η ^ (-2 : ℤ) := by
  have hT := arc611_T_bound A B hAB η h0 h1
  have he : ‖eC (-(η * n))‖ = 1 := by
    unfold eC
    rw [show (2 * π * Complex.I * ((-(η * n) : ℝ) : ℂ)) =
      ((2 * π * -(η * n) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, he, mul_one, norm_pow]
  have hb : 1 / 4 * η ^ (-2 : ℤ) = (1 / (2 * |η|)) ^ 2 := by
    rw [zpow_neg, zpow_two, div_pow, mul_pow, sq_abs]; field_simp; norm_num
  rw [hb]
  exact pow_le_pow_left₀ (norm_nonneg _) hT 2

/-- P0015 display 6.10, page 363: the integral of `|T|²` away from the arc is `≪ qQ`. -/
theorem arc611_tail (A B n : ℕ) (hAB : A ≤ B) (a b : ℝ) (hab : a ≤ b) (h0 : (0 : ℝ) ∉ Set.uIcc a b)
    (hη : ∀ η ∈ Set.Ioc a b, 0 < |η| ∧ |η| ≤ 1 / 2) :
    ‖∫ η in a..b, (∑ m ∈ Ioc A B, eC (η * m)) ^ 2 * eC (-(η * n))‖ ≤ 1 / 4 * (a⁻¹ - b⁻¹) := by
  have hg : IntervalIntegrable (fun η : ℝ => 1 / 4 * η ^ (-2 : ℤ)) MeasureTheory.volume a b :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul _
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun η hm => arc611_pointwise A B n hAB η (hη η hm).1 (hη η hm).2)
    hg).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  ring


/-- P0015 displays 6.10 and 6.11, page 363, for a general arc half width `r`: the arc integral
differs from `n` by at most `2A + 1 + 1/(2r)`. -/
theorem arc611_arc_bound (A B n : ℕ) (hAB : A ≤ B) (hn : n ≤ B) (r : ℝ) (hr0 : 0 < r)
    (hr : r ≤ 1 / 2) :
    ‖(∫ η in (-r)..r, (∑ m ∈ Ioc A B, eC (η * m)) ^ 2 * eC (-(η * n))) - (n : ℂ)‖ ≤
      (2 * A + 1 : ℝ) + 1 / 2 * r⁻¹ := by
  set f : ℝ → ℂ := fun η => (∑ m ∈ Ioc A B, eC (η * m)) ^ 2 * eC (-(η * n)) with hf
  have hfc : Continuous f := by
    rw [hf]
    exact ((continuous_finsetSum _ fun j _ => arc611_cont_eC _).pow 2).mul
      (by simpa using arc611_cont_eC (-(n : ℝ)))
  have hii : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hfc.intervalIntegrable a b
  have hsplit : (∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η) =
      (∫ η in (-(1 / 2) : ℝ)..(-r), f η) + (∫ η in (-r)..r, f η) + ∫ η in r..(1 / 2), f η := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have hfull : (∫ η in (-(1 / 2) : ℝ)..(1 / 2), f η) = ((n - A - A - 1 : ℕ) : ℂ) :=
    arc611_period A B n hn
  have hL := arc611_tail A B n hAB (-(1 / 2)) (-r) (by linarith)
    (by rw [Set.uIcc_of_le (by linarith)]; intro h; simp only [Set.mem_Icc] at h; linarith)
    (by
      intro η hm; simp only [Set.mem_Ioc] at hm
      rw [abs_of_neg (by linarith)]; constructor <;> linarith)
  have hR := arc611_tail A B n hAB r (1 / 2) hr
    (by rw [Set.uIcc_of_le hr]; intro h; simp only [Set.mem_Icc] at h; linarith)
    (by
      intro η hm; simp only [Set.mem_Ioc] at hm
      rw [abs_of_pos (by linarith)]; constructor <;> linarith)
  have hmid : (∫ η in (-r)..r, f η) - (n : ℂ) =
      (((n - A - A - 1 : ℕ) : ℂ) - n) - (∫ η in (-(1 / 2) : ℝ)..(-r), f η) -
        ∫ η in r..(1 / 2), f η := by
    rw [← hfull, hsplit]; ring
  have hcount : ‖((n - A - A - 1 : ℕ) : ℂ) - n‖ ≤ 2 * A + 1 := by
    have e : ((n - A - A - 1 : ℕ) : ℂ) - n = (((n - A - A - 1 : ℕ) : ℤ) - n : ℤ) := by push_cast; ring
    rw [e, Complex.norm_intCast, abs_le]
    constructor
    · have : (n : ℤ) ≤ ((n - A - A - 1 : ℕ) : ℤ) + 2 * A + 1 := by omega
      have : ((n : ℤ) : ℝ) ≤ (((n - A - A - 1 : ℕ) : ℤ) : ℝ) + 2 * A + 1 := by exact_mod_cast this
      push_cast at this ⊢; linarith
    · have : ((n - A - A - 1 : ℕ) : ℤ) ≤ n := by omega
      have : (((n - A - A - 1 : ℕ) : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢; have : (0 : ℝ) ≤ A := by positivity
      linarith
  rw [hmid]
  have hr2 : (2 : ℝ)⁻¹ ≤ r⁻¹ := by rw [inv_le_inv₀ (by norm_num) hr0]; linarith
  calc _ ≤ ‖((n - A - A - 1 : ℕ) : ℂ) - n‖ + ‖∫ η in (-(1 / 2) : ℝ)..(-r), f η‖ +
        ‖∫ η in r..(1 / 2), f η‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ (2 * A + 1) + 1 / 4 * ((-(1 / 2))⁻¹ - (-r)⁻¹) + 1 / 4 * (r⁻¹ - (1 / 2)⁻¹) := by
        gcongr
    _ ≤ _ := by rw [inv_neg, inv_neg]; norm_num; linarith


/-- P0015 displays 6.10 and 6.11, page 363, the leaf `mv_arc_main_611` of `Lemma2MVSplit`
with `T` and `arcIntegral` unfolded: for `q ≤ P = X^{6δ}` and `1 ≤ n ≤ X`, the integral of
`T(η)² e(-nη)` over `|η| ≤ 1/(qQ) = P/(qX)` is `n + O(qX/P)`, with constant `1` and `X₀ = 36`. -/
theorem arc611_main : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (6 * δ) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖(∫ η in (-(X ^ (6 * δ) / (q * X)))..(X ^ (6 * δ) / (q * X)),
            (∑ m ∈ Finset.Ioc ⌊X ^ (6 * δ)⌋₊ ⌊X⌋₊, LeanLab.ExceptionalSet.U1539.eC (η * m)) ^ 2 *
              LeanLab.ExceptionalSet.U1539.eC (-(η * n))) - (n : ℂ)‖ ≤
          C * q * (X / X ^ (6 * δ)) := by
  refine ⟨1, one_pos, fun δ hδ0 hδ1 => ⟨36, fun X hX q hq _ n _ hnX => ?_⟩⟩
  set P := X ^ (6 * δ) with hP
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hX1 (by linarith)
  have hP4 : P ^ 4 ≤ X := by
    rw [hP, ← Real.rpow_mul_natCast hX0.le]
    calc X ^ (6 * δ * ((4 : ℕ) : ℝ)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by push_cast; linarith)
      _ = X := Real.rpow_one X
  have hP2 : 6 * P ^ 2 ≤ X := by nlinarith [sq_nonneg (6 * P ^ 2 - X), sq_nonneg (6 * P ^ 2 + X)]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set r := P / (q * X) with hr
  have hr0 : 0 < r := by positivity
  have hrle : r ≤ 1 / 2 := by
    rw [hr, div_le_iff₀ (by positivity)]; nlinarith
  have hAP : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hAB : ⌊P⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (by nlinarith)
  have hnB : n ≤ ⌊X⌋₊ := Nat.le_floor hnX
  have key := arc611_arc_bound ⌊P⌋₊ ⌊X⌋₊ n hAB hnB r hr0 hrle
  refine key.trans ?_
  have hrinv : r⁻¹ = q * (X / P) := by rw [hr, inv_div]; ring
  rw [hrinv]
  have hXP : 6 * P ≤ X / P := by rw [le_div_iff₀ (by linarith)]; nlinarith
  have hqXP : X / P ≤ q * (X / P) := by
    have : 0 ≤ X / P := by positivity
    nlinarith
  nlinarith

end LeanLab.ExceptionalSet.UpJ200.Lemma2MV

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MV.arc611_main

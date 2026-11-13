import LeanLab.MissingDigit.Burst8P2

/-!
# Burst 8, an L¹ bound of Lemma 1.7 type for the missing digit set

Paper: P0057, J. Kim, arXiv 2412.19975v1, Lemma 1.7, page 5. The paper states
`∫_{[0,1]} |F_{[X,X+H]}(α)| dα ≪ |[X,X+H]^*|^{-1 + log((log g)+1)/log(g-1)}` without proof.
This file proves the same kind of bound with the exponent `log((log g)+4)/log(g-1)`, by the
standard digit recursion, as in Erdős, Mauduit and Sárközy and in Maynard, Primes with
restricted digits, Section 10. The weaker exponent still tends to `0` as `g → ∞`, which is all
the proofs of Propositions 2.2 and 2.5 use, so those propositions are then proved without
Lemma 1.7 as a cited input.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.MissingDigit.Burst8L17

open Finset Real MeasureTheory Filter
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split LeanLab.MissingDigit.Burst8P2

attribute [local instance] Classical.propDecidable

/-! ### The digit polynomial and its average over a residue system -/

/-- The full geometric sum `G_g(θ) = ∑_{d < g} e(dθ)`. -/
noncomputable def Gsum (g : ℕ) (θ : ℝ) : ℂ := ∑ d ∈ range g, eC (d * θ)

/-- The digit polynomial `f_{g,b}(θ) = ∑_{d < g, d ≠ b} e(dθ)`. -/
noncomputable def fD (g b : ℕ) (θ : ℝ) : ℂ := ∑ d ∈ (range g).filter (fun d => d ≠ b), eC (d * θ)

theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem eC_nat_mul (d : ℕ) (θ : ℝ) : eC (d * θ) = eC θ ^ d := by
  induction d with
  | zero => simp [eC]
  | succ d ih => rw [pow_succ, ← ih, ← eC_add]; congr 1; push_cast; ring

theorem norm_Gsum_le (g : ℕ) (θ : ℝ) : ‖Gsum g θ‖ ≤ g := by
  unfold Gsum
  refine le_trans (norm_sum_le _ _) ?_
  simp [norm_eC]

theorem norm_eC_sub_one (θ : ℝ) : ‖eC θ - 1‖ = 2 * |Real.sin (π * θ)| := by
  have : eC θ = Complex.exp (Complex.I * ((2 * π * θ : ℝ) : ℂ)) := by
    unfold eC; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  norm_num
  congr 2; ring

/-- `|G_g(θ)| ≤ 1 / sin(πθ)` for `0 < θ < 1`. -/
theorem norm_Gsum_le_inv_sin (g : ℕ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ‖Gsum g θ‖ ≤ 1 / Real.sin (π * θ) := by
  have hs : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hne : eC θ - 1 ≠ 0 := by
    intro h
    have := norm_eC_sub_one θ
    rw [h, norm_zero, abs_of_pos hs] at this
    linarith
  have hz : eC θ ≠ 1 := fun h => hne (by rw [h, sub_self])
  unfold Gsum
  simp_rw [eC_nat_mul]
  rw [geom_sum_eq hz, norm_div, norm_eC_sub_one, abs_of_pos hs]
  rw [div_le_div_iff₀ (by positivity) hs]
  have : ‖eC θ ^ g - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, norm_eC]; simp; norm_num
  nlinarith

/-- `1 / sin(πx) ≤ 1/(2x) + 1/(2(1-x))` for `0 < x < 1`, from `sin y ≥ 2y/π` on `[0, π/2]`. -/
theorem inv_sin_le (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    1 / Real.sin (π * x) ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
  have hp := Real.pi_pos
  have hA : 0 < 1 / (2 * x) := by positivity
  have hB : 0 < 1 / (2 * (1 - x)) := by
    have : 0 < 1 - x := by linarith
    positivity
  rcases le_or_gt x (1 / 2) with hx | hx
  · have hs : 2 * x ≤ Real.sin (π * x) := by
      have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
      have e : 2 / π * (π * x) = 2 * x := by field_simp
      linarith
    have : 1 / Real.sin (π * x) ≤ 1 / (2 * x) :=
      one_div_le_one_div_of_le (by positivity) hs
    linarith
  · have hs : 2 * (1 - x) ≤ Real.sin (π * x) := by
      have e1 : Real.sin (π * x) = Real.sin (π * (1 - x)) := by
        rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
      have := Real.mul_le_sin (x := π * (1 - x)) (by nlinarith) (by nlinarith)
      have e : 2 / π * (π * (1 - x)) = 2 * (1 - x) := by field_simp
      linarith
    have : 1 / Real.sin (π * x) ≤ 1 / (2 * (1 - x)) :=
      one_div_le_one_div_of_le (by nlinarith) hs
    linarith

/-- Pointwise bound at the shifted points `x_c = (β + c)/g`, with Lean's convention `t/0 = 0`
absorbing the two end terms. -/
theorem norm_Gsum_shift_le {g c : ℕ} (hg : 2 ≤ g) (hc : c < g) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    ‖Gsum g ((β + c) / g)‖ ≤ (if c = 0 then (g : ℝ) else 0) + (if c = g - 1 then (g : ℝ) else 0) +
      (g : ℝ) / (2 * c) + (g : ℝ) / (2 * ((g - 1 - c : ℕ) : ℝ)) := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (0 : ℝ) < g := by linarith
  have hn := norm_Gsum_le g ((β + c) / g)
  have hnn : 0 ≤ (g : ℝ) / (2 * c) := by positivity
  have hnn2 : 0 ≤ (g : ℝ) / (2 * ((g - 1 - c : ℕ) : ℝ)) := by positivity
  have hi0 : 0 ≤ (if c = 0 then (g : ℝ) else 0) := by split_ifs <;> linarith
  have hi1 : 0 ≤ (if c = g - 1 then (g : ℝ) else 0) := by split_ifs <;> linarith
  by_cases h0 : c = 0
  · have : (if c = 0 then (g : ℝ) else 0) = g := by simp [h0]
    rw [this]; linarith
  by_cases h1 : c = g - 1
  · have : (if c = g - 1 then (g : ℝ) else 0) = g := by simp [h1]
    rw [this]; linarith
  simp only [h0, h1, if_false, zero_add]
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 h0)
  have hcg : c + 2 ≤ g := by omega
  have hcgR : (c : ℝ) + 2 ≤ g := by exact_mod_cast hcg
  have hcast : ((g - 1 - c : ℕ) : ℝ) = (g : ℝ) - 1 - c := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [hcast]
  set x := (β + c) / g with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hgp]; linarith
  have hxc : (c : ℝ) / g ≤ x := by rw [hx]; exact div_le_div_of_nonneg_right (by linarith) hgp.le
  have hxc' : ((g : ℝ) - 1 - c) / g ≤ 1 - x := by
    rw [hx]; field_simp; linarith
  refine le_trans (norm_Gsum_le_inv_sin g hx0 hx1) (le_trans (inv_sin_le x hx0 hx1) ?_)
  have e1 : 1 / (2 * x) ≤ (g : ℝ) / (2 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ hgp] at hxc; nlinarith
  have e2 : 1 / (2 * (1 - x)) ≤ (g : ℝ) / (2 * ((g : ℝ) - 1 - c)) := by
    have hpos : 0 < (g : ℝ) - 1 - c := by linarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    rw [div_le_iff₀ hgp] at hxc'; nlinarith
  linarith

/-- `∑_{c < g} 1/c ≤ 1 + log g`, with `1/0 = 0`. -/
theorem sum_inv_range_le (g : ℕ) : ∑ c ∈ range g, (1 : ℝ) / c ≤ 1 + Real.log g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have e : ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) = ((harmonic n : ℚ) : ℝ) := by
    unfold harmonic; push_cast; simp [one_div]
  simp only [Nat.cast_zero, div_zero, add_zero]
  rw [e]
  refine le_trans (harmonic_le_one_add_log n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  linarith

theorem fD_eq {g b : ℕ} (hbg : b < g) (θ : ℝ) : fD g b θ = Gsum g θ - eC (b * θ) := by
  unfold fD Gsum
  rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_range.2 hbg)]

/-- The digit average bound: for `0 ≤ β ≤ 1`,
`∑_{c < g} |f_{g,b}((β + c)/g)| ≤ g (log g + 4)`. -/
theorem sum_norm_fD_le {g b : ℕ} (hg : 2 ≤ g) (hbg : b < g) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    ∑ c ∈ range g, ‖fD g b ((β + c) / g)‖ ≤ g * (Real.log g + 4) := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have h1 : ∀ c ∈ range g, ‖fD g b ((β + c) / g)‖ ≤
      ((if c = 0 then (g : ℝ) else 0) + (if c = g - 1 then (g : ℝ) else 0) +
        (g : ℝ) / 2 * (1 / (c : ℝ)) + (g : ℝ) / 2 * (1 / ((g - 1 - c : ℕ) : ℝ))) + 1 := by
    intro c hc
    rw [fD_eq hbg]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_eC]
    have := norm_Gsum_shift_le hg (Finset.mem_range.1 hc) hβ0 hβ1
    have e1 : (g : ℝ) / (2 * c) = (g : ℝ) / 2 * (1 / (c : ℝ)) := by ring
    have e2 : (g : ℝ) / (2 * ((g - 1 - c : ℕ) : ℝ)) =
        (g : ℝ) / 2 * (1 / ((g - 1 - c : ℕ) : ℝ)) := by ring
    linarith
  refine le_trans (Finset.sum_le_sum h1) ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq' (range g) 0 (fun _ => (g : ℝ)),
    Finset.sum_ite_eq' (range g) (g - 1) (fun _ => (g : ℝ)), ← Finset.mul_sum, ← Finset.mul_sum]
  have hr : ∑ c ∈ range g, (1 : ℝ) / ((g - 1 - c : ℕ) : ℝ) = ∑ c ∈ range g, (1 : ℝ) / (c : ℝ) :=
    Finset.sum_range_reflect (fun c => (1 : ℝ) / (c : ℝ)) g
  rw [hr]
  have h0 : (0 : ℕ) ∈ range g := Finset.mem_range.2 (by omega)
  have hg1 : g - 1 ∈ range g := Finset.mem_range.2 (by omega)
  simp only [h0, hg1, if_true]
  have hs := sum_inv_range_le g
  nlinarith

/-- The change of variables `α = (β + c)/g` on the `g` subintervals of `[0,1]`:
`∫_0^1 h(α) k(gα) dα ≤ D ∫_0^1 k` when `k ≥ 0` is `1`-periodic and
`∑_{c<g} h((β+c)/g) ≤ g D` on `[0,1]`. -/
theorem integral_mul_comp_le {g : ℕ} (hg : 1 ≤ g) (h k : ℝ → ℝ) (hh : Continuous h)
    (hk : Continuous k) (hk0 : ∀ x, 0 ≤ k x) (hkper : Function.Periodic k 1) {D : ℝ}
    (hD : ∀ β ∈ Set.Icc (0 : ℝ) 1, ∑ c ∈ range g, h ((β + c) / g) ≤ g * D) :
    ∫ α in (0 : ℝ)..1, h α * k (g * α) ≤ D * ∫ β in (0 : ℝ)..1, k β := by
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (0 : ℝ) < g := by linarith
  set F : ℝ → ℝ := fun α => h α * k (g * α) with hFdef
  have hF : Continuous F := by fun_prop
  have hsplit : ∫ α in (0 : ℝ)..1, F α =
      ∑ c ∈ range g, ∫ α in ((c : ℝ) / g)..(((c + 1 : ℕ) : ℝ) / g), F α := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (a := fun c : ℕ => (c : ℝ) / g) (fun _ _ => hF.intervalIntegrable _ _)]
    simp [hgp.ne']
  have hpiece : ∀ c : ℕ, ∫ α in ((c : ℝ) / g)..(((c + 1 : ℕ) : ℝ) / g), F α =
      (1 / (g : ℝ)) * ∫ β in (0 : ℝ)..1, h ((β + c) / g) * k β := by
    intro c
    have e1 : (fun β : ℝ => h ((β + c) / g) * k β) = fun β => F ((β + c) / g) := by
      funext β
      simp only [hFdef]
      congr 1
      rw [mul_div_cancel₀ _ hgp.ne']
      have := hkper.nat_mul c β
      simp only [mul_one] at this
      rw [this]
    rw [e1, intervalIntegral.integral_comp_add_right (fun y => F (y / g)),
      intervalIntegral.integral_comp_div F hgp.ne']
    rw [smul_eq_mul, ← mul_assoc, one_div_mul_cancel hgp.ne', one_mul]
    push_cast; ring_nf
  show ∫ α in (0 : ℝ)..1, F α ≤ _
  rw [hsplit]
  simp_rw [hpiece]
  have hsum : ∑ c ∈ range g, ∫ β in (0 : ℝ)..1, h ((β + c) / g) * k β =
      ∫ β in (0 : ℝ)..1, ∑ c ∈ range g, h ((β + c) / g) * k β := by
    rw [intervalIntegral.integral_finsetSum]
    intro c _
    exact (by fun_prop : Continuous fun β => h ((β + c) / g) * k β).intervalIntegrable _ _
  rw [← Finset.mul_sum, hsum]
  simp_rw [← Finset.sum_mul]
  have hmono : ∫ β in (0 : ℝ)..1, (∑ c ∈ range g, h ((β + c) / g)) * k β ≤
      ∫ β in (0 : ℝ)..1, (g * D) * k β := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous fun β => (∑ c ∈ range g, h ((β + c) / g)) * k β)
        |>.intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun β => (g * D) * k β).intervalIntegrable _ _
    · intro β hβ
      exact mul_le_mul_of_nonneg_right (hD β hβ) (hk0 β)
  rw [intervalIntegral.integral_const_mul] at hmono
  calc 1 / (g : ℝ) * ∫ β in (0 : ℝ)..1, (∑ c ∈ range g, h ((β + c) / g)) * k β
      ≤ 1 / (g : ℝ) * ((g * D) * ∫ β in (0 : ℝ)..1, k β) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = D * ∫ β in (0 : ℝ)..1, k β := by field_simp

/-! ### The digit recursion for `E_N(α) = ∑_{m < N}^* e(mα)` -/

/-- `E_N(α) = ∑_{0 ≤ m < N, m has no digit b} e(mα)`. -/
noncomputable def EN (g b N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ (range N).filter (NoDigit g b), eC (m * α)

theorem sum_range_mul_add (g q r : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ range (g * q + r), F m =
      ∑ y ∈ range q, ∑ x ∈ range g, F (x + g * y) + ∑ x ∈ range r, F (x + g * q) := by
  rw [Finset.sum_range_add]
  congr 1
  · induction q with
    | zero => simp
    | succ q ih =>
      rw [show g * (q + 1) = g * q + g by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by rw [add_comm]
  · exact Finset.sum_congr rfl fun x _ => by rw [add_comm]

/-- The digit recursion: `|E_N(α)| ≤ |f_{g,b}(α)| |E_{⌊N/g⌋}(gα)| + g`. -/
theorem norm_EN_le {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (N : ℕ) (α : ℝ) :
    ‖EN g b N α‖ ≤ ‖fD g b α‖ * ‖EN g b (N / g) (g * α)‖ + g := by
  have hg0 : 0 < g := by omega
  set q := N / g
  set r := N % g
  have hN : N = g * q + r := (Nat.div_add_mod N g).symm
  have hr : r < g := Nat.mod_lt _ hg0
  have key : ∀ y x : ℕ, x < g →
      (if NoDigit g b (x + g * y) then eC (((x + g * y : ℕ) : ℝ) * α) else 0) =
        (if x ≠ b then eC (x * α) else 0) *
          (if NoDigit g b y then eC (y * (g * α)) else 0) := by
    intro y x hx
    have hiff := md_add_mul (y := y) hg hb hx
    by_cases h1 : x = b
    · have : ¬ NoDigit g b (x + g * y) := fun h => (hiff.1 h).1 h1
      rw [if_neg this]; simp [h1]
    · by_cases h2 : NoDigit g b y
      · have : NoDigit g b (x + g * y) := hiff.2 ⟨h1, h2⟩
        simp only [this, h1, h2, if_true, ne_eq, not_false_eq_true]
        rw [← eC_add]; congr 1; push_cast; ring
      · have : ¬ NoDigit g b (x + g * y) := fun h => h2 (hiff.1 h).2
        simp [this, h2]
  have hEN : EN g b N α = fD g b α * EN g b q (g * α) +
      ∑ x ∈ range r, (if NoDigit g b (x + g * q) then eC (((x + g * q : ℕ) : ℝ) * α) else 0) := by
    unfold EN fD
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    conv_lhs => rw [hN]
    rw [sum_range_mul_add]
    congr 1
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    rw [key y x (Finset.mem_range.1 hx)]
  rw [hEN]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have hR : ‖∑ x ∈ range r, (if NoDigit g b (x + g * q) then
      eC (((x + g * q : ℕ) : ℝ) * α) else 0)‖ ≤ g := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ x ∈ range r, ‖(if NoDigit g b (x + g * q) then
        eC (((x + g * q : ℕ) : ℝ) * α) else 0)‖ ≤ 1 := by
      intro x _
      split_ifs
      · rw [norm_eC]
      · simp
    refine le_trans (Finset.sum_le_sum this) ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast hr.le
  linarith

theorem fD_continuous (g b : ℕ) : Continuous (fD g b) := by
  unfold fD; have := continuous_eC; fun_prop

theorem EN_continuous (g b N : ℕ) : Continuous (EN g b N) := by
  unfold EN; have := continuous_eC; fun_prop

/-- One step of the recursion for `a(N) = ∫_0^1 |E_N|`:
`a(N) ≤ (log g + 4) a(⌊N/g⌋) + g`. -/
theorem int_EN_step {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (hbg : b < g) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖EN g b N α‖ ≤
      (Real.log g + 4) * (∫ α in (0 : ℝ)..1, ‖EN g b (N / g) α‖) + g := by
  have hc1 : Continuous fun α => ‖EN g b N α‖ := (EN_continuous g b N).norm
  have hc2 : Continuous fun α => ‖fD g b α‖ * ‖EN g b (N / g) (g * α)‖ + g := by
    have := EN_continuous g b (N / g); have := fD_continuous g b; fun_prop
  have hmono : ∫ α in (0 : ℝ)..1, ‖EN g b N α‖ ≤
      ∫ α in (0 : ℝ)..1, (‖fD g b α‖ * ‖EN g b (N / g) (g * α)‖ + g) :=
    intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun α _ => norm_EN_le hg hb N α)
  have hc3 : Continuous fun α => ‖fD g b α‖ * ‖EN g b (N / g) (g * α)‖ := by
    have := EN_continuous g b (N / g); have := fD_continuous g b; fun_prop
  rw [intervalIntegral.integral_add (hc3.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, one_smul] at hmono
  have hcv := integral_mul_comp_le (g := g) (by omega) (fun α => ‖fD g b α‖)
    (fun α => ‖EN g b (N / g) α‖) (fD_continuous g b).norm (EN_continuous g b _).norm
    (fun _ => norm_nonneg _) (by
      have := periodic_norm_sum_eC ((range (N / g)).filter (NoDigit g b))
      exact this)
    (D := Real.log g + 4) (fun β hβ => sum_norm_fD_le hg hbg hβ.1 hβ.2)
  linarith

/-- `a(N) ≤ 2 g (log g + 4)^j - g` for `N < g^j`. -/
theorem int_EN_le {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (hbg : b < g) :
    ∀ j N : ℕ, N < g ^ j →
      ∫ α in (0 : ℝ)..1, ‖EN g b N α‖ ≤ 2 * g * (Real.log g + 4) ^ j - g := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hL : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  intro j
  induction j with
  | zero =>
    intro N hN
    have : N = 0 := by simpa using hN
    subst this
    simp [EN]; linarith
  | succ j ih =>
    intro N hN
    have hq : N / g < g ^ j := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← pow_succ]
    have h1 := int_EN_step hg hb hbg N
    have h2 := ih _ hq
    have hD : 2 ≤ Real.log g + 4 := by linarith
    have hDj : 0 ≤ (Real.log g + 4) ^ j := by positivity
    have h3 : (Real.log g + 4) * (∫ α in (0 : ℝ)..1, ‖EN g b (N / g) α‖) ≤
        (Real.log g + 4) * (2 * g * (Real.log g + 4) ^ j - g) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [pow_succ]
    nlinarith

/-! ### The exponent `log((log g)+s)/log(g-1)` and the comparison step for it -/

/-- `θ_{g,s} = log((log g)+s)/log(g-1)`; Kim's exponent of Lemma 1.7 is `s = 1`. -/
noncomputable def thetaS (s : ℝ) (g : ℕ) : ℝ :=
  Real.log (Real.log g + s) / Real.log ((g : ℝ) - 1)

/-- `ρ_{g,s} = (log(g-1)/log g)(1 - θ_{g,s})`. -/
noncomputable def rhoS (s : ℝ) (g : ℕ) : ℝ := Real.log ((g : ℝ) - 1) / Real.log g * (1 - thetaS s g)

/-- As `exists_g0`, for the exponent `θ_{g,s}` with `s ≥ 1`. -/
theorem exists_g0S {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 < κ) : ∃ g₀ : ℕ, 3 ≤ g₀ ∧ ∀ g : ℕ, g₀ ≤ g →
    0 ≤ thetaS s g ∧ thetaS s g ≤ 1 / 2 ∧ 0 ≤ rhoS s g ∧ rhoS s g ≤ 1 ∧ 1 - rhoS s g < κ := by
  set κ' := min κ 1 with hκ'
  have hκ'p : 0 < κ' := lt_min hκ one_pos
  have ht := Real.tendsto_pow_log_div_mul_add_atTop 1 (-(s + 1)) 1 one_ne_zero
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    ((ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ' / 2))))
  set E : ℝ := max (max T 3) (2 * Real.log 2 / κ + 1)
  have hce : 0 < ⌈Real.exp E⌉₊ := Nat.ceil_pos.2 (Real.exp_pos E)
  refine ⟨⌈Real.exp E⌉₊ + 2, by omega, fun g hg => ?_⟩
  have hgE : Real.exp E + 1 < (g : ℝ) - 1 + 1 := by
    have : (⌈Real.exp E⌉₊ + 2 : ℕ) ≤ (g : ℝ) := by exact_mod_cast hg
    push_cast at this
    linarith [Nat.le_ceil (Real.exp E)]
  have hg1 : Real.exp E < (g : ℝ) - 1 := by linarith
  have hgm : 0 < (g : ℝ) - 1 := lt_trans (Real.exp_pos E) hg1
  set t := Real.log ((g : ℝ) - 1) with htdef
  have htE : E < t := by rw [htdef, Real.lt_log_iff_exp_lt hgm]; exact hg1
  have ht3 : 3 < t := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) htE
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htE.le
  have htK : 2 * Real.log 2 / κ + 1 < t := lt_of_le_of_lt (le_max_right _ _) htE
  have hgp : (0 : ℝ) < g := by linarith
  set L := Real.log (g : ℝ) with hLdef
  have htL : t ≤ L := Real.log_le_log hgm (by linarith)
  have hLt : L ≤ t + Real.log 2 := by
    rw [htdef, ← Real.log_mul hgm.ne' (by norm_num)]
    have hE1 : 1 < Real.exp E := Real.one_lt_exp_iff.2
      (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right T 3) (le_max_left _ _)))
    exact Real.log_le_log hgp (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < L := by linarith
  -- θ bounds
  have hθ0 : 0 ≤ thetaS s g := by
    unfold thetaS
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hθt : thetaS s g ≤ Real.log (t + 1 + s) / t := by
    unfold thetaS
    rw [← htdef, ← hLdef]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  have hθκ : thetaS s g < κ' / 2 := by
    have h := hT (t + 1 + s) (by linarith)
    have e : Real.log (t + 1 + s) ^ 1 / (1 * (t + 1 + s) + -(s + 1)) = Real.log (t + 1 + s) / t := by
      rw [pow_one]; congr 1; ring
    rw [e] at h
    linarith
  have hθhalf : thetaS s g ≤ 1 / 2 := by
    have : κ' ≤ 1 := min_le_right _ _
    linarith
  have hθκ2 : thetaS s g < κ / 2 := by
    have : κ' ≤ κ := min_le_left _ _
    linarith
  -- a = t / L
  have ha0 : 0 ≤ t / L := div_nonneg (by linarith) hLp.le
  have ha1 : t / L ≤ 1 := (div_le_one hLp).2 htL
  have h1a : 1 - t / L < κ / 2 := by
    have e : 1 - t / L = (L - t) / L := by field_simp
    rw [e, div_lt_iff₀ hLp]
    have h2 : 2 * Real.log 2 / κ < L := by linarith
    rw [div_lt_iff₀ hκ] at h2
    nlinarith
  have hρ : rhoS s g = t / L * (1 - thetaS s g) := rfl
  refine ⟨hθ0, hθhalf, ?_, ?_, ?_⟩
  · rw [hρ]; exact mul_nonneg ha0 (by linarith)
  · rw [hρ]
    calc t / L * (1 - thetaS s g) ≤ 1 * 1 :=
          mul_le_mul ha1 (by linarith) (by linarith) (by norm_num)
      _ = 1 := by norm_num
  · rw [hρ]
    have : t / L * thetaS s g ≤ thetaS s g := by
      calc t / L * thetaS s g ≤ 1 * thetaS s g := mul_le_mul_of_nonneg_right ha1 hθ0
        _ = thetaS s g := one_mul _
    nlinarith

/-- As `tail_small`, for the exponent `θ_{g,s}` with `s ≥ 1`. -/
theorem tail_smallS {s : ℝ} (hs : 1 ≤ s) {cε : ℝ} (hcε : 0 < cε) : ∃ g₀ : ℕ, 3 ≤ g₀ ∧ ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b →
    b ≤ g - 1 → ∀ A η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k → 1 ≤ H →
      H < ((g ^ k : ℕ) : ℝ) →
      A * H * ((g ^ k : ℕ) : ℝ) ^ (-cε) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS s g ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨g₀, hg₀3, hg₀⟩ := exists_g0S hs hcε
  refine ⟨g₀, hg₀3, fun g b hg hb2 hbg A η hη => ?_⟩
  obtain ⟨hθ0, hθh, hρ0, hρ1, hρκ⟩ := hg₀ g hg
  have hg3 : 3 ≤ g := le_trans hg₀3 hg
  have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg3
  set θ := thetaS s g
  set ρ := rhoS s g with hρdef
  set κ := cε - (1 - ρ) with hκ
  have hκp : 0 < κ := by rw [hκ]; linarith
  set A' := max A 0
  have hX : Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun k : ℕ => (g : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    simpa using this
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop hκp).comp hX).eventually_ge_atTop (A' * (g : ℝ) ^ ρ / η))
  refine ⟨K₀, fun k H hk hH1 hHX => ?_⟩
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
  have hXκ : A' * (g : ℝ) ^ ρ / η ≤ X ^ κ := hK₀ k hk
  have hXp : 0 < X := by linarith
  have hHp : 0 < H := by linarith
  have hgp : (0 : ℝ) < g := by linarith
  -- counting
  have hcard := card_starSet_ge (by omega) hb2 (by omega) hH1 hHX
  set j := Nat.log g ⌊H⌋₊
  have hNj : ((g : ℝ) - 1) ^ j ≤ N := by
    have : (((g - 1) ^ j : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hcard
    push_cast [show 1 ≤ g by omega] at this; exact this
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ (by linarith)) hNj
  have hNp : 0 < N := by linarith
  have hlow := rpow_card_lower hg3 (θ := θ) (by linarith) hH1
    (lt_pow_log_succ (by omega) hHp.le) hNj
  have hρeq : Real.log ((g : ℝ) - 1) / Real.log g * (1 - θ) = ρ := rfl
  rw [hρeq] at hlow
  -- reduce to `A' H X^{-cε} ≤ η N^{1-θ}`
  have hsplitN : N = N ^ θ * N ^ (1 - θ) := by
    rw [← Real.rpow_add hNp, add_sub_cancel, Real.rpow_one]
  have hNθ : 0 ≤ N ^ θ := (Real.rpow_pos_of_pos hNp _).le
  have hgρ : 0 < (g : ℝ) ^ ρ := Real.rpow_pos_of_pos hgp _
  have hHρ : 0 < H ^ ρ := Real.rpow_pos_of_pos hHp _
  have hXcε : 0 < X ^ (-cε) := Real.rpow_pos_of_pos hXp _
  have hcore : A' * H * X ^ (-cε) ≤ η * N ^ (1 - θ) := by
    have hH1ρ : H ^ (1 - ρ) ≤ X ^ (1 - ρ) :=
      Real.rpow_le_rpow hHp.le hHX.le (by linarith)
    have hHsplit : H = H ^ ρ * H ^ (1 - ρ) := by
      rw [← Real.rpow_add hHp, add_sub_cancel, Real.rpow_one]
    have hXsplit : X ^ (1 - ρ) * X ^ (-cε) = (X ^ κ)⁻¹ := by
      rw [← Real.rpow_add hXp, ← Real.rpow_neg hXp.le, hκ]; congr 1; ring
    have hA' : 0 ≤ A' := le_max_right _ _
    have hXκp : 0 < X ^ κ := Real.rpow_pos_of_pos hXp _
    have step1 : A' * H * X ^ (-cε) ≤ A' * H ^ ρ * (X ^ κ)⁻¹ := by
      rw [← hXsplit]
      conv_lhs => rw [hHsplit]
      have : 0 ≤ A' * H ^ ρ := mul_nonneg hA' hHρ.le
      calc A' * (H ^ ρ * H ^ (1 - ρ)) * X ^ (-cε)
          = (A' * H ^ ρ) * (H ^ (1 - ρ) * X ^ (-cε)) := by ring
        _ ≤ (A' * H ^ ρ) * (X ^ (1 - ρ) * X ^ (-cε)) := by
          apply mul_le_mul_of_nonneg_left _ this
          exact mul_le_mul_of_nonneg_right hH1ρ hXcε.le
        _ = A' * H ^ ρ * (X ^ (1 - ρ) * X ^ (-cε)) := by ring
    have step2 : A' * H ^ ρ * (X ^ κ)⁻¹ ≤ η * (H ^ ρ / (g : ℝ) ^ ρ) := by
      rw [div_le_iff₀ hη] at hXκ
      rw [mul_inv_le_iff₀ hXκp]
      have e : η * (H ^ ρ / (g : ℝ) ^ ρ) * X ^ κ = H ^ ρ * (X ^ κ * η) / (g : ℝ) ^ ρ := by
        ring
      rw [e, le_div_iff₀ hgρ]
      nlinarith
    calc A' * H * X ^ (-cε) ≤ η * (H ^ ρ / (g : ℝ) ^ ρ) := le_trans step1 step2
      _ ≤ η * N ^ (1 - θ) := mul_le_mul_of_nonneg_left hlow hη.le
  have hAA : A * H * X ^ (-cε) * N ^ θ ≤ A' * H * X ^ (-cε) * N ^ θ := by
    have : 0 ≤ H * X ^ (-cε) * N ^ θ := mul_nonneg (mul_nonneg hHp.le hXcε.le) hNθ
    nlinarith [le_max_left A 0]
  calc A * H * X ^ (-cε) * N ^ θ ≤ A' * H * X ^ (-cε) * N ^ θ := hAA
    _ ≤ η * N ^ (1 - θ) * N ^ θ := mul_le_mul_of_nonneg_right hcore hNθ
    _ = η * N := by conv_rhs => rw [hsplitN]
                    ring

/-! ### The bound for `[X, X+H]^*` -/

theorem starSet_eq_map {g b k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) {H : ℝ} (hHX : ⌊H⌋₊ < g ^ k) :
    starSet g b (g ^ k) H =
      ((Ioc 0 ⌊H⌋₊).filter (NoDigit g b)).map (addLeftEmbedding (g ^ k)) := by
  have hS : ∀ m, m ≤ ⌊H⌋₊ → (NoDigit g b (g ^ k + m) ↔ NoDigit g b m) :=
    fun m hm => md_pow_add hg hb k m (by omega)
  ext n
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_map, addLeftEmbedding_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨n - g ^ k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [← hS _ (by omega), show g ^ k + (n - g ^ k) = n by omega]; exact h3
  · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, (hS m h2).2 h3⟩

theorem EN_succ_eq (g b M : ℕ) (α : ℝ) :
    EN g b (M + 1) α = 1 + ∑ m ∈ (Ioc 0 M).filter (NoDigit g b), eC (m * α) := by
  have e2 : (Finset.range (M + 1)).filter (NoDigit g b) =
      insert 0 ((Finset.Ioc 0 M).filter (NoDigit g b)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hp, by omega⟩, h2⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, md_zero g b⟩
      · exact ⟨by omega, h3⟩
  unfold EN
  rw [e2, Finset.sum_insert (by simp)]
  have := eC_int 0
  push_cast at this
  simp [this]

/-- `|∑_{n ∈ [X,X+H]^*} e(nα)| ≤ |E_{⌊H⌋+1}(α)| + 1` for `X = g^k > ⌊H⌋`. -/
theorem norm_sum_starSet_le {g b k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) {H : ℝ}
    (hHX : ⌊H⌋₊ < g ^ k) (α : ℝ) :
    ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤ ‖EN g b (⌊H⌋₊ + 1) α‖ + 1 := by
  rw [starSet_eq_map hg hb hHX, Finset.sum_map]
  simp only [addLeftEmbedding_apply]
  have e : ∀ m : ℕ, eC (((g ^ k + m : ℕ) : ℝ) * α) = eC (((g ^ k : ℕ) : ℝ) * α) * eC (m * α) := by
    intro m; rw [← eC_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [← Finset.mul_sum, norm_mul, norm_eC, one_mul]
  have h := EN_succ_eq g b ⌊H⌋₊ α
  have : ∑ m ∈ (Ioc 0 ⌊H⌋₊).filter (NoDigit g b), eC (m * α) = EN g b (⌊H⌋₊ + 1) α - 1 := by
    rw [h]; ring
  rw [this]
  refine le_trans (norm_sub_le _ _) ?_
  simp

/-- Lemma 1.7 type bound, PROVED, with the exponent `θ_{g,4} = log((log g)+4)/log(g-1)` in
place of Kim's `log((log g)+1)/log(g-1)`: for `g ≥ 3`, `2 ≤ b ≤ g-1`, `X = g^k` and
`1 ≤ H < X`, `∫_0^1 |∑_{n ∈ [X,X+H]^*} e(nα)| dα ≤ C |[X,X+H]^*|^{θ_{g,4}}` with
`C = 2g(log g + 4)^2 + 1`. -/
theorem lemma_1_7_weak {g b : ℕ} (hg : 3 ≤ g) (hb : 2 ≤ b) (hbg : b ≤ g - 1) : ∃ C : ℝ,
    ∀ (k : ℕ) (H : ℝ), 1 ≤ H → H < ((g ^ k : ℕ) : ℝ) →
      ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
        C * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
  have hgR : (3 : ℝ) ≤ g := by exact_mod_cast hg
  set D : ℝ := Real.log g + 4 with hD
  have hL : 0 < Real.log g := Real.log_pos (by linarith)
  have hD1 : 1 ≤ D := by linarith
  refine ⟨2 * g * D ^ 2 + 1, fun k H hH1 hHX => ?_⟩
  set M := ⌊H⌋₊ with hM
  have hMk : M < g ^ k := (Nat.floor_lt (by linarith)).2 hHX
  set j := Nat.log g M with hj
  have hMj : M < g ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) M
  have hMj2 : M + 1 < g ^ (j + 2) := by
    have : g ^ (j + 1) < g ^ (j + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  -- the integral
  have hc1 : Continuous fun α => ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ := by
    have := continuous_eC; fun_prop
  have hc2 : Continuous fun α => ‖EN g b (M + 1) α‖ + 1 := (EN_continuous g b _).norm.add
    continuous_const
  have hint : ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖ ≤
      2 * g * D ^ (j + 2) - g + 1 := by
    refine le_trans (intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun α _ => norm_sum_starSet_le (by omega) hb hMk α)) ?_
    rw [intervalIntegral.integral_add ((EN_continuous g b _).norm.intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, one_smul]
    have := int_EN_le (g := g) (b := b) (by omega) (by omega) (by omega) (j + 2) (M + 1) hMj2
    linarith
  -- `D^j ≤ N^{θ}`
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ) with hNdef
  have hcard := card_starSet_ge (by omega) hb (by omega) hH1 hHX
  have hNj : ((g : ℝ) - 1) ^ j ≤ N := by
    have : (((g - 1) ^ j : ℕ) : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hcard
    push_cast [show 1 ≤ g by omega] at this; exact this
  have hgm : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have hLm : 0 < Real.log ((g : ℝ) - 1) := Real.log_pos (by linarith)
  have hθ : thetaS 4 g = Real.log D / Real.log ((g : ℝ) - 1) := rfl
  have hθ0 : 0 ≤ thetaS 4 g := by
    rw [hθ]; exact div_nonneg (Real.log_nonneg hD1) hLm.le
  have hbase : ((g : ℝ) - 1) ^ thetaS 4 g = D := by
    rw [Real.rpow_def_of_pos hgm, hθ, mul_div_cancel₀ _ hLm.ne', Real.exp_log (by linarith)]
  have hDj : D ^ j ≤ N ^ thetaS 4 g := by
    calc D ^ j = (((g : ℝ) - 1) ^ thetaS 4 g) ^ j := by rw [hbase]
      _ = (((g : ℝ) - 1) ^ j) ^ thetaS 4 g := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hgm.le, mul_comm, Real.rpow_mul hgm.le,
            Real.rpow_natCast]
      _ ≤ N ^ thetaS 4 g := Real.rpow_le_rpow (by positivity) hNj hθ0
  have hDj1 : 1 ≤ D ^ j := one_le_pow₀ hD1
  have hgp : (0 : ℝ) ≤ g := by linarith
  have hD2 : 0 ≤ 2 * g * D ^ 2 := by positivity
  calc ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ 2 * g * D ^ (j + 2) - g + 1 := hint
    _ ≤ (2 * g * D ^ 2 + 1) * D ^ j := by rw [pow_add]; nlinarith
    _ ≤ (2 * g * D ^ 2 + 1) * N ^ thetaS 4 g :=
        mul_le_mul_of_nonneg_left hDj (by positivity)

/-! ### Propositions 2.2 and 2.5 without Lemma 1.7 as an input -/

/-- Kim, Proposition 2.2 with display (2.1), page 8, PROVED from `prop_2_1` and the proved `lemma_1_7_weak`
by the paper's display (2.2). Same statement as `Burst4Split.prop_2_2`. -/
theorem prop_2_2_p3 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H,
          ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h21⟩ := prop_2_1
  set g₁ : ℕ := 3
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨c, hc, C, X₀, hC⟩ := h21 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_smallS (by norm_num : (1 : ℝ) ≤ 4) (mul_pos hc hε)
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := lemma_1_7_weak hg3 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (C * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set M : ℝ := C * H * X ^ (-(c * ε))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb 0)
  have hF : Continuous (fun α => S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) :=
    (S4_continuous _ _).sub (S4sharp_cont _ _ _)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine le_trans (norm_sum_setIntegral_le (measurableSet_Ioc) Set.Ioc_subset_Icc_self _ hF _
    (fun α _ => hb α)) ?_
  rw [setIntegral_Ioc01_norm]
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g) :=
        mul_le_mul_of_nonneg_left hL hM0
    _ = C * C₂ * H * X ^ (-(c * ε)) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
        ring
    _ ≤ _ := h2

/-- Kim, Proposition 2.5, page 9, PROVED from `prop_3_5` and the proved `lemma_1_7_weak` by the paper's
proof: the minor arc contribution is at most `sup_𝔪 |S♯₄| ∫_𝔪 |∑_{n ∈ [X,X+H]^*} e(-nα)| dα`.
Same statement as `Burst4Split.prop_2_5`. -/
theorem prop_2_5_p3 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h35⟩ := prop_3_5
  set g₁ : ℕ := 3
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨C, X₀, hC⟩ := h35 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_smallS (by norm_num : (1 : ℝ) ≤ 4) hε
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := lemma_1_7_weak hg3 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (max C 0 * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hXp : 0 < X := by linarith
  have hδ : delta ε (g ^ k) = X ^ (-ε) := rfl
  have hδH : 0 ≤ delta ε (g ^ k) * H := by
    rw [hδ]; exact mul_nonneg (Real.rpow_pos_of_pos hXp _).le (by linarith)
  set M : ℝ := max C 0 * (delta ε (g ^ k) * H)
  have hM0 : 0 ≤ M := mul_nonneg (le_max_right _ _) hδH
  have hbM : ∀ α ∈ arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H, ‖S4sharp ε (g ^ k) H α‖ ≤ M :=
    fun α hα => le_trans (hb α hα) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδH)
  have hmeas : MeasurableSet (arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H) :=
    measurableSet_Ioc.diff (measurableSet_majorArcs _ _ _)
  have hsub : arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H ⊆
      Set.Icc (1 / Qpar ε (g ^ k)) (1 + 1 / Qpar ε (g ^ k)) :=
    fun α hα => Set.Ioc_subset_Icc_self hα.1
  unfold minorInt
  refine le_trans (norm_sum_setIntegral_le hmeas hsub _ (S4sharp_cont _ _ _) _ hbM) ?_
  have hce := continuous_eC
  have hmono : ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ ≤
      ∫ α in arcRange ε (g ^ k), ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ := by
    apply setIntegral_mono_set
    · have hc : Continuous (fun α : ℝ => ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖) := by
        fun_prop
      exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    · exact Set.diff_subset.eventuallyLE
  rw [setIntegral_arcRange_norm] at hmono
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g) :=
        mul_le_mul_of_nonneg_left (le_trans hmono hL) hM0
    _ = max C 0 * C₂ * H * X ^ (-ε) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
        simp only [M]; rw [hδ]; ring
    _ ≤ _ := h2

/-- Kim, Theorem 1.1, assembled from the Burst 8 split, NEW TOP LEVEL THEOREM. Same statement
as `LeanLab.MissingDigit.kim_thm1_1` and the same assembly as
`Burst4Split.kim_thm1_1_of_split`, with the three Burst 4 leaves replaced by `prop_2_2_p3`,
`major_arcs_bound_p2` and `prop_2_5_p3`. CONDITIONAL ON the cited `prop_2_1`, `prop_3_5`,
`prop_2_4` and `main_term_bound`; Lemma 1.7 is replaced by the proved `lemma_1_7_weak`. -/
theorem kim_thm1_1_of_p3 : D4Bound (3 / 5) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2_p3
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound_p2
  obtain ⟨e3, he3, h3⟩ := prop_2_5_p3
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((3 : ℝ) / 5 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((3 : ℝ) / 5 + ε) = X ^ ((3 : ℝ) / 5 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((3 : ℝ) / 5 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

#check (kim_thm1_1_of_p3 : D4Bound (3 / 5) 7)

#print axioms sum_norm_fD_le
#print axioms integral_mul_comp_le
#print axioms norm_EN_le
#print axioms int_EN_le
#print axioms exists_g0S
#print axioms tail_smallS
#print axioms lemma_1_7_weak
#print axioms prop_2_2_p3
#print axioms prop_2_5_p3
#print axioms kim_thm1_1_of_p3

end LeanLab.MissingDigit.Burst8L17

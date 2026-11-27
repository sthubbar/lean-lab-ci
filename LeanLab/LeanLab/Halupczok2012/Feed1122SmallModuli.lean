import LeanLab.Halupczok2012.U1495PPS
import Mathlib.Analysis.Real.Sqrt

/-!
Feed split of `Decomp398c.small_moduli`, burst-20261122.
Source: Perelli Pintz Salerno 1984 pages 530 to 531, the small modulus range
removed before display 5, which rests on the Huxley Iwaniec short interval range
for primes in progressions printed on page 530.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
The moduli at most x to the 1 over 100 are split at a power of log x into the
Siegel Walfisz range and the zero density range. Both leaves are sums of
nonnegative terms over sub ranges of the parent range.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122SmallModuli

open Finset
open scoped Classical

/-- LEAF: PPS1984 page 530, the Siegel Walfisz part of the small modulus range,
moduli at most a fixed power of log x, short interval prime number theorem in
progressions with y at least x to the 3 over 5 plus epsilon. Class HARD. -/
theorem siegel_walfisz_range :
    ∀ A D ε : ℝ, 0 < A → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ))).filter
          (fun q : ℕ => (q : ℝ) ≤ Real.log x ^ D),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- LEAF: PPS1984 pages 530 to 531, the zero density part of the small modulus range,
moduli between a power of log x and x to the 1 over 100, Huxley Iwaniec range at
theta 3 over 5 with the exceptional zero handled by Siegel. Class HARD. -/
theorem zero_density_range :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ D C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ))).filter
          (fun q : ℕ => Real.log x ^ D < (q : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- The two leaves give `Decomp398c.small_moduli`, same statement. -/
theorem small_moduli_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  intro A ε hA hε
  obtain ⟨D, C2, x2, h2⟩ := zero_density_range A ε hA hε
  obtain ⟨C1, x1, h1⟩ := siegel_walfisz_range A D ε hA hε
  refine ⟨C1 + C2, max x1 x2, ?_⟩
  intro x y Q hx hxy hyx a h z ha hh hz
  have hs1 := h1 x y Q ((le_max_left _ _).trans hx) hxy hyx a h z ha hh hz
  have hs2 := h2 x y Q ((le_max_right _ _).trans hx) hxy hyx a h z ha hh hz
  have he := sum_filter_add_sum_filter_not
    ((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)))
    (fun q : ℕ => (q : ℝ) ≤ Real.log x ^ D) (fun q => ppsTerm (z q) (h q) q (a q))
  simp only [not_le] at he
  rw [← he]
  have hr : (C1 + C2) * y * Real.log x ^ (-A) =
      C1 * y * Real.log x ^ (-A) + C2 * y * Real.log x ^ (-A) := by ring
  linarith


/-! Elementary checks for the corrected citation PPS1984 page 531 display 5.
The two open estimates above retain their original statements.
-/

/-- Huxley Iwaniec page 189 display 1.6 at theta equal to 3 over 5.
The cutoff exponent 1 over 100 is strictly inside the printed range. -/
theorem huxley_iwaniec_exponent_margin :
    (7 / 12 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) ≤ 29 / 48 ∧
      (1 / 100 : ℝ) < 3 * (3 / 5) - 7 / 4 := by
  norm_num

/-- Huxley Iwaniec page 191 display 2.20 at theta equal to 3 over 5.
The low zero range has exponent at least one twentieth throughout its interval.
This is only the rational optimization, not a zero density theorem. -/
theorem huxley_iwaniec_low_zero_density_margin (α : ℝ)
    (hα : α ≤ 3 / 4) :
    (1 / 20 : ℝ) ≤ (1 - α) * (3 * (3 / 5) - 1 - α) / (4 - 5 * α) := by
  have hd : 0 < 4 - 5 * α := by linarith
  apply (le_div_iff₀ hd).mpr
  have hp := mul_nonneg_of_nonpos_of_nonpos
    (show 4 * α - 3 ≤ 0 by linarith) (show 5 * α - 4 ≤ 0 by linarith)
  nlinarith

open Filter
open scoped Topology

/-- For every fixed logarithmic cutoff, a natural modulus eventually lies strictly
above that cutoff and at most x to 1 over 100. The density leaf is not vacuous.
Source: the nonnegative partition of the range removed at PPS page 531 display 5. -/
theorem zero_density_range_nonempty (D : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∃ q : ℕ, 1 ≤ q ∧ Real.log x ^ D < (q : ℝ) ∧ (q : ℝ) ≤ x ^ (1 / 100 : ℝ) := by
  have hb := (isLittleO_log_rpow_rpow_atTop D
    (by norm_num : (0 : ℝ) < 1 / 100)).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hb, eventually_ge_atTop (Real.exp 1),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_gt_atTop 2]
      with x hx he hp
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le he
  have hl : 0 ≤ Real.log x ^ D := Real.rpow_nonneg
    (Real.log_nonneg ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans he)) D
  have hsmall : Real.log x ^ D ≤ (1 / 2 : ℝ) * x ^ (1 / 100 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl,
      abs_of_nonneg (Real.rpow_nonneg hx0.le (1 / 100))] using hx
  refine ⟨⌊x ^ (1 / 100 : ℝ)⌋₊, ?_, ?_, Nat.floor_le (by positivity)⟩
  · have : (1 : ℝ) ≤ x ^ (1 / 100 : ℝ) := by linarith
    apply (Nat.le_floor_iff (by positivity : 0 ≤ x ^ (1 / 100 : ℝ))).mpr
    simpa only [Nat.cast_one] using this
  · have hf := Nat.lt_floor_add_one (x ^ (1 / 100 : ℝ))
    linarith


/-- A full interval error of size x exp of minus c sqrt log x eventually exceeds
x to theta for every theta less than one. It cannot supply a power short interval
estimate by direct comparison. Source target: PPS page 531 display 5 via reference 6. -/
theorem full_interval_error_exceeds_power (θ c : ℝ) (hθ : θ < 1) : ∀ᶠ x : ℝ in atTop,
    x ^ θ < x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hδ : 0 < 1 - θ := by linarith
  have hlim := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hlim.eventually_ge_atTop ((|c| + 1) / (1 - θ)),
    eventually_ge_atTop (Real.exp 1)] with x hu hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hl : 0 < Real.log x := Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hx)
  have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hl
  have he : |c| + 1 ≤ (1 - θ) * Real.sqrt (Real.log x) := by
    have := (div_le_iff₀ hδ).mp hu
    dsimp [Function.comp_def] at this
    nlinarith
  have he2 := mul_le_mul_of_nonneg_right he hs.le
  have hsq := Real.sq_sqrt hl.le
  have hexp : Real.log x * θ < Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith [le_abs_self c]
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_log hx0, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  simpa only [Real.log_exp, sub_eq_add_neg, neg_mul] using hexp

/-- No constant and threshold bound the full interval exponential error by
C x to theta times any fixed logarithmic power when theta is less than one.
This is an obstruction to the attempted replacement, not a paper error.
Source target: PPS page 531 display 5 through Huxley Iwaniec. -/
theorem full_interval_error_not_short_interval (θ c A : ℝ) (hθ : θ < 1) :
    ¬ ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x0 ≤ x → Real.exp 1 ≤ x →
      x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ C * x ^ θ * Real.log x ^ (-A) := by
  have hpow := full_interval_error_exceeds_power ((θ + 1) / 2) c (by linarith)
  rintro ⟨C, x0, hC, hbound⟩
  have hCp : 0 < C + 1 := by linarith
  have hδ : 0 < (1 - θ) / 2 := by linarith
  have hb := (isLittleO_log_rpow_rpow_atTop (-A) hδ).bound
    (div_pos (by norm_num : (0 : ℝ) < 1) hCp)
  obtain ⟨x, hx, hp, he, hX⟩ := (hb.and (hpow.and
    ((eventually_ge_atTop (Real.exp 1)).and (eventually_ge_atTop x0)))).exists
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le he
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg
    ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans he)
  have hs : Real.log x ^ (-A) ≤ (1 / (C + 1)) * x ^ ((1 - θ) / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 (-A)),
      abs_of_nonneg (Real.rpow_nonneg hx0.le ((1 - θ) / 2))] using hx
  have hexp : x ^ θ * x ^ ((1 - θ) / 2) = x ^ ((θ + 1) / 2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hsmall : C * x ^ θ * Real.log x ^ (-A) < x ^ ((θ + 1) / 2) := by
    calc
      _ ≤ C * x ^ θ * ((1 / (C + 1)) * x ^ ((1 - θ) / 2)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (C / (C + 1)) * x ^ ((θ + 1) / 2) := by rw [← hexp]; ring
      _ < 1 * x ^ ((θ + 1) / 2) := by
        apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hx0 _)
        rw [div_lt_one hCp]
        linarith
      _ = _ := one_mul _
  exact (hbound x hX he).not_gt (hsmall.trans hp)

/-- Prime powers cost an arbitrarily small logarithmic error over the small moduli.
Source: Huxley Iwaniec page 191, the paragraph after display 2.24.
Mathlib's global Chebyshev bound suffices because x to 51 over 100 is below
x to 3 over 5. This proves no short interval prime distribution estimate. -/
theorem small_moduli_prime_power_error : ∀ A : ℝ, ∃ C x0 : ℝ, ∀ x y Q : ℝ,
    x0 ≤ x → x ^ (3 / 5 : ℝ) ≤ y → y ≤ x →
    ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ),
      (∀ q, 0 ≤ h q ∧ h q ≤ y) → (∀ q, 0 ≤ z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ)),
        |psiAP (z q + h q) q (a q) - psiAP (z q) q (a q) -
          thetaAP (z q) (h q) q (a q)| ≤ C * y * Real.log x ^ (-A) := by
  intro A
  obtain ⟨Cp, hCp⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨xl, hl⟩ := eventually_log_rpow_le A (by norm_num : (0 : ℝ) < 9 / 100)
  refine ⟨2 * |Cp|, max xl 3, ?_⟩
  intro x y Q hx hxy hyx a h z hh hz
  have hx3 : (3 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hterm : ∀ q : ℕ,
      |psiAP (z q + h q) q (a q) - psiAP (z q) q (a q) -
        thetaAP (z q) (h q) q (a q)| ≤ |Cp| * (2 * Real.sqrt x) := by
    intro q
    obtain ⟨he0, he⟩ := psiDiff_sub_thetaAP (z q) (h q) (hz q).1 (hh q).1 q (a q)
    rw [abs_of_nonneg he0]
    have hs : Real.sqrt (z q + h q) ≤ 2 * Real.sqrt x := by
      have hfour : Real.sqrt (4 : ℝ) = 2 := by norm_num
      calc
        _ ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith [(hz q).2, (hh q).2])
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hfour]
    calc
      _ ≤ Chebyshev.psi (z q + h q) - Chebyshev.theta (z q + h q) := he
      _ ≤ Cp * Real.sqrt (z q + h q) := hCp _
      _ ≤ |Cp| * Real.sqrt (z q + h q) :=
        mul_le_mul_of_nonneg_right (le_abs_self Cp) (Real.sqrt_nonneg _)
      _ ≤ |Cp| * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hs (abs_nonneg Cp)
  let S := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (q : ℝ) ≤ x ^ (1 / 100 : ℝ))
  have hsub : S ⊆ Icc 1 ⌊x ^ (1 / 100 : ℝ)⌋₊ := by
    intro q hq
    obtain ⟨hq, hcut⟩ := mem_filter.mp hq
    exact mem_Icc.mpr ⟨(mem_Icc.mp hq).1, Nat.le_floor hcut⟩
  have hcard : (S.card : ℝ) ≤ x ^ (1 / 100 : ℝ) := by
    calc
      _ ≤ ((Icc 1 ⌊x ^ (1 / 100 : ℝ)⌋₊).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      _ = (⌊x ^ (1 / 100 : ℝ)⌋₊ : ℝ) := by simp
      _ ≤ _ := Nat.floor_le (by positivity)
  have hpow : x ^ (51 / 100 : ℝ) ≤ y * Real.log x ^ (-A) := by
    have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
    rw [Real.rpow_neg hlog.le, ← div_eq_mul_inv, le_div_iff₀ hLA]
    calc
      _ ≤ x ^ (51 / 100 : ℝ) * x ^ (9 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left (hl x ((le_max_left _ _).trans hx)) (by positivity)
      _ = x ^ (3 / 5 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
      _ ≤ y := hxy
  change ∑ q ∈ S, _ ≤ _
  calc
    _ ≤ ∑ _q ∈ S, |Cp| * (2 * Real.sqrt x) := sum_le_sum fun q _ => hterm q
    _ = S.card * (|Cp| * (2 * Real.sqrt x)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ x ^ (1 / 100 : ℝ) * (|Cp| * (2 * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * |Cp|) * x ^ (51 / 100 : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (51 / 100 : ℝ) = 1 / 100 + 1 / 2 by norm_num,
        Real.rpow_add hxpos]
      ring
    _ ≤ (2 * |Cp|) * (y * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- The attained minimum in Huxley Iwaniec page 191 display 2.20 at theta 3 over 5
is exactly one twentieth. The minimizer is alpha equal to three quarters.
This formalizes the optimization only and assumes no zero density result. -/
theorem huxley_iwaniec_low_zero_density_minimum : IsLeast
    ((fun α : ℝ => (1 - α) * (3 * (3 / 5) - 1 - α) / (4 - 5 * α)) ''
      Set.Icc (1 / 2 : ℝ) (3 / 4)) (1 / 20 : ℝ) := by
  constructor
  · refine ⟨3 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
    norm_num
  · rintro v ⟨α, hα, rfl⟩
    exact huxley_iwaniec_low_zero_density_margin α hα.2

end LeanLab.Halupczok2012.Feed1122SmallModuli

#print axioms LeanLab.Halupczok2012.Feed1122SmallModuli.small_moduli_of_leaves

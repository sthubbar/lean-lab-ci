import LeanLab.GoldbachAverage.Decomp402f
import LeanLab.GoldbachAverage.FinitePower444

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 pages 18 and 19, high zero proof.
The difference and translation step is separate from oscillatory pair integration.
The reciprocal square tail and separation count are already proved.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444c
open MeasureTheory
open Decomp287d Decomp402f

/-- The high zero primitive sum in the last display on BHMS page 18.
The two cutoffs and all multiplicities are retained. -/
def highPrimitive (x h u : ℝ) : ℂ :=
  zeroSum (fun ρ => if x / h < |ρ.im| ∧ |ρ.im| ≤ x then (u : ℂ) ^ ρ / ρ else 0)

/-- BHMS page 18 high cutoff sums have finite support, with the actual zero multiplicities. -/
theorem high_sum_finite (x h : ℝ) (hx : 0 ≤ x) :
    ∃ S : Finset NontrivialZero,
      (∀ ρ : NontrivialZero, ρ ∈ S ↔ x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x) ∧
      ∀ f : ℂ → ℂ,
        zeroSum (fun ρ => if x / h < |ρ.im| ∧ |ρ.im| ≤ x then f ρ else 0) =
          ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1 := by
  classical
  have hf : {ρ : NontrivialZero | x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x}.Finite :=
    (PairKernel402.low_zeros_finite x hx).subset (fun _ hp => hp.2)
  refine ⟨hf.toFinset, fun ρ => hf.mem_toFinset, ?_⟩
  intro f
  unfold zeroSum
  rw [tsum_eq_sum (s := hf.toFinset)]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have hp : x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x := hf.mem_toFinset.mp hρ
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then f ρ.1 else 0) = _
    rw [if_pos hp]
  · intro ρ hρ
    have hp : ¬ (x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x) := fun hc => hρ (hf.mem_toFinset.mpr hc)
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then f ρ.1 else 0) = 0
    rw [if_neg hp, mul_zero]

/-- BHMS page 18, the high primitive is a continuous finite sum of complex powers. -/
theorem highPrimitive_continuous (x h : ℝ) (hx : 0 ≤ x) :
    Continuous (fun u : ℝ => highPrimitive x h u) := by
  obtain ⟨S, _, he⟩ := high_sum_finite x h hx
  have heq : (fun u : ℝ => highPrimitive x h u) =
      (fun u : ℝ => ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((u : ℂ) ^ ρ.1 / ρ.1)) := by
    funext u
    exact he (fun ρ => (u : ℂ) ^ ρ / ρ)
  rw [heq]
  apply continuous_finsetSum
  intro ρ hρ
  exact ((Complex.continuous_ofReal_cpow_const ρ.2.2.1).div_const _).const_mul _

/-- BHMS page 18 difference before the final three displays, with finite sums justified. -/
theorem highZeros_eq_difference (x h t : ℝ) (hx : 0 ≤ x) :
    highZeros x h t = highPrimitive x h (t + h) - highPrimitive x h t := by
  obtain ⟨S, _, he⟩ := high_sum_finite x h hx
  unfold highZeros highPrimitive
  rw [he, he, he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- LEAF. BHMS page 18 final three displays, removing the high increment difference.
The two squared terms translate into subsets of x to three x.
The elementary square difference inequality gives the explicit constant four. -/
theorem high_difference_energy (x h : ℝ) (hx : 2 ≤ x) (hh : 2 ≤ h) (hhx : h ≤ x) :
    IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
    (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
      4 * ∫ u in x..(3 * x), ‖highPrimitive x h u‖ ^ 2 := by
  have hc := highPrimitive_continuous x h (by linarith)
  have hsq := hc.norm.pow 2
  have hcont : Continuous (fun t : ℝ => ‖highZeros x h t‖ ^ 2) := by
    have he : (fun t : ℝ => highZeros x h t) =
        (fun t : ℝ => highPrimitive x h (t + h) - highPrimitive x h t) := by
      funext t
      exact highZeros_eq_difference x h t (by linarith)
    change Continuous ((fun t : ℂ => ‖t‖ ^ 2) ∘ (fun t : ℝ => highZeros x h t))
    rw [he]
    exact ((hc.comp (continuous_id.add continuous_const)).sub hc).norm.pow 2
  refine ⟨hcont.intervalIntegrable _ _, ?_⟩
  have hb (t : ℝ) : ‖highZeros x h t‖ ^ 2 ≤
      2 * ‖highPrimitive x h (t + h)‖ ^ 2 + 2 * ‖highPrimitive x h t‖ ^ 2 := by
    rw [highZeros_eq_difference x h t (by linarith)]
    have hn := norm_sub_le (highPrimitive x h (t + h)) (highPrimitive x h t)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [norm_nonneg (highPrimitive x h (t + h)),
      norm_nonneg (highPrimitive x h t), sq_nonneg (‖highPrimitive x h (t + h)‖ -
        ‖highPrimitive x h t‖)]
  have hbound := intervalIntegral.integral_mono_on (μ := volume) (by linarith : x ≤ 2 * x)
    (hcont.intervalIntegrable _ _) ((hsq.comp (continuous_id.add continuous_const)).const_mul 2
      |>.add (hsq.const_mul 2) |>.intervalIntegrable x (2 * x)) (fun t _ => hb t)
  have hi1 : (∫ t in x..(2 * x), ‖highPrimitive x h (t + h)‖ ^ 2) ≤
      ∫ t in x..(3 * x), ‖highPrimitive x h t‖ ^ 2 := by
    rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => ‖highPrimitive x h u‖ ^ 2) h]
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hsq.intervalIntegrable _ _)
  have hi2 : (∫ t in x..(2 * x), ‖highPrimitive x h t‖ ^ 2) ≤
      ∫ t in x..(3 * x), ‖highPrimitive x h t‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hsq.intervalIntegrable _ _)
  change (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
    (∫ t in x..(2 * x), 2 * ‖highPrimitive x h (t + h)‖ ^ 2 +
      2 * ‖highPrimitive x h t‖ ^ 2) at hbound
  have hiA : IntervalIntegrable (fun t : ℝ => 2 * ‖highPrimitive x h (t + h)‖ ^ 2)
      volume x (2 * x) := by
    exact ((hsq.comp (continuous_id.add continuous_const)).const_mul 2).intervalIntegrable _ _
  have hiB : IntervalIntegrable (fun t : ℝ => 2 * ‖highPrimitive x h t‖ ^ 2)
      volume x (2 * x) := (hsq.const_mul 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hiA hiB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  linarith

/-- LEAF. BHMS page 19 first two displays, integrating the high primitive square.
Expand into complex power pairs, bound reciprocal ordinate products by squares,
and use symmetry to obtain the existing asymmetric highPairWeight.
This assertion contains no reciprocal tail count. -/
theorem high_primitive_pair_energy : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∫ u in x..(3 * x), ‖highPrimitive x h u‖ ^ 2) ≤
        K * x ^ (2 * Theta + 1) * highPairWeight x h := by
  intro hlo hhi
  refine ⟨112, by norm_num, ?_⟩
  intro x h hx hh hhx
  classical
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  obtain ⟨H, hH, he⟩ := high_sum_finite x h hx0.le
  let S := (PairKernel402.low_zeros_finite x hx0.le).toFinset
  have hS (ρ : NontrivialZero) : ρ ∈ S ↔ |ρ.1.im| ≤ x := Set.Finite.mem_toFinset _
  have hsub : H ⊆ S := fun ρ hρ => (hS ρ).mpr ((hH ρ).mp hρ).2
  let m : NontrivialZero → ℝ := fun ρ => analyticOrderNatAt riemannZeta ρ.1
  let g : NontrivialZero → ℝ := fun ρ => |ρ.1.im|
  let T : NontrivialZero → NontrivialZero → ℝ := fun ρ σ =>
    (m ρ / g ρ ^ 2) * (m σ / (1 + |ρ.1.im - σ.1.im|))
  have hg (ρ : NontrivialZero) (hρ : ρ ∈ H) : 0 < g ρ := by
    have hcut := ((hH ρ).mp hρ).1
    have hxh : 0 < x / h := div_pos hx0 hh0
    exact lt_trans hxh hcut
  have hn (ρ : NontrivialZero) (hρ : ρ ∈ H) : 0 < ‖ρ.1‖ :=
    lt_of_lt_of_le (hg ρ hρ) (Complex.abs_im_le_norm ρ.1)
  have hin (ρ : NontrivialZero) :
      (∑' σ : NontrivialZero, if |σ.1.im| ≤ x then
        (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|) else 0) =
        ∑ σ ∈ S, m σ / (1 + |ρ.1.im - σ.1.im|) := by
    rw [tsum_eq_sum (s := S) (fun σ hσ => if_neg (fun hc => hσ ((hS σ).mpr hc)))]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [if_pos ((hS σ).mp hσ)]
  have hweight : highPairWeight x h = ∑ ρ ∈ H,
      (m ρ / g ρ ^ 2) * (∑ σ ∈ S, m σ / (1 + |ρ.1.im - σ.1.im|)) := by
    unfold highPairWeight
    rw [tsum_eq_sum (s := H) (fun ρ hρ => if_neg (fun hc => hρ ((hH ρ).mpr hc)))]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [if_pos ((hH ρ).mp hρ), hin]
  have hpartial : (∑ ρ ∈ H, ∑ σ ∈ H, T ρ σ) ≤ highPairWeight x h := by
    rw [hweight]
    apply Finset.sum_le_sum
    intro ρ hρ
    dsimp only [T]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by dsimp [m]; positivity)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro σ _ _
    dsimp [m]
    positivity
  have hswap : (∑ ρ ∈ H, ∑ σ ∈ H, T σ ρ) = ∑ ρ ∈ H, ∑ σ ∈ H, T ρ σ := by
    rw [Finset.sum_comm]
  have hP (u : ℝ) : highPrimitive x h u =
      ∑ ρ ∈ H, ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) / ρ.1) * (u : ℂ) ^ ρ.1 := by
    unfold highPrimitive
    rw [he]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  have hb := FinitePower444.finite_power_energy H
    (fun ρ => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) / ρ.1) (fun ρ => ρ.1)
    (fun ρ _ => ρ.2.2.2.le) x hx0
  simp only [norm_div, Complex.norm_natCast] at hb
  have hterm (ρ : NontrivialZero) (hρ : ρ ∈ H) (σ : NontrivialZero) (hσ : σ ∈ H) :
      56 * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) *
        ((analyticOrderNatAt riemannZeta σ.1 : ℝ) / ‖σ.1‖) *
        x ^ (ρ.1.re + σ.1.re + 1) / (1 + |ρ.1.im - σ.1.im|) ≤
      (56 * x ^ (2 * Theta + 1)) * (T ρ σ + T σ ρ) := by
    have hnorm : g ρ * g σ ≤ ‖ρ.1‖ * ‖σ.1‖ := mul_le_mul
      (Complex.abs_im_le_norm ρ.1) (Complex.abs_im_le_norm σ.1)
      (hg σ hσ).le (norm_nonneg _)
    have hinv : 1 / (‖ρ.1‖ * ‖σ.1‖) ≤ 1 / g ρ ^ 2 + 1 / g σ ^ 2 :=
      (one_div_le_one_div_of_le (mul_pos (hg ρ hρ) (hg σ hσ)) hnorm).trans
        (FinitePower444.reciprocal_pair (g ρ) (g σ) (hg ρ hρ) (hg σ hσ))
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
      (show ρ.1.re + σ.1.re + 1 ≤ 2 * Theta + 1 from by
        linarith [GSCor2.re_le_Theta ρ, GSCor2.re_le_Theta σ])
    have hm := mul_le_mul hp hinv (by positivity) (by positivity : 0 ≤ x ^ (2 * Theta + 1))
    have hw := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 56 * m ρ * m σ / (1 + |ρ.1.im - σ.1.im|) by dsimp [m]; positivity)
    dsimp only [T, m] at *
    have hsep : |σ.1.im - ρ.1.im| = |ρ.1.im - σ.1.im| := abs_sub_comm _ _
    rw [hsep]
    convert hw using 1 <;>
      field_simp [(hn ρ hρ).ne', (hn σ hσ).ne', (hg ρ hρ).ne', (hg σ hσ).ne',
        show 1 + |ρ.1.im - σ.1.im| ≠ 0 by positivity] <;> ring
  calc (∫ u in x..(3 * x), ‖highPrimitive x h u‖ ^ 2)
      = ∫ u in x..(3 * x), ‖∑ ρ ∈ H,
          ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) / ρ.1) * (u : ℂ) ^ ρ.1‖ ^ 2 := by
        simp_rw [hP]
    _ ≤ _ := hb
    _ ≤ ∑ ρ ∈ H, ∑ σ ∈ H, (56 * x ^ (2 * Theta + 1)) * (T ρ σ + T σ ρ) :=
      Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun σ hσ => hterm ρ hρ σ hσ
    _ = (112 * x ^ (2 * Theta + 1)) * (∑ ρ ∈ H, ∑ σ ∈ H, T ρ σ) := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hpartial
        (show 0 ≤ 112 * x ^ (2 * Theta + 1) by positivity)
      simpa only [mul_assoc] using hm

/-- The exact high_pair_integral target follows from the smaller high zero steps.
The difference and pair integration components are both proved. -/
theorem high_pair_integral_assembled : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖highZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) ≤
        K * x ^ (2 * Theta + 1) * highPairWeight x h := by
  intro hlo hhi
  obtain ⟨K, hK, hE⟩ := high_primitive_pair_energy hlo hhi
  refine ⟨4 * K, by positivity, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := high_difference_energy x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  calc 4 * (∫ u in x..(3 * x), ‖highPrimitive x h u‖ ^ 2)
      ≤ 4 * (K * x ^ (2 * Theta + 1) * highPairWeight x h) :=
        mul_le_mul_of_nonneg_left (hE x h hx hh hhx) (by norm_num)
    _ = _ := by ring

example : type_of% Decomp402f.high_pair_integral = type_of% high_pair_integral_assembled := rfl

end LeanLab.GoldbachAverage.Decomp444c

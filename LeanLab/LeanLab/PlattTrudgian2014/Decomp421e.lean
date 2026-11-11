/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 174, the finite power expansion and Taylor regrouping in display 4.11.
-/
import LeanLab.PlattTrudgian2014.FiniteCosine421

namespace LeanLab.PlattTrudgian2014

set_option maxHeartbeats 2000000

/-- LEAF. P0026 page 174, every finite power has nonnegative cosine coefficients.
The coefficient mass is its value at zero. There is no exponential or infinite Taylor regrouping. -/
theorem real_power_cosine_coefficients421 (L n : ℕ) :
    ∃ b : ℕ → ℝ, (∀ k, 0 ≤ b k) ∧ Function.HasFiniteSupport b ∧ Summable b ∧
      (∑' k : ℕ, b k) = (L : ℝ) ^ n ∧
      ∀ x : ℝ, (G L x).re ^ n = ∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * x) := by
  exact real_power_cosine_coefficients_proved421 L n

/-- P0026 page 174 display 4.11, absolutely convergent Taylor coefficients can be regrouped by frequency. -/
theorem cosine_Taylor_regroup421 (t A : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (f : ℝ → ℝ) (b : ℕ → ℕ → ℝ) (hb : ∀ n k, 0 ≤ b n k)
    (hs : ∀ n, Summable (b n)) (hmass : ∀ n, (∑' k : ℕ, b n k) = A ^ n)
    (hpow : ∀ n x, f x ^ n = ∑' k : ℕ, b n k * Real.cos (2 * Real.pi * k * x)) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable (fun k => |a k|) ∧
      ∀ x : ℝ, Real.exp (t * f x) = ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x) := by
  let w : ℕ → ℕ → ℝ := fun n k => (t ^ n / n.factorial) * b n k
  have hwp (n k : ℕ) : 0 ≤ w n k :=
    mul_nonneg (div_nonneg (pow_nonneg ht n) (Nat.cast_nonneg _)) (hb n k)
  have hw : Summable (fun p : ℕ × ℕ => w p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p => hwp p.1 p.2)).mpr
    constructor
    · intro n
      change Summable (fun k : ℕ => (t ^ n / (n.factorial : ℝ)) * b n k)
      exact (hs n).mul_left (t ^ n / (n.factorial : ℝ))
    · change Summable (fun n : ℕ => ∑' k : ℕ, w n k)
      have he (n : ℕ) : (∑' k : ℕ, w n k) = (t * A) ^ n / n.factorial := by
        dsimp only [w]
        rw [tsum_mul_left, hmass n, mul_pow]
        ring
      simp_rw [he]
      exact NormedSpace.expSeries_div_summable (t * A)
  have hws : Summable (fun p : ℕ × ℕ => w p.2 p.1) :=
    hw.comp_injective (Equiv.prodComm ℕ ℕ).injective
  have hcols := (summable_prod_of_nonneg (fun p : ℕ × ℕ => hwp p.2 p.1)).mp hws
  let a : ℕ → ℝ := fun k => ∑' n : ℕ, w n k
  have hap (k : ℕ) : 0 ≤ a k := tsum_nonneg fun n => hwp n k
  refine ⟨a, hap, ?_, fun x => ?_⟩
  · have he : (fun k => |a k|) = a := funext fun k => abs_of_nonneg (hap k)
    rw [he]
    exact hcols.2
  · have hbound (p : ℕ × ℕ) :
        ‖w p.1 p.2 * Real.cos (2 * Real.pi * p.2 * x)‖ ≤ w p.1 p.2 := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hwp p.1 p.2)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hwp _ _)).trans_eq (mul_one _)
    have hfunc : Summable (Function.uncurry (fun n k =>
        w n k * Real.cos (2 * Real.pi * k * x))) := hw.of_norm_bounded hbound
    have hrow (n : ℕ) : (∑' k : ℕ, w n k * Real.cos (2 * Real.pi * k * x)) =
        (t * f x) ^ n / n.factorial := by
      calc
        _ = (t ^ n / n.factorial) * (∑' k : ℕ, b n k * Real.cos (2 * Real.pi * k * x)) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro k
          dsimp only [w]
          ring
        _ = _ := by rw [← hpow n x, mul_pow]; ring
    have hexp : HasSum (fun n : ℕ => (t * f x) ^ n / n.factorial) (Real.exp (t * f x)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    calc
      _ = ∑' n : ℕ, (t * f x) ^ n / n.factorial := hexp.tsum_eq.symm
      _ = ∑' n : ℕ, ∑' k : ℕ, w n k * Real.cos (2 * Real.pi * k * x) := by simp_rw [hrow]
      _ = ∑' k : ℕ, ∑' n : ℕ, w n k * Real.cos (2 * Real.pi * k * x) := hfunc.tsum_comm.symm
      _ = _ := by simp_rw [tsum_mul_right]; rfl

/-- P0026 page 174 display 4.11, exact existing positive exponential cosine expansion.
The finite power coefficient leaf is proved in FiniteCosine421. -/
theorem positive_cosine_expansion_decomposed421 (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable (fun k => |a k|) ∧
      ∀ x : ℝ, Real.exp (t * (G L x).re) =
        ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x) := by
  choose b hb hfin hs hm hp using real_power_cosine_coefficients421 L
  exact cosine_Taylor_regroup421 t L ht (Nat.cast_nonneg _) (fun x => (G L x).re) b hb hs hm hp

set_option format.width 240
#print axioms real_power_cosine_coefficients421
#print axioms cosine_Taylor_regroup421
#print axioms positive_cosine_expansion_decomposed421

end LeanLab.PlattTrudgian2014

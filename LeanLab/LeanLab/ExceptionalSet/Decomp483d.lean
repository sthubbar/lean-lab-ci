import LeanLab.ExceptionalSet.Decomp483a
import LeanLab.ExceptionalSet.Energy446

/-!
P0082 page369 display38, derived weighted mass supplies.
Balancing the compact interval and the tail improves the inherited inverse Delta loss.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483d
open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp)

/-- P0082 page365 before display24 and page369 display38. A symmetric
integer interval contains twice its radius many periods of prime energy. -/
theorem prime_energy_symmetric_nat (P X : ℝ) (hX : 2 ≤ X) (K : ℕ) :
    (∫ α in (-(K : ℝ))..(K : ℝ), ‖Sp P X α‖ ^ 2) ≤
      2 * K * (Real.log 4 * X * Real.log X) := by
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [Decomp371a.Sp_periodic P X α]
  have he := hp.intervalIntegral_add_zsmul_eq (2 * (K : ℤ)) (-(K : ℝ))
    (fun a b => hc.intervalIntegrable a b)
  have hend : -(K : ℝ) + (2 * (K : ℤ)) • (1 : ℝ) = (K : ℝ) := by
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  rw [hend] at he
  calc _ = (2 * (K : ℤ)) • (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := he
    _ = 2 * (K : ℝ) * (∫ α in (-(K : ℝ))..(-(K : ℝ)) + 1, ‖Sp P X α‖ ^ 2) := by
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (PrimeEnergy385.prime_energy_le P X (-(K : ℝ)) hX)
      (by positivity)

/-- P0082 page369 display38, auxiliary explicit cutoff bound. The compact
part uses the shifted kernel bound one. The two tails use OddTail467. -/
theorem shifted_weighted_mass_cutoff (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (K : ℕ) (hK : 2 ≤ K) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖) ≤
      2 * K * (Real.log 4 * X * Real.log X) +
      4 * (Real.log 4 * X * Real.log X) /
        (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := Real.log 4 * X * Real.log X
  let g := fun α : ℝ => ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖
  have hg : Integrable g := by
    simpa only [g, OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
      (OddTail467.total_integrable P X Δ 0 hΔ hΔ1).norm
  have hc : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2) := by unfold Sp U1539.eC; fun_prop
  have hgc : Continuous g := by
    exact (((by unfold Sp U1539.eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hk (α : ℝ) : ‖OddKernel467.evenKernel Δ α‖ ≤ 1 := by
    rw [OddTail467.norm_evenKernel]
    have h := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * α) hΔ hΔ1
    linarith
  have hab : -(K : ℝ) ≤ (K : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hcenter : (∫ α in Icc (-(K : ℝ)) (K : ℝ), g α) ≤ 2 * K * A := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ α in (-(K : ℝ))..(K : ℝ), ‖Sp P X α‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hab (hgc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)
        intro α hα
        dsimp only [g]
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (sq_nonneg _) (hk α)
      _ ≤ _ := prime_energy_symmetric_nat P X hX K
  have htail : (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, g α) ≤
      4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
    simpa only [g, A, OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
      OddTail467.outside_nat_tail_le P X Δ 0 hX hΔ hΔ1 K hK
  have hs := integral_add_compl (μ := volume) (s := Icc (-(K : ℝ)) (K : ℝ))
    measurableSet_Icc hg
  change (∫ α, g α) ≤ _
  rw [← hs]
  exact add_le_add hcenter htail

/-- P0082 page369 display38, derived weaker weighted mass bound. Choosing
an integer cutoff near one over square root Delta improves the old inverse Delta loss. -/
theorem shifted_weighted_mass_sqrt (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖) ≤
      7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ := by
  let d := Real.sqrt Δ
  let A := Real.log 4 * X * Real.log X
  let K : ℕ := ⌈1 / d⌉₊ + 1
  have hd : 0 < d := Real.sqrt_pos.mpr hΔ
  have hd1 : d ≤ 1 := Real.sqrt_le_one.mpr hΔ1.le
  have hsq : d ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have ht0 : 0 < 1 / d := by positivity
  have ht1 : 1 ≤ 1 / d := (one_le_div hd).mpr hd1
  have hceil : 1 ≤ ⌈1 / d⌉₊ := Nat.one_le_ceil_iff.mpr ht0
  have hK : 2 ≤ K := by dsimp only [K]; omega
  have hKu : (K : ℝ) ≤ 3 / d := by
    have h := (Nat.ceil_lt_add_one ht0.le).le
    dsimp only [K]
    push_cast
    rw [show 3 / d = 3 * (1 / d) by ring]
    linarith only [h, ht1]
  have hKl : 1 / d ≤ (K : ℝ) - 1 := by
    have h := Nat.le_ceil (1 / d)
    dsimp only [K]
    push_cast
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    positivity
  have hprod : d ≤ Δ * ((K : ℝ) - 1) := by
    calc d = Δ * (1 / d) := by rw [← hsq]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hKl hΔ.le
  have hpi : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hden : 4 * d ≤ Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := by
    calc _ ≤ Real.pi ^ 2 * d := mul_le_mul_of_nonneg_right hpi hd.le
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hprod (sq_nonneg Real.pi) using 1; ring
  have hden0 : 0 < Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := (by positivity : 0 < 4 * d).trans_le hden
  have htail : 4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) ≤ A / d := by
    apply (div_le_div_iff₀ hden0 hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden hA]
  have hcenter : 2 * K * A ≤ 6 * A / d := by
    calc _ ≤ 2 * (3 / d) * A := by gcongr
      _ = _ := by ring
  calc _ ≤ 2 * K * A + 4 * A / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) :=
      shifted_weighted_mass_cutoff P X Δ hX hΔ hΔ1 K hK
    _ ≤ 6 * A / d + A / d := add_le_add hcenter htail
    _ = _ := by dsimp only [A, d]; ring

end LeanLab.ExceptionalSet.Decomp483d

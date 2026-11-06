import LeanLab.HardyLittlewood1923.Series415
import LeanLab.HardyLittlewood1923.Decomp415a
import LeanLab.HardyLittlewood1923.Decomp296Farey
import LeanLab.HardyLittlewood1923.Decomp296Transfer

/-!
AI wrote this Lean code for CODEX task415.
P0004 page 22 equations 3.115 to 3.119 and page 25 equation 3.142.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp415b

open Real Finset MeasureTheory
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b

/-- The actual cubic prime integral on one translated Farey arc.
P0004 page 22 equation 3.116, the local j integral. -/
noncomputable def primeArc (n p q : ℕ) : ℂ :=
  (1 / (2 * π : ℂ)) *
    ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
      Complex.exp ((n : ℂ) * localY n θ) *
        primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) ^ 3

/-- LEAF. P0004 page 22 equation 3.115.
Cubic coefficient extraction on the full circle gives an exact identity.
There is no Farey dissection, rational approximation or square mean bound here. -/
theorem coefficient_integral {n : ℕ} (hn : 4 ≤ n) :
    (nur 3 n : ℂ) = (1 / (2 * π : ℂ)) *
      ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((n : ℂ) * localY n θ) *
        primeSeries (localY n θ) ^ 3 := by
  sorry

/-- P0004 page 22 equation 3.116.
The coefficient weight has period two pi because n is an integer. -/
theorem circle_weight_periodic (n : ℕ) :
    Function.Periodic (fun θ : ℝ => Complex.exp ((n : ℂ) * localY n θ)) (2 * π) := by
  intro θ
  dsimp only
  have he : (n : ℂ) * localY n (θ + 2 * π) =
      (n : ℂ) * localY n θ - (n : ℂ) * (2 * π * Complex.I) := by
    simp only [localY, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_sub]
  simp only [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, div_one]

/-- P0004 page 22 equations 3.115 and 3.116.
The exact cubic dissection uses the shared geometric leaf.
CONDITIONAL on coefficient_integral and farey_integral_dissection. -/
theorem coefficient_dissection {n : ℕ} (hn : 4 ≤ n) :
    (nur 3 n : ℂ) =
      ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) * primeArc n p q := by
  have hnpos : 0 < n := by omega
  let f : ℝ → ℂ := fun θ => Complex.exp ((n : ℂ) * localY n θ) *
    primeSeries (localY n θ) ^ 3
  have hw : Continuous (fun θ : ℝ => Complex.exp ((n : ℂ) * localY n θ)) := by
    unfold localY
    fun_prop
  have hf : Continuous f := hw.mul ((Series415.continuous_prime_circle hnpos).pow 3)
  have hp : Function.Periodic f (2 * π) := by
    intro θ
    have hwper := circle_weight_periodic n θ
    have hfper := Series415.periodic_prime_circle n θ
    dsimp only at hwper hfper
    dsimp only [f]
    rw [hwper, hfper]
  have hpart := Decomp415a.farey_integral_dissection
    (show 1 ≤ Nat.sqrt n from Nat.le_sqrt.mpr (by omega)) f hf hp
  rw [coefficient_integral hn, ← hpart, mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [mul_sum]
  apply sum_congr rfl
  intro p hpq
  have hshift (θ : ℝ) :
      Complex.exp ((n : ℂ) * localY n (2 * π * (p : ℝ) / q + θ)) =
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
          Complex.exp ((n : ℂ) * localY n θ) := by
    rw [show (n : ℂ) * localY n (2 * π * (p : ℝ) / q + θ) =
        (-2 * π * Complex.I * (n : ℂ) * p / q) + (n : ℂ) * localY n θ by
      simp only [localY, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_natCast]
      ring, Complex.exp_add]
  rw [primeArc]
  calc
    _ = (1 / (2 * π : ℂ)) *
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
            (Complex.exp ((n : ℂ) * localY n θ) *
              primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) ^ 3) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp [f]
      rw [hshift]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- P0004 page 22 before equation 3.117.
The coefficient weight has constant norm exp of one on the chosen circle. -/
theorem circle_weight_norm {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ‖Complex.exp ((n : ℂ) * localY n θ)‖ = Real.exp 1 := by
  rw [Complex.norm_exp]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [localY, hnR]

/-- P0004 page 22 equation 3.118 and page 25 equation 3.151.
The existing modelArc is the integral of the cube of localPhi with the same weight. -/
theorem modelArc_eq_integral (n p q : ℕ) :
    modelArc n p q = (1 / (2 * π : ℂ)) *
      ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
        Complex.exp ((n : ℂ) * localY n θ) * localPhi n q θ ^ 3 := by
  unfold modelArc
  rw [mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  change ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
      ((localY n θ) ^ (-3 : ℤ) * Complex.exp ((n : ℂ) * localY n θ)) = _
  simp only [localPhi, div_pow, div_eq_mul_inv, zpow_neg,
    zpow_ofNat, ← inv_pow]
  ring

/-- P0004 pages 22 and 23 equations 3.118 and 3.121.
The rational approximation is continuous in angle on every positive radius circle. -/
theorem continuous_localPhi {n : ℕ} (hn : 0 < n) (q : ℕ) :
    Continuous (localPhi n q) := by
  have hY : Continuous (localY n) := by unfold localY; fun_prop
  apply continuous_const.div hY
  intro θ h
  have hh := congrArg Complex.re h
  rw [localY_re] at hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Complex.zero_re] at hh
  exact (one_div_ne_zero hnR.ne') hh

/-- P0004 page 22 equation 3.119 at r equal to three.
One actual arc differs from its model by the cubic square mean estimate.
Only the finite pointwise error bound is an input. -/
theorem primeArc_error {n p q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hqN : q ≤ Nat.sqrt n) (hp : p < q) (hpq : p.Coprime q)
    {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ θ : ℝ,
      θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ E) :
    ‖primeArc n p q - modelArc n p q‖ ≤
      (3 * Real.exp 1 / (4 * π)) * E *
        ((∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
         (∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ‖localPhi n q θ‖ ^ 2)) := by
  let L := arcLeft (Nat.sqrt n) p q
  let R := arcRight (Nat.sqrt n) p q
  let f : ℝ → ℂ := fun θ => primeSeries (localY n (2 * π * (p : ℝ) / q + θ))
  let g : ℝ → ℂ := localPhi n q
  let w : ℝ → ℂ := fun θ => Complex.exp ((n : ℂ) * localY n θ)
  have hnpos : 0 < n := by omega
  have hN : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  obtain ⟨hL, hR⟩ := Decomp296Farey.arc_widths hN hq hqN hp hpq
  have hLR : L ≤ R := by
    have ht : 0 < 1 / (2 * (q : ℝ) * Nat.sqrt n) := by positivity
    dsimp [L, R]
    linarith
  have hf : Continuous f :=
    (Series415.continuous_prime_circle hnpos).comp (continuous_const.add continuous_id)
  have hg : Continuous g := continuous_localPhi hnpos q
  have hw : Continuous w := by dsimp [w, localY]; fun_prop
  have hf2 : IntervalIntegrable (fun θ => ‖f θ‖ ^ 2) volume L R :=
    (hf.norm.pow 2).intervalIntegrable L R
  have hg2 : IntervalIntegrable (fun θ => ‖g θ‖ ^ 2) volume L R :=
    (hg.norm.pow 2).intervalIntegrable L R
  have ht := Decomp296Transfer.cubic_integral_transfer
    (μ := volume.restrict (Set.Ioc L R)) hE (le_of_lt (Real.exp_pos 1))
    hf.aestronglyMeasurable hg.aestronglyMeasurable hw.aestronglyMeasurable
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hLR).mp hf2)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hLR).mp hg2)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
        exact hbound θ ⟨hθ.1.le, hθ.2⟩)
    (by filter_upwards [] with θ
        exact (circle_weight_norm hnpos θ).le)
  have hid : primeArc n p q - modelArc n p q =
      (1 / (2 * π : ℂ)) * ∫ θ in L..R, w θ * (f θ ^ 3 - g θ ^ 3) := by
    rw [primeArc, modelArc_eq_integral, ← mul_sub]
    change (1 / (2 * π : ℂ)) *
      ((∫ θ in L..R, w θ * f θ ^ 3) - (∫ θ in L..R, w θ * g θ ^ 3)) = _
    have hif : IntervalIntegrable (fun θ => w θ * f θ ^ 3) volume L R :=
      (hw.mul (hf.pow 3)).intervalIntegrable L R
    have hig : IntervalIntegrable (fun θ => w θ * g θ ^ 3) volume L R :=
      (hw.mul (hg.pow 3)).intervalIntegrable L R
    rw [← intervalIntegral.integral_sub hif hig]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [f, g, w]
    ring
  rw [hid, norm_mul]
  have hc : ‖(1 / (2 * π : ℂ))‖ = 1 / (2 * π) := by
    simp [norm_div, norm_mul, Real.pi_pos.le]
  rw [hc]
  have hi := ht.2
  rw [← intervalIntegral.integral_of_le hLR,
    ← intervalIntegral.integral_of_le hLR,
    ← intervalIntegral.integral_of_le hLR] at hi
  calc
    _ ≤ (1 / (2 * π)) * ((3 / 2 : ℝ) * Real.exp 1 * E *
          ((∫ θ in L..R, ‖f θ‖ ^ 2) + ∫ θ in L..R, ‖g θ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [L, R, f, g]; ring

/-- P0004 page 22 equations 3.115 to 3.119 and page 25 equation 3.142.
The exact sealed transfer target follows from coefficient_dissection and proved local estimates.
CONDITIONAL on coefficient_integral and the shared geometric partition. -/
theorem coefficient_transfer {n : ℕ} (hn : 4 ≤ n) {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ E) :
    ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
      (3 * Real.exp 1 / (4 * π)) * E *
        ((∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
         (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖localPhi n q θ‖ ^ 2)) := by
  rw [coefficient_dissection hn, fareyModel, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ‖Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
          (primeArc n p q - modelArc n p q)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun q _ => norm_sum_le _ _)
    _ ≤ ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        (3 * Real.exp 1 / (4 * π)) * E *
          ((∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
           (∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖localPhi n q θ‖ ^ 2)) := by
      apply sum_le_sum
      intro q hq
      apply sum_le_sum
      intro p hp
      have hphase : ‖Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [norm_mul, hphase, one_mul]
      exact primeArc_error hn (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
        (mem_range.mp (mem_filter.mp hp).1) (mem_filter.mp hp).2 hE
        (hbound q (mem_Icc.mp hq).1 (mem_Icc.mp hq).2 p
          (mem_range.mp (mem_filter.mp hp).1) (mem_filter.mp hp).2)
    _ = _ := by simp_rw [mul_add, sum_add_distrib, mul_sum]

#print axioms coefficient_dissection
#print axioms coefficient_integral
#print axioms circle_weight_periodic
#print axioms circle_weight_norm
#print axioms modelArc_eq_integral
#print axioms continuous_localPhi
#print axioms primeArc_error
#print axioms coefficient_transfer

end LeanLab.HardyLittlewood1923.Decomp415b

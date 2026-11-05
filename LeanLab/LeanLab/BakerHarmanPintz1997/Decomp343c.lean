/-
P0069 page 21, supply for the exact nonresonant discretization leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp343a
import LeanLab.BakerHarmanPintz1997.Decomp343b

noncomputable section

namespace LeanLab.BakerHarmanPintz1997.Decomp343c
open Finset MeasureTheory intervalIntegral Decomp343a Decomp343b
attribute [local instance] Classical.propDecidable

/-- Page 21 local implementation. The critical line power with real frequency t. -/
def critical (t y : ℝ) : ℂ := (y : ℂ) ^ ((-1 / 2 : ℂ) - (t : ℂ) * Complex.I)

/-- Page 21 local implementation. The derivative of the critical line power at positive y. -/
def criticalDeriv (t y : ℝ) : ℂ :=
  ((-1 / 2 : ℂ) - (t : ℂ) * Complex.I) *
    (y : ℂ) ^ (((-1 / 2 : ℂ) - (t : ℂ) * Complex.I) - 1)

/-- Page 21 Euler infrastructure. Differentiate the critical line term on the positive axis. -/
theorem critical_hasDerivAt (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (critical t) (criticalDeriv t y) y := by
  apply hasDerivAt_ofReal_cpow_const hy.ne'
  intro h
  have he := congrArg Complex.re h
  norm_num at he

/-- Page 21 Euler infrastructure. The critical line amplitude has inverse square root norm. -/
theorem critical_norm (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖critical t y‖ = y ^ (-1 / 2 : ℝ) := by
  rw [critical, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  norm_num

/-- Page 21 diagnostic. The absolute derivative has the full frequency factor. -/
theorem criticalDeriv_norm (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖criticalDeriv t y‖ = ‖(-1 / 2 : ℂ) - (t : ℂ) * Complex.I‖ * y ^ (-3 / 2 : ℝ) := by
  rw [criticalDeriv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  norm_num

/-- Page 21 Euler infrastructure. A uniform bound for the sum of shifted derivatives.
The absolute estimate handles small t and the first derivative test handles absolute t at least one. -/
theorem shifted_derivative_sum (a m : ℕ) (ha : 1 ≤ a) (hm : m ≤ a)
    (u t : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (ht : |t| ≤ a) :
    ‖∑ k ∈ range m, criticalDeriv t ((a : ℝ) + k + u)‖ ≤
      64 * (a : ℝ) ^ (-1 / 2 : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  let s : ℂ := (-1 / 2 : ℂ) - (t : ℂ) * Complex.I
  have hs : ‖s‖ ≤ |t| + 1 := by
    calc
      _ ≤ ‖(-1 / 2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ |t| + 1 := by simp; linarith
  have hexp : s - 1 = ((-3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I := by
    dsimp [s]
    push_cast
    ring
  have heq : (∑ k ∈ range m, criticalDeriv t ((a : ℝ) + k + u)) =
      s * ∑ k ∈ range m,
        ((a : ℝ) + k + u : ℂ) ^ (((-3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) := by
    simp only [criticalDeriv, ← mul_sum, s, hexp]
    congr 1
    apply sum_congr rfl
    intro k hk
    congr 1
    push_cast
    ring
  have hpow : (a : ℝ) ^ (-3 / 2 : ℝ) * a = (a : ℝ) ^ (-1 / 2 : ℝ) := by
    calc
      _ = (a : ℝ) ^ (-3 / 2 : ℝ) * (a : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (a : ℝ) ^ ((-3 / 2 : ℝ) + 1) := (Real.rpow_add ha0 _ _).symm
      _ = _ := by norm_num
  have hpos : 0 ≤ (a : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg ha0.le _
  rw [heq, norm_mul]
  by_cases ht1 : |t| ≤ 1
  · have hb := weighted_shifted_phase_sum a m ha u (-3 / 2) t a hu (by norm_num)
      (Nat.cast_nonneg a) (fun k hk => (shifted_phase_trivial a k ha u t hu).trans
        (by exact_mod_cast hk.trans hm))
    calc
      _ ≤ (|t| + 1) * ((a : ℝ) ^ (-3 / 2 : ℝ) * a) :=
        mul_le_mul hs hb (norm_nonneg _) (by positivity)
      _ = (|t| + 1) * (a : ℝ) ^ (-1 / 2 : ℝ) := by rw [hpow]
      _ ≤ 64 * (a : ℝ) ^ (-1 / 2 : ℝ) := by gcongr; linarith
  · have ht0 : 0 < |t| := by linarith [abs_nonneg t]
    have hb := weighted_shifted_phase_sum a m ha u (-3 / 2) t
      (8 * Real.pi * a / |t|) hu (by norm_num) (by positivity)
      (fun k hk => shifted_phase_sum a k ha (hk.trans hm) u t hu hu1 ht0 ht)
    calc
      _ ≤ (|t| + 1) * ((a : ℝ) ^ (-3 / 2 : ℝ) * (8 * Real.pi * a / |t|)) :=
        mul_le_mul hs hb (norm_nonneg _) (by positivity)
      _ = (|t| + 1) / |t| * (8 * Real.pi) * (a : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [← hpow]
        ring
      _ ≤ 2 * (8 * Real.pi) * (a : ℝ) ^ (-1 / 2 : ℝ) := by
        gcongr
        apply (div_le_iff₀ ht0).mpr
        linarith
      _ ≤ 64 * (a : ℝ) ^ (-1 / 2 : ℝ) := by
        gcongr
        linarith [Real.pi_le_four]

example : ‖∑ k ∈ range 2, criticalDeriv 1 ((4 : ℝ) + k + (1 / 2 : ℝ))‖ ≤
    64 * (4 : ℝ) ^ (-1 / 2 : ℝ) :=
  shifted_derivative_sum 4 2 (by norm_num) (by norm_num) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num)

/-- Page 21 Euler infrastructure. The derivative is continuous on the positive axis. -/
theorem criticalDeriv_continuousAt (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (criticalDeriv t) y := by
  exact continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const y _ (Or.inr hy.ne'))

/-- Page 21 Euler infrastructure. Exact Euler identity for the critical line power. -/
theorem critical_euler (a m : ℕ) (ha : 1 ≤ a) (t : ℝ) :
    (∑ k ∈ range m, critical t ((a : ℝ) + k + 1)) -
      (∫ y in (a : ℝ)..((a : ℝ) + m), critical t y) =
      ∫ u in (0 : ℝ)..1, (u : ℂ) *
        ∑ k ∈ range m, criticalDeriv t ((a : ℝ) + k + u) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hpos : ∀ (k : ℕ) (y : ℝ), y ∈ Set.uIcc ((a : ℝ) + k) ((a : ℝ) + k + 1) → 0 < y := by
    intro k y hy
    rw [Set.uIcc_of_le (by linarith : (a : ℝ) + k ≤ (a : ℝ) + k + 1)] at hy
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hy.1]
  apply euler_sum (critical t) (criticalDeriv t) (a : ℝ) m
  · intro k hk y hy
    exact (critical_hasDerivAt t (hpos k y hy)).continuousAt.continuousWithinAt
  · intro k hk y hy
    exact critical_hasDerivAt t (hpos k y hy)
  · intro k hk
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (criticalDeriv_continuousAt t (hpos k y hy)).continuousWithinAt
  · intro k hk
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hy : 0 < (a : ℝ) + k + u := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hu.1]
    have hc : ContinuousAt (fun v : ℝ => criticalDeriv t ((a : ℝ) + k + v)) u :=
      (criticalDeriv_continuousAt t hy).comp (by fun_prop)
    exact ((by fun_prop : ContinuousAt (fun v : ℝ => (v : ℂ)) u).mul hc).continuousWithinAt

/-- Page 21 Euler infrastructure. Integer aligned nonresonant quadrature bound. -/
theorem integer_discretization (a m : ℕ) (ha : 1 ≤ a) (hm : m ≤ a)
    (t : ℝ) (ht : |t| ≤ a) :
    ‖(∑ k ∈ range m, critical t ((a : ℝ) + k + 1)) -
      (∫ y in (a : ℝ)..((a : ℝ) + m), critical t y)‖ ≤
      64 * (a : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [critical_euler a m ha t]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun u : ℝ => (u : ℂ) * ∑ k ∈ range m, criticalDeriv t ((a : ℝ) + k + u))
    (C := 64 * (a : ℝ) ^ (-1 / 2 : ℝ)) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.1.le]
      have hs := shifted_derivative_sum a m ha hm u t hu.1.le hu.2 ht
      exact (mul_le_mul_of_nonneg_left hs hu.1.le).trans
        (by nlinarith [hu.2, Real.rpow_nonneg (Nat.cast_nonneg a) (-1 / 2 : ℝ)]))
  simpa using hb

/-- Page 21 endpoint infrastructure. The critical power is integrable between positive endpoints. -/
theorem critical_intervalIntegrable (t : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (critical t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hy0 : 0 < y := (lt_min ha hb).trans_le hy.1
  exact (critical_hasDerivAt t hy0).continuousAt.continuousWithinAt

/-- Page 21 endpoint infrastructure. An interval of length at most one costs one initial amplitude. -/
theorem short_critical_integral (N a b t : ℝ) (hN : 0 < N) (hNa : N ≤ a)
    (hab : a ≤ b) (hlen : b - a ≤ 1) :
    ‖∫ y in a..b, critical t y‖ ≤ N ^ (-1 / 2 : ℝ) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := critical t) (C := N ^ (-1 / 2 : ℝ)) (fun y hy => by
      rw [Set.uIoc_of_le hab] at hy
      have hNy : N ≤ y := hNa.trans hy.1.le
      rw [critical_norm t (hN.trans_le hNy)]
      exact Real.rpow_le_rpow_of_nonpos hN hNy (by norm_num))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  exact hb.trans (by nlinarith [Real.rpow_nonneg hN.le (-1 / 2 : ℝ)])

/-- Page 21 finite sum bookkeeping. Right endpoints of m cells form a natural open closed interval. -/
theorem sum_right_cells (f : ℝ → ℂ) (a m : ℕ) :
    (∑ n ∈ Ioc a (a + m), f n) = ∑ k ∈ range m, f ((a : ℝ) + k + 1) := by
  symm
  apply sum_bij (fun (k : ℕ) _ => a + k + 1)
  · intro k hk
    have := mem_range.mp hk
    exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro k hk l hl h
    omega
  · intro n hn
    have := mem_Ioc.mp hn
    exact ⟨n - a - 1, mem_range.mpr (by omega), by omega⟩
  · intro k hk
    push_cast
    rfl

/-- Page 21 local implementation. The power convention equals the weighted phase in the leaf. -/
theorem critical_eq_product (t : ℝ) {y : ℝ} (hy : 0 < y) :
    critical t y = (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rw [critical, show (-1 / 2 : ℂ) - (t : ℂ) * Complex.I =
      (-1 / 2 : ℂ) + (-(t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hy.ne')]

/-- Page 21 supply. Fractional endpoints cost at most three initial amplitudes. -/
theorem real_discretization (N N1 t : ℝ) (hN : 1 ≤ N) (hNN1 : N ≤ N1)
    (hN1 : N1 ≤ 2 * N) (ht : |t| ≤ N) :
    ‖(∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n) -
      (∫ y in N..N1, critical t y)‖ ≤ 67 * N ^ (-1 / 2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hN10 : 0 < N1 := hN0.trans_le hNN1
  let a : ℕ := ⌊N⌋₊ + 1
  let b : ℕ := ⌊N1⌋₊
  have ha : 1 ≤ a := by dsimp [a]; omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hNa : N < (a : ℝ) := by simpa [a] using Nat.lt_floor_add_one N
  have haN : (a : ℝ) ≤ N + 1 := by
    have hh := Nat.floor_le hN0.le
    dsimp [a]
    push_cast
    linarith
  have hbN1 : (b : ℝ) ≤ N1 := Nat.floor_le hN10.le
  have hN1b : N1 < (b : ℝ) + 1 := Nat.lt_floor_add_one N1
  have hp : 0 ≤ N ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
  by_cases hab : a ≤ b
  · have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hb0 : (0 : ℝ) < b := ha0.trans_le habR
    have hb2a : b ≤ 2 * a := by
      have hh : (b : ℝ) ≤ 2 * (a : ℝ) := by linarith
      exact_mod_cast hh
    have hm : b - a ≤ a := by omega
    have hnat : a + (b - a) = b := by omega
    have hreal : (a : ℝ) + (b - a : ℕ) = b := by exact_mod_cast hnat
    have hcore := integer_discretization a (b - a) ha hm t (ht.trans hNa.le)
    have hcells := sum_right_cells (critical t) a (b - a)
    rw [hnat] at hcells
    rw [hreal, ← hcells] at hcore
    have hmono : (a : ℝ) ^ (-1 / 2 : ℝ) ≤ N ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hN0 hNa.le (by norm_num)
    have hterm : ‖critical t a‖ ≤ N ^ (-1 / 2 : ℝ) := by
      rw [critical_norm t ha0]
      exact hmono
    have hleft := short_critical_integral N N a t hN0 le_rfl hNa.le (by linarith)
    have hright := short_critical_integral N b N1 t hN0 (hNa.le.trans habR) hbN1 (by linarith)
    have hsplit : Ioc ⌊N⌋₊ b = insert a (Ioc a b) := by
      ext n
      simp only [mem_Ioc, mem_insert]
      dsimp [a] at *
      omega
    have hsum : (∑ n ∈ Ioc ⌊N⌋₊ b, critical t n) =
        critical t a + ∑ n ∈ Ioc a b, critical t n := by
      rw [hsplit, sum_insert (by simp)]
    have hIleft := integral_add_adjacent_intervals
      (critical_intervalIntegrable t hN0 ha0) (critical_intervalIntegrable t ha0 hb0)
    have hIright := integral_add_adjacent_intervals
      (critical_intervalIntegrable t hN0 hb0) (critical_intervalIntegrable t hb0 hN10)
    have hI : (∫ y in N..N1, critical t y) =
        (∫ y in N..(a : ℝ), critical t y) + (∫ y in (a : ℝ)..b, critical t y) +
          (∫ y in (b : ℝ)..N1, critical t y) := by rw [← hIright, ← hIleft]
    change ‖(∑ n ∈ Ioc ⌊N⌋₊ b, critical t n) - _‖ ≤ _
    rw [hsum, hI]
    let S : ℂ := ∑ n ∈ Ioc a b, critical t n
    let J : ℂ := ∫ y in (a : ℝ)..b, critical t y
    let U : ℂ := ∫ y in N..(a : ℝ), critical t y
    let V : ℂ := ∫ y in (b : ℝ)..N1, critical t y
    change ‖critical t a + S - (U + J + V)‖ ≤ _
    calc
      _ = ‖((S - J) + critical t a) - U - V‖ := by congr 1; ring
      _ ≤ ‖((S - J) + critical t a) - U‖ + ‖V‖ := norm_sub_le _ _
      _ ≤ (‖(S - J) + critical t a‖ + ‖U‖) + ‖V‖ :=
        add_le_add (norm_sub_le ((S - J) + critical t a) U) le_rfl
      _ ≤ ((‖S - J‖ + ‖critical t a‖) + ‖U‖) + ‖V‖ :=
        add_le_add (add_le_add (norm_add_le (S - J) (critical t a)) le_rfl) le_rfl
      _ ≤ 67 * N ^ (-1 / 2 : ℝ) := by
        change ‖S - J‖ ≤ _ at hcore
        change ‖U‖ ≤ _ at hleft
        change ‖V‖ ≤ _ at hright
        nlinarith
  · have hb : b ≤ ⌊N⌋₊ := by dsimp [a] at hab; omega
    have hempty : Ioc ⌊N⌋₊ ⌊N1⌋₊ = ∅ := Ioc_eq_empty_of_le hb
    rw [hempty, sum_empty, zero_sub, norm_neg]
    have hlen : N1 - N ≤ 1 := by
      have hba : (b : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hb
      linarith [Nat.floor_le hN0.le]
    exact (short_critical_integral N N N1 t hN0 le_rfl hNN1 hlen).trans (by nlinarith)

/-- Page 21 supply. Exact sealed nonresonant discretization statement.
No declaration in DecompJ883 is changed. -/
theorem fgm_discretization_error :
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ, |t| ≤ N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
    ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ) := by
  refine ⟨67, by norm_num, ?_⟩
  intro N N1 hN hNN1 hN1 t ht
  have hN0 : 0 < N := by linarith
  have hsum : (∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊,
      (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ)) =
      ∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, critical t n := by
    apply sum_congr rfl
    intro n hn
    have hn0 : 0 < (n : ℝ) := by
      have hni := (mem_Ioc.mp hn).1
      have hpos : 0 < n := by omega
      exact_mod_cast hpos
    rw [critical_eq_product t hn0]
    push_cast
    ring
  have hint : (∫ y in N..N1,
      (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ∫ y in N..N1, critical t y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hNN1] at hy
    exact (critical_eq_product t (hN0.trans_le hy.1)).symm
  rw [hsum, hint]
  exact real_discretization N N1 t hN hNN1 hN1 ht

example : ‖(∑ n ∈ Ioc ⌊(3 / 2 : ℝ)⌋₊ ⌊(5 / 2 : ℝ)⌋₊, critical (-3 / 2) n) -
    (∫ y in (3 / 2 : ℝ)..(5 / 2), critical (-3 / 2) y)‖ ≤
    67 * (3 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
  real_discretization (3 / 2) (5 / 2) (-3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ‖(∑ n ∈ Ioc ⌊(5 / 4 : ℝ)⌋₊ ⌊(3 / 2 : ℝ)⌋₊, critical 1 n) -
    (∫ y in (5 / 4 : ℝ)..(3 / 2), critical 1 y)‖ ≤
    67 * (5 / 4 : ℝ) ^ (-1 / 2 : ℝ) :=
  real_discretization (5 / 4) (3 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms real_discretization
#print axioms fgm_discretization_error
#print axioms critical_intervalIntegrable
#print axioms short_critical_integral
#print axioms sum_right_cells
#print axioms critical_eq_product
#print axioms criticalDeriv_continuousAt
#print axioms critical_euler
#print axioms integer_discretization
#print axioms critical
#print axioms criticalDeriv
#print axioms criticalDeriv_norm
#print axioms critical_hasDerivAt
#print axioms critical_norm
#print axioms shifted_derivative_sum
end LeanLab.BakerHarmanPintz1997.Decomp343c

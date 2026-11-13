/-
Gallagher 1975 p.127 definition of J and p.131 display 13.
Support estimates for the separate main series summand audit.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp486b
import LeanLab.Linnik.Decomp1532c

namespace LeanLab.Linnik.Decomp497a

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp1532b (Jn singSeries majorArcs excSet)
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482b

/-- Gallagher 1975 p.127 definition of J and p.130 nonnegativity.
The norm of the main series product is J times the singular series norm. -/
theorem main_series_norm (N : ℕ) (n : ℤ) :
    ‖(Jn N n : ℂ) * singSeries n‖ = Jn N n * ‖singSeries n‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (LeanLab.Linnik.MajorArcEnergy.Jn_nonneg N n)]

/-- Gallagher 1975 p.127 definition of J.
A nonnegative shift k leaves exactly the pairs b plus k and b. -/
theorem Jn_nat_eq_sum (N k : ℕ) :
    Jn N (k : ℤ) = ∑ b ∈ Ioc 1 (N - k),
      1 / (Real.log (b + k) * Real.log b) := by
  unfold Jn
  apply Finset.sum_bij (fun m _ => m.2)
  · intro m hm
    obtain ⟨hm, heq⟩ := mem_filter.mp hm
    obtain ⟨ha, hb⟩ := mem_product.mp hm
    simp only [mem_Ioc] at ha hb ⊢
    omega
  · intro a ha b hb hab
    obtain ⟨_, heqa⟩ := mem_filter.mp ha
    obtain ⟨_, heqb⟩ := mem_filter.mp hb
    apply Prod.ext <;> omega
  · intro b hb
    simp only [mem_Ioc] at hb
    refine ⟨(b + k, b), mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · simp only [mem_Ioc]; omega
    · simp only [mem_Ioc]; omega
    · push_cast; ring
  · intro m hm
    have heq := (mem_filter.mp hm).2
    have hmk : m.1 = m.2 + k := by omega
    rw [hmk, Nat.cast_add]

/-- Gallagher 1975 p.127 definition of J and p.130 natural main scale.
Every admissible pair has weight at least the reciprocal of log squared N. -/
theorem Jn_nat_lower (N k : ℕ) :
    ((N - k - 1 : ℕ) : ℝ) / Real.log N ^ 2 ≤ Jn N (k : ℤ) := by
  rw [Jn_nat_eq_sum]
  calc
    _ = ∑ b ∈ Ioc 1 (N - k), 1 / Real.log N ^ 2 := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro b hb
      obtain ⟨hb1, hbN⟩ := mem_Ioc.mp hb
      have hbkN : b + k ≤ N := by omega
      have hbN' : b ≤ N := by omega
      have hblog : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb1)
      have hbklog : 0 < Real.log (b + k) := Real.log_pos (by exact_mod_cast (by omega : 1 < b + k))
      have hbL : Real.log b ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast hbN')
      have hbkL : Real.log (b + k) ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast hbkN)
      apply one_div_le_one_div_of_le (mul_pos hbklog hblog)
      simpa only [pow_two] using mul_le_mul hbkL hbL hblog.le (hbklog.le.trans hbkL)

/-- Gallagher 1975 p.127 main term and p.131 display 13.
The separate main term has a lower bound at the natural main scale. -/
theorem main_series_nat_lower (N k : ℕ) :
    ((N - k - 1 : ℕ) : ℝ) / Real.log N ^ 2 * ‖singSeries (k : ℤ)‖ ≤
      ‖(Jn N (k : ℤ) : ℂ) * singSeries (k : ℤ)‖ := by
  rw [main_series_norm]
  exact mul_le_mul_of_nonneg_right (Jn_nat_lower N k) (norm_nonneg _)

/-- Gallagher 1975 p.130 bound J of n by J of zero.
This upper bound retains the norm of the singular series main factor. -/
theorem main_series_upper : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ,
    ‖(Jn N n : ℂ) * singSeries n‖ ≤
      2 * ((N : ℝ) / Real.log N ^ 2) * ‖singSeries n‖ := by
  obtain ⟨N₀, hN₀⟩ := LeanLab.Linnik.MajorArcEnergy.J0_le_two
  refine ⟨N₀, fun N hN n => ?_⟩
  rw [main_series_norm]
  exact mul_le_mul_of_nonneg_right
    ((LeanLab.Linnik.Decomp1532b.Jn_le_J0 N n).trans (hN₀ N hN)) (norm_nonneg _)

/-- Gallagher 1975 p.125 Euler factor at two and p.134 parity convention.
The separate main term vanishes for an odd frequency. -/
theorem main_series_odd (N : ℕ) {n : ℤ} (hn : Odd n) :
    ‖(Jn N n : ℂ) * singSeries n‖ = 0 := by
  rw [LeanLab.Linnik.Decomp1532b.singSeries_odd hn, mul_zero, norm_zero]

/-- Gallagher 1975 p.127 definition of J.
The difference of two integers strictly above one and at most N has absolute
value at most N minus two. -/
theorem Jn_eq_zero_of_natAbs (N : ℕ) (n : ℤ) (hn : N - 2 < n.natAbs) :
    Jn N n = 0 := by
  unfold Jn
  apply sum_eq_zero
  intro m hm
  obtain ⟨hm, heq⟩ := mem_filter.mp hm
  obtain ⟨ha, hb⟩ := mem_product.mp hm
  simp only [mem_Ioc] at ha hb
  have habZ : |n| ≤ ((N - 2 : ℕ) : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  rw [← Int.natCast_natAbs] at habZ
  have hab : n.natAbs ≤ N - 2 := by exact_mod_cast habZ
  omega

/-- Gallagher 1975 p.127 main term support.
The separate main term vanishes outside the exact difference range. -/
theorem main_series_outside (N : ℕ) (n : ℤ) (hn : N - 2 < n.natAbs) :
    ‖(Jn N n : ℂ) * singSeries n‖ = 0 := by
  rw [Jn_eq_zero_of_natAbs N n hn]
  simp

/-- Gallagher 1975 p.127 Theorem 3 and p.131 displays 13 and 17.
The exceptional error budget is nonnegative for nonnegative K and positive theta. -/
theorem exceptional_budget_nonneg {N : ℕ} (hN : 2 ≤ N) {K θ : ℝ}
    (hK : 0 ≤ K) (hθ : 0 ≤ θ) (r : ℕ) (γ : ℝ) (n : ℤ) :
    0 ≤ K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
      (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
        (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
        exceptionalWeight r n) := by
  have hP : 1 ≤ (N : ℝ) ^ θ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hθ
  have hlogP : 0 ≤ Real.log ((N : ℝ) ^ θ) := Real.log_nonneg hP
  have hE := normalizedEnergy_nonneg hN θ r γ
  unfold totientWeight exceptionalWeight
  positivity

/-- Gallagher 1975 p.125 Euler factor, p.134 parity and p.127 Theorem 3 budget.
The requested separate main bound holds at every odd frequency. -/
theorem main_series_odd_bound {N : ℕ} (hN : 2 ≤ N) {K θ : ℝ}
    (hK : 0 ≤ K) (hθ : 0 ≤ θ) (r : ℕ) (γ : ℝ) {n : ℤ} (hn : Odd n) :
    ‖(Jn N n : ℂ) * singSeries n‖ ≤
      K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
        (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
          (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
          exceptionalWeight r n) := by
  rw [main_series_odd N hn]
  exact exceptional_budget_nonneg hN hK hθ r γ n

/-- Gallagher 1975 p.127 difference range and Theorem 3 budget.
The requested separate main bound holds outside the exact difference range. -/
theorem main_series_outside_bound {N : ℕ} (hN : 2 ≤ N) {K θ : ℝ}
    (hK : 0 ≤ K) (hθ : 0 ≤ θ) (r : ℕ) (γ : ℝ) (n : ℤ)
    (hn : N - 2 < n.natAbs) :
    ‖(Jn N n : ℂ) * singSeries n‖ ≤
      K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
        (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
          (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
          exceptionalWeight r n) := by
  rw [main_series_outside N n hn]
  exact exceptional_budget_nonneg hN hK hθ r γ n

/-- Gallagher 1975 p.127 definition of J and p.131 main term.
Once N is at least twice k plus two, the main norm is at least half of
N over log squared N times the singular series norm. -/
theorem main_series_nat_half_lower (N k : ℕ) (hNk : 2 * (k + 1) ≤ N) :
    ((N : ℝ) / Real.log N ^ 2) / 2 * ‖singSeries (k : ℤ)‖ ≤
      ‖(Jn N (k : ℤ) : ℂ) * singSeries (k : ℤ)‖ := by
  have hc : (N : ℝ) / 2 ≤ ((N - k - 1 : ℕ) : ℝ) := by
    have hid : (N - k - 1 : ℕ) + k + 1 = N := by omega
    have hidR : ((N - k - 1 : ℕ) : ℝ) + k + 1 = N := by exact_mod_cast hid
    have hNkR : 2 * ((k : ℝ) + 1) ≤ N := by exact_mod_cast hNk
    linarith
  calc
    _ = ((N : ℝ) / 2 / Real.log N ^ 2) * ‖singSeries (k : ℤ)‖ := by ring
    _ ≤ ((N - k - 1 : ℕ) : ℝ) / Real.log N ^ 2 * ‖singSeries (k : ℤ)‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (sq_nonneg _)) (norm_nonneg _)
    _ ≤ _ := main_series_nat_lower N k

/-- CONDITIONAL ON the supplied norm bounds. Gallagher 1975 p.131 display 13, audit of separate summand bounds.
Any bound on the separate main term by the natural scale times A forces
A to be at least half the singular series norm for a fixed natural shift. -/
theorem main_series_bound_requires_budget (N k : ℕ) (hNk : 2 * (k + 1) ≤ N)
    (A : ℝ) (hA : ‖(Jn N (k : ℤ) : ℂ) * singSeries (k : ℤ)‖ ≤
      ((N : ℝ) / Real.log N ^ 2) * A) :
    ‖singSeries (k : ℤ)‖ ≤ 2 * A := by
  have hN : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hQ : 0 < (N : ℝ) / Real.log N ^ 2 :=
    div_pos (by linarith) (sq_pos_of_pos (Real.log_pos hN))
  have hlower := (main_series_nat_half_lower N k hNk).trans hA
  nlinarith

/-- Gallagher 1975 p.131 display 13, audit of separate summand bounds.
A budget below half the singular series norm cannot bound the separate main term.
This is a statement about the lab split and asserts no paper error. -/
theorem main_series_small_budget_impossible (N k : ℕ) (hNk : 2 * (k + 1) ≤ N)
    (A : ℝ) (hA : 2 * A < ‖singSeries (k : ℤ)‖) :
    ¬ ‖(Jn N (k : ℤ) : ℂ) * singSeries (k : ℤ)‖ ≤
      ((N : ℝ) / Real.log N ^ 2) * A := by
  intro h
  exact (not_le_of_gt hA) (main_series_bound_requires_budget N k hNk A h)

/-- Gallagher 1975 p.131 display 13, triangle inequality with the main term retained. -/
theorem arc_integral_le_error_add_main (N : ℕ) (θ : ℝ) (n : ℤ) :
    ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      complexFrequencyError N θ n + ‖(Jn N n : ℂ) * singSeries n‖ := by
  exact norm_le_norm_sub_add _ _

/-- Gallagher 1975 p.131 display 13, reverse triangle inequality.
The main term is at most the arc norm plus the error norm. -/
theorem main_series_le_arc_add_error (N : ℕ) (θ : ℝ) (n : ℤ) :
    ‖(Jn N n : ℂ) * singSeries n‖ ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
        ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
      complexFrequencyError N θ n := by
  exact norm_le_norm_add_norm_sub _ _

/-- CONDITIONAL ON the supplied norm bounds. Gallagher 1975 p.131 display 13, audit consequence.
If the true error and the arc norm are bounded by the same normalized budget A,
then four times A is at least the singular series norm at a fixed natural shift. -/
theorem arc_bound_requires_budget (N k : ℕ) (hNk : 2 * (k + 1) ≤ N)
    (θ A : ℝ) (hError : complexFrequencyError N θ (k : ℤ) ≤
      ((N : ℝ) / Real.log N ^ 2) * A)
    (hArc : ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * α)‖ ≤
      ((N : ℝ) / Real.log N ^ 2) * A) :
    ‖singSeries (k : ℤ)‖ ≤ 4 * A := by
  have hM := main_series_le_arc_add_error N θ (k : ℤ)
  have hmain : ‖(Jn N (k : ℤ) : ℂ) * singSeries (k : ℤ)‖ ≤
      ((N : ℝ) / Real.log N ^ 2) * (2 * A) := by
    have hArc' : ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
        ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e (((k : ℤ) : ℝ) * α)‖ ≤
        ((N : ℝ) / Real.log N ^ 2) * A := by simpa using hArc
    linarith
  have := main_series_bound_requires_budget N k hNk (2 * A) hmain
  linarith

/-- Gallagher 1975 p.125 singular product and p.130 singular series.
At every nonzero even frequency the singular series norm is at least one.
Use the existing truncated binary singular series lower bound and its limit. -/
theorem one_le_singSeries_norm {n : ℤ} (hn : n ≠ 0) (he : Even n) :
    1 ≤ ‖singSeries n‖ := by
  have hm : Even n.natAbs := Int.natAbs_even.mpr he
  have hm0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hsc : Summable (fun q : ℕ => (LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q : ℂ)) :=
    (LeanLab.Linnik.Decomp1532b.summable_singSeries hn).congr
      (fun q => LeanLab.Linnik.Decomp1532c.singSeries_term_eq_f2 q n)
  have hsr : Summable (fun q : ℕ => LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q) := by
    simpa using Complex.reCLM.summable hsc
  have hpartial : Filter.Tendsto (fun P : ℕ => ∑ q ∈ Icc 1 P,
      LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q) Filter.atTop
      (nhds (∑' q : ℕ, LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q)) := by
    have ht := hsr.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    convert ht using 1
    ext P
    change _ = ∑ q ∈ range (P + 1), LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q
    have hs : range (P + 1) = insert 0 (Icc 1 P) := by
      ext q
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hs, sum_insert (by simp)]
    simp
  have hlo : Filter.Tendsto (fun P : ℕ =>
      1 - Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G n.natAbs / Real.sqrt (P : ℝ))
      Filter.atTop (nhds 1) := by
    have hz : Filter.Tendsto (fun P : ℕ =>
        Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G n.natAbs / Real.sqrt (P : ℝ))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.sub hz
  have hlower : 1 ≤ ∑' q : ℕ, LeanLab.ExceptionalSet.MVMajor.f2 n.natAbs q := by
    apply le_of_tendsto_of_tendsto hlo hpartial
    filter_upwards [Filter.eventually_ge_atTop 2] with P hP
    exact LeanLab.ExceptionalSet.MVMajor.sing2_ge hm hm0 hP
  have hre : 1 ≤ (singSeries n).re := by
    rw [LeanLab.Linnik.Decomp1532c.singSeries_eq_tsum_f2, Complex.ofReal_re]
    exact hlower
  exact hre.trans (Complex.re_le_norm _)

/-- Gallagher 1975 p.127 main term, fixed nonzero even frequency two.
For N at least six, the main norm is at least half the natural main scale. -/
theorem main_series_two_lower (N : ℕ) (hN : 6 ≤ N) :
    ((N : ℝ) / Real.log N ^ 2) / 2 ≤ ‖(Jn N 2 : ℂ) * singSeries 2‖ := by
  have hS : 1 ≤ ‖singSeries (2 : ℤ)‖ :=
    one_le_singSeries_norm (by norm_num) (by norm_num)
  have hQ : 0 ≤ ((N : ℝ) / Real.log N ^ 2) / 2 := by positivity
  calc _ = ((N : ℝ) / Real.log N ^ 2) / 2 * 1 := by ring
    _ ≤ ((N : ℝ) / Real.log N ^ 2) / 2 * ‖singSeries (2 : ℤ)‖ :=
      mul_le_mul_of_nonneg_left hS hQ
    _ ≤ _ := main_series_nat_half_lower N 2 hN

/-- CONDITIONAL ON the supplied norm bounds. Gallagher 1975 p.131 display 13, fixed frequency audit.
A separate main estimate at frequency two must pay at least one half in its
normalized budget once N is at least six. -/
theorem main_series_two_budget (N : ℕ) (hN : 6 ≤ N) (A : ℝ)
    (hA : ‖(Jn N 2 : ℂ) * singSeries 2‖ ≤ ((N : ℝ) / Real.log N ^ 2) * A) :
    (1 : ℝ) / 2 ≤ A := by
  have hS : 1 ≤ ‖singSeries (2 : ℤ)‖ :=
    one_le_singSeries_norm (by norm_num) (by norm_num)
  have hb : ‖singSeries (2 : ℤ)‖ ≤ 2 * A := by
    simpa using main_series_bound_requires_budget N 2 hN A hA
  linarith

/-- CONDITIONAL ON the supplied norm bounds. Gallagher 1975 p.131 display 13 and displays 15 to 17, lab split audit.
At frequency two the exact separate main bound requires one quarter to be at most
K times its bracket. No existence of an exceptional zero is asserted. -/
theorem exceptional_main_bound_requires_budget (N : ℕ) (hN : 6 ≤ N)
    (K θ γ : ℝ) (r : ℕ)
    (hMain : ‖(Jn N 2 : ℂ) * singSeries 2‖ ≤
      K * ((N : ℝ) / Real.log N ^ 2) * totientWeight 2 *
        (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * (2 : ℤ).natAbs.divisors.card +
          (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
          exceptionalWeight r 2)) :
    (1 : ℝ) / 4 ≤ K *
      (2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) +
        (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
        exceptionalWeight r 2) := by
  have htw : totientWeight (2 : ℤ) = 2 := by norm_num [totientWeight]
  have hd : (2 : ℤ).natAbs.divisors.card = 2 := by decide
  rw [htw, hd] at hMain
  have h := main_series_two_budget N hN
    (2 * K * (2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) +
      (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ + exceptionalWeight r 2))
    (by convert hMain using 1; push_cast; ring)
  linarith

/-- Gallagher 1975 p.127 main term and p.131 display 13, lab split audit.
The separate main term at frequency two is not little o of the natural main scale.
This does not assert a decay estimate for the actual exceptional budget. -/
theorem main_series_two_not_littleO :
    ¬ Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => ‖(Jn N 2 : ℂ) * singSeries 2‖)
      (fun N : ℕ => (N : ℝ) / Real.log N ^ 2) := by
  intro h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h.bound (by norm_num : (0 : ℝ) < 1 / 4))
  let N := max 6 N₀
  have hN6 : 6 ≤ N := le_max_left _ _
  have hN₀' : N₀ ≤ N := le_max_right _ _
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hQ : 0 < (N : ℝ) / Real.log N ^ 2 :=
    div_pos (by linarith) (sq_pos_of_pos (Real.log_pos hN1))
  have hb := hN₀ N hN₀'
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_pos hQ] at hb
  have hlower := main_series_two_lower N hN6
  linarith

/-- Gallagher 1975 pp.127, 130, 131 and 134, concrete support and scale instances.
The odd and outside cases vanish, the interior main term has positive scale,
and a quarter scale budget already fails at N equal to six. -/
theorem concrete_main_series_instances :
    1 / Real.log 4 ^ 2 ≤ Jn 4 2 ∧
    Jn 4 3 = 0 ∧
    ‖(Jn 4 1 : ℂ) * singSeries 1‖ = 0 ∧
    ((6 : ℝ) / Real.log 6 ^ 2) / 2 ≤ ‖(Jn 6 2 : ℂ) * singSeries 2‖ ∧
    ¬ ‖(Jn 6 2 : ℂ) * singSeries 2‖ ≤ ((6 : ℝ) / Real.log 6 ^ 2) / 4 := by
  refine ⟨?_, Jn_eq_zero_of_natAbs 4 3 (by norm_num),
    main_series_odd 4 (by norm_num), main_series_two_lower 6 (by norm_num), ?_⟩
  · simpa using Jn_nat_lower 4 2
  · intro h
    have hb := main_series_two_budget 6 (by norm_num) (1 / 4) (by simpa [div_eq_mul_inv] using h)
    norm_num at hb

/-- Gallagher 1975 p.127 exceptional weight at frequency two.
The existing totient estimate gives an explicit decaying conductor bound. -/
theorem exceptionalWeight_two_le (r : ℕ) (hr : 0 < r) :
    exceptionalWeight r 2 ≤ 14 * (r : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hg : ((Nat.gcd r (2 : ℤ).natAbs).totient : ℝ) ≤ 2 := by
    have h := (Nat.totient_le (Nat.gcd r 2)).trans (Nat.gcd_le_right r (by norm_num : 0 < 2))
    exact_mod_cast h
  have hp : (r : ℝ) * (r : ℝ) ^ (-(7 : ℝ) / 4) = (r : ℝ) ^ (-(3 : ℝ) / 4) := by
    calc _ = (r : ℝ) ^ (1 : ℝ) * (r : ℝ) ^ (-(7 : ℝ) / 4) := by rw [Real.rpow_one]
      _ = (r : ℝ) ^ ((1 : ℝ) + -(7 : ℝ) / 4) := (Real.rpow_add hrR _ _).symm
      _ = _ := by norm_num
  unfold exceptionalWeight
  calc _ ≤ (r : ℝ) * 2 / (r.totient : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hrR.le) (sq_nonneg _)
    _ = 2 * (r : ℝ) * (1 / (r.totient : ℝ) ^ 2) := by ring
    _ ≤ 2 * (r : ℝ) * (7 * (r : ℝ) ^ (-(7 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (LeanLab.Zinoviev1997.inv_totient_sq_seven r hr) (by positivity)
    _ = 14 * ((r : ℝ) * (r : ℝ) ^ (-(7 : ℝ) / 4)) := by ring
    _ = _ := by rw [hp]

/-- Gallagher 1975 p.127 quoted exceptional weight.
At frequency two the exceptional weight tends to zero as the conductor tends to infinity. -/
theorem exceptionalWeight_two_tendsto_zero :
    Filter.Tendsto (fun r : ℕ => exceptionalWeight r 2) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun r : ℕ => 14 * (r : ℝ) ^ (-(3 : ℝ) / 4))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, neg_div, mul_zero] using h.const_mul 14
  apply squeeze_zero' ?_ ?_ hp
  · exact Filter.Eventually.of_forall fun r => by unfold exceptionalWeight; positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    exact exceptionalWeight_two_le r hr

/-- Gallagher 1975 p.127 divisor tail at frequency two.
For every fixed positive theta its factor twice log P over P tends to zero. -/
theorem divisor_budget_two_tendsto_zero (θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto (fun N : ℕ =>
      2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ)) Filter.atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, id_eq, mul_zero] using h.const_mul 2

/-- Gallagher 1975 p.131 display 13, lab split obstruction.
No normalized budget tending to zero can eventually bound the separate main norm
at frequency two. This asserts no decay for the actual exceptional energy. -/
theorem no_eventual_main_bound_of_budget_tendsto_zero (A : ℕ → ℝ)
    (hA : Filter.Tendsto A Filter.atTop (nhds 0)) :
    ¬ ∀ᶠ N : ℕ in Filter.atTop,
      ‖(Jn N 2 : ℂ) * singSeries 2‖ ≤ ((N : ℝ) / Real.log N ^ 2) * A N := by
  intro hbound
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop, A N < 1 / 2 :=
    hA.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hfalse : ∀ᶠ N : ℕ in Filter.atTop, False := by
    filter_upwards [hbound, hsmall, Filter.eventually_ge_atTop 6] with N hN hs h6
    have h := main_series_two_budget N h6 (A N) hN
    linarith
  obtain ⟨N, hN⟩ := hfalse.exists
  exact hN

/-- Gallagher 1975 p.131 display 13, lab split obstruction.
The arc norm and the error norm at frequency two cannot both eventually have
the same normalized budget tending to zero. No exceptional zero is asserted. -/
theorem no_eventual_arc_and_error_small (θ : ℝ) (A : ℕ → ℝ)
    (hA : Filter.Tendsto A Filter.atTop (nhds 0)) :
    ¬ ∀ᶠ N : ℕ in Filter.atTop,
      complexFrequencyError N θ 2 ≤ ((N : ℝ) / Real.log N ^ 2) * A N ∧
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
        ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((2 : ℝ) * α)‖ ≤
        ((N : ℝ) / Real.log N ^ 2) * A N := by
  intro hbound
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop, A N < 1 / 4 :=
    hA.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hfalse : ∀ᶠ N : ℕ in Filter.atTop, False := by
    filter_upwards [hbound, hsmall, Filter.eventually_ge_atTop 6] with N hN hs h6
    have h : ‖singSeries (2 : ℤ)‖ ≤ 4 * A N := by
      simpa using arc_bound_requires_budget N 2 h6 θ (A N) hN.1 hN.2
    have hS : 1 ≤ ‖singSeries (2 : ℤ)‖ :=
      one_le_singSeries_norm (by norm_num) (by norm_num)
    linarith
  obtain ⟨N, hN⟩ := hfalse.exists
  exact hN

/-- Gallagher 1975 p.127 exceptional conductor growth and quoted weight.
Uniformly over characters in the exceptional strip, their frequency two weight
is eventually smaller than every fixed positive epsilon. -/
theorem exceptionalWeight_two_uniform_small (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ x ∈ LeanLab.Linnik.Decomp1532b.excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        exceptionalWeight (x.1 + 1) 2 < ε := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    (exceptionalWeight_two_tendsto_zero.eventually (gt_mem_nhds hε))
  filter_upwards [LeanLab.Linnik.Decomp466b.exceptional_conductor_escape θ hθ R] with N hN
  intro x hx
  exact hR (x.1 + 1) (hN x hx).1

/-- Gallagher 1975 p.127 divisor and exceptional weights at frequency two.
For fixed positive theta, their sum is uniformly eventually smaller than every
positive epsilon over all exceptional characters at height P to the fifth. -/
theorem two_tail_budget_uniform_small (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ x ∈ LeanLab.Linnik.Decomp1532b.excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        2 * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) +
          exceptionalWeight (x.1 + 1) 2 < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  have hd := (divisor_budget_two_tendsto_zero θ hθ).eventually (gt_mem_nhds hhalf)
  filter_upwards [hd, exceptionalWeight_two_uniform_small θ hθ (ε / 2) hhalf] with N hN hW
  intro x hx
  have hw := hW x hx
  linarith

/-- Gallagher 1975 p.131 displays 13 and 15 to 17, lab split obstruction.
For any fixed positive theta and K, at every sufficiently large exceptional case,
the separate main bound at frequency two fails if K times the corrected quadratic
energy is less than one eighth. No such energy saving or exceptional zero is asserted. -/
theorem main_series_bound_fails_of_small_corrected_energy (θ K : ℝ)
    (hθ : 0 < θ) (hK : 0 < K) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ x ∈ LeanLab.Linnik.Decomp1532b.excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        ∀ γ : ℝ,
          K * ((1 + normalizedEnergy N θ (x.1 + 1) γ) *
            normalizedEnergy N θ (x.1 + 1) γ) < 1 / 8 →
          ¬ ‖(Jn N 2 : ℂ) * singSeries 2‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight 2 *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * (2 : ℤ).natAbs.divisors.card +
                (1 + normalizedEnergy N θ (x.1 + 1) γ) *
                  normalizedEnergy N θ (x.1 + 1) γ + exceptionalWeight (x.1 + 1) 2) := by
  have hε : 0 < 1 / (8 * K) := by positivity
  filter_upwards [two_tail_budget_uniform_small θ hθ (1 / (8 * K)) hε,
    Filter.eventually_ge_atTop 6] with N ht h6
  intro x hx γ hEnergy hMain
  have hNec := exceptional_main_bound_requires_budget N h6 K θ γ (x.1 + 1) hMain
  have ht' := mul_lt_mul_of_pos_left (ht x hx) hK
  have hcancel : K * (1 / (8 * K)) = (1 : ℝ) / 8 := by
    field_simp [ne_of_gt hK]
  rw [hcancel] at ht'
  linarith

/-- Gallagher 1975 p.131 displays 13 and 14, elementary scale arithmetic.
For positive c, C and K, sufficiently small positive theta makes K times the
quadratic energy smaller than one eighth whenever E has the printed exponential bound. -/
theorem exists_small_theta_quadratic (c C K : ℝ) (hc : 0 < c) (hC : 0 < C) (hK : 0 < K) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∀ E : ℝ, 0 ≤ E → E ≤ C * Real.exp (-c / θ) → K * ((1 + E) * E) < 1 / 8 := by
  refine ⟨min c (c / (64 * K * C * (1 + C))), lt_min hc (by positivity), ?_⟩
  intro θ hθ hθ₀ E hE0 hE
  have hden : 0 < 64 * K * C * (1 + C) := by positivity
  have ht := (le_div_iff₀ hden).mp (hθ₀.trans (min_le_right _ _))
  have he : c / θ ≤ Real.exp (c / θ) := by linarith [Real.add_one_le_exp (c / θ)]
  have hExp : Real.exp (-c / θ) ≤ θ / c := by
    calc _ = 1 / Real.exp (c / θ) := by rw [neg_div, Real.exp_neg, one_div]
      _ ≤ 1 / (c / θ) := one_div_le_one_div_of_le (div_pos hc hθ) he
      _ = θ / c := by rw [one_div_div]
  have hExp1 : Real.exp (-c / θ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le)
  have hquad := LeanLab.Linnik.Decomp482c.quadratic_energy_decay hE0 hC.le
    (Real.exp_pos _).le hExp1 hE
  have hsmall : K * (C * (1 + C)) * (θ / c) ≤ (1 : ℝ) / 64 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hc).mpr
    nlinarith only [ht]
  calc K * ((1 + E) * E) ≤ K * (C * (1 + C) * Real.exp (-c / θ)) :=
      mul_le_mul_of_nonneg_left hquad hK.le
    _ = K * (C * (1 + C)) * Real.exp (-c / θ) := by ring
    _ ≤ K * (C * (1 + C)) * (θ / c) := mul_le_mul_of_nonneg_left hExp (by positivity)
    _ ≤ 1 / 64 := hsmall
    _ < 1 / 8 := by norm_num

/-- CONDITIONAL ON the exact separate main bound supplied as hBound.
Gallagher 1975 pp.127 and 131, lab split audit consequence.
The assigned separate main bound would imply eventual absence of exceptional
characters with conductor at most P at all sufficiently small positive theta.
This asserts no such zero free theorem unconditionally and no paper error. -/
theorem separate_main_bound_forces_eventual_no_exception
    (hBound : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∀ᶠ N : ℕ in Filter.atTop,
        ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ := by
  obtain ⟨K, θb, hK, hθb, hθb1, hb⟩ := hBound
  obtain ⟨c, C, θe, hc, hC, hθe, hθe1, he⟩ :=
    LeanLab.Linnik.Decomp486c.energy_decay_with_exception
  obtain ⟨θs, hθs, hs⟩ := exists_small_theta_quadratic c C K hc hC hK
  refine ⟨min θb (min θe θs), lt_min hθb (lt_min hθe hθs), ?_⟩
  intro θ hθ hθ₀
  have hθb' : θ ≤ θb := hθ₀.trans (min_le_left _ _)
  have hθe' : θ ≤ θe := hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθs' : θ ≤ θs := hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Nb, hNb⟩ := hb θ hθ hθb'
  obtain ⟨Ne, hNe⟩ := he θ hθ hθe'
  filter_upwards [main_series_bound_fails_of_small_corrected_energy θ K hθ hK,
    Filter.eventually_ge_atTop Nb, Filter.eventually_ge_atTop Ne,
    Filter.eventually_ge_atTop 2] with N hBad hNb' hNe' hN2
  rintro ⟨x, hx, hxP⟩
  obtain ⟨γ, hz, hlo, hlt, hE⟩ := hNe N hNe' x hx hxP
  have hSmall := hs θ hθ hθs' (normalizedEnergy N θ (x.1 + 1) γ)
    (normalizedEnergy_nonneg hN2 θ (x.1 + 1) γ) hE
  have hMain := hNb N hNb' (x.1 + 1) γ
    (Or.inr ⟨x, hx, rfl, hxP, hz, hlo, hlt⟩) (by omega) 2 (by norm_num)
  exact hBad x hx γ hSmall hMain

/-- CONDITIONAL ON the supplied separate arc and faithful difference bounds.
Gallagher 1975 p.131 display 13 and displays 15 to 17, reverse assembly audit.
The main norm is bounded by the arc norm plus the error norm. Uniform constants
add and theta cutoffs intersect. Neither analytic input is asserted here. -/
theorem separate_main_bound_of_arc_and_error
    (hArc : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n))
    (hError : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  obtain ⟨Ka, θa, hKa, hθa, hθa1, ha⟩ := hArc
  obtain ⟨Ke, θe, hKe, hθe, hθe1, he⟩ := hError
  refine ⟨Ka + Ke, min θa θe, by linarith, lt_min hθa hθe,
    (min_le_left _ _).trans hθa1, ?_⟩
  intro θ hθ hθ₀
  obtain ⟨Na, hNa⟩ := ha θ hθ (hθ₀.trans (min_le_left _ _))
  obtain ⟨Ne, hNe⟩ := he θ hθ (hθ₀.trans (min_le_right _ _))
  refine ⟨max Na Ne, ?_⟩
  intro N hN r γ hcase hr n hn
  have hI := hNa N ((le_max_left _ _).trans hN) r γ hcase hr n hn
  have hD := hNe N ((le_max_right _ _).trans hN) r γ hcase hr n hn
  apply (main_series_le_arc_add_error N θ n).trans
  convert add_le_add hI hD using 1; ring

/-- CONDITIONAL ON the supplied separate arc and faithful difference bounds.
Gallagher 1975 pp.127 and 131, lab split audit consequence.
These two uniform bounds together would force eventual absence of exceptional
conductors below P for all sufficiently small positive theta. No absence theorem
is asserted unconditionally and no paper error is asserted. -/
theorem separate_arc_bound_forces_eventual_no_exception
    (hArc : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n))
    (hError : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∀ᶠ N : ℕ in Filter.atTop,
        ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ := by
  exact separate_main_bound_forces_eventual_no_exception
    (separate_main_bound_of_arc_and_error hArc hError)

/-- Gallagher 1975 pp.127 and 131, exact lab split audit equivalence.
The assigned separate main bound is equivalent to eventual absence of exceptional
conductors below P for all sufficiently small positive theta. The forward direction
uses the proved energy selection and the main scale obstruction. The reverse direction
is the empty exceptional case. Neither side is asserted to hold unconditionally. -/
theorem separate_main_bound_iff_eventual_no_exception :
    (∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) ↔
      ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
        ∀ᶠ N : ℕ in Filter.atTop,
          ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ := by
  constructor
  · exact separate_main_bound_forces_eventual_no_exception
  · rintro ⟨θz, hθz, hz⟩
    refine ⟨1, min θz 1, by norm_num, lt_min hθz (by norm_num), min_le_right _ _, ?_⟩
    intro θ hθ hθ₀
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
      (hz θ hθ (hθ₀.trans (min_le_left _ _)))
    refine ⟨N₀, ?_⟩
    intro N hN r γ hcase hr n hn
    rcases hcase with h0 | ⟨x, hx, hrx, hrP, hz, hlo, hlt⟩
    · omega
    · exact False.elim (hN₀ N hN ⟨x, hx, by simpa only [hrx] using hrP⟩)

end LeanLab.Linnik.Decomp497a

#print axioms LeanLab.Linnik.Decomp497a.main_series_norm
#print axioms LeanLab.Linnik.Decomp497a.Jn_nat_eq_sum
#print axioms LeanLab.Linnik.Decomp497a.Jn_nat_lower
#print axioms LeanLab.Linnik.Decomp497a.main_series_nat_lower
#print axioms LeanLab.Linnik.Decomp497a.main_series_upper
#print axioms LeanLab.Linnik.Decomp497a.main_series_odd
#print axioms LeanLab.Linnik.Decomp497a.Jn_eq_zero_of_natAbs
#print axioms LeanLab.Linnik.Decomp497a.main_series_outside
#print axioms LeanLab.Linnik.Decomp497a.exceptional_budget_nonneg
#print axioms LeanLab.Linnik.Decomp497a.main_series_odd_bound
#print axioms LeanLab.Linnik.Decomp497a.main_series_outside_bound
#print axioms LeanLab.Linnik.Decomp497a.main_series_nat_half_lower
#print axioms LeanLab.Linnik.Decomp497a.main_series_bound_requires_budget
#print axioms LeanLab.Linnik.Decomp497a.main_series_small_budget_impossible
#print axioms LeanLab.Linnik.Decomp497a.arc_integral_le_error_add_main
#print axioms LeanLab.Linnik.Decomp497a.main_series_le_arc_add_error
#print axioms LeanLab.Linnik.Decomp497a.arc_bound_requires_budget
#print axioms LeanLab.Linnik.Decomp497a.one_le_singSeries_norm
#print axioms LeanLab.Linnik.Decomp497a.main_series_two_lower
#print axioms LeanLab.Linnik.Decomp497a.main_series_two_budget
#print axioms LeanLab.Linnik.Decomp497a.exceptional_main_bound_requires_budget
#print axioms LeanLab.Linnik.Decomp497a.main_series_two_not_littleO
#print axioms LeanLab.Linnik.Decomp497a.concrete_main_series_instances
#print axioms LeanLab.Linnik.Decomp497a.exceptionalWeight_two_le
#print axioms LeanLab.Linnik.Decomp497a.exceptionalWeight_two_tendsto_zero
#print axioms LeanLab.Linnik.Decomp497a.divisor_budget_two_tendsto_zero
#print axioms LeanLab.Linnik.Decomp497a.no_eventual_main_bound_of_budget_tendsto_zero
#print axioms LeanLab.Linnik.Decomp497a.no_eventual_arc_and_error_small
#print axioms LeanLab.Linnik.Decomp497a.exceptionalWeight_two_uniform_small
#print axioms LeanLab.Linnik.Decomp497a.two_tail_budget_uniform_small
#print axioms LeanLab.Linnik.Decomp497a.main_series_bound_fails_of_small_corrected_energy
#print axioms LeanLab.Linnik.Decomp497a.exists_small_theta_quadratic
#print axioms LeanLab.Linnik.Decomp497a.separate_main_bound_forces_eventual_no_exception
#print axioms LeanLab.Linnik.Decomp497a.separate_main_bound_of_arc_and_error
#print axioms LeanLab.Linnik.Decomp497a.separate_arc_bound_forces_eventual_no_exception
#print axioms LeanLab.Linnik.Decomp497a.separate_main_bound_iff_eventual_no_exception

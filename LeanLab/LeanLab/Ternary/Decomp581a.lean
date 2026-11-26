/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 bottom Buchstab display.
Separate primes from composite rough numbers before the mean evaluation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp571a
import LeanLab.Ternary.Decomp678b
import LeanLab.AlmostPrimeSums.Decomp1544c

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- The normalized weighted prime term in the first Buchstab step.
MMS page 11 bottom display, prime number theorem contribution. -/
noncomputable def primeMean (x : ℝ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    Task379.referenceWeight x n * ρ n) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The composite part of the rough indicator.
MMS page 11 bottom display, first Buchstab step with primes removed.
The finite extension retains n one. Only n above one occur asymptotically. -/
noncomputable def compositeRough (n : ℕ) (y : ℝ) : ℝ :=
  if n.Prime then 0 else Task361.roughIndicator n y

/-- The normalized weighted composite rough term.
MMS page 11 bottom Buchstab display. -/
noncomputable def compositeMean (x : ℝ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    Task379.referenceWeight x n * compositeRough n (x ^ (1 / 4 : ℝ))) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The rough indicator is exactly the threshold test on the least prime factor.
Derived arithmetic form of the Buchstab identity used on MMS page 11.
The exclusion of one is essential. -/
theorem roughIndicator_minFac {n : ℕ} (hn : n ≠ 1) (y : ℝ) :
    Task361.roughIndicator n y = if y ≤ (n.minFac : ℝ) then 1 else 0 := by
  classical
  unfold Task361.roughIndicator
  congr 1
  apply propext
  constructor
  · intro h
    by_contra hy
    exact h n.minFac (Nat.minFac_prime hn) (lt_of_not_ge hy) (Nat.minFac_dvd n)
  · intro h p hp hpy hd
    have hm : (n.minFac : ℝ) ≤ p := by
      exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hd
    linarith

/-- The composite term is a single least prime factor bucket.
Derived finite Buchstab partition for MMS page 11 bottom display. -/
theorem compositeRough_bucket {n : ℕ} (hn : n ≠ 1) (y : ℝ) :
    compositeRough n y =
      if ¬n.Prime ∧ y ≤ (n.minFac : ℝ) then 1 else 0 := by
  classical
  unfold compositeRough
  rw [roughIndicator_minFac hn]
  split_ifs <;> simp_all

/-- The cofactor after removing the least prime factor remains rough at that prime.
Derived arithmetic Buchstab step for MMS page 11 bottom display. -/
theorem minFac_cofactor_rough (n : ℕ) :
    Task361.roughIndicator (n / n.minFac) n.minFac = 1 := by
  classical
  unfold Task361.roughIndicator
  apply if_pos
  intro q hq hlt hd
  have hqn : q ∣ n := hd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd n))
  have hle : (n.minFac : ℝ) ≤ q := by
    exact_mod_cast Nat.minFac_le_of_dvd hq.two_le hqn
  linarith

/-- Composite rough numbers partition by their unique least prime factor.
Derived finite Buchstab identity for MMS page 11 bottom display.
Each bucket retains the actual rough cofactor at its least prime. -/
theorem compositeRough_buchstab {n : ℕ} (hn : 2 ≤ n) (y : ℝ) :
    compositeRough n y = ∑ p ∈ range (n + 1),
      if ¬n.Prime ∧ p = n.minFac ∧ y ≤ (p : ℝ) then
        Task361.roughIndicator (n / p) p else 0 := by
  classical
  rw [sum_eq_single n.minFac]
  · rw [minFac_cofactor_rough, compositeRough_bucket (by omega)]
    simp
  · intro p hp hne
    exact if_neg (fun h => hne h.2.1)
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (Nat.lt_succ_of_le (Nat.minFac_le (by omega)))))

/-- Prime and composite parts partition the rough indicator above the cutoff.
Derived first Buchstab step for MMS page 11 bottom display. -/
theorem roughIndicator_split {n : ℕ} {y : ℝ} (hy : y ≤ n) :
    Task361.roughIndicator n y = ρ n + compositeRough n y := by
  classical
  by_cases hp : n.Prime
  · simp [compositeRough, ρ, hp, Task361.roughIndicator_prime hp hy]
  · simp [compositeRough, ρ, hp]

/-- Every reference interval integer lies above the fourth root cutoff.
Derived endpoint check for MMS page 11. -/
theorem reference_cutoff {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∈ ints x (x + Task379.referenceLength x)) : x ^ (1 / 4 : ℝ) ≤ n := by
  have hxn : x ≤ n :=
    (Nat.le_ceil x).trans (by exact_mod_cast (mem_Icc.mp hn).1)
  exact (Real.rpow_le_self_of_one_le hx (by norm_num)).trans hxn

/-- The normalized first rough mean splits exactly into primes and composites.
MMS page 11 bottom display, before either analytic limit is used. -/
theorem weighted_rough_split {x : ℝ} (hx : 1 ≤ x) :
    Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
        primeMean x + compositeMean x := by
  have hs : (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) =
      (∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * ρ n) +
      ∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * compositeRough n (x ^ (1 / 4 : ℝ)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [roughIndicator_split (reference_cutoff hx hn), mul_add]
  rw [hs]
  unfold primeMean compositeMean
  ring

/-- LEAF. The weighted prime contribution has normalized limit one.
MMS page 11 bottom display, the prime number theorem in the reference interval.
This is only the prime term and contains no composite rough numbers. -/
theorem primeMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  sorry

/-- LEAF. The composite least prime factor buckets give the Buchstab integral.
MMS page 11 bottom display, Buchstab identity and prime number theorem,
with the prime term removed. The substitution u equals log x over log p
minus one gives the integral from one to three. This contains no prime term
and no ordered triple correction from equation 5.1. -/
theorem compositeMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - (∫ t in (1 : ℝ)..3, Task571.buchstabModel t)| ≤ δ := by
  sorry

/-- The Buchstab recursion identifies the sum of the two limiting coefficients.
MMS page 11 bottom display and the finite model recursion. -/
theorem rough_coefficient_identity :
    1 + (∫ t in (1 : ℝ)..3, Task571.buchstabModel t) =
      4 * Task571.buchstabModel 4 := by
  rw [Task571.buchstabModel_recursion (by norm_num) (by norm_num)]
  norm_num
  ring

/-- The exact first rough mean limit follows from its prime and composite pieces.
MMS page 11 first term of the bottom display.
CONDITIONAL ON primeMean_limit and compositeMean_limit.
This is the exact statement of the sealed roughReferenceMean_limit after unfolding. -/
theorem roughReferenceMean_limit_supply :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
        (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) -
          4 * Task571.buchstabModel 4| ≤ δ := by
  intro δ hδ
  obtain ⟨Xp, hp⟩ := primeMean_limit (δ / 2) (by linarith)
  obtain ⟨Xc, hc⟩ := compositeMean_limit (δ / 2) (by linarith)
  refine ⟨max 1 (max Xp Xc), fun x hx => ?_⟩
  rw [weighted_rough_split ((le_max_left _ _).trans hx), ← rough_coefficient_identity]
  have hp' := hp x ((le_max_left Xp Xc).trans ((le_max_right _ _).trans hx))
  have hc' := hc x ((le_max_right Xp Xc).trans ((le_max_right _ _).trans hx))
  have he : primeMean x + compositeMean x -
      (1 + ∫ t in (1 : ℝ)..3, Task571.buchstabModel t) =
      (primeMean x - 1) +
        (compositeMean x - ∫ t in (1 : ℝ)..3, Task571.buchstabModel t) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- The zero endpoint lets the closed reference sum use the Abel convention.
Derived endpoint bookkeeping for MMS page 11 bottom display. -/
theorem referenceWeight_sum_Ioc {x : ℝ} (hx : 0 < x) (c : ℕ → ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * c n) =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + Task379.referenceLength x⌋₊,
        Task379.referenceWeight x n * c n := by
  symm
  apply sum_subset
  · intro n hn
    have hn' := mem_Ioc.mp hn
    apply mem_Icc.mpr
    exact ⟨Nat.ceil_le.mpr (le_of_lt ((Nat.floor_lt hx.le).mp hn'.1)), hn'.2⟩
  · intro n hn hnot
    have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast (mem_Icc.mp hn).1)
    have hnfl : n ≤ ⌊x⌋₊ := by
      by_contra h
      exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
    have hnx : (n : ℝ) ≤ x := (by exact_mod_cast hnfl : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx.le)
    rw [Task379.referenceWeight_zero_outside hx (Or.inl hnx), zero_mul]

/-- The smooth reference sum is the Abel integral of the cumulative coefficients.
Derived partial summation for MMS page 11 bottom display. -/
theorem referenceWeight_abel {x : ℝ} (hx : 0 < x) (c : ℕ → ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * c n) =
      -(∫ t in x..(x + Task379.referenceLength x),
        deriv (Task379.referenceWeight x) t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) := by
  rw [referenceWeight_sum_Ioc hx]
  have hh := Task379.referenceLength_pos hx
  have hd := Task379.referenceWeight_contDiff x 1
  have he := sum_mul_eq_sub_sub_integral_mul c hx.le (by linarith : x ≤ x + Task379.referenceLength x)
    (fun t _ => hd.differentiable (by norm_num) t)
    (hd.continuous_deriv (by norm_num)).integrableOn_Icc
  rw [Task379.referenceWeight_zero_outside hx (Or.inr le_rfl),
    Task379.referenceWeight_zero_outside hx (Or.inl le_rfl), zero_mul, zero_mul,
    sub_self, zero_sub] at he
  rw [intervalIntegral.integral_of_le (by linarith : x ≤ x + Task379.referenceLength x)]
  exact he

/-- Subtracting an affine counting model leaves exactly its primitive error.
Derived partial summation identity for MMS page 11 bottom display. -/
theorem referenceWeight_abel_error {x : ℝ} (hx : 0 < x) (c : ℕ → ℝ) (A B : ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * c n) -
      A * (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
      -(∫ t in x..(x + Task379.referenceLength x),
        deriv (Task379.referenceWeight x) t *
          ((∑ n ∈ Icc 0 ⌊t⌋₊, c n) - (A * t + B))) := by
  have hh := Task379.referenceLength_pos hx
  have hab : x ≤ x + Task379.referenceLength x := by linarith
  have hd := Task379.referenceWeight_contDiff x 1
  have hw := hd.continuous
  have hd' : Continuous (deriv (Task379.referenceWeight x)) := hd.continuous_deriv (by norm_num)
  have hiw : IntervalIntegrable (Task379.referenceWeight x) volume x (x + Task379.referenceLength x) := hw.intervalIntegrable _ _
  have hid : IntervalIntegrable (deriv (Task379.referenceWeight x)) volume x (x + Task379.referenceLength x) := hd'.intervalIntegrable _ _
  have hip : IntervalIntegrable (fun t => deriv (Task379.referenceWeight x) t *
      ∑ n ∈ Icc 0 ⌊t⌋₊, c n) volume x (x + Task379.referenceLength x) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_mul_sum_Icc c hx.le hd'.integrableOn_Icc)
  have hia : IntervalIntegrable (fun t => deriv (Task379.referenceWeight x) t * (A * t + B))
      volume x (x + Task379.referenceLength x) :=
    (hd'.mul (continuous_const.mul continuous_id |>.add continuous_const)).intervalIntegrable _ _
  have he := intervalIntegral.integral_deriv_mul_eq_sub
    (u := Task379.referenceWeight x) (u' := deriv (Task379.referenceWeight x))
    (v := fun t => A * t + B) (v' := fun _ => A)
    (fun t _ => (hd.differentiable (by norm_num) t).hasDerivAt)
    (fun t _ => by convert ((hasDerivAt_id t).const_mul A).add_const B using 1 <;> simp)
    hid (intervalIntegrable_const)
  rw [intervalIntegral.integral_add hia (hiw.mul_const A),
    intervalIntegral.integral_mul_const,
    Task379.referenceWeight_zero_outside hx (Or.inr le_rfl),
    Task379.referenceWeight_zero_outside hx (Or.inl le_rfl), zero_mul, zero_mul, sub_self] at he
  rw [referenceWeight_abel hx c]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hip hia]
  linarith


/-- A uniform primitive error costs only the derivative constant.
Derived partial summation estimate for MMS page 11 bottom display. -/
theorem referenceWeight_abel_error_le {x : ℝ} (hx : 0 < x) (c : ℕ → ℝ)
    (A B C E : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t : ℝ, |deriv (Task379.referenceWeight x) t| ≤ C / Task379.referenceLength x)
    (hcount : ∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
      |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - (A * t + B)| ≤ E) :
    |(∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * c n) -
      A * (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)| ≤ C * E := by
  rw [referenceWeight_abel_error hx c A B, abs_neg]
  have hh := Task379.referenceLength_pos hx
  have hab : x ≤ x + Task379.referenceLength x := by linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := x + Task379.referenceLength x)
    (C := C / Task379.referenceLength x * E)
    (f := fun t => deriv (Task379.referenceWeight x) t *
      ((∑ n ∈ Icc 0 ⌊t⌋₊, c n) - (A * t + B))) (fun t ht => ?_)
  · rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at hb
    have he : C / Task379.referenceLength x * E * Task379.referenceLength x = C * E := by
      field_simp
    simpa only [he] using hb
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hderiv t) (hcount t ((Set.uIoc_of_le hab ▸ ht).1.le |> fun h => ⟨h, (Set.uIoc_of_le hab ▸ ht).2⟩))
      (abs_nonneg _) (div_nonneg hC hh.le)


/-- One constant controls the weighted discrepancy at every positive scale.
Derived use of the uniform g1 derivative bound on MMS page 11. -/
theorem referenceWeight_counting_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ∀ (c : ℕ → ℝ) (A B E : ℝ),
      (∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
        |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - (A * t + B)| ≤ E) →
      |(∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * c n) -
        A * (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)| ≤ C * E := by
  obtain ⟨C, hC, hd⟩ := Task678.referenceWeight_deriv_bound 1
  refine ⟨C, hC, fun x hx c A B E he => ?_⟩
  apply referenceWeight_abel_error_le hx c A B C E hC.le _ he
  intro t
  simpa only [iteratedDeriv_one, pow_one] using hd x hx t

/-- The weighted prime limit follows from a uniform local counting error.
Derived partial summation for MMS page 11 bottom display.
CONDITIONAL ON the displayed short interval prime counting hypothesis. -/
theorem primeMean_limit_of_counting_error
    (hPNT : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
        |(∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) -
          (t - x) / Real.log x| ≤ ε * Task379.referenceLength x / Real.log x) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  obtain ⟨C, hC, hb⟩ := referenceWeight_counting_error_bound
  let m : ℝ := ∫ u in (0 : ℝ)..1, Task678.referenceProfile u
  have hm : 0 < m := by
    have hi := Task379.referenceWeight_integral_pos (x := 1) (by norm_num)
    rw [Task678.referenceWeight_integral_scale (by norm_num)] at hi
    simpa [Task379.referenceLength, m] using hi
  intro δ hδ
  let ε : ℝ := δ * m / C
  have hε : 0 < ε := div_pos (mul_pos hδ hm) hC
  obtain ⟨X, hX⟩ := hPNT ε hε
  refine ⟨max 2 X, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := Task379.referenceLength_pos hx0
  have hW := Task379.referenceWeight_integral_pos hx0
  have hc := hb x hx0 ρ (1 / Real.log x)
    ((∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) - x / Real.log x)
    (ε * Task379.referenceLength x / Real.log x) (fun t ht => ?_)
  · have he : primeMean x - 1 =
        (Real.log x / (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)) *
          ((∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * ρ n) -
            (1 / Real.log x) * (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)) := by
      unfold primeMean
      field_simp
    rw [he, abs_mul, abs_of_pos (div_pos hl hW)]
    apply (mul_le_mul_of_nonneg_left hc (div_nonneg hl.le hW.le)).trans
    rw [Task678.referenceWeight_integral_scale hx0]
    change Real.log x / (Task379.referenceLength x * m) *
      (C * (ε * Task379.referenceLength x / Real.log x)) ≤ δ
    dsimp [ε]
    field_simp
    nlinarith
  · convert hX x ((le_max_right _ _).trans hx) t ht using 1
    congr 1
    ring

/-- Above the cubic stopping threshold the least prime factor cofactor is prime.
Derived terminating Buchstab bucket for MMS page 11 bottom display. -/
theorem minFac_cofactor_prime_of_cube {n : ℕ} (hn : 2 ≤ n) (hc : ¬ n.Prime)
    (hcube : n < n.minFac ^ 3) : (n / n.minFac).Prime := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hdiv : n.minFac ∣ n := Nat.minFac_dvd n
  have hnprod : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdiv
  have hqpos : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hp.pos
  have hq1 : n / n.minFac ≠ 1 := by
    intro he
    have heq : n.minFac = n := by simpa [he] using hnprod
    exact hc (heq ▸ hp)
  by_contra hq
  have hqp := Nat.minFac_prime hq1
  have hd : (n / n.minFac).minFac ∣ n :=
    (Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd hdiv)
  have hmin : n.minFac ≤ (n / n.minFac).minFac := Nat.minFac_le_of_dvd hqp.two_le hd
  have hs := Nat.minFac_sq_le_self hqpos hq
  have hp2 : n.minFac ^ 2 ≤ n / n.minFac := (Nat.pow_le_pow_left hmin 2).trans hs
  have hbound := Nat.mul_le_mul_left n.minFac hp2
  rw [hnprod] at hbound
  nlinarith
open Filter Topology

/-- The logarithmic integral is uniformly close to its local linear main term.
Derived PNT normalization for MMS page 11 and Davenport second edition page 113. -/
theorem logIntegral_local_error {x t : ℝ} (hx : 2 ≤ x) (hxt : x ≤ t) (htx : t ≤ 2 * x) :
    |(∫ u in x..t, 1 / Real.log u) - (t - x) / Real.log x| ≤
      (t - x) * Real.log 2 / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi : IntervalIntegrable (fun u => 1 / Real.log u) volume x t := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hxt] at hu
    have hu0 : 0 < u := hx0.trans_le hu.1
    have hlog : Real.log u ≠ 0 := (Real.log_pos (by linarith [hu.1])).ne'
    exact continuousWithinAt_const.div (Real.continuousAt_log hu0.ne').continuousWithinAt hlog
  have he : (∫ u in x..t, 1 / Real.log u - 1 / Real.log x) =
      (∫ u in x..t, 1 / Real.log u) - (t - x) / Real.log x := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := t) (C := Real.log 2 / Real.log x ^ 2)
    (f := fun u => 1 / Real.log u - 1 / Real.log x) (fun u hu => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxt)] at hb
    convert hb using 1
    ring
  · rw [Set.uIoc_of_le hxt] at hu
    have hu0 : 0 < u := hx0.trans hu.1
    have hlu : Real.log x ≤ Real.log u := Real.log_le_log hx0 hu.1.le
    have hlu0 : 0 < Real.log u := hlx.trans_le hlu
    have hlu2 : Real.log u ≤ Real.log x + Real.log 2 := by
      have := Real.log_le_log hu0 (hu.2.trans htx)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at this
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hlx hlu))]
    apply (le_div_iff₀ (sq_pos_of_pos hlx)).mpr
    field_simp
    nlinarith

/-- A PNT power saving above one half supplies square root coefficient two.
Davenport second edition page 113, with exponent eleven twentieths.
CONDITIONAL ON the displayed Vinogradov and Korobov PNT hypothesis. -/
theorem prime_count_error_exp_two_of_power
    (hPNT : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∃ Y : ℝ, 2 ≤ Y ∧
      ∀ y : ℝ, Y ≤ y →
        |(∑ n ∈ Icc 0 ⌊y⌋₊, ρ n) - (∫ u in (2 : ℝ)..y, 1 / Real.log u)| ≤
          K * y * Real.exp (-c * (Real.log y) ^ (11 / 20 : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y : ℝ, 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      |(∑ n ∈ Icc 0 ⌊y⌋₊, ρ n) - (∫ u in (2 : ℝ)..y, 1 / Real.log u)| ≤
        K * y * Real.exp (-2 * Real.sqrt (Real.log y)) := by
  obtain ⟨c, hc, K, hK, Y, hY2, hY⟩ := hPNT
  have ht : Tendsto (fun y : ℝ => c * (Real.log y) ^ (1 / 20 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp Real.tendsto_log_atTop).const_mul_atTop hc
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 2)
  refine ⟨K, hK, max Y Z, hY2.trans (le_max_left _ _), fun y hy => ?_⟩
  have hyy := (le_max_left Y Z).trans hy
  have hy2 : 2 ≤ y := hY2.trans hyy
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hc2 := hZ y ((le_max_right Y Z).trans hy)
  have he : 2 * Real.sqrt (Real.log y) ≤ c * (Real.log y) ^ (11 / 20 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have hp : (Real.log y) ^ (11 / 20 : ℝ) =
        (Real.log y) ^ (1 / 2 : ℝ) * (Real.log y) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      norm_num
    rw [hp]
    nlinarith [Real.rpow_nonneg hly (1 / 2 : ℝ)]
  exact (hY y hyy).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (mul_nonneg hK.le (by linarith)))

/-- The stronger PNT error is negligible at the reference interval scale.
Derived comparison for MMS page 11 using coefficient two, not the spent global envelope. -/
theorem reference_prime_error_ratio_tendsto :
    Tendsto (fun x : ℝ => Real.log x * Real.exp (-Real.sqrt (Real.log x))) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp ht
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [Real.sq_sqrt (Real.log_nonneg hx)]

/-- The global coefficient two PNT gives a uniform local counting error.
Derived endpoint subtraction and logarithmic integral estimate for MMS page 11.
CONDITIONAL ON the displayed global prime counting estimate. -/
theorem prime_counting_error_of_exp_two
    (hPNT : ∃ K : ℝ, 0 < K ∧ ∃ Y : ℝ, 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      |(∑ n ∈ Icc 0 ⌊y⌋₊, ρ n) - (∫ u in (2 : ℝ)..y, 1 / Real.log u)| ≤
        K * y * Real.exp (-2 * Real.sqrt (Real.log y))) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
        |(∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) -
          (t - x) / Real.log x| ≤ ε * Task379.referenceLength x / Real.log x := by
  obtain ⟨K, hK, Y, hY2, hY⟩ := hPNT
  have ht : Tendsto (fun x : ℝ =>
      3 * K * (Real.log x * Real.exp (-Real.sqrt (Real.log x))) +
        Real.log 2 * (Real.log x)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_apply] using
      (reference_prime_error_ratio_tendsto.const_mul (3 * K)).add
        ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (Real.log 2))
  intro ε hε
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨max Y Z, fun x hx t htx => ?_⟩
  have hxY : Y ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := hY2.trans hxY
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := Task379.referenceLength_pos hx0
  have hhx : Task379.referenceLength x ≤ x := by
    unfold Task379.referenceLength
    exact mul_le_of_le_one_right hx0.le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _)))
  have ht2x : t ≤ 2 * x := by linarith [htx.2]
  have ht0 : 0 < t := hx0.trans_le htx.1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi (b : ℝ) (hb : 2 ≤ b) : IntervalIntegrable (fun u => 1 / Real.log u) volume 2 b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hb] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact continuousWithinAt_const.div (Real.continuousAt_log hu0.ne').continuousWithinAt
      (Real.log_pos (by linarith [hu.1])).ne'
  have hLi : (∫ u in (2 : ℝ)..t, 1 / Real.log u) -
      (∫ u in (2 : ℝ)..x, 1 / Real.log u) = ∫ u in x..t, 1 / Real.log u :=
    intervalIntegral.integral_interval_sub_left (hi t (hx2.trans htx.1)) (hi x hx2)
  have hexp : Real.exp (-2 * Real.sqrt (Real.log t)) ≤
      Real.exp (-2 * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_le_sqrt (Real.log_le_log hx0 htx.1)
    linarith
  have hpt : |(∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∫ u in (2 : ℝ)..t, 1 / Real.log u)| ≤
      2 * K * x * Real.exp (-2 * Real.sqrt (Real.log x)) := by
    have he := mul_le_mul (mul_le_mul_of_nonneg_left ht2x hK.le) hexp
      (Real.exp_pos _).le (mul_nonneg hK.le (by linarith))
    exact (hY t (hxY.trans htx.1)).trans (by nlinarith [he])
  have hpx := hY x hxY
  have hlocal := logIntegral_local_error hx2 htx.1 ht2x
  have hid : (∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) -
      (t - x) / Real.log x =
      ((∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∫ u in (2 : ℝ)..t, 1 / Real.log u)) -
      ((∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) - (∫ u in (2 : ℝ)..x, 1 / Real.log u)) +
      ((∫ u in x..t, 1 / Real.log u) - (t - x) / Real.log x) := by rw [← hLi]; ring
  rw [hid]
  have hraw : |((∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∫ u in (2 : ℝ)..t, 1 / Real.log u)) -
      ((∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) - (∫ u in (2 : ℝ)..x, 1 / Real.log u)) +
      ((∫ u in x..t, 1 / Real.log u) - (t - x) / Real.log x)| ≤
      3 * K * x * Real.exp (-2 * Real.sqrt (Real.log x)) +
        Task379.referenceLength x * Real.log 2 / Real.log x ^ 2 := by
    have ha := (abs_add_le
      (((∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∫ u in (2 : ℝ)..t, 1 / Real.log u)) -
        ((∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) - (∫ u in (2 : ℝ)..x, 1 / Real.log u)))
      ((∫ u in x..t, 1 / Real.log u) - (t - x) / Real.log x))
    have habs := abs_sub
      ((∑ n ∈ Icc 0 ⌊t⌋₊, ρ n) - (∫ u in (2 : ℝ)..t, 1 / Real.log u))
      ((∑ n ∈ Icc 0 ⌊x⌋₊, ρ n) - (∫ u in (2 : ℝ)..x, 1 / Real.log u))
    have hlen : (t - x) * Real.log 2 / Real.log x ^ 2 ≤
        Task379.referenceLength x * Real.log 2 / Real.log x ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [htx.2]) hl2.le) (sq_nonneg _)
    linarith
  apply hraw.trans
  have he : 3 * K * x * Real.exp (-2 * Real.sqrt (Real.log x)) +
      Task379.referenceLength x * Real.log 2 / Real.log x ^ 2 =
      (3 * K * (Real.log x * Real.exp (-Real.sqrt (Real.log x))) +
        Real.log 2 * (Real.log x)⁻¹) * Task379.referenceLength x / Real.log x := by
    have hex : Real.exp (-2 * Real.sqrt (Real.log x)) =
        Real.exp (-Real.sqrt (Real.log x)) * Real.exp (-Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hex, Task379.referenceLength]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hZ x ((le_max_right _ _).trans hx)).le hh.le) hl.le

/-- The exact weighted prime limit follows from one stronger PNT input.
MMS page 11 bottom display and Davenport second edition page 113.
CONDITIONAL ON the sole LEAF hypothesis hPNT stated explicitly below.
No weighted prime limit or rough number estimate is hidden in that hypothesis. -/
theorem primeMean_limit_of_power_PNT
    (hPNT : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∃ Y : ℝ, 2 ≤ Y ∧
      ∀ y : ℝ, Y ≤ y →
        |(∑ n ∈ Icc 0 ⌊y⌋₊, ρ n) - (∫ u in (2 : ℝ)..y, 1 / Real.log u)| ≤
          K * y * Real.exp (-c * (Real.log y) ^ (11 / 20 : ℝ))) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  exact primeMean_limit_of_counting_error
    (prime_counting_error_of_exp_two (prime_count_error_exp_two_of_power hPNT))

/-- Uniform unweighted local counts imply the corresponding smooth weighted limit.
Derived smoothing step for MMS page 11 bottom display.
CONDITIONAL ON the explicit cumulative counting error for the coefficient family. -/
theorem referenceWeightedMean_limit_of_counting_error
    (c : ℝ → ℕ → ℝ) (α : ℝ)
    (hPNT : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
        |(∑ n ∈ Icc 0 ⌊t⌋₊, c x n) - (∑ n ∈ Icc 0 ⌊x⌋₊, c x n) -
          α * (t - x) / Real.log x| ≤ ε * Task379.referenceLength x / Real.log x) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * c x n) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) - α| ≤ δ := by
  obtain ⟨C, hC, hb⟩ := referenceWeight_counting_error_bound
  let m : ℝ := ∫ u in (0 : ℝ)..1, Task678.referenceProfile u
  have hm : 0 < m := by
    have hi := Task379.referenceWeight_integral_pos (x := 1) (by norm_num)
    rw [Task678.referenceWeight_integral_scale (by norm_num)] at hi
    simpa [Task379.referenceLength, m] using hi
  intro δ hδ
  let ε : ℝ := δ * m / C
  have hε : 0 < ε := div_pos (mul_pos hδ hm) hC
  obtain ⟨X, hX⟩ := hPNT ε hε
  refine ⟨max 2 X, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hh := Task379.referenceLength_pos hx0
  have hW := Task379.referenceWeight_integral_pos hx0
  have hc := hb x hx0 (c x) (α / Real.log x)
    ((∑ n ∈ Icc 0 ⌊x⌋₊, c x n) - α * x / Real.log x)
    (ε * Task379.referenceLength x / Real.log x) (fun t ht => ?_)
  · have he : Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * c x n) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) - α =
        (Real.log x / (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)) *
          ((∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * c x n) -
            (α / Real.log x) * (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)) := by
      field_simp
    rw [he, abs_mul, abs_of_pos (div_pos hl hW)]
    apply (mul_le_mul_of_nonneg_left hc (div_nonneg hl.le hW.le)).trans
    rw [Task678.referenceWeight_integral_scale hx0]
    change Real.log x / (Task379.referenceLength x * m) *
      (C * (ε * Task379.referenceLength x / Real.log x)) ≤ δ
    dsimp [ε]
    field_simp
    nlinarith
  · convert hX x ((le_max_right _ _).trans hx) t ht using 1
    congr 1
    ring

/-- The composite weighted limit follows from the unweighted Buchstab count.
Derived smoothing reduction for MMS page 11 bottom display.
CONDITIONAL ON the displayed composite counting asymptotic.
This does not derive that asymptotic from the prime PNT hypothesis. -/
theorem compositeMean_limit_of_counting_error
    (hcount : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ t ∈ Set.Icc x (x + Task379.referenceLength x),
        |(∑ n ∈ Icc 0 ⌊t⌋₊, compositeRough n (x ^ (1 / 4 : ℝ))) -
          (∑ n ∈ Icc 0 ⌊x⌋₊, compositeRough n (x ^ (1 / 4 : ℝ))) -
          (∫ u in (1 : ℝ)..3, Task571.buchstabModel u) * (t - x) / Real.log x| ≤
          ε * Task379.referenceLength x / Real.log x) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - (∫ u in (1 : ℝ)..3, Task571.buchstabModel u)| ≤ δ := by
  exact referenceWeightedMean_limit_of_counting_error
    (fun x n => compositeRough n (x ^ (1 / 4 : ℝ)))
    (∫ u in (1 : ℝ)..3, Task571.buchstabModel u) hcount

/-- A composite least prime factor bucket retains both cofactor parts.
Derived second Buchstab step for MMS page 11 bottom display. -/
theorem compositeRough_cofactor_split {n : ℕ} (hn : 2 ≤ n) (hc : ¬ n.Prime) (y : ℝ) :
    compositeRough n y = if y ≤ (n.minFac : ℝ) then
      ρ (n / n.minFac) + compositeRough (n / n.minFac) n.minFac else 0 := by
  have hle : (n.minFac : ℝ) ≤ (n / n.minFac : ℕ) := by
    exact_mod_cast Nat.minFac_le_div (by omega : 0 < n) hc
  rw [← roughIndicator_split hle, minFac_cofactor_rough, compositeRough_bucket (by omega)]
  simp only [hc, not_false_eq_true, true_and]

/-- The finite Buchstab partition uses one fixed square root upper bound.
Derived least prime factor support for MMS page 11 bottom display. -/
theorem compositeRough_buchstab_fixed {n N : ℕ} (hn : 2 ≤ n) (hN : n ≤ N) (y : ℝ) :
    compositeRough n y = ∑ p ∈ Icc 2 (Nat.sqrt N),
      if ¬n.Prime ∧ p = n.minFac ∧ y ≤ (p : ℝ) then
        Task361.roughIndicator (n / p) p else 0 := by
  classical
  by_cases hp : n.Prime
  · simp [compositeRough, hp]
  have hmem : n.minFac ∈ Icc 2 (Nat.sqrt N) := by
    exact mem_Icc.mpr ⟨(Nat.minFac_prime (by omega)).two_le,
      Nat.le_sqrt'.mpr ((Nat.minFac_sq_le_self (by omega) hp).trans hN)⟩
  rw [sum_eq_single n.minFac]
  · rw [minFac_cofactor_rough, compositeRough_bucket (by omega)]
    simp
  · intro p hp hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot hmem)

/-- Weighted composite sums reindex over a fixed least prime factor range.
Derived finite Buchstab rearrangement for MMS page 11 bottom display.
The exact upper endpoint is the square root of the reference interval upper endpoint. -/
theorem weighted_composite_buchstab_fixed {x : ℝ} (hx : 2 ≤ x) (y : ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * compositeRough n y) =
    ∑ p ∈ Icc 2 (Nat.sqrt ⌊x + Task379.referenceLength x⌋₊),
      ∑ n ∈ ints x (x + Task379.referenceLength x),
        if ¬n.Prime ∧ p = n.minFac ∧ y ≤ (p : ℝ) then
          Task379.referenceWeight x n * Task361.roughIndicator (n / p) p else 0 := by
  classical
  have hi {n : ℕ} (hn : n ∈ ints x (x + Task379.referenceLength x)) :
      2 ≤ n ∧ n ≤ ⌊x + Task379.referenceLength x⌋₊ := by
    have hn' := mem_Icc.mp hn
    have hxle : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hn'.1)
    exact ⟨by exact_mod_cast (hx.trans hxle), hn'.2⟩
  calc
    _ = ∑ n ∈ ints x (x + Task379.referenceLength x),
        ∑ p ∈ Icc 2 (Nat.sqrt ⌊x + Task379.referenceLength x⌋₊),
          if ¬n.Prime ∧ p = n.minFac ∧ y ≤ (p : ℝ) then
            Task379.referenceWeight x n * Task361.roughIndicator (n / p) p else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [compositeRough_buchstab_fixed (hi hn).1 (hi hn).2, mul_sum]
      apply sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ = _ := sum_comm

/-- The logarithmic bucket coordinate gives the exact Buchstab coefficient.
Derived substitution u equals one over a minus one for MMS page 11 bottom display. -/
theorem buchstab_integral_log_coordinates :
    (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ),
      Task571.buchstabModel (1 / a - 1) / a ^ 2) =
      ∫ u in (1 : ℝ)..3, Task571.buchstabModel u := by
  have hw : ContinuousOn Task571.buchstabModel (Set.Icc (1 : ℝ) 3) := by
    apply (Task571.buchstabStage_continuous_clamp 8).continuousOn.congr
    intro u hu
    simp only [Task571.buchstabModel, max_eq_right hu.1]
  have hd : ∀ a ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ),
      HasDerivAt (fun a : ℝ => 1 / a - 1) (-1 / a ^ 2) a := by
    intro a ha
    have ha0 : a ≠ 0 := by rw [Set.uIcc_of_le (by norm_num)] at ha; linarith [ha.1]
    simpa only [one_div, neg_div, one_mul] using (hasDerivAt_inv ha0).sub_const 1
  have hd' : ContinuousOn (fun a : ℝ => -1 / a ^ 2) (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
    intro a ha
    have ha0 : a ≠ 0 := by rw [Set.uIcc_of_le (by norm_num)] at ha; linarith [ha.1]
    exact continuousWithinAt_const.div (continuousWithinAt_id.pow 2) (pow_ne_zero 2 ha0)
  have hsub : (fun a : ℝ => 1 / a - 1) '' Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ) ⊆ Set.Icc (1 : ℝ) 3 := by
    rintro u ⟨a, ha, rfl⟩
    rw [Set.uIcc_of_le (by norm_num)] at ha
    have ha0 : 0 < a := by linarith [ha.1]
    constructor
    · have h := (le_div_iff₀ ha0).mpr (show 2 * a ≤ 1 by linarith [ha.2])
      linarith
    · have h := (div_le_iff₀ ha0).mpr (show 1 ≤ 4 * a by linarith [ha.1])
      linarith
  have hs := intervalIntegral.integral_comp_mul_deriv' hd hd' (hw.mono hsub)
  norm_num only [Function.comp_apply, one_div_div, div_one, sub_self,
    show (1 : ℝ) / (1 / 4) - 1 = 3 by norm_num,
    show (1 : ℝ) / (1 / 2) - 1 = 1 by norm_num] at hs
  have he : (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ),
      Task571.buchstabModel (1 / a - 1) * (-1 / a ^ 2)) =
      -(∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel (1 / a - 1) / a ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    ring
  rw [he, intervalIntegral.integral_symm (a := (1 : ℝ)) (b := 3)] at hs
  linarith

/-- The local rough cofactor model has exactly the Mertens prime atom Jacobian.
Derived logarithmic normalization for MMS page 11 bottom display. -/
theorem compositeModel_log_coordinates {x p : ℝ} (hx : 1 < x) (hp : 1 < p) :
    Real.log x / (p * Real.log p) *
      Task571.buchstabModel (Real.log (x / p) / Real.log p) =
      (Task571.buchstabModel (1 / (Real.log p / Real.log x) - 1) /
        (Real.log p / Real.log x) ^ 2) * (Real.log p / p / Real.log x) := by
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlp : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  have hx0 : x ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by linarith
  have ha : Real.log (x / p) / Real.log p = 1 / (Real.log p / Real.log x) - 1 := by
    rw [Real.log_div hx0 hp0]
    field_simp
  rw [ha]
  field_simp

open Real

/-- A bad sequence lifts the existing natural index block theorem to real scales.
Derived continuous quadrature step for MMS page 11.
CONDITIONAL ON the explicit block limits, which are supplied below for prime weights. -/
theorem continuous_test_of_blocks_real
    (s : ℝ → Finset ℕ) (t w : ℝ → ℕ → ℝ)
    (hw : ∀ x q, q ∈ s x → 0 ≤ w x q)
    (ht : ∀ x q, q ∈ s x → 3 ≤ t x q ∧ t x q < 6)
    (hb : ∀ a b : ℝ, 3 ≤ a → a < b → b ≤ 6 →
      Tendsto (fun x => ∑ q ∈ (s x).filter (fun q => a ≤ t x q ∧ t x q < b), w x q)
        atTop (𝓝 (log (b / a))))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 3 6)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∑ q ∈ s x, φ (t x q) * w x q ≤
      (∫ u in (3 : ℝ)..6, φ u / u) + η := by
  by_contra h
  simp only [eventually_atTop, not_exists, not_forall, not_le] at h
  choose x hx hbad using fun N : ℕ => h (N : ℝ)
  have hxlim : Tendsto x atTop atTop :=
    tendsto_atTop_mono hx tendsto_natCast_atTop_atTop
  have hh := LeanLab.AlmostPrimeSums.Decomp1544c.continuous_test_of_blocks
    (fun N => s (x N)) (fun N => t (x N)) (fun N => w (x N))
    (fun N q hq => hw (x N) q hq) (fun N q hq => ht (x N) q hq)
    (fun a b ha hab hb' => (hb a b ha hab hb').comp hxlim) φ hφ hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  exact (not_le_of_gt (hbad N)) (hN N le_rfl)

/-- An auxiliary real scale prime window for the continuous block test.
Derived coordinate normalization for MMS page 11 bottom display. -/
noncomputable def primeQuadratureWindow (X : ℝ) : Finset ℕ := by
  classical
  exact (range (⌊X⌋₊ + 1)).filter fun q =>
    q.Prime ∧ 2 ≤ X ∧ X < (q : ℝ) ^ 6 ∧ (q : ℝ) ^ 3 ≤ X

/-- The auxiliary prime cutoffs are exactly the logarithmic coordinate range.
Derived real endpoint check for MMS page 11 quadrature. -/
theorem real_prime_log_window {X : ℝ} (hX : 2 ≤ X) {q : ℕ} (hq : q.Prime) :
    (X < (q : ℝ) ^ 6 ∧ (q : ℝ) ^ 3 ≤ X) ↔
      3 ≤ log X / log q ∧ log X / log q < 6 := by
  have hX0 : 0 < X := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hq.one_lt)
  rw [le_div_iff₀ hlq, div_lt_iff₀ hlq]
  constructor
  · rintro ⟨h6, h3⟩
    have h6' := log_lt_log hX0 h6
    have h3' := log_le_log (pow_pos hq0 3) h3
    rw [log_pow] at h6' h3'
    norm_num only [Nat.cast_ofNat] at h6' h3'
    exact ⟨h3', by linarith⟩
  · rintro ⟨h3, h6⟩
    constructor
    · apply (log_lt_log_iff hX0 (pow_pos hq0 6)).mp
      rw [log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    · apply (log_le_log_iff (pow_pos hq0 3) hX0).mp
      rw [log_pow]
      norm_num only [Nat.cast_ofNat]
      exact h3

/-- Each auxiliary coordinate block has exact real exponential endpoints.
Derived finite endpoint identity for MMS page 11 quadrature. -/
theorem real_prime_block_eq {X : ℝ} (hX : 2 ≤ X) {a b : ℝ}
    (ha : 3 ≤ a) (hab : a < b) (hb : b ≤ 6) :
    (primeQuadratureWindow X).filter (fun q : ℕ => a ≤ log X / log q ∧ log X / log q < b) =
      (Ioc ⌊exp (log X / b)⌋₊ ⌊exp (log X / a)⌋₊).filter Nat.Prime := by
  classical
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  ext q
  simp only [primeQuadratureWindow, mem_filter, mem_range, mem_Ioc]
  by_cases hqp : q.Prime
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hqp.one_lt)
    have hcut : (⌊exp (log X / b)⌋₊ < q ∧ q ≤ ⌊exp (log X / a)⌋₊) ↔
        a ≤ log X / log q ∧ log X / log q < b := by
      rw [Nat.floor_lt (exp_pos _).le, Nat.le_floor_iff (exp_pos _).le,
        ← lt_log_iff_exp_lt hq0, ← log_le_iff_le_exp hq0,
        div_lt_iff₀ hb0, le_div_iff₀ ha0,
        le_div_iff₀ hlq, div_lt_iff₀ hlq]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    have hwindow := real_prime_log_window hX hqp
    constructor
    · rintro ⟨⟨_, _, _, _, _⟩, ht⟩
      exact ⟨hcut.mpr ht, hqp⟩
    · rintro ⟨hcut', _⟩
      have ht := hcut.mp hcut'
      have hwin := hwindow.mpr ⟨ha.trans ht.1, ht.2.trans_le hb⟩
      have hqX : q ≤ ⌊X⌋₊ := by
        have hqpow : (q : ℝ) ≤ (q : ℝ) ^ 3 := by
          exact_mod_cast (Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) q)
        exact Nat.le_floor (hqpow.trans hwin.2)
      exact ⟨⟨by omega, hqp, hX, hwin⟩, ht⟩
  · simp [hqp]

/-- Real scale prime block masses follow from the proved second Mertens estimate.
Derived primitive measure convergence for MMS page 11 quadrature. -/
theorem real_prime_block_tendsto {a b : ℝ} (ha : 3 ≤ a) (hab : a < b) (hb : b ≤ 6) :
    Tendsto (fun X : ℝ => ∑ q ∈ (primeQuadratureWindow X).filter
      (fun q : ℕ => a ≤ log X / log q ∧ log X / log q < b), (1 : ℝ) / q)
      atTop (𝓝 (log (b / a))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have herr : Tendsto (fun X : ℝ => 4 * b / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_ge_atTop (2 : ℝ), tendsto_log_atTop.eventually_ge_atTop (b * log 2),
    herr.eventually (gt_mem_nhds hε)] with X hX hL hsmall
  have hL0 : 0 < log X := log_pos (by linarith)
  have hy : (2 : ℝ) ≤ exp (log X / b) := by
    rw [← log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hb0]
    nlinarith
  have hyx : exp (log X / b) ≤ exp (log X / a) := by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL0.le ha0 hab.le
  have hm := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy hyx
  simp only [log_exp] at hm
  have hmain : log (log X / a) - log (log X / b) = log (b / a) := by
    rw [log_div hL0.ne' ha0.ne', log_div hL0.ne' hb0.ne', log_div hb0.ne' ha0.ne']
    ring
  have he : 4 / (log X / b) = 4 * b / log X := by field_simp
  rw [hmain, he] at hm
  rw [Real.dist_eq, real_prime_block_eq hX ha hab hb]
  exact hm.trans_lt hsmall

/-- Every continuous test on the auxiliary prime window has the exact limiting integral.
Derived continuous Mertens quadrature for MMS page 11 bottom display.
The block hypotheses are proved internally and no cited input remains. -/
theorem real_prime_sum_integral_tendsto (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc 3 6)) :
    Tendsto (fun X : ℝ => ∑ q ∈ primeQuadratureWindow X,
      φ (log X / log q) / q) atTop (𝓝 (∫ u in (3 : ℝ)..6, φ u / u)) := by
  have upper (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 3 6)) (η : ℝ) (hη : 0 < η) :
      ∀ᶠ X : ℝ in atTop, ∑ q ∈ primeQuadratureWindow X, f (log X / log q) / q ≤
        (∫ u in (3 : ℝ)..6, f u / u) + η := by
    have ht : ∀ X q, q ∈ primeQuadratureWindow X →
        3 ≤ log X / log q ∧ log X / log q < 6 := by
      intro X q hq
      have h := (mem_filter.mp hq).2
      exact (real_prime_log_window h.2.1 h.1).mp h.2.2
    simpa only [div_eq_mul_inv, one_mul] using continuous_test_of_blocks_real
      primeQuadratureWindow (fun X q => log X / log q) (fun _ q => (1 : ℝ) / q)
      (fun _ _ _ => by positivity) ht
      (fun a b ha hab hb => real_prime_block_tendsto ha hab hb) f hf hη
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [upper φ hφ (η / 2) (by positivity),
    upper (fun u => -φ u) hφ.neg (η / 2) (by positivity)] with X hu hl
  simp only [neg_div, sum_neg_distrib, intervalIntegral.integral_neg] at hl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The fixed scalar Buchstab profile for the auxiliary logarithmic coordinate.
Derived normalization for MMS page 11 bottom display. -/
noncomputable def compositeQuadratureProfile (u : ℝ) : ℝ :=
  ((2 / 3 : ℝ) * u) * Task571.buchstabModel ((2 / 3 : ℝ) * u - 1)

/-- The scalar composite model profile is continuous on the complete auxiliary interval.
Derived regularity for MMS page 11 continuous prime quadrature. -/
theorem compositeQuadratureProfile_continuous :
    ContinuousOn compositeQuadratureProfile (Set.Icc (3 : ℝ) 6) := by
  have hc : Continuous (fun u : ℝ => Task571.buchstabStage 8 (max 1 ((2 / 3 : ℝ) * u - 1))) :=
    (Task571.buchstabStage_continuous_clamp 8).comp
    (((continuous_const : Continuous (fun _ : ℝ => (2 / 3 : ℝ))).mul continuous_id).sub continuous_const)
  apply (((continuous_const : Continuous (fun _ : ℝ => (2 / 3 : ℝ))).mul continuous_id).mul hc).continuousOn.congr
  intro u hu
  have hu1 : 1 ≤ (2 / 3 : ℝ) * u - 1 := by linarith [hu.1]
  change (2 / 3 : ℝ) * u * Task571.buchstabStage 8 ((2 / 3 : ℝ) * u - 1) =
    (2 / 3 : ℝ) * u * Task571.buchstabStage 8 (max 1 ((2 / 3 : ℝ) * u - 1))
  rw [max_eq_right hu1]

/-- The auxiliary logarithmic density gives the required Buchstab coefficient.
Derived affine substitution for MMS page 11 bottom display. -/
theorem compositeQuadratureProfile_integral :
    (∫ u in (3 : ℝ)..6, compositeQuadratureProfile u / u) =
      ∫ u in (1 : ℝ)..3, Task571.buchstabModel u := by
  let g : ℝ → ℝ := fun v => Task571.buchstabStage 8 (max 1 v)
  have hg : Continuous g := Task571.buchstabStage_continuous_clamp 8
  have hd : ∀ u ∈ Set.uIcc (3 : ℝ) 6,
      HasDerivAt (fun u : ℝ => (2 / 3 : ℝ) * u - 1) (2 / 3 : ℝ) u := by
    intro u hu
    convert ((hasDerivAt_id u).const_mul (2 / 3 : ℝ)).sub_const 1 using 1 <;> norm_num
  have hs := intervalIntegral.integral_comp_mul_deriv hd continuous_const.continuousOn hg
  norm_num only [show (2 / 3 : ℝ) * 3 - 1 = 1 by norm_num,
    show (2 / 3 : ℝ) * 6 - 1 = 3 by norm_num] at hs
  calc
    _ = ∫ u in (3 : ℝ)..6, (g ∘ (fun v => (2 / 3 : ℝ) * v - 1)) u * (2 / 3 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hu0 : u ≠ 0 := by linarith [hu.1]
      have hu1 : 1 ≤ (2 / 3 : ℝ) * u - 1 := by linarith [hu.1]
      simp only [g, Function.comp_apply, compositeQuadratureProfile, Task571.buchstabModel, max_eq_right hu1]
      field_simp
    _ = ∫ u in (1 : ℝ)..3, g u := hs
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      simp only [g, Task571.buchstabModel, max_eq_right hu.1]

/-- The scalar prime cofactor model has the exact Buchstab integral limit.
Derived continuous prime quadrature for MMS page 11 bottom display.
This is a model sum and asserts no estimate for the actual composite count. -/
theorem compositePrimeModel_sum_tendsto :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime,
        Real.log x / ((p : ℝ) * Real.log p) *
          Task571.buchstabModel (Real.log (x / p) / Real.log p))
      atTop (𝓝 (∫ u in (1 : ℝ)..3, Task571.buchstabModel u)) := by
  have hh := (real_prime_sum_integral_tendsto compositeQuadratureProfile
    compositeQuadratureProfile_continuous).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2))
  rw [compositeQuadratureProfile_integral] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hpow : 2 ≤ x ^ (3 / 2 : ℝ) := hx.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hln : log (x ^ (3 / 2 : ℝ)) = (3 / 2 : ℝ) * log x := by rw [Real.log_rpow hx0]
  have hW := real_prime_block_eq hpow (a := 3) (b := 6) (by norm_num) (by norm_num) (by norm_num)
  have hfilter : (primeQuadratureWindow (x ^ (3 / 2 : ℝ))).filter
      (fun q : ℕ => 3 ≤ log (x ^ (3 / 2 : ℝ)) / log q ∧ log (x ^ (3 / 2 : ℝ)) / log q < 6) =
        primeQuadratureWindow (x ^ (3 / 2 : ℝ)) := by
    apply filter_eq_self.mpr
    intro q hq
    have h := (mem_filter.mp hq).2
    exact (real_prime_log_window h.2.1 h.1).mp h.2.2
  rw [hfilter] at hW
  have he₁ : exp (log (x ^ (3 / 2 : ℝ)) / 6) = x ^ (1 / 4 : ℝ) := by
    rw [hln, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have he₂ : exp (log (x ^ (3 / 2 : ℝ)) / 3) = x ^ (1 / 2 : ℝ) := by
    rw [hln, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [he₁, he₂] at hW
  simp only [Function.comp_apply]
  rw [hW]
  apply sum_congr rfl
  intro p hp
  have hprime := (mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hlp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hprime.one_lt)).ne'
  have heq : (2 / 3 : ℝ) * (((3 / 2 : ℝ) * log x) / log p) - 1 =
      log (x / p) / log p := by
    rw [log_div hx0.ne' hp0]
    field_simp
  simp only [compositeQuadratureProfile, hln]
  rw [heq]
  field_simp

end LeanLab.Ternary.MMS.Task581

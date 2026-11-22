/-
P0076, Section 4, pages 13 to 17.
Decomposition of the bounded shift and changed scale restriction input in MainInputs.
The three unresolved LEAF theorems remain CONDITIONAL. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Restriction
import LeanLab.Teravainen2016.TernaryBridge

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Page 14, the number of excluded residues at a prime above w. -/
def envelopingOmega (w p : ℕ) : ℕ :=
  if p ≤ w then 0 else if p % 4 = 1 then 1 else 2

/-- Page 15, the squarefree multiplicative weight h.
The natural subtraction agrees with the printed denominator at primes above w. -/
noncomputable def envelopingH (w d : ℕ) : ℝ :=
  if Squarefree d then
    ∏ p ∈ d.primeFactors, (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ)
  else 0

/-- Page 15, the sum G_d of z. -/
noncomputable def envelopingG (w d : ℕ) (z : ℝ) : ℝ :=
  ∑ δ ∈ (Icc 1 ⌊z⌋₊).filter (fun δ => (Nat.lcm d δ : ℝ) ≤ z), envelopingH w δ

/-- Page 15, the Selberg coefficients rho_d. -/
noncomputable def envelopingRho (w d : ℕ) (z : ℝ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * envelopingG w d z / envelopingG w 1 z

/-- Page 15, the prime product with an inclusive upper endpoint to match G.
The printed strict endpoint is recorded as a QUESTION in PROGRESS.md. -/
noncomputable def envelopingPrimeProduct (w : ℕ) (z : ℝ) : ℕ :=
  ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), p

/-- Pages 14 to 15, membership in A_d, written on integer representatives. -/
def EnvelopingSifted (w d : ℕ) (m : ℤ) : Prop :=
  Squarefree d ∧ ∀ p ∈ d.primeFactors,
    w < p ∧ ((p : ℤ) ∣ m ∨ (p % 4 = 3 ∧ (p : ℤ) ∣ m - 1))

/-- Display 4.3 at z equal to M to the power one tenth.
Residue zero is transported from the endpoint M, as in Restriction.lean. -/
noncomputable def envelopingBeta (w : ℕ) (W b : ℤ) (M n : ℕ) : ℝ :=
  let z := (M : ℝ) ^ ((1 : ℝ) / 10)
  let t := if n = 0 then M else n
  envelopingG w 1 z *
    (∑ d ∈ (envelopingPrimeProduct w z).divisors.filter
      (fun d => EnvelopingSifted w d (W * t + b)), envelopingRho w d z) ^ 2

/-- Display 4.3 is nonnegative because G_1 and the square are nonnegative. -/
theorem envelopingBeta_nonneg (w : ℕ) (W b : ℤ) (M n : ℕ) :
    0 ≤ envelopingBeta w W b M n := by
  unfold envelopingBeta
  apply mul_nonneg _ (sq_nonneg _)
  unfold envelopingG
  apply sum_nonneg
  intro δ hδ
  unfold envelopingH
  split_ifs
  · apply prod_nonneg
    intro p hp
    positivity
  · exact le_rfl

/-- A logarithmic cap above every prime weight used at a smaller scale. -/
noncomputable def envelopingCap (M : ℕ) : ℝ := (1 + Real.log M) ^ ((3 : ℝ) / 2)

/-- The original sieve capped only to remove large values away from the prime support. -/
noncomputable def restrictionBeta (w : ℕ) (W b : ℤ) (M n : ℕ) : ℝ :=
  min (envelopingBeta w W b M n) (envelopingCap M)

/-- Uniform constants for the subpower growth of the cap. -/
noncomputable def envelopingGrowthConstant (ε : ℝ) : ℝ :=
  (1 + 1 / (ε * 2 / 3)) ^ ((3 : ℝ) / 2)

/-- The cap is nonnegative at every natural scale. -/
theorem envelopingCap_nonneg (M : ℕ) : 0 ≤ envelopingCap M :=
  Real.rpow_nonneg (by linarith [Real.log_natCast_nonneg M]) _

/-- The cap gives a nonnegative weight dominated by the original sieve. -/
theorem restrictionBeta_nonneg (w : ℕ) (W b : ℤ) (M n : ℕ) :
    0 ≤ restrictionBeta w W b M n :=
  le_min (envelopingBeta_nonneg w W b M n) (envelopingCap_nonneg M)

/-- The growth constant is positive for every positive exponent. -/
theorem envelopingGrowthConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < envelopingGrowthConstant ε := by
  apply Real.rpow_pos_of_pos
  positivity

/-- The logarithmic cap has a uniform subpower bound at every positive scale. -/
theorem envelopingCap_le_rpow {ε : ℝ} (hε : 0 < ε) {M : ℕ} (hM : 1 ≤ M) :
    envelopingCap M ≤ envelopingGrowthConstant ε * (M : ℝ) ^ ε := by
  let t := ε * 2 / 3
  have ht : 0 < t := by dsimp [t]; positivity
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le (by norm_num) hM1
  have hx : 1 ≤ (M : ℝ) ^ t := Real.one_le_rpow hM1 ht.le
  have hlog := Real.log_le_rpow_div hMp.le ht
  have hbase : 1 + Real.log M ≤ (1 + 1 / t) * (M : ℝ) ^ t := by
    calc 1 + Real.log M ≤ 1 + (M : ℝ) ^ t / t := by linarith
      _ ≤ (M : ℝ) ^ t + (M : ℝ) ^ t / t := by linarith
      _ = (1 + 1 / t) * (M : ℝ) ^ t := by ring
  calc envelopingCap M ≤ ((1 + 1 / t) * (M : ℝ) ^ t) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith [Real.log_natCast_nonneg M]) hbase (by norm_num)
    _ = envelopingGrowthConstant ε * (M : ℝ) ^ ε := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hMp.le _), ← Real.rpow_mul hMp.le]
      have he : t * ((3 : ℝ) / 2) = ε := by dsimp [t]; ring
      rw [he]
      rfl

/-- Every prime weight at L below M lies below the cap at M. -/
theorem fW_le_envelopingCap {W b : ℤ} (hW : 0 < W) {L M : ℕ}
    (hL : 1 ≤ L) (hLM : L ≤ M) (n : ℕ) : fW W b L n ≤ envelopingCap M := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hφ : (Nat.totient W.toNat : ℝ) ≤ W := by
    calc (Nat.totient W.toNat : ℝ) ≤ (W.toNat : ℝ) := by exact_mod_cast Nat.totient_le W.toNat
      _ = (W : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hW.le
  have hratio0 : 0 ≤ (Nat.totient W.toNat : ℝ) / W := div_nonneg (Nat.cast_nonneg _) hWr.le
  have hratio : (Nat.totient W.toNat : ℝ) / W ≤ 1 := (div_le_one hWr).mpr hφ
  have hratio' : ((Nat.totient W.toNat : ℝ) / W) ^ ((3 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one hratio0 hratio (by norm_num)
  have hlog : Real.log L ≤ 1 + Real.log M := by
    have hLr : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have h := Real.log_le_log hLr (show (L : ℝ) ≤ M by exact_mod_cast hLM)
    linarith
  unfold fW
  split_ifs
  · calc _ ≤ Real.log L ^ ((3 : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio' (Real.rpow_nonneg (Real.log_natCast_nonneg L) _)
      _ ≤ envelopingCap M := by
        simpa only [mul_one, envelopingCap] using Real.rpow_le_rpow (Real.log_natCast_nonneg L) hlog (by norm_num : (0 : ℝ) ≤ 3 / 2)
  · exact envelopingCap_nonneg M

/-- Proposition 4.1 iv and v for the uncapped sieve, on transported representatives. -/
def EnvelopingFourierExpansion (w : ℕ) (W b : ℤ) (M : ℕ) (D : ℝ → ℝ) : Prop :=
  ∃ v : ℕ → ℕ → ℂ,
    v 1 0 = 1 ∧
    (∀ q a : ℕ, (¬ Squarefree q ∨ (q : ℤ) ∣ W) → q ≠ 1 → v q a = 0) ∧
    (∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
      ‖v q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1)) ∧
    ∀ n < M, (envelopingBeta w W b M n : ℂ) =
      ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          v q a * eC (-((a : ℝ) * (if n = 0 then M else n) / q))

/-- The capped weight has uniform growth and the original sieve has Fourier decay.
This is the bounded majorant version of Proposition 4.1 used in the restriction leaf. -/
def EnvelopingFourierBounds (w : ℕ) (W b : ℤ) (M : ℕ)
    (A D : ℝ → ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ n < M,
    restrictionBeta w W b M n ≤ A ε * (M : ℝ) ^ ε) ∧
  EnvelopingFourierExpansion w W b M D

/-- Page 15, the local factors and their product are nonnegative. -/
theorem envelopingH_nonneg (w d : ℕ) : 0 ≤ envelopingH w d := by
  unfold envelopingH
  split_ifs
  · exact prod_nonneg (fun p _ => by positivity)
  · exact le_rfl

/-- Page 15, the sum G_d is nonnegative. -/
theorem envelopingG_nonneg (w d : ℕ) (z : ℝ) : 0 ≤ envelopingG w d z :=
  sum_nonneg (fun δ _ => envelopingH_nonneg w δ)

/-- Page 15, G_d is bounded by G_1 because its summation set is smaller. -/
theorem envelopingG_le (w d : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    envelopingG w d z ≤ envelopingG w 1 z := by
  unfold envelopingG
  apply sum_le_sum_of_subset_of_nonneg
  · intro δ hδ
    obtain ⟨hδ, _⟩ := mem_filter.mp hδ
    refine mem_filter.mpr ⟨hδ, ?_⟩
    simp only [Nat.lcm_one_left]
    exact (Nat.cast_le.mpr (mem_Icc.mp hδ).2).trans (Nat.floor_le hz)
  · intro δ _ _
    exact envelopingH_nonneg w δ

/-- Page 15, the term delta equal to one gives G_1 at least one. -/
theorem envelopingG_one_le (w : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    1 ≤ envelopingG w 1 z := by
  have hmem : 1 ∈ (Icc 1 ⌊z⌋₊).filter (fun δ => (Nat.lcm 1 δ : ℝ) ≤ z) := by
    simp only [mem_filter, mem_Icc, le_refl, Nat.lcm_one_left, Nat.cast_one, true_and]
    exact ⟨Nat.le_floor (by simpa only [Nat.cast_one] using hz), hz⟩
  have h := single_le_sum (fun δ _ => envelopingH_nonneg w δ) hmem
  change envelopingH w 1 ≤ envelopingG w 1 z at h
  simpa only [envelopingH, squarefree_one, ite_true, Nat.primeFactors_one, prod_empty] using h

/-- Page 16, the Selberg coefficients have absolute value at most one. -/
theorem envelopingRho_abs_le_one (w d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |envelopingRho w d z| ≤ 1 := by
  have hG : 0 < envelopingG w 1 z := lt_of_lt_of_le (by norm_num) (envelopingG_one_le w hz)
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  rw [envelopingRho, abs_div, abs_mul,
    abs_of_nonneg (envelopingG_nonneg w d z), abs_of_pos hG]
  apply (div_le_one hG).mpr
  calc |(ArithmeticFunction.moebius d : ℝ)| * envelopingG w d z
      ≤ 1 * envelopingG w d z := mul_le_mul_of_nonneg_right hμ (envelopingG_nonneg w d z)
    _ ≤ envelopingG w 1 z := by simpa using envelopingG_le w d (by linarith : 0 ≤ z)

/-- Display 4.4, the crude pointwise bound by the number of selected divisors. -/
theorem envelopingBeta_le_count (w : ℕ) (W b : ℤ) {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    envelopingBeta w W b M n ≤
      envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
        (((envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors.filter
          (fun d => EnvelopingSifted w d (W * (if n = 0 then M else n) + b))).card : ℝ) ^ 2 := by
  let z := (M : ℝ) ^ ((1 : ℝ) / 10)
  let S := (envelopingPrimeProduct w z).divisors.filter
    (fun d => EnvelopingSifted w d (W * (if n = 0 then M else n) + b))
  have hz : 1 ≤ z := Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hs : |∑ d ∈ S, envelopingRho w d z| ≤ (S.card : ℝ) := by
    calc |∑ d ∈ S, envelopingRho w d z|
        ≤ ∑ d ∈ S, |envelopingRho w d z| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ S, (1 : ℝ) := sum_le_sum (fun d _ => envelopingRho_abs_le_one w d hz)
      _ = (S.card : ℝ) := by simp
  have hsq := pow_le_pow_left₀ (abs_nonneg (∑ d ∈ S, envelopingRho w d z)) hs 2
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (envelopingG_nonneg w 1 z)

/-- Proposition 4.2 controls the mean by testing the constant sequence and frequency zero. -/
theorem mean_le_sq_of_restriction (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ)
    (hβ : ∀ n, 0 ≤ β n) {r C : ℝ} (hr : 2 < r) (hC : 0 ≤ C)
    (h42 : Restriction42 M β r C) :
    (M : ℝ)⁻¹ * ∑ n ∈ range M, β n ≤ C ^ 2 := by
  let m : ℝ := (M : ℝ)⁻¹ * ∑ n ∈ range M, β n
  have hm : 0 ≤ m := mul_nonneg (by positivity) (sum_nonneg (fun n _ => hβ n))
  have hzero : fhat M β 0 = (m : ℂ) := by
    simp only [fhat, Nat.cast_zero, zero_mul, zero_div, neg_zero, eC,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    dsimp [m]
    push_cast
    rfl
  have hterm : m ^ r ≤ ∑ ξ ∈ range M, ‖fhat M β ξ‖ ^ r := by
    have h := single_le_sum (fun ξ (_ : ξ ∈ range M) => Real.rpow_nonneg (norm_nonneg (fhat M β ξ)) r)
      (mem_range.mpr (by omega : 0 < M))
    simpa only [hzero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm] using h
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hm r) hterm (by positivity : 0 ≤ 1 / r)
  rw [← Real.rpow_mul hm, mul_one_div_cancel (by linarith : r ≠ 0), Real.rpow_one] at hroot
  have h42' := h42 (fun _ => 1)
  have htransform : (fun n => (1 : ℂ) * (β n : ℂ)) = (fun n => (β n : ℂ)) := by simp
  rw [htransform] at h42'
  change (∑ ξ ∈ range M, ‖fhat M β ξ‖ ^ r) ^ (1 / r) ≤ _ at h42'
  simp only [norm_one, one_pow, one_mul] at h42'
  have hmle : m ≤ C * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow]
    exact hroot.trans h42'
  have hs : Real.sqrt m ≤ C := by
    by_contra h
    have hlt : C < Real.sqrt m := lt_of_not_ge h
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg m]
  calc m = (Real.sqrt m) ^ 2 := (Real.sq_sqrt hm).symm
    _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg m) hs 2

/-- Display 4.3 has the constant value one at scale one. -/
theorem envelopingBeta_one (w : ℕ) (W b : ℤ) (n : ℕ) :
    envelopingBeta w W b 1 n = 1 := by
  have hP : envelopingPrimeProduct w 1 = 1 := by
    simp [envelopingPrimeProduct, range_add_one]
  have hG : envelopingG w 1 1 = 1 := by
    simp [envelopingG, envelopingH, filter_singleton]
  have hS : ∀ m : ℤ, EnvelopingSifted w 1 m := by
    intro m
    simp [EnvelopingSifted]
  simp [envelopingBeta, Nat.cast_one, Real.one_rpow, hP, Nat.divisors_one,
    filter_singleton, hS, ite_true, sum_singleton, envelopingRho, hG,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, mul_one, div_one, one_pow]


/-- The capped majorant is also one at scale one. -/
theorem restrictionBeta_one (w : ℕ) (W b : ℤ) (n : ℕ) :
    restrictionBeta w W b 1 n = 1 := by
  simp [restrictionBeta, envelopingBeta_one, envelopingCap]

/-- A nonvacuous Fourier certificate at scale one. -/
theorem envelopingFourierBounds_one (w : ℕ) (W b : ℤ) :
    EnvelopingFourierBounds w W b 1 (fun _ => 1) (fun _ => 1) := by
  refine ⟨?_, (fun q _ => if q = 1 then 1 else 0), ?_, ?_, ?_, ?_⟩
  · intro ε hε n hn
    simp [restrictionBeta, envelopingCap, envelopingBeta_one]
  · simp
  · intro q a _ hq
    simp [hq]
  · intro ε hε q hq a ha hcop
    by_cases hq1 : q = 1
    · simp [hq1]
    · simpa [hq1] using Real.rpow_nonneg (Nat.cast_nonneg q) (ε - 1)
  · intro n hn
    norm_num [envelopingBeta_one, eC]

/-- Proposition 4.2 has a nonzero weight instance at scale one. -/
theorem enveloping_restriction_one (w : ℕ) (W b : ℤ) :
    Restriction42 1 (restrictionBeta w W b 1) 3 1 := by
  intro a
  simp only [complexFhat, restrictionBeta_one, Nat.cast_one, inv_one,
    range_one, sum_singleton, mul_one, Nat.cast_zero, zero_mul, zero_div,
    neg_zero, eC, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.ofReal_one, norm_one, one_pow]
  rw [← Real.rpow_mul (norm_nonneg _)]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq]
  exact norm_nonneg _


/-- Page 15, the sieve equals G_1 whenever every sieving prime is avoided. -/
theorem envelopingBeta_eq_G_of_rough (w : ℕ) (W b : ℤ) {M : ℕ} (hM : 1 ≤ M) (n : ℕ)
    (hrough : ∀ p ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).primeFactors,
      ¬ (p : ℤ) ∣ W * (if n = 0 then M else n) + b ∧
      (p % 4 = 3 → ¬ (p : ℤ) ∣ W * (if n = 0 then M else n) + b - 1)) :
    envelopingBeta w W b M n = envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  let z := (M : ℝ) ^ ((1 : ℝ) / 10)
  let P := envelopingPrimeProduct w z
  let m : ℤ := W * (if n = 0 then M else n) + b
  let S := P.divisors.filter (fun d => EnvelopingSifted w d m)
  have hP : P ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact (mem_filter.mp hp).2.1.ne_zero
  have hd1 : ∀ d ∈ S, d = 1 := by
    intro d hd
    obtain ⟨hdP, hsift⟩ := mem_filter.mp hd
    have hdiv : d ∣ P := Nat.dvd_of_mem_divisors hdP
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz, zero_dvd_iff] at hdiv
      exact hP hdiv
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpP := hp.mem_primeFactors (hpd.trans hdiv) hP
    have hpd' := hp.mem_primeFactors hpd hd0
    have hbad := (hsift.2 p hpd').2
    rcases hbad with hbad | ⟨hp3, hbad⟩
    · exact (hrough p hpP).1 hbad
    · exact (hrough p hpP).2 hp3 hbad
  have hS : S = {1} := by
    ext d
    constructor
    · intro hd
      exact mem_singleton.mpr (hd1 d hd)
    · intro hd
      have hd' : d = 1 := mem_singleton.mp hd
      subst d
      exact mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hP, by simp [EnvelopingSifted]⟩
  have hz : 1 ≤ z := Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hG : envelopingG w 1 z ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (envelopingG_one_le w hz))
  change envelopingG w 1 z * (∑ d ∈ S, envelopingRho w d z) ^ 2 = envelopingG w 1 z
  rw [hS, sum_singleton, envelopingRho, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    one_mul, div_self hG, one_pow, mul_one]

/-- Page 15, a number in S has no prime factor three modulo four above three. -/
theorem sSet_no_sieving_prime {s : ℤ} (hs : s ∈ SSet) {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 3) (hp3 : 3 < p) : ¬ (p : ℤ) ∣ s := by
  obtain ⟨x, y, hxy, k, hk⟩ := hs
  intro hd
  rw [hxy] at hd
  letI : Fact p.Prime := ⟨hp⟩
  have hmod : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 + y ^ 2) p).mpr hd
    push_cast at h
    exact h
  have hx : (x : ZMod p) = 0 := by
    by_contra hx
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq (x := (x : ZMod p)) (y := (y : ZMod p)) hx (by linear_combination hmod)) hp4
  have hy : (y : ZMod p) = 0 := by
    have hsq : (y : ZMod p) ^ 2 = 0 := by simpa only [hx, zero_pow (by decide : 2 ≠ 0), zero_add] using hmod
    exact sq_eq_zero_iff.mp hsq
  have hx' : (p : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx
  have hy' : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy
  have hgcd := Int.dvd_gcd hx' hy'
  have hgcd' : (p : ℤ) ∣ (Int.gcd x y : ℤ) := by exact_mod_cast hgcd
  have hp6 : (p : ℤ) ∣ 6 := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (hgcd'.trans hk)
  have hp6' : p ∣ 2 * 3 := by exact_mod_cast hp6
  rcases hp.dvd_mul.mp hp6' with h | h
  · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega

/-- Page 15, every prime factor of P of z is above w and at most z. -/
theorem envelopingPrimeProduct_factor {w p : ℕ} {z : ℝ}
    (hp : p ∈ (envelopingPrimeProduct w z).primeFactors) : w < p ∧ (p : ℝ) ≤ z := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  unfold envelopingPrimeProduct at hdiv
  have hdiv' : (p : ℤ) ∣
      ∏ q ∈ (range (⌊z⌋₊ + 1)).filter (fun q => q.Prime ∧ w < q ∧ (q : ℝ) ≤ z), (q : ℤ) := by
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨d, ?_⟩
    simpa only [Nat.cast_prod, Nat.cast_mul] using congrArg (fun x : ℕ => (x : ℤ)) hd
  have hmem := prime_dvd_prod (fun q hq => (mem_filter.mp hq).2.1) hprime hdiv'
  exact (mem_filter.mp hmem).2.2

/-- Page 15, Good values above the sieve level lie on the sieve plateau. -/
theorem good_enveloping_plateau {w M n : ℕ} {W b : ℤ} (hM : 1 ≤ M) (hw : 3 ≤ w)
    (hn : n ≠ 0) (hg : Good (W * n + b))
    (hsize : (M : ℝ) ^ ((1 : ℝ) / 10) < (W * n + b : ℤ)) :
    envelopingBeta w W b M n = envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  apply envelopingBeta_eq_G_of_rough w W b hM n
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨hpw, hpz⟩ := envelopingPrimeProduct_factor hp
  have hlt : (p : ℤ) < W * n + b := by exact_mod_cast (hpz.trans_lt hsize)
  simp only [if_neg hn]
  constructor
  · intro hd
    have hcast : ((W * n + b).toNat : ℤ) = W * n + b := Int.toNat_of_nonneg hg.1.le
    have hd' : p ∣ (W * n + b).toNat := Int.natCast_dvd_natCast.mp (by rwa [hcast])
    have he := (Nat.prime_dvd_prime_iff_eq hprime hg.2.1).mp hd'
    omega
  · intro hp4
    exact sSet_no_sieving_prime hg.2.2 hprime hp4 (by omega)

/-- Page 15, every supported affine value exceeds the sieve level at the changed scale. -/
theorem cross_scale_sieving_level_lt {W b : ℤ} {L M n : ℕ}
    (hW : 6 ≤ W) (hb : 0 ≤ b) (hL : 1 ≤ L) (hLM : L ≤ M) (hML : M ≤ 2 * L)
    (hn : (L : ℝ) / 3 < n) :
    (M : ℝ) ^ ((1 : ℝ) / 10) < (W * n + b : ℤ) := by
  have hLn : L < 3 * n := by exact_mod_cast (by linarith : (L : ℝ) < 3 * n)
  have hMn : M < 6 * n := by omega
  have hsize : (M : ℤ) < W * n + b := by
    have hMn' : (M : ℤ) < 6 * n := by exact_mod_cast hMn
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (hL.trans hLM)
  have hz : (M : ℝ) ^ ((1 : ℝ) / 10) ≤ M := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num : (1 : ℝ) / 10 ≤ 1))
  exact hz.trans_lt (by exact_mod_cast hsize)

/-- Page 15, a unit lower bound for G_1 alone cannot control the logarithmic normalization. -/
theorem normalization_unit_bound_obstruction {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ x : ℝ, 1 ≤ x ∧ c < a * Real.log x ^ ((3 : ℝ) / 2) := by
  let y := max (c / a) 1 + 1
  have hy1 : 1 ≤ y := by dsimp [y]; linarith [le_max_right (c / a) 1]
  have hcy : c / a < y := by dsimp [y]; linarith [le_max_left (c / a) 1]
  have hcy' : c < a * y := by
    have h := (div_lt_iff₀ ha).mp hcy
    nlinarith
  refine ⟨Real.exp y, (Real.one_le_exp_iff).mpr (by linarith), ?_⟩
  rw [Real.log_exp]
  have hyp : y ≤ y ^ ((3 : ℝ) / 2) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num : (1 : ℝ) ≤ 3 / 2))
  exact hcy'.trans_le (mul_le_mul_of_nonneg_left hyp ha.le)

/-- LEAF. Page 15, the lower bound for G_1 after display 4.3, and display 3.4.
Reconstructed uniform normalization comparison, including small positive scales.
It contains the remaining Mertens product estimate in the domination step. -/
theorem paper_enveloping_normalization_input :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L →
        Real.log L ^ ((3 : ℝ) / 2) *
          ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) ≤
            c * envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  sorry

/-- LEAF. Proposition 4.1 i, pages 13 to 15, and the comparison on page 14.
CONDITIONAL ON the uniform normalization leaf.
The prime avoidance and sieve plateau steps are proved below. -/
theorem paper_enveloping_domination_input :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L → ∀ n < M,
        fW (WW J w) b L n ≤ c * restrictionBeta w (WW J w) b M n := by
  obtain ⟨c, hc, H⟩ := paper_enveloping_normalization_input
  refine ⟨max c 1, lt_of_lt_of_le hc (le_max_left c 1), ?_⟩
  intro J w hJ hw b hb hbW hamen L M hL hLM hML n hn
  have hraw : fW (WW J w) b L n ≤ c * envelopingBeta w (WW J w) b M n := by
    by_cases hf : fW (WW J w) b L n = 0
    · rw [hf]
      exact mul_nonneg hc.le (envelopingBeta_nonneg w (WW J w) b M n)
    · obtain hgood := fW_ne_zero hf
      have hn0 : n ≠ 0 := by
        intro hz
        simp only [hz, Nat.cast_zero] at hgood
        have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        linarith [hgood.1]
      have hW0 : 0 < WW J w := lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hamen.1
      have hW216 : (216 : ℤ) ≤ WW J w := Int.le_of_dvd hW0 (by simpa using hamen.2.1)
      have hwBig : (3 : ℝ) ≤ wBig := by
        calc (3 : ℝ) ≤ 10 := by norm_num
          _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (Real.one_le_rpow (by norm_num) (by positivity))
      have hw3 : 3 ≤ w := by exact_mod_cast (hwBig.trans hw)
      have hsize := cross_scale_sieving_level_lt (by omega : (6 : ℤ) ≤ WW J w) hb hL hLM hML hgood.1
      rw [good_enveloping_plateau (hL.trans hLM) hw3 hn0 hgood.2.2 hsize]
      simpa only [fW, if_pos hgood] using H J w hJ hw L M hL hLM hML
  have hW : 0 < WW J w := lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hamen.1
  have hleft : fW (WW J w) b L n ≤ max c 1 * envelopingBeta w (WW J w) b M n :=
    hraw.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (envelopingBeta_nonneg w (WW J w) b M n))
  have hright : fW (WW J w) b L n ≤ max c 1 * envelopingCap M := by
    apply (fW_le_envelopingCap hW hL hLM n).trans
    have h := mul_le_mul_of_nonneg_right (le_max_right c 1) (envelopingCap_nonneg M)
    simpa only [one_mul] using h
  change fW (WW J w) b L n ≤ max c 1 * min _ _
  rw [mul_min_of_nonneg _ _ (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right c 1))]
  exact le_min hleft hright

/-- LEAF. Proposition 4.1 iv and v, pages 13 and 16 to 17, display 4.1.
Only the uncapped rational Fourier expansion and its uniform decay remain cited. -/
theorem paper_enveloping_fourier_decay_input :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierExpansion w (WW J w) b M D := by
  sorry

/-- The combined certificate is CONDITIONAL ON the Fourier decay leaf.
The uniform growth of the capped weight is proved. -/
theorem paper_enveloping_fourier_input :
    ∃ A D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D := by
  obtain ⟨D, hD, H⟩ := paper_enveloping_fourier_decay_input
  refine ⟨envelopingGrowthConstant, D, fun ε hε => ⟨envelopingGrowthConstant_pos hε, hD ε hε⟩, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  refine ⟨?_, H J w hJ hw b hb hbW hamen M hM⟩
  intro ε hε n hn
  exact (min_le_right _ _).trans (envelopingCap_le_rpow hε hM)

/-- LEAF. Proposition 4.2, pages 13 to 14, citing Green Tao Proposition 4.2.
The capped weight is bounded above by the original Fourier majorant.
Reconstructed bounded shift form of the Green Tao argument: use the cap for large
frequency sets and the uncapped Fourier majorant for small frequency sets. -/
theorem paper_enveloping_restriction_input (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ r : ℝ, 2 < r → ∃ C : ℝ, 0 < C ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          Restriction42 M (restrictionBeta w (WW J w) b M) r C := by
  sorry

/-- Proposition 4.1 ii, page 13. CONDITIONAL ON the Fourier and restriction leaves.
The constant sequence in Proposition 4.2 gives the required uniform mean. -/
theorem paper_enveloping_mean_input :
    ∃ κ : ℝ, 0 < κ ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
        (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n ≤ κ := by
  obtain ⟨A, D, hAD, hfourier⟩ := paper_enveloping_fourier_input
  obtain ⟨C, hC, H⟩ := paper_enveloping_restriction_input A D hAD 3 (by norm_num)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM
  exact mean_le_sq_of_restriction M hM (restrictionBeta w (WW J w) b M)
    (restrictionBeta_nonneg w (WW J w) b M) (by norm_num : (2 : ℝ) < 3) hC.le
    (H J w hJ hw b hb hbW hamen M hM (hfourier J w hJ hw b hb hbW hamen M hM))

/-- Page 14, a uniform first moment for the prime weight.
CONDITIONAL ON the normalization, Fourier decay and capped restriction leaves. -/
theorem paper_prime_weight_mass_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ N : ℕ, 1 ≤ N →
        ∑ n ∈ range N, fW (WW J w) b N n ≤ K * N := by
  obtain ⟨c, hc, hdom⟩ := paper_enveloping_domination_input
  obtain ⟨κ, hκ, hmean⟩ := paper_enveloping_mean_input
  refine ⟨c * κ, mul_pos hc hκ, ?_⟩
  intro J w hJ hw b hb hbW hamen N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm := hmean J w hJ hw b hb hbW hamen N hN
  rw [← div_eq_inv_mul] at hm
  have hm' := (div_le_iff₀ hNr).mp hm
  calc ∑ n ∈ range N, fW (WW J w) b N n
      ≤ ∑ n ∈ range N, c * restrictionBeta w (WW J w) b N n := by
        apply sum_le_sum
        intro n hn
        exact hdom J w hJ hw b hb hbW hamen N N hN le_rfl (by omega) n (mem_range.mp hn)
    _ = c * ∑ n ∈ range N, restrictionBeta w (WW J w) b N n := (mul_sum _ _ _).symm
    _ ≤ c * (κ * N) := mul_le_mul_of_nonneg_left hm' hc.le
    _ = c * κ * N := by ring

#print axioms paper_prime_weight_mass_bound

/-- Page 14, the elementary quotient deduction with all analytic inputs explicit. -/
theorem cross_scale_of_enveloping (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (hdom : ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L → ∀ n < M,
        fW (WW J w) b L n ≤ c * restrictionBeta w (WW J w) b M n)
    (hmean : ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
        (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n ≤ κ)
    (hres : ∀ r : ℝ, 2 < r → ∃ C : ℝ, 0 < C ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          Restriction42 M (restrictionBeta w (WW J w) b M) r C) : Prop33Cross := by
  intro r hr
  obtain ⟨C, hC, H⟩ := hres r hr
  refine ⟨(C * (c ^ 2 * κ) ^ ((1 : ℝ) / 2)) ^ r, ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (mul_pos hC (Real.rpow_pos_of_pos (by positivity) _)) _
  · intro J w hJ hw b hb hbW hamen L M hL hLM hML g hg hgf
    exact restriction_dominated_moment M g (restrictionBeta w (WW J w) b M) hr
      (restrictionBeta_nonneg w (WW J w) b M) hg hc.le hC.le
      (fun n hn => (hgf n hn).trans (hdom J w hJ hw b hb hbW hamen L M hL hLM hML n hn))
      (hmean J w hJ hw b hb hbW hamen M (hL.trans hLM))
      (H J w hJ hw b hb hbW hamen M (hL.trans hLM))

#print axioms paper_enveloping_fourier_decay_input
#print axioms restrictionBeta_one
#print axioms envelopingCap_nonneg
#print axioms restrictionBeta_nonneg
#print axioms envelopingGrowthConstant_pos
#print axioms envelopingCap_le_rpow
#print axioms fW_le_envelopingCap
#print axioms normalization_unit_bound_obstruction
#print axioms cross_scale_sieving_level_lt
#print axioms paper_enveloping_normalization_input
#print axioms sSet_no_sieving_prime
#print axioms envelopingPrimeProduct_factor
#print axioms good_enveloping_plateau
#print axioms envelopingBeta_eq_G_of_rough
#print axioms envelopingBeta_le_count
#print axioms envelopingBeta_one
#print axioms envelopingFourierBounds_one
#print axioms enveloping_restriction_one
#print axioms envelopingH_nonneg
#print axioms envelopingG_nonneg
#print axioms envelopingG_le
#print axioms envelopingG_one_le
#print axioms envelopingRho_abs_le_one
#print axioms mean_le_sq_of_restriction
#print axioms envelopingBeta_nonneg
#print axioms cross_scale_of_enveloping
#print axioms paper_enveloping_domination_input
#print axioms paper_enveloping_mean_input
#print axioms paper_enveloping_fourier_input
#print axioms paper_enveloping_restriction_input

example : envelopingBeta 5 1 10 1 1 = envelopingG 5 1 1 := by
  have hg : Good (11 : ℤ) := ⟨by norm_num, by norm_num, 1, 3, by norm_num, 0, by norm_num⟩
  simpa only [Nat.cast_one, Real.one_rpow] using
    good_enveloping_plateau (w := 5) (W := 1) (b := 10) (M := 1) (n := 1)
      (by decide) (by decide) (by decide) (by simpa using hg) (by norm_num)

example : envelopingG 5 1 7 = (7 : ℝ) / 5 := by
  have hset : (Icc 1 7 : Finset ℕ) = {1, 2, 3, 4, 5, 6, 7} := by decide
  have h4 : ¬ Squarefree (4 : ℕ) := by decide
  have h6 : Squarefree (6 : ℕ) := by
    change Squarefree (2 * 3 : ℕ)
    exact Nat.squarefree_mul_iff.mpr ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have h7 : Squarefree (7 : ℕ) := (by decide : Nat.Prime 7).squarefree
  have hp6 : (6 : ℕ).primeFactors = {2, 3} := by
    change (2 * 3 : ℕ).primeFactors = {2, 3}
    rw [Nat.primeFactors_mul (by decide) (by decide), Nat.prime_two.primeFactors,
      Nat.prime_three.primeFactors]
    decide
  have hp7 : (7 : ℕ).primeFactors = {7} := (by decide : Nat.Prime 7).primeFactors
  norm_num [envelopingG, hset, envelopingH, envelopingOmega, filter_insert,
    filter_singleton, h4, h6, h7, hp6, hp7]

example : (∏ p ∈ (range 8).filter (fun p => p.Prime ∧ 5 < p ∧ p < 7), p) = 1 := by decide

example : envelopingPrimeProduct 5 7 = 7 := by
  norm_num [envelopingPrimeProduct, prod_filter, prod_range_succ]

end LeanLab.Teravainen2016

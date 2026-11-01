/-
P0087 Akeno 2026 Theorem 2.1, pages 4 to 6, equations 2 to 8.
The printed D/q estimate implies the sealed D squared over q estimate.
The final assembly is CONDITIONAL ON the named analytic leaves below.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.ExpSumPrinted
import LeanLab.Akeno2026.DiophantineBlocks
import LeanLab.Akeno2026.Vaughan86
import LeanLab.Akeno2026.Cauchy86
import LeanLab.Akeno2026.Balance86
import LeanLab.Akeno2026.Phase86
import LeanLab.Akeno2026.Correlation86
import LeanLab.Akeno2026.Localization86
import LeanLab.Akeno2026.Kernel86
import LeanLab.Akeno2026.Weight86
import LeanLab.Akeno2026.VaughanCoeffs86

namespace LeanLab.Akeno2026.Decomp86
open Real Finset
open scoped ContDiff

/-- The smooth exponential sum in Lemma 2.2, specialized to support in the unit interval. -/
noncomputable def smoothSum (w : ℝ → ℝ) (X α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (0 : ℤ) ⌊X⌋, e (α * n) * (w ((n : ℝ) / X) : ℂ)

/-- The integer count in equation 3. -/
noncomputable def nearCount (α ρ : ℝ) : ℕ :=
  (Finset.Icc ⌈α - ρ⌉ ⌊α + ρ⌋).card

/-- Lemma 2.2 equation 3 for weights supported on the unit interval. -/
def Localization22 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w →
    Function.support w ⊆ Set.Icc 0 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X α : ℝ, 1 ≤ X →
      ‖smoothSum w X α‖ ≤ C *
        (X * nearCount α (X ^ (ε - 1)) + X ^ (-(100 : ℝ)))

/-- The count in Lemma 2.4 equation 6, with b running from 1 to d. -/
noncomputable def count24 (α D N δ : ℝ) : ℕ :=
  ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.Icc 1 d,
    DiophantineCount.pairCount (-(α + (b : ℝ) / d)) N δ

/-- Lemma 2.4 equation 6 with all scale and rational approximation hypotheses explicit. -/
def Counting24 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ X D N α δ : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X →
      0 ≤ α → α ≤ 1 → 0 < δ →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
        |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
        (count24 α D N δ : ℝ) ≤
          C * X ^ ε * N * D * (1 / (q : ℝ) + q * δ + δ * N * D)

/-- The Type I bilinear sum on page 5. -/
noncomputable def typeISum (w : ℝ → ℝ) (A : ℕ → ℂ) (X M β : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
    A m * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)

/-- The Type II bilinear sum on pages 5 to 6. -/
noncomputable def typeIISum (w : ℝ → ℝ) (A B : ℕ → ℂ) (X M N β : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    A m * B n * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)

/-- The outer mean square used in equations 2, 7 and 8. -/
noncomputable def energy (F : ℝ → ℂ) (D α : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
    ‖F (α + (b : ℝ) / d)‖ ^ 2

/-- The Type I estimate of equation 7, normalized coefficients of norm at most one. -/
def TypeI7 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w →
    Function.support w ⊆ Set.Icc 0 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X D M α : ℝ,
      1 ≤ X → 0 < D → D ≤ X → 0 < M → M ≤ X → 0 ≤ α → α ≤ 1 →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
        |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
        ∀ A : ℕ → ℂ, (∀ m, ‖A m‖ ≤ 1) →
          energy (typeISum w A X M) D α ≤
            C * X ^ (2 + 2 * ε) * (D / q + q * D / X + M * D ^ 2 / X)

/-- The Type II estimate of equation 8 with explicit fixed comparability constants. -/
def TypeII8 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w →
    Function.support w ⊆ Set.Icc 0 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X D M N α : ℝ,
      1 ≤ X → 0 < D → D ≤ X → 0 < M → M ≤ X → 0 < N → N ≤ X →
      X / 4 ≤ M * N → M * N ≤ 4 * X → 0 ≤ α → α ≤ 1 →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
        |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
        ∀ A B : ℕ → ℂ, (∀ m, ‖A m‖ ≤ 1) → (∀ n, ‖B n‖ ≤ 1) →
          energy (typeIISum w A B X M N) D α ≤
            C * X ^ (2 + 2 * ε) *
              (D / q + q * D / X + M * D ^ 2 / X + N * D ^ 2 / X)

/-- Page 6 Type I count, reflection identifies near integers with rational numerators. -/
theorem nearCount_eq_numerator (β δ : ℝ) (m : ℤ) :
    nearCount (β * m) ((m : ℝ) * δ) =
      (DiophantineCount.numeratorRange (-β) δ m).card := by
  have hlo : (m : ℝ) * (-β - δ) = -(β * m + (m : ℝ) * δ) := by ring
  have hhi : (m : ℝ) * (-β + δ) = -(β * m - (m : ℝ) * δ) := by ring
  simp only [nearCount, DiophantineCount.numeratorRange, hlo, hhi,
    Int.ceil_neg, Int.floor_neg, Int.card_Icc]
  congr 1
  omega

/-- Page 6 residue convention, the rational numerator count is periodic by integers. -/
theorem pairCount_add_int (β M δ : ℝ) (z : ℤ) :
    DiophantineCount.pairCount (β + z) M δ =
      DiophantineCount.pairCount β M δ := by
  unfold DiophantineCount.pairCount
  apply Finset.sum_congr rfl
  intro m hm
  have hlo : (m : ℝ) * (β + z - δ) = (m : ℝ) * (β - δ) + (m * z : ℤ) := by
    push_cast
    ring
  have hhi : (m : ℝ) * (β + z + δ) = (m : ℝ) * (β + δ) + (m * z : ℤ) := by
    push_cast
    ring
  simp only [DiophantineCount.numeratorRange, hlo, hhi,
    Int.ceil_add_intCast, Int.floor_add_intCast, Int.card_Icc]
  congr 1
  omega

/-- Page 6 Type I count, the natural dyadic sum equals the integer denominator count. -/
theorem sum_nearCount_eq_pairCount (β δ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      nearCount (β * m) ((m : ℝ) * δ)) =
      DiophantineCount.pairCount (-β) M δ := by
  unfold DiophantineCount.pairCount
  apply Finset.sum_bij (fun (m : ℕ) (_ : m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊) => (m : ℤ))
  · intro m hm
    apply DiophantineCount.mem_denominatorRange.mpr
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hm
    exact ⟨(Nat.floor_lt hM).mp hlo, (Nat.le_floor_iff (by positivity)).mp hhi⟩
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro m hm
    obtain ⟨hlo, hhi⟩ := DiophantineCount.mem_denominatorRange.mp hm
    have hm0 : 0 ≤ m := by exact_mod_cast (hM.trans hlo.le)
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
    have hr : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast he
    refine ⟨m.toNat, Finset.mem_Ioc.mpr ?_, he⟩
    constructor
    · exact (Nat.floor_lt hM).mpr (hr ▸ hlo)
    · exact Nat.le_floor (hr ▸ hhi)
  · intro m hm
    simpa only [Int.cast_natCast] using nearCount_eq_numerator β δ (m : ℤ)

/-- Page 6 Type I count, enlarging the near integer radius only increases its cardinality. -/
theorem nearCount_mono (β : ℝ) {r s : ℝ} (hrs : r ≤ s) :
    nearCount β r ≤ nearCount β s := by
  apply Finset.card_le_card
  apply Finset.Icc_subset_Icc
  · exact Int.ceil_mono (by linarith)
  · exact Int.floor_mono (by linarith)

/-- Pages 5 to 6, the residue representatives zero through d minus one give the same count. -/
theorem count24_residue_convention (α D N δ : ℝ) :
    (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
      DiophantineCount.pairCount (-(α + (b : ℝ) / d)) N δ) = count24 α D N δ := by
  unfold count24
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by have hh := (Finset.mem_Ioc.mp hd).1; omega
  apply Finset.sum_bij (fun (b : ℕ) (_ : b ∈ Finset.range d) => if b = 0 then d else b)
  · intro b hb
    have hb' := Finset.mem_range.mp hb
    by_cases hz : b = 0 <;> simp only [hz, ite_true, ite_false, Finset.mem_Icc] <;> omega
  · intro b hb c hc he
    have hb' := Finset.mem_range.mp hb
    have hc' := Finset.mem_range.mp hc
    split_ifs at he <;> omega
  · intro b hb
    obtain ⟨hb1, hbd⟩ := Finset.mem_Icc.mp hb
    by_cases he : b = d
    · refine ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hd0), ?_⟩
      simp [he]
    · refine ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
      simp [show b ≠ 0 by omega]
  · intro b hb
    by_cases hz : b = 0
    · subst b
      simp only [ite_true, Nat.cast_zero, zero_div, add_zero,
        div_self (show (d : ℝ) ≠ 0 by exact_mod_cast hd0)]
      have hh := pairCount_add_int (-α) N δ (-1)
      convert hh.symm using 1 <;> push_cast <;> congr 1 <;> ring
    · simp only [hz, ite_false]

/-- Page 6 Type I count after rescaling, reflection and a change of residue convention. -/
theorem typeI_near_count (α D δ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
        nearCount ((α + (b : ℝ) / d) * m) ((m : ℝ) * δ)) = count24 α D M δ := by
  simp_rw [sum_nearCount_eq_pairCount _ _ hM]
  exact count24_residue_convention α D M δ

/-- Page 5 coefficient input, the divisor count is bounded by every positive power. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- Page 5 coefficient input, the long Mobius convolution has a uniform positive power bound. -/
theorem long_mu_zeta_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ) (n : ℕ),
      |(((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        Vaughan86.shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n| ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := card_divisors_le_rpow hε
  exact ⟨C, hC, fun U n => (VaughanCoeffs86.long_mu_zeta_bound U n).trans (hb n)⟩

/-- Page 4 Poisson bound with a free cutoff and decay order for the page 6 Type I sum. -/
theorem smoothSum_cutoff (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y α T : ℝ, 1 ≤ Y → 1 ≤ T →
      ‖smoothSum w Y α‖ ≤ C * Y * (nearCount α (T / Y) + 1 / T ^ k) := by
  obtain ⟨C, hC, hdec⟩ := Localization86.weightFourier_decay w hw hs (k + 2)
  obtain ⟨S, hS, hK⟩ := Kernel86.uniform_shifted_kernel
  refine ⟨C * S, mul_pos hC hS, ?_⟩
  intro Y α T hY hT
  have hY0 : 0 < Y := by linarith
  let K : ℤ → ℝ := fun n => 1 / (1 + |(n : ℝ) - α|) ^ 2
  let F : ℤ → ℂ := fun n => (Y : ℂ) * Localization86.weightFourier w (Y * ((n : ℝ) - α))
  let den : ℤ → ℝ := fun n => 1 + Y * |(n : ℝ) - α|
  have hkSum : Summable K := (hK α).1
  have hkBound : (∑' n : ℤ, K n) ≤ S := (hK α).2
  have hden (n : ℤ) : 1 + |(n : ℝ) - α| ≤ den n := by
    have hh := mul_le_mul_of_nonneg_right hY (abs_nonneg ((n : ℝ) - α))
    dsimp [den]
    linarith
  have hbound (R : ℝ) (hR : 0 < R) (hfreq : ∀ n : ℤ, R ≤ den n) :
      ‖smoothSum w Y α‖ ≤ (C * S) * Y / R ^ k := by
    have hmajor (n : ℤ) : ‖F n‖ ≤ (Y * C / R ^ k) * K n := by
      have hp : R ^ k * (1 + |(n : ℝ) - α|) ^ 2 ≤ den n ^ (k + 2) := by
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ hR.le (hfreq n) k)
          (pow_le_pow_left₀ (by positivity) (hden n) 2) (by positivity)
          (pow_nonneg (hR.le.trans (hfreq n)) k)
      have hdec' : den n ^ (k + 2) *
          ‖Localization86.weightFourier w (Y * ((n : ℝ) - α))‖ ≤ C := by
        simpa only [den, abs_mul, abs_of_pos hY0] using hdec (Y * ((n : ℝ) - α))
      have hh := (mul_le_mul_of_nonneg_right hp
        (norm_nonneg (Localization86.weightFourier w (Y * ((n : ℝ) - α))))).trans hdec'
      have hv : ‖Localization86.weightFourier w (Y * ((n : ℝ) - α))‖ ≤
          C / (R ^ k * (1 + |(n : ℝ) - α|) ^ 2) := by
        apply (le_div_iff₀ (by positivity)).mpr
        simpa only [mul_comm] using hh
      have hn : ‖F n‖ = Y *
          ‖Localization86.weightFourier w (Y * ((n : ℝ) - α))‖ := by
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0]
      rw [hn]
      apply (mul_le_mul_of_nonneg_left hv hY0.le).trans_eq
      dsimp [K]
      field_simp
    have hns : Summable (fun n : ℤ => ‖F n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor (hkSum.mul_left _)
    rw [show smoothSum w Y α = ∑' n : ℤ, F n from Localization86.poisson_scaled w hw hs Y hY0 α]
    calc
      _ ≤ ∑' n : ℤ, ‖F n‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n : ℤ, (Y * C / R ^ k) * K n :=
        Summable.tsum_le_tsum hmajor hns (hkSum.mul_left _)
      _ = (Y * C / R ^ k) * ∑' n : ℤ, K n := tsum_mul_left
      _ ≤ (Y * C / R ^ k) * S := mul_le_mul_of_nonneg_left hkBound (by positivity)
      _ = _ := by ring
  by_cases hz : nearCount α (T / Y) = 0
  · have hfar (n : ℤ) : T / Y < |(n : ℝ) - α| := by
      by_contra! hh
      have hb := abs_le.mp hh
      have hm : n ∈ Finset.Icc ⌈α - T / Y⌉ ⌊α + T / Y⌋ := by
        simp only [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
        constructor <;> linarith
      have he : Finset.Icc ⌈α - T / Y⌉ ⌊α + T / Y⌋ = ∅ := Finset.card_eq_zero.mp hz
      rw [he] at hm
      exact Finset.notMem_empty n hm
    have hh := hbound T (by linarith) (fun n => by
      have hn := (div_lt_iff₀ hY0).mp (hfar n)
      dsimp [den]
      nlinarith)
    simp only [hz, Nat.cast_zero, zero_add]
    convert hh using 1 <;> ring
  · have hc : (1 : ℝ) ≤ nearCount α (T / Y) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hh := hbound 1 zero_lt_one (fun n => by dsimp [den]; exact le_add_of_nonneg_right (mul_nonneg hY0.le (abs_nonneg _)))
    simp only [one_pow, div_one] at hh
    apply hh.trans
    exact le_mul_of_one_le_right (by positivity) (by
      have ht : 0 ≤ 1 / T ^ k := by positivity
      linarith)

/-- Page 6, the natural dyadic interval has at most twice its scale many elements. -/
theorem dyadic_card_le {M : ℝ} (hM : 0 ≤ M) :
    ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) ≤ 2 * M := by
  rw [Nat.card_Ioc]
  exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (by positivity))

/-- Page 6, the Type I sum is a weighted sum of smooth sums at scale X over m. -/
theorem typeISum_eq_smoothSum {w : ℝ → ℝ} (hs : Function.support w ⊆ Set.Icc 0 1)
    (A : ℕ → ℂ) {X : ℝ} (hX : 0 < X) (M β : ℝ) :
    typeISum w A X M β = ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      A m * smoothSum w (X / m) (β * m) := by
  unfold typeISum
  apply Finset.sum_congr rfl
  intro m hm
  have hm1 : 1 ≤ m := by have hh := (Finset.mem_Ioc.mp hm).1; omega
  have hi : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)) =
      smoothSum w (X / m) (β * m) := Weight86.typeI_inner_sum hs hX hm1 β
  rw [← hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_assoc _ _ _

/-- Page 6 trivial bound, a smooth unit interval sum is bounded by a constant times its scale. -/
theorem smoothSum_trivial (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y α : ℝ, 0 < Y → ‖smoothSum w Y α‖ ≤ C * Y := by
  obtain ⟨C, hC, hb⟩ := smoothSum_cutoff w hw hs 0
  refine ⟨4 * C, by positivity, ?_⟩
  intro Y α hY
  by_cases hY1 : 1 ≤ Y
  · have hh := hb Y α 1 hY1 le_rfl
    have hc : (nearCount α (1 / Y) : ℝ) ≤ 3 := by
      have hr : 1 / Y ≤ 1 := (div_le_one hY).mpr hY1
      have hh := DiophantineCount.card_integer_interval_le
        (a := α - 1 / Y) (b := α + 1 / Y) (by linarith [one_div_nonneg.mpr hY.le])
      change ((Finset.Icc ⌈α - 1 / Y⌉ ⌊α + 1 / Y⌋).card : ℝ) ≤ 3
      linarith
    simp only [pow_zero, div_one] at hh
    apply hh.trans
    have ht := mul_le_mul_of_nonneg_left (show (nearCount α (1 / Y) : ℝ) + 1 ≤ 4 by linarith)
      (show 0 ≤ C * Y by positivity)
    convert ht using 1 <;> ring
  · have hf : ⌊Y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hY.le, lt_of_not_ge hY1⟩
    have hw0 := (Weight86.weight_endpoints hw.continuous hs).1
    simp only [smoothSum, hf, Finset.Icc_self, Finset.sum_singleton,
      Int.cast_zero, mul_zero, zero_div, hw0, Complex.ofReal_zero, mul_zero, norm_zero]
    positivity

/-- Page 6 first Type I bound, uniform in the dyadic m scale and the frequency. -/
theorem typeI_trivial (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X M β : ℝ, 0 < X → 0 < M →
      ∀ A : ℕ → ℂ, (∀ m, ‖A m‖ ≤ 1) → ‖typeISum w A X M β‖ ≤ C * X := by
  obtain ⟨C, hC, hb⟩ := smoothSum_trivial w hw hs
  refine ⟨2 * C, by positivity, ?_⟩
  intro X M β hX hM A hA
  rw [typeISum_eq_smoothSum hs A hX M β]
  have hmB (m : ℕ) (hm : m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊) :
      ‖A m * smoothSum w (X / m) (β * m)‖ ≤ C * X / M := by
    have hmM : M < (m : ℝ) := (Nat.floor_lt hM.le).mp (Finset.mem_Ioc.mp hm).1
    have hm0 : (0 : ℝ) < m := hM.trans hmM
    rw [norm_mul]
    calc
      _ ≤ ‖smoothSum w (X / m) (β * m)‖ := mul_le_of_le_one_left (norm_nonneg _) (hA m)
      _ ≤ C * (X / m) := hb _ _ (div_pos hX hm0)
      _ ≤ C * (X / M) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hX.le hM hmM.le) hC.le
      _ = _ := by ring
  calc
    _ ≤ ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖A m * smoothSum w (X / m) (β * m)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, C * X / M := Finset.sum_le_sum hmB
    _ = ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) * (C * X / M) := by simp
    _ ≤ (2 * M) * (C * X / M) := mul_le_mul_of_nonneg_right (dyadic_card_le hM.le) (by positivity)
    _ = _ := by field_simp <;> ring

/-- Page 6 second Type I bound, with free cutoff T and explicit summable remainder. -/
theorem typeI_localized (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X M β T : ℝ, 0 < X → 0 < M → 2 * M ≤ X → 1 ≤ T →
      ∀ A : ℕ → ℂ, (∀ m, ‖A m‖ ≤ 1) →
        ‖typeISum w A X M β‖ ≤ C *
          (X / M * DiophantineCount.pairCount (-β) M (T / X) + 2 * X / T ^ k) := by
  obtain ⟨C, hC, hb⟩ := smoothSum_cutoff w hw hs k
  refine ⟨C, hC, ?_⟩
  intro X M β T hX hM hMX hT A hA
  rw [typeISum_eq_smoothSum hs A hX M β]
  have hmB (m : ℕ) (hm : m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊) :
      ‖A m * smoothSum w (X / m) (β * m)‖ ≤
        C * (X / M) * (nearCount (β * m) ((m : ℝ) * (T / X)) + 1 / T ^ k) := by
    have hmM : M < (m : ℝ) := (Nat.floor_lt hM.le).mp (Finset.mem_Ioc.mp hm).1
    have hm0 : (0 : ℝ) < m := hM.trans hmM
    have hmX : (m : ℝ) ≤ X := ((Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hm).2).trans hMX
    have hr : T / (X / m) = (m : ℝ) * (T / X) := by field_simp
    rw [norm_mul]
    calc
      _ ≤ ‖smoothSum w (X / m) (β * m)‖ := mul_le_of_le_one_left (norm_nonneg _) (hA m)
      _ ≤ C * (X / m) * (nearCount (β * m) ((m : ℝ) * (T / X)) + 1 / T ^ k) := by
        simpa only [hr] using hb (X / m) (β * m) T ((one_le_div hm0).mpr hmX) hT
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hX.le hM hmM.le) hC.le) (by positivity)
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hmB)
  have he : (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      (nearCount (β * m) ((m : ℝ) * (T / X)) : ℝ)) =
      (DiophantineCount.pairCount (-β) M (T / X) : ℝ) := by
    exact_mod_cast (sum_nearCount_eq_pairCount β (T / X) hM.le)
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum, he] at hsum
  have hc := mul_le_mul_of_nonneg_right (dyadic_card_le hM.le)
    (show 0 ≤ C * (X / M) * (1 / T ^ k) by positivity)
  have he2 : (2 * M) * (C * (X / M) * (1 / T ^ k)) = C * (2 * X / T ^ k) := by field_simp <;> ring
  rw [he2] at hc
  nlinarith

/-- Page 6 outer sum, there are at most four D squared residue representatives. -/
theorem residue_card_le {D : ℝ} (hD : 0 ≤ D) :
    (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, (d : ℝ)) ≤ 4 * D ^ 2 := by
  calc
    _ ≤ ∑ _d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, 2 * D := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hd).2
    _ = ((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊).card : ℝ) * (2 * D) := by simp
    _ ≤ (2 * D) * (2 * D) := mul_le_mul_of_nonneg_right (dyadic_card_le hD) (by positivity)
    _ = _ := by ring

/-- Page 6 trivial outer mean square estimate from a uniform norm bound. -/
theorem energy_le_const (F : ℝ → ℂ) {α D B : ℝ} (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hb : ∀ β : ℝ, ‖F β‖ ≤ B) :
    energy F D α ≤ 4 * D ^ 2 * B ^ 2 := by
  unfold energy
  calc
    _ ≤ ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ _b ∈ Finset.range d, B ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro b hb'
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
    _ = (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, (d : ℝ)) * B ^ 2 := by simp [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (residue_card_le hD) (sq_nonneg B)

/-- Page 6 Type I mean square before applying the Diophantine counting estimate. -/
theorem typeI_energy_cutoff (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X D M α T : ℝ,
      0 < X → 0 < D → 0 < M → 2 * M ≤ X → 1 ≤ T →
      ∀ A : ℕ → ℂ, (∀ m, ‖A m‖ ≤ 1) →
        energy (typeISum w A X M) D α ≤ C *
          (X ^ 2 / M * count24 α D M (T / X) + X ^ 2 * D ^ 2 / T ^ k) := by
  obtain ⟨C₀, hC₀, htriv⟩ := typeI_trivial w hw hs
  obtain ⟨C₁, hC₁, hloc⟩ := typeI_localized w hw hs k
  refine ⟨8 * C₀ * C₁, by positivity, ?_⟩
  intro X D M α T hX hD hM hMX hT A hA
  have hpoint (β : ℝ) : ‖typeISum w A X M β‖ ^ 2 ≤
      (C₀ * C₁ * X ^ 2 / M) * DiophantineCount.pairCount (-β) M (T / X) +
        2 * C₀ * C₁ * X ^ 2 / T ^ k := by
    have ht := htriv X M β hX hM A hA
    have hl := hloc X M β T hX hM hMX hT A hA
    calc
      _ ≤ (C₀ * X) * ‖typeISum w A X M β‖ := by
        nlinarith [norm_nonneg (typeISum w A X M β)]
      _ ≤ (C₀ * X) * (C₁ *
          (X / M * DiophantineCount.pairCount (-β) M (T / X) + 2 * X / T ^ k)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by ring
  have hcount : (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
      (DiophantineCount.pairCount (-(α + (b : ℝ) / d)) M (T / X) : ℝ)) =
      (count24 α D M (T / X) : ℝ) := by
    exact_mod_cast (count24_residue_convention α D M (T / X))
  have hsum : energy (typeISum w A X M) D α ≤
      (C₀ * C₁ * X ^ 2 / M) * count24 α D M (T / X) +
        (∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, (d : ℝ)) *
          (2 * C₀ * C₁ * X ^ 2 / T ^ k) := by
    unfold energy
    calc
      _ ≤ ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
          ((C₀ * C₁ * X ^ 2 / M) * DiophantineCount.pairCount (-(α + (b : ℝ) / d)) M (T / X) +
            2 * C₀ * C₁ * X ^ 2 / T ^ k) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun b hb => hpoint _))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.card_range]
        simp_rw [← Finset.mul_sum]
        rw [hcount, Finset.sum_mul]
  have hout := mul_le_mul_of_nonneg_right (residue_card_le hD.le)
    (show 0 ≤ 2 * C₀ * C₁ * X ^ 2 / T ^ k by positivity)
  have hin : X ^ 2 / M * (count24 α D M (T / X) : ℝ) +
      8 * (X ^ 2 * D ^ 2 / T ^ k) ≤
      8 * (X ^ 2 / M * (count24 α D M (T / X) : ℝ) + X ^ 2 * D ^ 2 / T ^ k) := by
    have hh : 0 ≤ X ^ 2 / M * (count24 α D M (T / X) : ℝ) := by positivity
    linarith
  calc
    _ ≤ (C₀ * C₁ * X ^ 2 / M) * count24 α D M (T / X) +
        (4 * D ^ 2) * (2 * C₀ * C₁ * X ^ 2 / T ^ k) := hsum.trans (add_le_add le_rfl hout)
    _ = (C₀ * C₁) * (X ^ 2 / M * count24 α D M (T / X) + 8 * (X ^ 2 * D ^ 2 / T ^ k)) := by ring
    _ ≤ (C₀ * C₁) * (8 * (X ^ 2 / M * count24 α D M (T / X) + X ^ 2 * D ^ 2 / T ^ k)) :=
      mul_le_mul_of_nonneg_left hin (by positivity)
    _ = _ := by ring

/-- Page 6 equation 7, the counting budget absorbs one additional cutoff power. -/
theorem typeI_counting_budget {X M D P C : ℝ} {q : ℕ}
    (hX : 0 < X) (hM : 0 < M) (hD : 0 ≤ D) (hP : 1 ≤ P) (hC : 0 ≤ C) (hq : 1 ≤ q) :
    X ^ 2 / M * (C * P * M * D * (1 / (q : ℝ) + q * (P / X) + (P / X) * M * D)) ≤
      C * (X ^ 2 * P ^ 2) * (D / q + q * D / X + M * D ^ 2 / X) := by
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hh := mul_le_mul_of_nonneg_right hP2 (show 0 ≤ D / q by positivity)
  calc
    _ = (C * X ^ 2) * (P * (D / q) + P ^ 2 * (q * D / X + M * D ^ 2 / X)) := by
      field_simp <;> ring
    _ ≤ (C * X ^ 2) * (P ^ 2 * (D / q) + P ^ 2 * (q * D / X + M * D ^ 2 / X)) :=
      mul_le_mul_of_nonneg_left (add_le_add hh le_rfl) (by positivity)
    _ = _ := by ring

/-- Page 6 Type II difference, two indices in the same dyadic interval differ by at most N. -/
theorem typeII_difference_bound {N : ℝ} (hN : 0 < N) {n₁ n₂ : ℕ}
    (h₁ : n₁ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊)
    (h₂ : n₂ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) :
    |(n₁ : ℝ) - n₂| ≤ N := by
  have h₁lo := (Nat.floor_lt hN.le).mp (Finset.mem_Ioc.mp h₁).1
  have h₂lo := (Nat.floor_lt hN.le).mp (Finset.mem_Ioc.mp h₂).1
  have h₁hi : (n₁ : ℝ) ≤ 2 * N := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp h₁).2
  have h₂hi : (n₂ : ℝ) ≤ 2 * N := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp h₂).2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Page 6 Type II multiplicity, a fixed difference has at most the size of one index interval. -/
theorem typeII_difference_multiplicity (N : ℝ) (z : ℤ) :
    (((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = z)).card) ≤
        (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    have hpz := (Finset.mem_filter.mp hp).2
    have hqz := (Finset.mem_filter.mp hq).2
    apply Prod.ext hpq
    omega

/-- Page 6 Type II grouping, every nonnegative function of the difference has multiplicity at most 2N. -/
theorem typeII_difference_sum {N : ℝ} (hN : 0 < N) (f : ℤ → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∑ n₁ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ∑ n₂ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      f ((n₁ : ℤ) - n₂)) ≤ 2 * N * ∑ z ∈ Finset.Icc (-⌈N⌉) ⌈N⌉, f z := by
  let s := Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊
  let g : ℕ × ℕ → ℤ := fun p => (p.1 : ℤ) - p.2
  have hg (p : ℕ × ℕ) (hp : p ∈ s ×ˢ s) : g p ∈ Finset.Icc (-⌈N⌉) ⌈N⌉ := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    have hh := abs_le.mp (typeII_difference_bound hN h₁ h₂)
    have hceil := Int.le_ceil N
    apply Finset.mem_Icc.mpr
    constructor
    · have hr : -(⌈N⌉ : ℝ) ≤ (p.1 : ℝ) - p.2 := by linarith
      dsimp [g]
      exact_mod_cast hr
    · have hr : (p.1 : ℝ) - p.2 ≤ (⌈N⌉ : ℝ) := by linarith
      dsimp [g]
      exact_mod_cast hr
  have he := Finset.sum_fiberwise_of_maps_to' hg f
  have hsum : (∑ p ∈ s ×ˢ s, f (g p)) ≤
      (s.card : ℝ) * ∑ z ∈ Finset.Icc (-⌈N⌉) ⌈N⌉, f z := by
    rw [← he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (typeII_difference_multiplicity N z)) (hf z)
  have hcard := mul_le_mul_of_nonneg_right (dyadic_card_le hN.le)
    (Finset.sum_nonneg (fun z hz => hf z) : 0 ≤ ∑ z ∈ Finset.Icc (-⌈N⌉) ⌈N⌉, f z)
  apply LE.le.trans ?_ hcard
  simpa only [Finset.sum_product, s, g] using hsum

/-- Page 6 dyadic difference count with the number of scales retained explicitly.
CONDITIONAL ON Counting24. -/
theorem typeII_dyadic_count (hcount : Counting24) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X D N α L : ℝ,
      1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X → 0 ≤ α → α ≤ 1 → 0 < L →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
        |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → ∀ K : ℕ,
          (∑ j ∈ Finset.range K,
            (count24 α D (N / 2 ^ (j + 1)) (2 ^ (j + 1) / L) : ℝ)) ≤
              C * X ^ ε * (N * D / q + K * (q * N * D / L) + N ^ 2 * D ^ 2 / L) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := hcount ε hε
  refine ⟨C, hC, ?_⟩
  intro X D N α L hX hD hDX hN hNX hα0 hα1 hL a q hq hcop happ K
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hterm (j : ℕ) : (count24 α D (N / 2 ^ (j + 1)) (2 ^ (j + 1) / L) : ℝ) ≤
      (C * X ^ ε) * ((N / 2 ^ (j + 1)) * (D / q + N * D ^ 2 / L) + q * N * D / L) := by
    have hH : 0 < N / (2 : ℝ) ^ (j + 1) := by positivity
    have hHX : N / (2 : ℝ) ^ (j + 1) ≤ X :=
      (div_le_self hN.le (one_le_pow₀ (by norm_num))).trans hNX
    have hc := hb X D (N / 2 ^ (j + 1)) α (2 ^ (j + 1) / L)
      hX hD hDX hH hHX hα0 hα1 (by positivity) a q hq hcop happ
    apply hc.trans_eq
    field_simp
    ring
  have hgeom (k : ℕ) : (∑ j ∈ Finset.range k, N / (2 : ℝ) ^ (j + 1)) = N - N / 2 ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring
  have hsumH : (∑ j ∈ Finset.range K, N / (2 : ℝ) ^ (j + 1)) ≤ N := by
    rw [hgeom]
    have hh : 0 ≤ N / (2 : ℝ) ^ K := by positivity
    linarith
  have hsum : (∑ j ∈ Finset.range K,
      (count24 α D (N / 2 ^ (j + 1)) (2 ^ (j + 1) / L) : ℝ)) ≤
      (C * X ^ ε) * ((∑ j ∈ Finset.range K, N / (2 : ℝ) ^ (j + 1)) *
        (D / q + N * D ^ 2 / L) + (K : ℝ) * (q * N * D / L)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range K, (C * X ^ ε) *
          ((N / (2 : ℝ) ^ (j + 1)) * (D / q + N * D ^ 2 / L) + q * N * D / L) :=
        Finset.sum_le_sum (fun j hj => hterm j)
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
        simp
  calc
    _ ≤ (C * X ^ ε) * ((∑ j ∈ Finset.range K, N / (2 : ℝ) ^ (j + 1)) *
        (D / q + N * D ^ 2 / L) + (K : ℝ) * (q * N * D / L)) := hsum
    _ ≤ (C * X ^ ε) * (N * (D / q + N * D ^ 2 / L) + (K : ℝ) * (q * N * D / L)) := by
      gcongr
    _ = _ := by ring

/-- Page 5 Lemma 2.4 grouping, a nonzero denominator has at most tau squared ordered triple factorizations. -/
theorem triple_factorization_card_le {r : ℕ} (hr : r ≠ 0) (s : Finset (ℕ × ℕ × ℕ))
    (hs : ∀ p ∈ s, p.1 * p.2.1 * p.2.2 = r) : s.card ≤ r.divisors.card ^ 2 := by
  have hc : s.card ≤ (r.divisors ×ˢ r.divisors).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ × ℕ => (p.1, p.2.1))
    · intro p hp
      have he := hs p hp
      apply Finset.mem_product.mpr
      constructor
      · apply Nat.mem_divisors.mpr
        refine ⟨⟨p.2.1 * p.2.2, ?_⟩, hr⟩
        rw [← he]
        ring
      · apply Nat.mem_divisors.mpr
        refine ⟨⟨p.1 * p.2.2, ?_⟩, hr⟩
        rw [← he]
        ring
    · intro p hp q hq hpq
      rcases p with ⟨d, n, g⟩
      rcases q with ⟨d', n', g'⟩
      obtain ⟨hd, hn⟩ := Prod.mk.inj hpq
      dsimp only at hd hn
      subst d'
      subst n'
      have hp' : d * n * g = r := hs _ hp
      have hq' : d * n * g' = r := hs _ hq
      have hdn : d * n ≠ 0 := by intro hz; rw [hz, zero_mul] at hp'; exact hr hp'.symm
      have hg : g = g' := mul_left_cancel₀ hdn (hp'.trans hq'.symm)
      simp [hg]
  simpa only [Finset.card_product, pow_two] using hc

/-- Page 5 Lemma 2.4 grouping, triple factorization multiplicity is bounded by every positive power. -/
theorem triple_factorization_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), r ≠ 0 → ∀ s : Finset (ℕ × ℕ × ℕ),
      (∀ p ∈ s, p.1 * p.2.1 * p.2.2 = r) → (s.card : ℝ) ≤ C * (r : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := card_divisors_le_rpow (show 0 < ε / 2 by linarith)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro r hr s hs
  calc
    (s.card : ℝ) ≤ (r.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast (triple_factorization_card_le hr s hs)
    _ ≤ (C * (r : ℝ) ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hb r) 2
    _ = C ^ 2 * (r : ℝ) ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg r)]
      congr 2
      ring

/-- Page 5 Vaughan coefficient input, the short convolution has a uniform positive power bound. -/
theorem short_mu_lambda_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V : ℝ) (n : ℕ),
      |(Vaughan86.shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
        Vaughan86.shortPart ArithmeticFunction.vonMangoldt V) n| ≤ C * (n : ℝ) ^ ε := by
  refine ⟨1 / ε, by positivity, ?_⟩
  intro U V n
  calc
    _ ≤ Real.log n := VaughanCoeffs86.short_mu_lambda_bound U V n
    _ ≤ (n : ℝ) ^ ε / ε := Real.log_natCast_le_rpow_div n hε
    _ = _ := by ring

/-- Page 5 Lemma 2.4 numerator fiber, reduced coprime denominators give at most g solutions. -/
theorem reduced_numerator_fiber_card {d n : ℤ} (hd : 0 < d) (hc : IsCoprime n d)
    (g : ℕ) (c : ℤ) (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 ≤ d * g ∧ n * p.1 + d * p.2 = c) :
    s.card ≤ g := by
  have hcard : s.card ≤ (Finset.Ico (0 : ℤ) g).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => (p.1 - 1) / d)
    · intro p hp
      obtain ⟨hlo, hhi, he⟩ := hs p hp
      apply Finset.mem_Ico.mpr
      constructor
      · exact Int.ediv_nonneg (by omega) hd.le
      · apply (Int.ediv_lt_iff_lt_mul hd).mpr
        nlinarith
    · intro p hp q hq hpq
      have hpdec := Int.mul_ediv_add_emod (p.1 - 1) d
      have hqdec := Int.mul_ediv_add_emod (q.1 - 1) d
      have hp0 := Int.emod_nonneg (p.1 - 1) hd.ne'
      have hq0 := Int.emod_nonneg (q.1 - 1) hd.ne'
      have hp1 := Int.emod_lt_of_pos (p.1 - 1) hd
      have hq1 := Int.emod_lt_of_pos (q.1 - 1) hd
      have hwidth : |p.1 - q.1| < d := by
        apply abs_lt.mpr
        constructor <;> nlinarith
      have he : n * p.1 - d * (-p.2) = n * q.1 - d * (-q.2) := by
        have hh := (hs p hp).2.2
        have hh' := (hs q hq).2.2
        nlinarith
      obtain ⟨hb, hm⟩ := DiophantineCount.determinant_injective hd hc hwidth he
      exact Prod.ext hb (neg_injective hm)
  simpa only [Int.card_Ico, sub_zero, Int.toNat_natCast] using hcard

/-- LEAF. Page 4 equation 3. Poisson summation and integration by parts.
The exact Poisson formula and a uniform shifted kernel bound prove the estimate. -/
theorem localization22 : Localization22 := by
  intro ε hε w hw hs
  let k : ℕ := ⌈101 / ε⌉₊
  obtain ⟨C, hC, hdec⟩ := Localization86.weightFourier_decay w hw hs (k + 2)
  obtain ⟨S, hS, hK⟩ := Kernel86.uniform_shifted_kernel
  refine ⟨C * S, by positivity, ?_⟩
  intro X α hX
  have hX0 : 0 < X := by linarith
  let K : ℤ → ℝ := fun n => 1 / (1 + |(n : ℝ) - α|) ^ 2
  let F : ℤ → ℂ := fun n => (X : ℂ) * Localization86.weightFourier w (X * ((n : ℝ) - α))
  let den : ℤ → ℝ := fun n => 1 + X * |(n : ℝ) - α|
  have hkSum : Summable K := (hK α).1
  have hkBound : (∑' n : ℤ, K n) ≤ S := (hK α).2
  have hden (n : ℤ) : 1 + |(n : ℝ) - α| ≤ den n := by
    have hh := mul_le_mul_of_nonneg_right hX (abs_nonneg ((n : ℝ) - α))
    dsimp [den]
    linarith
  have hdec' (n : ℤ) : den n ^ (k + 2) *
      ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ ≤ C := by
    simpa only [den, abs_mul, abs_of_pos hX0] using hdec (X * ((n : ℝ) - α))
  have hnorm (n : ℤ) : ‖F n‖ = X *
      ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ := by
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
  have hmajor (n : ℤ) : ‖F n‖ ≤ (X * C) * K n := by
    have hp : (1 + |(n : ℝ) - α|) ^ 2 ≤ den n ^ (k + 2) := by
      apply (pow_le_pow_left₀ (by positivity) (hden n) 2).trans
      exact pow_le_pow_right₀ (show 1 ≤ den n by dsimp [den]; nlinarith [abs_nonneg ((n : ℝ) - α)]) (by omega)
    have hh := (mul_le_mul_of_nonneg_right hp
      (norm_nonneg (Localization86.weightFourier w (X * ((n : ℝ) - α))))).trans (hdec' n)
    have hv : ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ ≤
        C / (1 + |(n : ℝ) - α|) ^ 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using hh
    rw [hnorm]
    apply (mul_le_mul_of_nonneg_left hv hX0.le).trans_eq
    dsimp [K]
    ring
  have hns : Summable (fun n : ℤ => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor (hkSum.mul_left (X * C))
  have hpoisson : smoothSum w X α = ∑' n : ℤ, F n :=
    Localization86.poisson_scaled w hw hs X hX0 α
  have hsum : ‖smoothSum w X α‖ ≤ X * C * S := by
    rw [hpoisson]
    calc
      _ ≤ ∑' n : ℤ, ‖F n‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n : ℤ, (X * C) * K n :=
        Summable.tsum_le_tsum hmajor hns (hkSum.mul_left (X * C))
      _ = (X * C) * ∑' n : ℤ, K n := tsum_mul_left
      _ ≤ (X * C) * S := mul_le_mul_of_nonneg_left hkBound (by positivity)
      _ = _ := by ring
  by_cases hz : nearCount α (X ^ (ε - 1)) = 0
  · have hfar (n : ℤ) : X ^ (ε - 1) < |(n : ℝ) - α| := by
      by_contra! hh
      have hb := abs_le.mp hh
      have hm : n ∈ Finset.Icc ⌈α - X ^ (ε - 1)⌉ ⌊α + X ^ (ε - 1)⌋ := by
        simp only [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
        constructor <;> linarith
      have he : Finset.Icc ⌈α - X ^ (ε - 1)⌉ ⌊α + X ^ (ε - 1)⌋ = ∅ :=
        Finset.card_eq_zero.mp hz
      rw [he] at hm
      exact Finset.notMem_empty n hm
    have hmul101 : (101 : ℝ) ≤ ε * (k : ℝ) := by
      have hh : 101 / ε ≤ (k : ℝ) := Nat.le_ceil _
      have hb := (div_le_iff₀ hε).mp hh
      nlinarith
    have hxpower : X * X ^ (ε - 1) = X ^ ε := by
      calc
        _ = X ^ (1 : ℝ) * X ^ (ε - 1) := by rw [Real.rpow_one]
        _ = X ^ ((1 : ℝ) + (ε - 1)) := (Real.rpow_add hX0 _ _).symm
        _ = _ := by congr 1; ring
    have hmajorFar (n : ℤ) : ‖F n‖ ≤ (C * X ^ (-(100 : ℝ))) * K n := by
      have hfreq : X ^ ε ≤ den n := by
        have hh := mul_le_mul_of_nonneg_left (hfar n).le hX0.le
        rw [hxpower] at hh
        dsimp [den]
        linarith
      have hp101 : X ^ (101 : ℕ) ≤ den n ^ k := by
        calc
          _ = X ^ (101 : ℝ) := by norm_num
          _ ≤ X ^ (ε * (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hX hmul101
          _ = (X ^ ε) ^ k := Real.rpow_mul_natCast hX0.le ε k
          _ ≤ den n ^ k := pow_le_pow_left₀ (Real.rpow_nonneg hX0.le ε) hfreq k
      have hp : X ^ (101 : ℕ) * (1 + |(n : ℝ) - α|) ^ 2 ≤ den n ^ (k + 2) := by
        rw [pow_add]
        exact mul_le_mul hp101 (pow_le_pow_left₀ (by positivity) (hden n) 2)
          (by positivity) (by positivity)
      have hh := (mul_le_mul_of_nonneg_right hp
        (norm_nonneg (Localization86.weightFourier w (X * ((n : ℝ) - α))))).trans (hdec' n)
      have hv : ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ ≤
          C / (X ^ (101 : ℕ) * (1 + |(n : ℝ) - α|) ^ 2) := by
        apply (le_div_iff₀ (by positivity)).mpr
        simpa only [mul_comm] using hh
      rw [hnorm]
      apply (mul_le_mul_of_nonneg_left hv hX0.le).trans_eq
      have hneg : X ^ (-(100 : ℝ)) = (X ^ (100 : ℕ))⁻¹ := by
        rw [Real.rpow_neg hX0.le]
        norm_num
      rw [hneg]
      dsimp [K]
      field_simp
    have hbound : ‖smoothSum w X α‖ ≤ (C * X ^ (-(100 : ℝ))) * S := by
      rw [hpoisson]
      calc
        _ ≤ ∑' n : ℤ, ‖F n‖ := norm_tsum_le_tsum_norm hns
        _ ≤ ∑' n : ℤ, (C * X ^ (-(100 : ℝ))) * K n :=
          Summable.tsum_le_tsum hmajorFar hns (hkSum.mul_left _)
        _ = (C * X ^ (-(100 : ℝ))) * ∑' n : ℤ, K n := tsum_mul_left
        _ ≤ _ := mul_le_mul_of_nonneg_left hkBound (by positivity)
    simp only [hz, Nat.cast_zero, mul_zero, zero_add]
    convert hbound using 1; ring
  · have hc : (1 : ℝ) ≤ nearCount α (X ^ (ε - 1)) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hsub : X ≤ X * nearCount α (X ^ (ε - 1)) + X ^ (-(100 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hc hX0.le
      have hp := Real.rpow_nonneg hX0.le (-(100 : ℝ))
      linarith
    apply hsum.trans
    have hh := mul_le_mul_of_nonneg_left hsub (show 0 ≤ C * S by positivity)
    convert hh using 1; ring

/-- LEAF. Pages 4 to 5 equation 5. This is the existing task42 proof with constant 64. -/
theorem lemma23 : DiophantineCount.Lemma23Bound := by
  exact DiophantineCount.lemma23_bound

/-- LEAF. Page 5 equation 6, the dense numerator case. Constant 64 is uniform in alpha. -/
theorem count24_large_delta {α D N δ : ℝ} (hD : 0 < D) (hN : 0 < N) (hδ : 0 < δ)
    (hlarge : 1 / 4 ≤ N * δ) :
    (count24 α D N δ : ℝ) ≤ 64 * δ * N ^ 2 * D ^ 2 := by
  have hD0 : 0 ≤ 2 * D := by positivity
  have hdcard : ((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊).card : ℝ) ≤ 2 * D := by
    rw [Nat.card_Ioc]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le hD0)
  have hbcard : ∀ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊,
      ((Finset.Icc 1 d).card : ℝ) ≤ 2 * D := by
    intro d hd
    have hd2 : (d : ℝ) ≤ 2 * D :=
      (Nat.le_floor_iff hD0).mp (Finset.mem_Ioc.mp hd).2
    simpa [Nat.card_Icc] using hd2
  unfold count24
  push_cast
  calc
    ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊,
        ∑ b ∈ Finset.Icc 1 d,
          (DiophantineCount.pairCount (-(α + (b : ℝ) / d)) N δ : ℝ) ≤
        ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊,
          ∑ _b ∈ Finset.Icc 1 d, 16 * δ * N ^ 2 := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro b hb
      exact DiophantineCount.pairCount_large_delta hN hδ hlarge
    _ ≤ ∑ _d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, 2 * D * (16 * δ * N ^ 2) := by
      apply sum_le_sum
      intro d hd
      simpa using mul_le_mul_of_nonneg_right (hbcard d hd)
        (show 0 ≤ 16 * δ * N ^ 2 by positivity)
    _ = ((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊).card : ℝ) * (2 * D * (16 * δ * N ^ 2)) := by simp
    _ ≤ 2 * D * (2 * D * (16 * δ * N ^ 2)) :=
      mul_le_mul_of_nonneg_right hdcard (by positivity)
    _ = 64 * δ * N ^ 2 * D ^ 2 := by ring

/-- LEAF. Page 5 equation 6, the dense branch formula cannot be used without its threshold. -/
theorem dense_bound_needs_threshold : 64 * (1 / 1000 : ℝ) < (count24 0 1 1 (1 / 1000) : ℝ) := by
  have hi : Finset.Ioc (1 : ℤ) 2 = {2} := by decide
  norm_num [hi,count24, DiophantineCount.pairCount, DiophantineCount.denominatorRange,
    DiophantineCount.numeratorRange, Finset.sum_Icc_succ_top]

/-- LEAF. Page 5 equation 6. The remaining gcd grouping and divisor multiplicity bound.
CONDITIONAL ON the Lemma 2.3 input. -/
theorem counting24_sparse (h23 : DiophantineCount.Lemma23Bound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X D N α δ : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X →
        0 ≤ α → α ≤ 1 → 0 < δ → N * δ < 1 / 4 →
        ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
          |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
          (count24 α D N δ : ℝ) ≤
            C * X ^ ε * N * D * (1 / (q : ℝ) + q * δ + δ * N * D) := by sorry

/-- Page 5 equation 6 assembled from the proved dense case and the sparse leaf.
CONDITIONAL ON counting24_sparse and its Lemma 2.3 input. -/
theorem counting24 (h23 : DiophantineCount.Lemma23Bound) : Counting24 := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := counting24_sparse h23 ε hε
  refine ⟨C + 64, by positivity, ?_⟩
  intro X D N α δ hX hD hDX hN hNX hα0 hα1 hδ a q hq hcop happ
  let B : ℝ := 1 / (q : ℝ) + q * δ + δ * N * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ X ^ ε * N * D * B := by positivity
  by_cases hs : N * δ < 1 / 4
  · have hh := hb X D N α δ hX hD hDX hN hNX hα0 hα1 hδ hs a q hq hcop happ
    have hc := mul_le_mul_of_nonneg_right (show C ≤ C + 64 by linarith) hP
    apply hh.trans
    convert hc using 1 <;> ring
  · have hh := count24_large_delta (α := α) hD hN hδ (le_of_not_gt hs)
    have hsub : δ * N * D ≤ B := by
      dsimp [B]
      have h0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
      have h1 : (0 : ℝ) ≤ q * δ := by positivity
      linarith
    have hpow : 1 ≤ X ^ ε := Real.one_le_rpow hX hε.le
    have hbase : 64 * δ * N ^ 2 * D ^ 2 ≤ 64 * X ^ ε * N * D * B := by
      calc
        _ = 64 * N * D * (δ * N * D) := by ring
        _ ≤ 64 * N * D * B := mul_le_mul_of_nonneg_left hsub (by positivity)
        _ ≤ X ^ ε * (64 * N * D * B) :=
          le_mul_of_one_le_left (by positivity) hpow
        _ = _ := by ring
    have hc := mul_le_mul_of_nonneg_right (show (64 : ℝ) ≤ C + 64 by linarith) hP
    apply hh.trans (hbase.trans ?_)
    convert hc using 1 <;> ring


/-- LEAF. Page 6 proof of equation 7. Combine the trivial sum bound with localization.
CONDITIONAL ON equations 3 and 6. -/
theorem typeI7 (hloc : Localization22) (hcount : Counting24) : TypeI7 := by
  intro ε hε w hw hs
  let k : ℕ := ⌈2 / ε⌉₊
  obtain ⟨C₀, hC₀, htriv⟩ := typeI_trivial w hw hs
  obtain ⟨C₁, hC₁, hcut⟩ := typeI_energy_cutoff w hw hs k
  obtain ⟨C₂, hC₂, hcountB⟩ := hcount ε hε
  let C : ℝ := C₁ * (C₂ + 2) + 8 * C₀ ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro X D M α hX hD hDX hM hMX hα0 hα1 a q hq hcop happ A hA
  have hX0 : 0 < X := by linarith
  let P : ℝ := X ^ ε
  let R : ℝ := X ^ (2 + 2 * ε) * (D / q + q * D / X + M * D ^ 2 / X)
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpow : X ^ (2 + 2 * ε) = X ^ 2 * P ^ 2 := by
    calc
      _ = X ^ (2 : ℝ) * X ^ (ε * (2 : ℕ)) := by
        rw [← Real.rpow_add hX0]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_mul_natCast hX0.le]; norm_num [P]
  have hRlower : X * M * D ^ 2 ≤ R := by
    have hp : X ^ 2 ≤ X ^ (2 + 2 * ε) := by
      calc
        _ = X ^ (2 : ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hb : M * D ^ 2 / X ≤ D / q + q * D / X + M * D ^ 2 / X := by
      have hh : 0 ≤ D / (q : ℝ) := by positivity
      have hh' : 0 ≤ (q : ℝ) * D / X := by positivity
      linarith
    calc
      _ = X ^ 2 * (M * D ^ 2 / X) := by field_simp <;> ring
      _ ≤ R := mul_le_mul hp hb (by positivity) (by positivity)
  rw [mul_assoc]
  change energy (typeISum w A X M) D α ≤ C * R
  by_cases hsmall : 2 * M < 1
  · have hf : ⌊2 * M⌋₊ = 0 := Nat.floor_eq_zero.mpr hsmall
    simp only [energy, typeISum, hf, Finset.Ioc_eq_empty_of_le (Nat.zero_le _),
      Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact mul_nonneg (by dsimp [C]; nlinarith [sq_nonneg C₀]) hR
  have hMhalf : 1 / 2 ≤ M := by linarith
  by_cases hshort : 2 * M ≤ X
  · have hk : (2 : ℝ) ≤ ε * k := by
      have hh : 2 / ε ≤ (k : ℝ) := Nat.le_ceil _
      have hh' := (div_le_iff₀ hε).mp hh
      nlinarith
    have hTk : X ^ 2 ≤ P ^ k := by
      calc
        _ = X ^ (2 : ℝ) := by norm_num
        _ ≤ X ^ (ε * k) := Real.rpow_le_rpow_of_exponent_le hX hk
        _ = P ^ k := Real.rpow_mul_natCast hX0.le ε k
    have herr : X ^ 2 * D ^ 2 / P ^ k ≤ 2 * R := by
      have he : X ^ 2 * D ^ 2 / P ^ k ≤ D ^ 2 := by
        apply (div_le_iff₀ (pow_pos hP0 k)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hTk (sq_nonneg D)]
      have hm : D ^ 2 ≤ 2 * (X * M * D ^ 2) := by
        have hxM : 1 / 2 ≤ X * M := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hxM (sq_nonneg D)]
      exact he.trans (hm.trans (by linarith))
    have hc := hcountB X D M α (P / X) hX hD hDX hM hMX hα0 hα1
      (div_pos hP0 hX0) a q hq hcop happ
    have hb := typeI_counting_budget hX0 hM hD.le hP hC₂ hq
    have hmain : X ^ 2 / M * (count24 α D M (P / X) : ℝ) ≤ C₂ * R := by
      have ht := mul_le_mul_of_nonneg_left hc (show 0 ≤ X ^ 2 / M by positivity)
      apply ht.trans
      convert hb using 1 <;> dsimp [R] <;> rw [hpow] <;> ring
    have hh := hcut X D M α P hX0 hD hM hshort hP A hA
    calc
      _ ≤ C₁ * (X ^ 2 / M * count24 α D M (P / X) + X ^ 2 * D ^ 2 / P ^ k) := hh
      _ ≤ C₁ * (C₂ * R + 2 * R) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain herr) hC₁.le
      _ = (C₁ * (C₂ + 2)) * R := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg C₀]) hR
  · have ht := energy_le_const (α := α) (typeISum w A X M) hD.le
      (show 0 ≤ C₀ * X by positivity) (fun β => htriv X M β hX0 hM A hA)
    have hl : X ^ 2 * D ^ 2 ≤ 2 * R := by
      have hh : X ^ 2 * D ^ 2 ≤ 2 * (X * M * D ^ 2) := by
        have hx : X ≤ 2 * M := by linarith
        have hm := mul_le_mul_of_nonneg_right hx (show 0 ≤ X * D ^ 2 by positivity)
        nlinarith
      exact hh.trans (by linarith)
    calc
      _ ≤ 4 * D ^ 2 * (C₀ * X) ^ 2 := ht
      _ = (4 * C₀ ^ 2) * (X ^ 2 * D ^ 2) := by ring
      _ ≤ (4 * C₀ ^ 2) * (2 * R) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = (8 * C₀ ^ 2) * R := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg C₀]) hR

/-- LEAF. Page 6 first Type II inequality with the exact cardinality of the dyadic range. -/
theorem typeII_cauchy (w : ℝ → ℝ) (A B : ℕ → ℂ) (X M N β : ℝ)
    (hA : ∀ m, ‖A m‖ ≤ 1) :
    ‖typeIISum w A B X M N β‖ ^ 2 ≤
      ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) *
        ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
          ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
            B n * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)‖ ^ 2 := by
  have hc := Cauchy86.finite_cauchy (Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊) A
    (fun m => ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      B n * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)) (fun m _ => hA m)
  simpa only [typeIISum, Finset.mul_sum, mul_assoc] using hc

/-- LEAF. Page 6 second Type II inequality, including the exact difference phase. -/
theorem typeII_correlation (w : ℝ → ℝ) (A B : ℕ → ℂ) (X M N β : ℝ)
    (hA : ∀ m, ‖A m‖ ≤ 1) (hB : ∀ n, ‖B n‖ ≤ 1) :
    ‖typeIISum w A B X M N β‖ ^ 2 ≤
      ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) *
        ∑ n₁ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ∑ n₂ ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          ‖∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
            e (β * ((n₁ : ℝ) - n₂) * m) * (w ((m : ℝ) * n₁ / X) : ℂ) *
              (w ((m : ℝ) * n₂ / X) : ℂ)‖ := by
  have hc := Correlation86.bilinear_bound (Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊)
    (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) A B
    (fun m n => e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ))
    (fun m _ => hA m) (fun n _ => hB n)
  simp_rw [Phase86.kernel_correlation] at hc
  simpa only [typeIISum, mul_assoc] using hc

/-- LEAF. Page 6 proof of equation 8. Cauchy Schwarz, differences and dyadic counting.
CONDITIONAL ON equations 3 and 6. -/
theorem typeII8 (hloc : Localization22) (hcount : Counting24) : TypeII8 := by sorry

/-- LEAF. Page 5 proof of Theorem 2.1 and page 6 equation 8.
Vaughan identity, dyadic decomposition, coefficient bounds and epsilon absorption.
The algebraic identity is proved in Vaughan86.vaughan_identity from Mathlib convolution.
The dyadic localization and coefficient estimates are still open.
CONDITIONAL ON equations 7 and 8. -/
theorem vaughan_transfer (hI : TypeI7) (hII : TypeII8) : ExpSumBoundPrinted := by sorry

/-- The exact sealed cited Prop, assembled from named leaves with no sorry in this proof.
Uses proved localization22. CONDITIONAL ON counting24_sparse, typeI7, typeII8 and vaughan_transfer. -/
theorem akeno_thm2_1_assembled : ExpSumBound := by
  have hc : Counting24 := counting24 lemma23
  exact expSumBound_of_printed
    (vaughan_transfer (typeI7 localization22 hc) (typeII8 localization22 hc))

end LeanLab.Akeno2026.Decomp86

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

/-! ## Counting 2.4, the sparse case: the lcm regrouping

The paper's proof of equation 6 (Lemma 2.4) is the following.  For a solution `(d, b, n, m)` of
`|α + b/d + m/n| ≤ δ` write `g = gcd d n`, `d = d' g`, `n = n' g` and `c = b n' + d' m`; then

    b/d + m/n = c/(d' n' g),

so `|α + c/M| ≤ δ` with `M = d' n' g = lcm d n`, an approximation of the *same* `α` — and hence
of the same `a/q` — at the larger denominator `M`.  For fixed `(d, n, c)` there are at most `g`
pairs `(b, m)` (`reduced_numerator_fiber_card`), so

    count24 α D N δ ≤ Σ_{d, n} g(d,n) · #{c : |α + c/M(d,n)| ≤ δ},

and regrouping by `M` the pairs sharing an `M` number at most `(card M.divisors)^2`, while the
inner count over `c` is `pairCount (-α) M δ`, which Lemma 2.3 bounds by `M (1/q + qδ + δM)`.
Summing the dyadic blocks of `M` gives `ND (1/q + qδ + δND)`.
-/

/-- The reduced denominator data of a pair `(d, n)`. -/
private theorem gcd_data {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < Nat.gcd d n ∧ d / Nat.gcd d n * Nat.gcd d n = d ∧
      n / Nat.gcd d n * Nat.gcd d n = n ∧ Nat.Coprime (n / Nat.gcd d n) (d / Nat.gcd d n) := by
  have hg : 0 < Nat.gcd d n := Nat.gcd_pos_of_pos_left n hd
  refine ⟨hg, Nat.div_mul_cancel (Nat.gcd_dvd_left d n),
    Nat.div_mul_cancel (Nat.gcd_dvd_right d n), (Nat.coprime_div_gcd_div_gcd hg).symm⟩

/-- The key fraction identity: `b/d + m/n = c/(d' n' g)` with `c = b n' + d' m`. -/
private theorem frac_identity {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (b m : ℤ) :
    (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ) =
      ((b * ((n / Nat.gcd d n : ℕ) : ℤ) + ((d / Nat.gcd d n : ℕ) : ℤ) * m : ℤ) : ℝ) /
        (((d / Nat.gcd d n) * (n / Nat.gcd d n) * Nat.gcd d n : ℕ) : ℝ) := by
  obtain ⟨hg, hd', hn', -⟩ := gcd_data hd hn
  set g := Nat.gcd d n with hgdef
  set dp := d / g with hdpdef
  set np := n / g with hnpdef
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hdpR : (0 : ℝ) < (dp : ℝ) := by
    rcases Nat.eq_zero_or_pos dp with h | h
    · rw [h] at hd'; simp at hd'; omega
    · exact_mod_cast h
  have hnpR : (0 : ℝ) < (np : ℝ) := by
    rcases Nat.eq_zero_or_pos np with h | h
    · rw [h] at hn'; simp at hn'; omega
    · exact_mod_cast h
  have hdR : (d : ℝ) = (dp : ℝ) * (g : ℝ) := by
    rw [← hd']; push_cast; ring
  have hnR : (n : ℝ) = (np : ℝ) * (g : ℝ) := by
    rw [← hn']; push_cast; ring
  have hMR : ((dp * np * g : ℕ) : ℝ) = (dp : ℝ) * (np : ℝ) * (g : ℝ) := by push_cast; ring
  rw [hdR, hnR, hMR]
  push_cast
  field_simp

/-- The natural-indexed form of `pairCount`, matching `count24`'s inner sum. -/
private theorem pairCount_eq_sum_nat (β M δ : ℝ) (hM : 0 ≤ M) :
    (DiophantineCount.pairCount β M δ : ℝ) =
      ∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
        ((DiophantineCount.numeratorRange β δ (n : ℤ)).card : ℝ) := by
  have h := sum_nearCount_eq_pairCount (-β) δ hM
  rw [neg_neg] at h
  rw [← h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hh : nearCount (-β * (n : ℝ)) ((n : ℝ) * δ) =
      (DiophantineCount.numeratorRange β δ (n : ℤ)).card := by
    simpa using nearCount_eq_numerator (-β) δ (n : ℤ)
  rw [hh]


/-- The cast embedding `ℕ × ℤ ↪ ℤ × ℤ` used to move fibres between the two index types. -/
private def natPairEmbed : ℕ × ℤ ↪ ℤ × ℤ :=
  ⟨fun p => ((p.1 : ℤ), p.2), fun p q h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (by exact_mod_cast h1) h2⟩

/-- Fixed `(d,n)`: every shifted numerator count is controlled by the numerator count of the
*same* `α` at the combined denominator `M = d' n' g`.  This is the step of the paper's proof of
(6) that keeps the rational approximation `a/q` unchanged. -/
private theorem inner_fiber_bound {α δ : ℝ} {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ b ∈ Finset.Icc 1 d,
        ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / (d : ℝ))) δ (n : ℤ)).card : ℝ))
      ≤ (Nat.gcd d n : ℝ) *
        ((DiophantineCount.numeratorRange (-α) δ
          (((d / Nat.gcd d n) * (n / Nat.gcd d n) * Nat.gcd d n : ℕ) : ℤ)).card : ℝ) := by
  obtain ⟨hg, hd', hn', hcop⟩ := gcd_data hd hn
  set g := Nat.gcd d n with hgdef
  set dp := d / g with hdpdef
  set np := n / g with hnpdef
  have hdR : (d : ℝ) = (dp : ℝ) * (g : ℝ) := by rw [← hd']; push_cast; ring
  have hnR : (n : ℝ) = (np : ℝ) * (g : ℝ) := by rw [← hn']; push_cast; ring
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnZR : (0 : ℝ) < ((n : ℤ) : ℝ) := by exact_mod_cast hn
  have hMpos : (0 : ℝ) < ((dp * np * g : ℕ) : ℝ) := by
    have : 0 < dp * np * g := by
      rcases Nat.eq_zero_or_pos dp with h | h
      · rw [h] at hd'; simp at hd'; omega
      rcases Nat.eq_zero_or_pos np with h' | h'
      · rw [h'] at hn'; simp at hn'; omega
      positivity
    exact_mod_cast this
  -- the solution set of one pair `(d, n)`
  set Sol : Finset (ℕ × ℤ) :=
    ((Finset.Icc 1 d) ×ˢ Finset.Icc (-(4 * (n : ℤ))) (4 * (n : ℤ))).filter
      (fun p => |α + (p.1 : ℝ) / (d : ℝ) + (p.2 : ℝ) / (n : ℝ)| ≤ δ) with hSol
  -- the numerator bound: a solution forces `|m| ≤ 3n`
  have hmemIcc : ∀ (b : ℕ) (m : ℤ), 1 ≤ b → b ≤ d → |α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)| ≤ δ →
      m ∈ Finset.Icc (-(4 * (n : ℤ))) (4 * (n : ℤ)) := by
    intro b m hb1 hbd habs
    have hbR : (0 : ℝ) ≤ (b : ℝ) / (d : ℝ) := by positivity
    have hb1' : (b : ℝ) / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdpos]; exact_mod_cast hbd
    have hle : |(m : ℝ) / (n : ℝ)| ≤ 3 := by
      have h2 : |α + (b : ℝ) / (d : ℝ)| ≤ 2 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h1 : |(m : ℝ) / (n : ℝ)| ≤
          |α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)| + |α + (b : ℝ) / (d : ℝ)| := by
        have hh := abs_sub_le (α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)) (0 : ℝ)
          (α + (b : ℝ) / (d : ℝ))
        rwa [show (α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)) - (α + (b : ℝ) / (d : ℝ))
          = (m : ℝ) / (n : ℝ) from by ring, sub_zero, zero_sub, abs_neg] at hh
      linarith [h1, h2, habs, hδ1]
    have habsm : |(m : ℝ)| ≤ 3 * (n : ℝ) := by
      have hd1 : |(m : ℝ)| / (n : ℝ) ≤ 3 := by
        rwa [abs_div, abs_of_pos hnpos] at hle
      have := (div_le_iff₀ hnpos).mp hd1
      linarith
    have habsm' : |(m : ℝ)| ≤ 4 * (n : ℝ) := by linarith
    have hZ : |m| ≤ 4 * (n : ℤ) := by exact_mod_cast habsm'
    have h1 := (abs_le.mp hZ).1
    have h2 := (abs_le.mp hZ).2
    simp only [Finset.mem_Icc]
    constructor <;> linarith
  -- one fibre at numerator `b`, for `b` inside the modulus range
  have hfib : ∀ b ∈ Finset.Icc 1 d, (Sol.filter (fun p : ℕ × ℤ => p.1 = b)).card =
      (DiophantineCount.numeratorRange (-(α + (b : ℝ) / (d : ℝ))) δ (n : ℤ)).card := by
    intro b hb
    apply Finset.card_bij (fun (p : ℕ × ℤ) (_ : p ∈ Sol.filter (fun p => p.1 = b)) => p.2)
    · intro p hp
      obtain ⟨hpS, hpb⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, habs⟩ := Finset.mem_filter.mp hpS
      rw [show p.1 = b from hpb] at habs
      rw [DiophantineCount.mem_numeratorRange hnZR]
      have he : (-(α + (b : ℝ) / (d : ℝ)) - (p.2 : ℝ) / ((n : ℤ) : ℝ)) =
          -(α + (b : ℝ) / (d : ℝ) + (p.2 : ℝ) / (n : ℝ)) := by push_cast; ring
      rw [he, abs_neg]
      exact habs
    · intro p hp q hq heq
      obtain ⟨hpS, hpb⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqS, hqb⟩ := Finset.mem_filter.mp hq
      exact Prod.ext (by rw [hpb, hqb]) heq
    · intro m hm
      rw [DiophantineCount.mem_numeratorRange hnZR] at hm
      have habs : |α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)| ≤ δ := by
        have he : (-(α + (b : ℝ) / (d : ℝ)) - (m : ℝ) / ((n : ℤ) : ℝ)) =
            -(α + (b : ℝ) / (d : ℝ) + (m : ℝ) / (n : ℝ)) := by push_cast; ring
        rw [he, abs_neg] at hm
        exact hm
      have hb' : 1 ≤ b ∧ b ≤ d := by simpa using hb
      exact ⟨(b, m), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hb, hmemIcc b m hb'.1 hb'.2 habs⟩, habs⟩, rfl⟩, rfl⟩
  -- split `Sol` by the first coordinate
  have hcover : Set.MapsTo (fun p : ℕ × ℤ => p.1) (↑Sol : Set (ℕ × ℤ)) (↑(Finset.Icc 1 d) : Set ℕ) := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hcard : Sol.card = ∑ b ∈ Finset.Icc 1 d, (Sol.filter (fun p : ℕ × ℤ => p.1 = b)).card :=
    Finset.card_eq_sum_card_fiberwise hcover
  -- the numerator fibre map
  set cOf : ℕ × ℤ → ℤ := fun p => (p.1 : ℤ) * (np : ℤ) + (dp : ℤ) * p.2 with hcOf
  have hcOfmem : ∀ p ∈ Sol, cOf p ∈
      DiophantineCount.numeratorRange (-α) δ ((dp * np * g : ℕ) : ℤ) := by
    intro p hp
    obtain ⟨-, habs⟩ := Finset.mem_filter.mp hp
    have hid : (p.1 : ℝ) / (d : ℝ) + (p.2 : ℝ) / (n : ℝ) =
        ((cOf p : ℤ) : ℝ) / ((dp * np * g : ℕ) : ℝ) := by
      have := frac_identity (d := d) (n := n) hd hn (p.1 : ℤ) p.2
      simpa only [hcOf, hdpdef, hnpdef, hgdef, Int.cast_natCast] using this
    have hconv : ((cOf p : ℤ) : ℝ) / ((((dp * np * g : ℕ)) : ℤ) : ℝ)
        = ((cOf p : ℤ) : ℝ) / ((dp * np * g : ℕ) : ℝ) := by push_cast; ring
    refine (DiophantineCount.mem_numeratorRange hMpos).mpr ?_
    rw [hconv, ← hid]
    have he : (-α - ((p.1 : ℝ) / (d : ℝ) + (p.2 : ℝ) / (n : ℝ))) =
        -(α + (p.1 : ℝ) / (d : ℝ) + (p.2 : ℝ) / (n : ℝ)) := by ring
    rw [he, abs_neg]
    exact habs
  have hfibg : ∀ c : ℤ, (Sol.filter (fun p : ℕ × ℤ => cOf p = c)).card ≤ g := by
    intro c
    have hcardm : (Sol.filter (fun p : ℕ × ℤ => cOf p = c)).card =
        ((Sol.filter (fun p : ℕ × ℤ => cOf p = c)).map natPairEmbed).card :=
      (Finset.card_map _).symm
    rw [hcardm]
    apply reduced_numerator_fiber_card (d := (dp : ℤ)) (n := (np : ℤ))
      (g := g) (c := c)
    · -- positivity of the reduced denominator
      rcases Nat.eq_zero_or_pos dp with h | h
      · rw [h] at hd'; simp at hd'; omega
      · exact_mod_cast h
    · -- coprimality
      exact Nat.isCoprime_iff_coprime.mpr hcop
    · intro p hp
      obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨hpS, hpc⟩ := Finset.mem_filter.mp hp'
      obtain ⟨hpP, habs⟩ := Finset.mem_filter.mp hpS
      obtain ⟨hbI, hmI⟩ := Finset.mem_product.mp hpP
      have hbI' : 1 ≤ p'.1 ∧ p'.1 ≤ d := by simpa using hbI
      have hPr1 : (natPairEmbed p').1 = (p'.1 : ℤ) := rfl
      have hPr2 : (natPairEmbed p').2 = p'.2 := rfl
      have hdg : (dp : ℤ) * (g : ℤ) = (d : ℤ) := by rw [← hd']; push_cast; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hPr1]; exact_mod_cast hbI'.1
      · rw [hPr1, hdg]; exact_mod_cast hbI'.2
      · rw [hPr1, hPr2]
        simp only [hcOf] at hpc
        simpa only [mul_comm] using hpc
  have hsum_le : Sol.card ≤ ∑ _c ∈ DiophantineCount.numeratorRange (-α) δ ((dp * np * g : ℕ) : ℤ), g := by
    rw [Finset.card_eq_sum_card_fiberwise hcOfmem]
    exact Finset.sum_le_sum (fun c _ => hfibg c)
  have hfin : Sol.card ≤ g * (DiophantineCount.numeratorRange (-α) δ ((dp * np * g : ℕ) : ℤ)).card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm] at hsum_le
    exact hsum_le
  -- assemble in `ℝ`
  have hSolcard : (Sol.card : ℝ) = ∑ b ∈ Finset.Icc 1 d,
      ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / (d : ℝ))) δ (n : ℤ)).card : ℝ) := by
    rw [hcard, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun b hb => by rw [hfib b hb])
  rw [← hSolcard]
  calc (Sol.card : ℝ) ≤ (g : ℝ) *
      ((DiophantineCount.numeratorRange (-α) δ ((dp * np * g : ℕ) : ℤ)).card : ℝ) := by
        exact_mod_cast hfin
    _ = _ := by rw [hgdef, hdpdef, hnpdef]


/-- The reduction: `count24` is at most the `(d,n)` sum of `gcd d n` times the numerator window
count of the *unshifted* `α` at the combined denominator `lcm d n = d' n' g`. -/
private theorem count24_le_sum_gcd {α δ : ℝ} {D N : ℝ} (hD : 0 < D) (hN : 0 < N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (count24 α D N δ : ℝ) ≤
      ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        (Nat.gcd d n : ℝ) *
          ((DiophantineCount.numeratorRange (-α) δ
            (((d / Nat.gcd d n) * (n / Nat.gcd d n) * Nat.gcd d n : ℕ) : ℤ)).card : ℝ) := by
  have hD0 : (0 : ℝ) ≤ D := hD.le
  have hN0 : (0 : ℝ) ≤ N := hN.le
  calc (count24 α D N δ : ℝ)
      = ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.Icc 1 d,
          ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
            ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / (d : ℝ))) δ (n : ℤ)).card : ℝ) := by
        rw [count24, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun b _ => pairCount_eq_sum_nat _ _ _ hN0)
    _ = ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          ∑ b ∈ Finset.Icc 1 d,
            ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / (d : ℝ))) δ (n : ℤ)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_comm
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro n hn
        exact inner_fiber_bound (by have := (Finset.mem_Ioc.mp hd).1; omega)
          (by have := (Finset.mem_Ioc.mp hn).1; omega) hα0 hα1 hδ hδ1


/-- The product of the reduced parts and the gcd is `d * n`. -/
private theorem lcm_data {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    d / Nat.gcd d n * (n / Nat.gcd d n) * Nat.gcd d n * Nat.gcd d n = d * n := by
  obtain ⟨hg, hd', hn', -⟩ := gcd_data hd hn
  calc
    d / Nat.gcd d n * (n / Nat.gcd d n) * Nat.gcd d n * Nat.gcd d n
        = (d / Nat.gcd d n * Nat.gcd d n) * (n / Nat.gcd d n * Nat.gcd d n) := by ring
    _ = d * n := by rw [hd', hn']

/-- The combined denominator of `inner_fiber_bound` is the least common multiple. -/
private theorem lcm_eq_form {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Nat.lcm d n = (d / Nat.gcd d n) * (n / Nat.gcd d n) * Nat.gcd d n := by
  obtain ⟨hg, hd', hn', -⟩ := gcd_data hd hn
  have hdn : d * n = ((d / Nat.gcd d n) * (n / Nat.gcd d n) * Nat.gcd d n) * Nat.gcd d n := by
    rw [← lcm_data hd hn]
  rw [Nat.lcm_eq_mul_div, hdn, Nat.mul_div_cancel _ hg]

/-- At most `(card M.divisors)^2` pairs of modulus ranges have least common multiple `M`. -/
private theorem fiber_card_lcm_le {D N : ℝ} {M : ℕ} (hM : M ≠ 0) :
    ((((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊)).filter
      (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = M)).card ≤ M.divisors.card ^ 2 := by
  classical
  have hmem : ∀ p ∈ ((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = M), p ∈ M.divisors ×ˢ M.divisors := by
    intro p hp
    obtain ⟨-, hpM⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨hpM ▸ Nat.dvd_lcm_left _ _, hM⟩
    · exact Nat.mem_divisors.mpr ⟨hpM ▸ Nat.dvd_lcm_right _ _, hM⟩
  calc (((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
        (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = M)).card
      ≤ (M.divisors ×ˢ M.divisors).card := Finset.card_le_card hmem
    _ = M.divisors.card ^ 2 := by rw [Finset.card_product, pow_two]

/-- The dyadic blocks of the numerator count are exactly the `pairCount` sums. -/
private theorem sum_blocks_eq_pairCount_sum (α δ : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, ∑ M ∈ Finset.Ioc ((2 : ℤ) ^ k) ((2 : ℤ) ^ (k + 1)),
        ((DiophantineCount.numeratorRange (-α) δ M).card : ℝ)) =
      ∑ k ∈ Finset.range K, (DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℝ) := by
  apply Finset.sum_congr rfl
  intro k _
  unfold DiophantineCount.pairCount DiophantineCount.denominatorRange
  have hcast : ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hfl : ⌊((2 ^ k : ℕ) : ℝ)⌋ = ((2 : ℤ) ^ k) := by
    rw [Int.floor_natCast]
    push_cast
    ring
  have hfl2 : ⌊2 * ((2 ^ k : ℕ) : ℝ)⌋ = ((2 : ℤ) ^ (k + 1)) := by
    rw [show (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) from by push_cast; ring,
      Int.floor_natCast]
    push_cast
    ring
  rw [hfl, hfl2, Nat.cast_sum]


/-- Every `M` with `2 ≤ M ≤ 2^K` lies in exactly one dyadic block `(2^k, 2^(k+1)]` with `k < K`. -/
private theorem dyadic_block_of_le_pow : ∀ (K M : ℕ), 2 ≤ M → M ≤ 2 ^ K →
    ∃ k, k < K ∧ 2 ^ k < M ∧ M ≤ 2 ^ (k + 1)
  | 0, M, h2, hM => by
    rw [Nat.pow_zero] at hM
    omega
  | K + 1, M, h2, hM => by
    by_cases h : M ≤ 2 ^ K
    · obtain ⟨k, hk1, hk2, hk3⟩ := dyadic_block_of_le_pow K M h2 h
      exact ⟨k, by omega, hk2, hk3⟩
    · push_neg at h
      exact ⟨K, by omega, h, hM⟩

/-- The dyadic blocks of the numerator count are exactly the `pairCount` sums, `ℕ`-indexed. -/
private theorem sum_blocks_nat_eq_pairCount_sum (α δ : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, ∑ M ∈ (Finset.Ioc (2 ^ k) (2 ^ (k + 1)) : Finset ℕ),
        ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) =
      ∑ k ∈ Finset.range K, (DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℝ) := by
  apply Finset.sum_congr rfl
  intro k _
  have hcast : ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hI : (Finset.Ioc (2 ^ k) (2 ^ (k + 1)) : Finset ℕ) =
      Finset.Ioc ⌊((2 ^ k : ℕ) : ℝ)⌋₊ ⌊2 * ((2 ^ k : ℕ) : ℝ)⌋₊ := by
    have h1 : ⌊((2 ^ k : ℕ) : ℝ)⌋₊ = 2 ^ k := Nat.floor_natCast _
    have h2 : ⌊2 * ((2 ^ k : ℕ) : ℝ)⌋₊ = 2 ^ (k + 1) := by
      rw [show (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) from by push_cast; ring]
      exact Nat.floor_natCast _
    rw [h1, h2]
  rw [hI, ← hcast, ← pairCount_eq_sum_nat (-α) ((2 : ℝ) ^ k) δ (by positivity)]

/-- The numerator-window count summed over any set of denominators below `2^K` is bounded by the
`pairCount` sums of the dyadic scales, plus the `M = 1` corner, which is itself `pairCount` at
the scale `1/2`. -/
private theorem sum_numRange_le_pairCount_sum (α δ : ℝ) {A : Finset ℕ}
    (hA1 : ∀ M ∈ A, 1 ≤ M) (K : ℕ) (hAK : ∀ M ∈ A, M < 2 ^ K) :
    (∑ M ∈ A, ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) ≤
      (∑ k ∈ Finset.range K, (DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℝ)) +
        (DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℝ) := by
  classical
  have hX1 : (DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℝ) =
      ((DiophantineCount.numeratorRange (-α) δ ((1 : ℕ) : ℤ)).card : ℝ) := by
    unfold DiophantineCount.pairCount DiophantineCount.denominatorRange
    have h1 : ⌊(1 : ℝ) / 2⌋ = 0 := by norm_num
    have h2 : ⌊2 * ((1 : ℝ) / 2)⌋ = 1 := by norm_num
    rw [h1, h2, show Finset.Ioc (0 : ℤ) 1 = {1} from by decide]
    simp
  set A' := A.filter (fun M => 1 < M) with hA'
  have hsplit : (∑ M ∈ A, ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) =
      (∑ M ∈ A', ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) +
        ∑ M ∈ A.filter (fun M => ¬ 1 < M),
          ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not A (fun M => 1 < M)
      (fun M => ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ))).symm
  have hsmall : (∑ M ∈ A.filter (fun M => ¬ 1 < M),
      ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) ≤
      ((DiophantineCount.numeratorRange (-α) δ ((1 : ℕ) : ℤ)).card : ℝ) := by
    have hsub : A.filter (fun M => ¬ 1 < M) ⊆ {1} := by
      intro M hM
      obtain ⟨hMA, hM1⟩ := Finset.mem_filter.mp hM
      have := hA1 M hMA
      simp only [Finset.mem_singleton]
      omega
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun M : ℕ => ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ))
      hsub (fun M _ _ => by positivity)
    simpa using h
  have hcover : A' ⊆ (Finset.range K).biUnion
      (fun k => (Finset.Ioc (2 ^ k) (2 ^ (k + 1)) : Finset ℕ)) := by
    intro M hM
    obtain ⟨hMA, hM1⟩ := Finset.mem_filter.mp hM
    obtain ⟨k, hk1, hk2, hk3⟩ := dyadic_block_of_le_pow K M (by omega) (le_of_lt (hAK M hMA))
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk1, Finset.mem_Ioc.mpr ⟨hk2, hk3⟩⟩
  have hstep : (∑ M ∈ A', ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) ≤
      ∑ M ∈ (Finset.range K).biUnion
        (fun k => (Finset.Ioc (2 ^ k) (2 ^ (k + 1)) : Finset ℕ)),
        ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun M : ℕ => ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) hcover ?_
    intro M _ _
    positivity
  have hdisj : (Finset.range K : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.Ioc (2 ^ k) (2 ^ (k + 1)) : Finset ℕ)) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    refine Finset.disjoint_left.mpr ?_
    intro x hxa hxb
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp hxa
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hxb
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have hp : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
      omega
    · have hp : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
      omega
  have hunion := Finset.sum_biUnion hdisj (f := fun M =>
    ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ))
  have h1 : (∑ M ∈ A', ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) ≤
      ∑ k ∈ Finset.range K, (DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℝ) := by
    refine hstep.trans ?_
    rw [hunion, sum_blocks_nat_eq_pairCount_sum]
  rw [hsplit]
  have h2 : (∑ M ∈ A.filter (fun M => ¬ 1 < M),
      ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)) ≤
      (DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℝ) := by
    rw [hX1]
    exact hsmall
  linarith

/-- `2 ^ Nat.log2 n ≤ n` for positive `n`. -/
private theorem pow_log2_le_nat {n : ℕ} (hn : 0 < n) : 2 ^ Nat.log2 n ≤ n :=
  (Nat.le_log2 (ne_of_gt hn)).mp le_rfl

/-- `n < 2 ^ (Nat.log2 n + 1)` for positive `n`. -/
private theorem lt_pow_succ_log2_nat {n : ℕ} (hn : 0 < n) : n < 2 ^ (Nat.log2 n + 1) := by
  by_contra hcon
  push_neg at hcon
  have h2 := (Nat.le_log2 (ne_of_gt hn)).mpr hcon
  omega

/-- The gcd factor of the counting estimate, split into dyadic buckets: on the bucket where
`Nat.log2 (gcd d n) = j` the gcd is at most `2 · 2^j`. -/
private theorem sum_gcd_mul_le_buckets {P : Finset (ℕ × ℕ)} {K : ℕ} {c : ℕ × ℕ → ℕ} {F : ℕ × ℕ → ℝ}
    (hc1 : ∀ p ∈ P, 1 ≤ c p) (hK : ∀ p ∈ P, c p < 2 ^ K) (hF : ∀ p, 0 ≤ F p) :
    (∑ p ∈ P, (c p : ℝ) * F p) ≤
      2 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j *
        ∑ p ∈ P.filter (fun p => Nat.log2 (c p) = j), F p := by
  classical
  have hmemK : ∀ p ∈ P, Nat.log2 (c p) ∈ Finset.range K := by
    intro p hP
    refine Finset.mem_range.mpr ?_
    by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ K ≤ 2 ^ Nat.log2 (c p) := Nat.pow_le_pow_right (by norm_num) hcon
    have h2 := pow_log2_le_nat (hc1 p hP)
    exact absurd (h1.trans h2) (not_le.mpr (hK p hP))
  have hpoint : ∀ p ∈ P, (c p : ℝ) * F p ≤ 2 * (2 : ℝ) ^ Nat.log2 (c p) * F p := by
    intro p hp
    have h1 : c p < 2 ^ (Nat.log2 (c p) + 1) := lt_pow_succ_log2_nat (hc1 p hp)
    have h2 : (2 : ℕ) ^ (Nat.log2 (c p) + 1) = 2 * 2 ^ Nat.log2 (c p) := by
      rw [pow_succ]; ring
    rw [h2] at h1
    have h3 : (c p : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log2 (c p) := by
      have h4 : (c p : ℝ) ≤ ((2 * 2 ^ Nat.log2 (c p) : ℕ) : ℝ) := by exact_mod_cast le_of_lt h1
      push_cast at h4
      linarith
    exact mul_le_mul_of_nonneg_right h3 (hF p)
  calc (∑ p ∈ P, (c p : ℝ) * F p)
      ≤ ∑ p ∈ P, 2 * (2 : ℝ) ^ Nat.log2 (c p) * F p := Finset.sum_le_sum hpoint
    _ = 2 * ∑ p ∈ P, (2 : ℝ) ^ Nat.log2 (c p) * F p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ = 2 * ∑ j ∈ Finset.range K,
          ∑ p ∈ P.filter (fun p => Nat.log2 (c p) = j), (2 : ℝ) ^ Nat.log2 (c p) * F p := by
        rw [Finset.sum_fiberwise_of_maps_to hmemK]
    _ = 2 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j *
          ∑ p ∈ P.filter (fun p => Nat.log2 (c p) = j), F p := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]


/-- One dyadic gcd bucket: the numerator-window counts at the combined denominators, with the
multiplicity of `M = lcm d n` paid for by `T ≥ (card M.divisors)^2`, reduce to the `pairCount`
sums below the bound `2 ^ K`. -/
private theorem bucket_le_pairCount_sum (α δ : ℝ) {D N : ℝ}
    {Pj : Finset (ℕ × ℕ)} {K : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hsub : ∀ p ∈ Pj, p ∈ (Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊)
    (hMpos : ∀ p ∈ Pj, Nat.lcm p.1 p.2 ≠ 0)
    (hM : ∀ p ∈ Pj, Nat.lcm p.1 p.2 < 2 ^ K)
    (hτ : ∀ p ∈ Pj, ((Nat.lcm p.1 p.2).divisors.card : ℝ) ^ 2 ≤ T) :
    (∑ p ∈ Pj, ((DiophantineCount.numeratorRange (-α) δ ((Nat.lcm p.1 p.2 : ℕ) : ℤ)).card : ℝ)) ≤
      T * ((∑ k ∈ Finset.range K, ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
        ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ)) := by
  classical
  set img := Pj.image (fun p => Nat.lcm p.1 p.2) with himg
  set X : ℕ → ℝ := fun M => ((DiophantineCount.numeratorRange (-α) δ ((M : ℕ) : ℤ)).card : ℝ)
    with hX
  have hXnonneg : ∀ M, 0 ≤ X M := fun M => by positivity
  have hmap : ∀ p ∈ Pj, Nat.lcm p.1 p.2 ∈ img := fun p hp => Finset.mem_image_of_mem _ hp
  have hconst : ∀ M ∈ img,
      (∑ p ∈ Pj.filter (fun p => Nat.lcm p.1 p.2 = M), X (Nat.lcm p.1 p.2)) =
        ((Pj.filter (fun p => Nat.lcm p.1 p.2 = M)).card : ℝ) * X M := by
    intro M _
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hfibre : ∀ M ∈ img,
      ((Pj.filter (fun p => Nat.lcm p.1 p.2 = M)).card : ℝ) * X M ≤ T * X M := by
    intro M hM'
    have hzero : M ≠ 0 := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM'
      exact hMpos p hp
    have hcard : ((Pj.filter (fun p => Nat.lcm p.1 p.2 = M)).card : ℝ) ≤ T := by
      have hle : (Pj.filter (fun p => Nat.lcm p.1 p.2 = M)).card ≤
          (((Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
            (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = M)).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨hpj, hpl⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hsub p hpj, hpl⟩
      refine (Nat.cast_le.mpr hle).trans ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM'
      have hb := fiber_card_lcm_le (D := D) (N := N) (M := Nat.lcm p.1 p.2) hzero
      exact le_trans (by exact_mod_cast hb) (hτ p hp)
    exact mul_le_mul_of_nonneg_right hcard (hXnonneg M)
  have hdisj : (img : Set ℕ).PairwiseDisjoint
      (fun M => Pj.filter (fun p => Nat.lcm p.1 p.2 = M)) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    refine Finset.disjoint_left.mpr ?_
    intro p hpa hpb
    have h1 : Nat.lcm p.1 p.2 = a := (Finset.mem_filter.mp hpa).2
    have h2 : Nat.lcm p.1 p.2 = b := (Finset.mem_filter.mp hpb).2
    exact hab (h1.symm.trans h2)
  have hbiU : img.biUnion (fun M => Pj.filter (fun p => Nat.lcm p.1 p.2 = M)) = Pj := by
    ext p
    constructor
    · intro hp
      obtain ⟨M, -, hp'⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp hp').1
    · intro hp
      exact Finset.mem_biUnion.mpr
        ⟨Nat.lcm p.1 p.2, Finset.mem_image_of_mem _ hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  have hstep1 : (∑ p ∈ Pj, X (Nat.lcm p.1 p.2)) ≤ T * ∑ M ∈ img, X M := by
    rw [← hbiU, Finset.sum_biUnion hdisj, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro M hM'
    rw [hconst M hM']
    exact hfibre M hM'
  have himg1 : ∀ M ∈ img, 1 ≤ M := by
    intro M hM'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM'
    have h := hMpos p hp
    omega
  have himgK : ∀ M ∈ img, M < 2 ^ K := by
    intro M hM'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hM'
    exact hM p hp
  have hstep2 := sum_numRange_le_pairCount_sum α δ himg1 K himgK
  have hstep2' : (∑ M ∈ img, X M) ≤
      (∑ k ∈ Finset.range K, ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
        ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ) := by
    simpa only [hX, Nat.cast_sum] using hstep2
  calc (∑ p ∈ Pj, X (Nat.lcm p.1 p.2)) ≤ T * ∑ M ∈ img, X M := hstep1
    _ ≤ T * ((∑ k ∈ Finset.range K, ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
        ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2' hT


/-- Lemma 2.3 applied to `-α`: the rational approximation `a/q` of `α` also controls the
`pairCount` at the unshifted centre `-α`. -/
private theorem pairCount_bound_of_h23 (h23 : DiophantineCount.Lemma23Bound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      ∀ M δ : ℝ, 0 < M → 0 < δ →
        (DiophantineCount.pairCount (-α) M δ : ℝ) ≤
          C * M * (1 / (q : ℝ) + q * δ + δ * M) := by
  obtain ⟨C, hC, hb⟩ := h23
  refine ⟨C, hC, ?_⟩
  intro α a q hq hc ha M δ hM hδ
  have hc' : Int.gcd (-a) q = 1 := by
    have hcop : IsCoprime (a : ℤ) (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hc
    have hcop' : IsCoprime (-a : ℤ) (q : ℤ) := hcop.neg_left
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop'
  have ha' : |(-α) - ((-a : ℤ) : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
    have he : (-α) - ((-a : ℤ) : ℝ) / (q : ℝ) = -(α - (a : ℝ) / (q : ℝ)) := by
      push_cast
      ring
    rw [he, abs_neg]
    exact ha
  exact hb (-α) (-a) q hq hc' ha' M δ hM hδ

/-- The geometric sums behind the dyadic `pairCount` budget, by induction on the number of
scales. -/
private theorem geom_pairCount_sum {C : ℝ} (hC : 0 ≤ C) {q : ℕ} {δ : ℝ} (hq : 1 ≤ q) (hδ : 0 ≤ δ) :
    ∀ K : ℕ,
      (∑ k ∈ Finset.range K, C * (2 : ℝ) ^ k *
          (1 / (q : ℝ) + q * δ + δ * (2 : ℝ) ^ k)) ≤
        C * ((1 / (q : ℝ) + q * δ) * 2 ^ K + δ * 4 ^ K) := by
  intro K
  have hA : (0 : ℝ) ≤ 1 / (q : ℝ) + q * δ := by positivity
  have h4k : ∀ k : ℕ, (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
    intro k
    rw [← mul_pow]
    norm_num
  have hterm : ∀ k : ℕ, C * (2 : ℝ) ^ k * (1 / (q : ℝ) + q * δ + δ * (2 : ℝ) ^ k) =
      C * ((1 / (q : ℝ) + q * δ) * (2 : ℝ) ^ k + δ * (4 : ℝ) ^ k) := by
    intro k
    rw [← h4k k]
    ring
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
    positivity
  | succ K ih =>
    rw [Finset.sum_range_succ, hterm K]
    have h2 : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
    have h4 : (4 : ℝ) ^ (K + 1) = 4 * 4 ^ K := by rw [pow_succ]; ring
    have h4n : (0 : ℝ) ≤ 4 ^ K := by positivity
    have h2n : (0 : ℝ) ≤ 2 ^ K := by positivity
    rw [h2, h4]
    have hexp : C * ((1 / (q : ℝ) + q * δ) * (2 * 2 ^ K) + δ * (4 * 4 ^ K)) =
        C * ((1 / (q : ℝ) + q * δ) * 2 ^ K + δ * 4 ^ K) +
          C * ((1 / (q : ℝ) + q * δ) * 2 ^ K + δ * 4 ^ K) +
            C * (δ * 2 * 4 ^ K) := by ring
    rw [hexp]
    have hstep : 0 ≤ C * (δ * 2 * 4 ^ K) := by positivity
    linarith


/-- `count24` as a single sum over the product of the modulus ranges, at the combined
denominator `lcm d n`. -/
private theorem count24_le_product_sum {α δ : ℝ} {D N : ℝ} (hD : 0 < D) (hN : 0 < N)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (count24 α D N δ : ℝ) ≤
      ∑ p ∈ (Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊),
        (Nat.gcd p.1 p.2 : ℝ) *
          ((DiophantineCount.numeratorRange (-α) δ (((Nat.lcm p.1 p.2 : ℕ) : ℕ) : ℤ)).card : ℝ) := by
  refine (count24_le_sum_gcd hD hN hα0 hα1 hδ hδ1).trans (le_of_eq ?_)
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun n hn => ?_))
  have hd0 : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
  rw [← lcm_eq_form hd0 hn0]

/-- `Nat.log2` is at most `log n / log 2`. -/
private theorem nat_log2_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hpos : 0 < n := hn
  have h2k : 2 ^ Nat.log2 n ≤ n := pow_log2_le_nat hpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  have h1 : Real.log (((2 : ℕ) : ℝ) ^ Nat.log2 n) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2k
  rw [Real.log_pow] at h1
  simp only [Nat.cast_ofNat] at h1
  rw [le_div_iff₀ hlog2pos]
  linarith [h1]

/-- `Nat.log2 n` is bounded by a fixed multiple of `n ^ (ε/2)`. -/
private theorem nat_log2_le_rpow_div {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (Nat.log2 n : ℝ) ≤ (n : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) := by
  have h1 := nat_log2_le_log_div hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hε2 : 0 < ε / 2 := by linarith
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (ε / 2) / (ε / 2) :=
    Real.log_le_rpow_div hnpos.le hε2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (n : ℝ) / Real.log 2 ≤
      ((n : ℝ) ^ (ε / 2) / (ε / 2)) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog hlog2pos.le
  have he : ((n : ℝ) ^ (ε / 2) / (ε / 2)) / Real.log 2 =
      (n : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) := by
    rw [div_div]
  linarith [h1, hdiv, he]


/-- The squared divisor-count of any modulus at most `4 X^2` is bounded by one constant times
`X ^ (ε/2)`. -/
private theorem card_divisors_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (X : ℝ) (M : ℕ), 1 ≤ X → (M : ℝ) ≤ 4 * X ^ 2 →
      ((M.divisors.card : ℝ)) ^ 2 ≤ κ * X ^ (ε / 2) := by
  obtain ⟨Cτ, hCτ, hb⟩ := card_divisors_le_rpow (show 0 < ε / 8 by linarith)
  refine ⟨(Cτ * (4 : ℝ) ^ (ε / 8)) ^ 2, by positivity, ?_⟩
  intro X M hX hM
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have h1 : (M.divisors.card : ℝ) ≤ Cτ * (M : ℝ) ^ (ε / 8) := hb M
  have h1' : (0 : ℝ) ≤ (M.divisors.card : ℝ) := by positivity
  have h2 : (M : ℝ) ^ (ε / 8) ≤ (4 * X ^ 2) ^ (ε / 8) :=
    Real.rpow_le_rpow (by positivity) hM (by linarith)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have h3 : (4 * X ^ 2) ^ (ε / 8) = (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    rw [show X ^ 2 = X ^ (2 : ℝ) from (Real.rpow_natCast X 2).symm, ← Real.rpow_mul hX0]
    rw [show (2 : ℝ) * (ε / 8) = ε / 4 by ring]
  have h4 : (M.divisors.card : ℝ) ≤ Cτ * (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4) := by
    have := h1.trans (mul_le_mul_of_nonneg_left h2 hCτ.le)
    rw [h3] at this
    calc (M.divisors.card : ℝ) ≤ Cτ * ((4 : ℝ) ^ (ε / 8) * X ^ (ε / 4)) := this
      _ = Cτ * (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4) := by ring
  have h5 : (0 : ℝ) ≤ Cτ * (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4) := by positivity
  have h6 : ((M.divisors.card : ℝ)) ^ 2 ≤ (Cτ * (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4)) ^ 2 :=
    pow_le_pow_left₀ h1' h4 2
  have h7a : (X ^ (ε / 4)) ^ 2 = X ^ (ε / 2) := by
    rw [pow_two, show X ^ (ε / 4) * X ^ (ε / 4) = X ^ (ε / 4 + ε / 4) from
      (Real.rpow_add hXpos _ _).symm]
    congr 1
    ring
  have h7 : (Cτ * (4 : ℝ) ^ (ε / 8) * X ^ (ε / 4)) ^ 2 =
      (Cτ * (4 : ℝ) ^ (ε / 8)) ^ 2 * X ^ (ε / 2) := by
    rw [mul_pow, mul_pow, h7a]
  linarith [h6, h7]


/-- The dyadic scale attached to the gcd bucket `j` dominates every `lcm d n` in that bucket. -/
private theorem lcm_lt_pow_bucket {D N : ℝ} {d n j : ℕ} (hD : 0 < D) (hN : 0 < N)
    (hd : 0 < d) (hn : 0 < n) (hdD : (d : ℝ) ≤ 2 * D) (hnN : (n : ℝ) ≤ 2 * N)
    (h2j : 2 ^ j ≤ Nat.gcd d n) :
    Nat.lcm d n < 2 ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) := by
  set x : ℝ := 4 * D * N / (2 : ℝ) ^ j with hx
  set m : ℕ := ⌊x⌋₊ with hm
  have hg : 0 < Nat.gcd d n := Nat.gcd_pos_of_pos_left n hd
  have hg0 : (0 : ℝ) < (Nat.gcd d n : ℝ) := by exact_mod_cast hg
  have hge : (2 : ℝ) ^ j ≤ (Nat.gcd d n : ℝ) := by exact_mod_cast h2j
  have heq : (Nat.gcd d n : ℝ) * (Nat.lcm d n : ℝ) = (d : ℝ) * (n : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d n
  have hlcm : (Nat.lcm d n : ℝ) = (d : ℝ) * (n : ℝ) / (Nat.gcd d n : ℝ) := by
    rw [eq_div_iff (ne_of_gt hg0), mul_comm]
    exact heq
  have hlcm_le : (Nat.lcm d n : ℝ) ≤ x := by
    rw [hlcm, hx]
    have h1 : (d : ℝ) * (n : ℝ) / (Nat.gcd d n : ℝ) ≤ (d : ℝ) * (n : ℝ) / (2 : ℝ) ^ j := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    have h2 : (d : ℝ) * (n : ℝ) ≤ 2 * D * (2 * N) := by nlinarith
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ j * (4 * D * N / (2 : ℝ) ^ j) = 4 * D * N := by
      field_simp
    nlinarith [this]
  have hx1 : (1 : ℝ) ≤ x := by
    have hl1 : (1 : ℝ) ≤ (Nat.lcm d n : ℝ) := by
      have : 0 < Nat.lcm d n := Nat.pos_of_ne_zero (by
        intro h
        have := Nat.lcm_eq_zero_iff.mp h
        omega)
      exact_mod_cast this
    linarith
  have hm1 : 1 ≤ m := by
    rw [hm]
    refine Nat.one_le_iff_ne_zero.mpr ?_
    intro hzero
    have : x < 1 := by
      have := Nat.floor_eq_zero.mp hzero
      linarith
    linarith
  have hmpos : 0 < m := hm1
  have hmlt : m < 2 ^ (Nat.log2 m + 1) := lt_pow_succ_log2_nat hmpos
  have hmR : (m : ℝ) ≤ x := by
    rw [hm]
    exact Nat.floor_le (by rw [hx]; positivity)
  have hxlt : x < 2 * (m : ℝ) := by
    have h1 : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : ((⌊x⌋₊ : ℕ) : ℝ) = (m : ℝ) := by rw [hm]
    rw [h2] at h1
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have hscale : ((2 ^ (Nat.log2 m + 2) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ (Nat.log2 m + 1) := by
    rw [show Nat.log2 m + 2 = Nat.log2 m + 1 + 1 from by ring, pow_succ]
    push_cast
    ring
  have hplt : (m : ℝ) < (2 : ℝ) ^ (Nat.log2 m + 1) := by exact_mod_cast hmlt
  have : (Nat.lcm d n : ℝ) < ((2 ^ (Nat.log2 m + 2) : ℕ) : ℝ) := by
    rw [hscale]
    linarith
  calc Nat.lcm d n < 2 ^ (Nat.log2 m + 2) := by exact_mod_cast this
    _ = 2 ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) := by rw [hm, hx]

/-- The reciprocal bound: the bucket scale is at most `16 D N / 2^j + 4`. -/
private theorem pow_bucket_le {D N : ℝ} (hD : 0 < D) (hN : 0 < N) (j : ℕ) :
    ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ≤
      16 * D * N / (2 : ℝ) ^ j + 4 := by
  set m : ℕ := ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ with hm
  have h1 : (2 : ℝ) ^ Nat.log2 m ≤ (m : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]; simp
    · have := pow_log2_le_nat h
      have : ((2 : ℝ) ^ Nat.log2 m) ≤ (m : ℝ) := by exact_mod_cast this
      linarith
  have h2 : (2 : ℝ) ^ (Nat.log2 m + 2) = 4 * (2 : ℝ) ^ Nat.log2 m := by
    rw [show Nat.log2 m + 2 = Nat.log2 m + 1 + 1 from by ring, pow_succ, pow_succ]
    ring
  have h3 : (m : ℝ) ≤ 4 * D * N / (2 : ℝ) ^ j := Nat.floor_le (by positivity)
  rw [h2]
  have h4 : 4 * (2 : ℝ) ^ Nat.log2 m ≤ 4 * ((m : ℝ) + 1) := by linarith
  have hid : 4 * (4 * D * N / (2 : ℝ) ^ j) = 16 * D * N / (2 : ℝ) ^ j := by ring
  have h5 : 4 * ((m : ℝ) + 1) ≤ 16 * D * N / (2 : ℝ) ^ j + 4 := by linarith [h3, hid]
  linarith


/-- `Nat.log2 ⌊2N⌋₊ + 2` is at most `(2^(ε/2)/((ε/2) log 2) + 2) X^(ε/2)`. -/
private theorem nat_log2_twoN_le {ε : ℝ} (hε : 0 < ε) {X N : ℝ} (hX : 1 ≤ X) (hN : 0 < N)
    (hNX : N ≤ X) :
    ((Nat.log2 ⌊2 * N⌋₊ : ℕ) : ℝ) + 2 ≤
      ((2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) + 2) * X ^ (ε / 2) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX0 : 0 < X := by linarith
  by_cases hN2 : ⌊2 * N⌋₊ = 0
  · have hzero : ((Nat.log2 ⌊2 * N⌋₊ : ℕ) : ℝ) = 0 := by rw [hN2]; simp
    rw [hzero]
    have hXp : (1 : ℝ) ≤ X ^ (ε / 2) := Real.one_le_rpow hX hε2.le
    have hlam0 : (0 : ℝ) ≤ (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) := by positivity
    have : (2 : ℝ) ≤ ((2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) + 2) * X ^ (ε / 2) := by
      nlinarith
    linarith
  have hNpos : 1 ≤ ⌊2 * N⌋₊ := by omega
  have h1 : ((Nat.log2 ⌊2 * N⌋₊ : ℕ) : ℝ) ≤
      ((⌊2 * N⌋₊ : ℝ)) ^ (ε / 2) / ((ε / 2) * Real.log 2) :=
    nat_log2_le_rpow_div hNpos hε
  have h2 : ((⌊2 * N⌋₊ : ℝ)) ≤ 2 * X := by
    have hh : ((⌊2 * N⌋₊ : ℕ) : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
    nlinarith
  have h3 : ((⌊2 * N⌋₊ : ℝ)) ^ (ε / 2) ≤ (2 * X) ^ (ε / 2) :=
    Real.rpow_le_rpow (by positivity) h2 hε2.le
  have h4 : (2 * X) ^ (ε / 2) = (2 : ℝ) ^ (ε / 2) * X ^ (ε / 2) :=
    Real.mul_rpow (by norm_num) hX0.le
  have hpos : (0 : ℝ) < (ε / 2) * Real.log 2 := by positivity
  have h3' : ((⌊2 * N⌋₊ : ℝ)) ^ (ε / 2) ≤ (2 : ℝ) ^ (ε / 2) * X ^ (ε / 2) := by
    rw [← h4]
    exact h3
  have h5 : ((⌊2 * N⌋₊ : ℝ)) ^ (ε / 2) / ((ε / 2) * Real.log 2) ≤
      (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) * X ^ (ε / 2) := by
    have hstep : ((⌊2 * N⌋₊ : ℝ)) ^ (ε / 2) / ((ε / 2) * Real.log 2) ≤
        ((2 : ℝ) ^ (ε / 2) * X ^ (ε / 2)) / ((ε / 2) * Real.log 2) :=
      div_le_div_of_nonneg_right h3' hpos.le
    have he : ((2 : ℝ) ^ (ε / 2) * X ^ (ε / 2)) / ((ε / 2) * Real.log 2) =
        (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) * X ^ (ε / 2) := by
      field_simp
    rw [he] at hstep
    exact hstep
  have h7 : (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) * X ^ (ε / 2) + 2 ≤
      ((2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) + 2) * X ^ (ε / 2) := by
    have hXp : (1 : ℝ) ≤ X ^ (ε / 2) := Real.one_le_rpow hX hε2.le
    have hlam0 : (0 : ℝ) ≤ (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2) := by positivity
    nlinarith
  linarith [h1, h5, h7]

/-- The geometric sums used to price the dyadic bucket budget. -/
private theorem sum_two_pow (L : ℕ) :
    (∑ j ∈ Finset.range L, (2 : ℝ) ^ j) = (2 : ℝ) ^ L - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring


set_option maxHeartbeats 2000000 in
/-- Page 5 equation 6, the sparse case: the reduction of `count24` to the dyadic bucket budget.
The only step still missing is the scalar estimate of the double sum against
`X^ε N D (1/q + qδ + δND)`. -/
private theorem counting24_le_bucketed (h23 : DiophantineCount.Lemma23Bound) :
    ∀ ε : ℝ, 0 < ε → ∃ C₂ κ lam : ℝ, 0 < C₂ ∧ 0 < κ ∧ 0 ≤ lam ∧
      (∀ X N : ℝ, 1 ≤ X → 0 < N → N ≤ X →
        ((Nat.log2 ⌊2 * N⌋₊ : ℕ) : ℝ) + 2 ≤ (lam + 2) * X ^ (ε / 2)) ∧
      ∀ X D N α δ : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X → 0 ≤ α → α ≤ 1 →
        0 < δ → N * δ < 1 / 4 →
        ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
          |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
          (count24 α D N δ : ℝ) ≤
            2 * ∑ j ∈ Finset.range (Nat.log2 ⌊2 * N⌋₊ + 2),
              (2 : ℝ) ^ j * (κ * X ^ (ε / 2) * (C₂ * (((1 / (q : ℝ) + q * δ) *
                ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
                δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
  intro ε hε
  obtain ⟨C₂, hC₂, hb2⟩ := pairCount_bound_of_h23 h23
  obtain ⟨κ, hκ, hbκ⟩ := card_divisors_sq_le_rpow hε
  have hε2 : 0 < ε / 2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₂, κ, (2 : ℝ) ^ (ε / 2) / ((ε / 2) * Real.log 2), hC₂, hκ, by positivity, ?_, ?_⟩
  · intro X N hX hN hNX
    exact nat_log2_twoN_le hε hX hN hNX
  intro X D N α δ hX hD hDX hN hNX hα0 hα1 hδ hNδ a q hq hc ha
  have hX0 : 0 < X := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  -- degenerate modulus range: the count vanishes
  rcases Nat.eq_zero_or_pos ⌊2 * D⌋₊ with hDz | hDp
  · have hzero : count24 α D N δ = 0 := by
      rw [count24]
      apply Finset.sum_eq_zero
      intro d hd
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hd
      exfalso
      omega
    rw [hzero]
    push_cast
    have hXp : (0 : ℝ) ≤ X ^ (ε / 2) := Real.rpow_nonneg hX0.le _
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) + q * δ := by positivity
    have hd0 : (0 : ℝ) ≤ δ := hδ.le
    have hk0 : (0 : ℝ) ≤ κ := hκ.le
    have hc20 : (0 : ℝ) ≤ C₂ := hC₂.le
    positivity
  rcases Nat.eq_zero_or_pos ⌊2 * N⌋₊ with hNz | hNp
  · have hpc0 : ∀ β : ℝ, DiophantineCount.pairCount β N δ = 0 := by
      intro β
      have hsum := pairCount_eq_sum_nat β N δ hN.le
      have hz : (∑ m ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          ((DiophantineCount.numeratorRange β δ (m : ℤ)).card : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
        exfalso
        omega
      have hcast : (DiophantineCount.pairCount β N δ : ℝ) = 0 := by rw [hsum, hz]
      exact_mod_cast hcast

    have hzero : count24 α D N δ = 0 := by
      rw [count24]
      apply Finset.sum_eq_zero
      intro d _
      apply Finset.sum_eq_zero
      intro b _
      exact hpc0 _
    rw [hzero]
    push_cast
    have hXp : (0 : ℝ) ≤ X ^ (ε / 2) := Real.rpow_nonneg hX0.le _
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) + q * δ := by positivity
    have hd0 : (0 : ℝ) ≤ δ := hδ.le
    have hk0 : (0 : ℝ) ≤ κ := hκ.le
    have hc20 : (0 : ℝ) ≤ C₂ := hC₂.le
    positivity
  have hDhalf : (1 / 2 : ℝ) ≤ D := by
    have h1 : (1 : ℝ) ≤ (⌊2 * D⌋₊ : ℝ) := by exact_mod_cast hDp
    have h2 : (⌊2 * D⌋₊ : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
    linarith
  have hNhalf : (1 / 2 : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ (⌊2 * N⌋₊ : ℝ) := by exact_mod_cast hNp
    have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
    linarith
  have hδ1 : δ ≤ 1 := by nlinarith
  set S : Finset ℕ := Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊ with hS
  set R : Finset ℕ := Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ with hR
  set P : Finset (ℕ × ℕ) := S ×ˢ R with hP
  set gg : ℕ × ℕ → ℕ := fun p => Nat.gcd p.1 p.2 with hgg
  set FF : ℕ × ℕ → ℝ :=
    fun p => ((DiophantineCount.numeratorRange (-α) δ ((Nat.lcm p.1 p.2 : ℕ) : ℤ)).card : ℝ)
    with hFF
  set K : ℕ := Nat.log2 ⌊2 * N⌋₊ + 2 with hK
  set TT : ℝ := κ * X ^ (ε / 2) with hTT
  have hTT0 : 0 ≤ TT := by rw [hTT]; positivity
  have hstep1 : (count24 α D N δ : ℝ) ≤ ∑ p ∈ P, (gg p : ℝ) * FF p := by
    have := count24_le_product_sum hD hN hα0 hα1 hδ hδ1
    simpa only [hS, hR, hP, hgg, hFF] using this
  have hg1 : ∀ p ∈ P, 1 ≤ gg p := by
    intro p hp
    have h1 : 1 ≤ p.1 := by
      have := (Finset.mem_Ioc.mp (Finset.mem_product.mp hp).1).1
      omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.gcd_ne_zero_left (by omega))
  have hgK : ∀ p ∈ P, gg p < 2 ^ K := by
    intro p hp
    have h2 : p.2 ≤ ⌊2 * N⌋₊ := (Finset.mem_Ioc.mp (Finset.mem_product.mp hp).2).2
    have hp2 : 0 < p.2 := by
      have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hp).2).1
      omega
    have hgle : gg p ≤ p.2 := Nat.gcd_le_right _ hp2
    have hlt : ⌊2 * N⌋₊ < 2 ^ K := by
      rw [hK]
      have h := lt_pow_succ_log2_nat hNp
      rw [show Nat.log2 ⌊2 * N⌋₊ + 2 = Nat.log2 ⌊2 * N⌋₊ + 1 + 1 from by ring, pow_succ]
      have hpos : (0 : ℕ) < 2 ^ (Nat.log2 ⌊2 * N⌋₊ + 1) := by positivity
      omega
    omega
  have hstep2 : ∑ p ∈ P, (gg p : ℝ) * FF p ≤
      2 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j *
        ∑ p ∈ P.filter (fun p => Nat.log2 (gg p) = j), FF p :=
    sum_gcd_mul_le_buckets hg1 hgK (fun p => by positivity)
  have hbucket : ∀ j ∈ Finset.range K,
      (2 : ℝ) ^ j * (∑ p ∈ P.filter (fun p => Nat.log2 (gg p) = j), FF p) ≤
        (2 : ℝ) ^ j * (TT * (C₂ * (((1 / (q : ℝ) + q * δ) *
          ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
          δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
    intro j _
    set Kj : ℕ := Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2 with hKj
    set Pj : Finset (ℕ × ℕ) := P.filter (fun p => Nat.log2 (gg p) = j) with hPj
    have hsub : ∀ p ∈ Pj, p ∈ (Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊) ×ˢ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hMpos : ∀ p ∈ Pj, Nat.lcm p.1 p.2 ≠ 0 := by
      intro p hp
      have h1 : 1 ≤ p.1 := by
        have := (Finset.mem_Ioc.mp (Finset.mem_product.mp (hsub p hp)).1).1
        omega
      have h2 : 1 ≤ p.2 := by
        have := (Finset.mem_Ioc.mp (Finset.mem_product.mp (hsub p hp)).2).1
        omega
      exact Nat.lcm_ne_zero (by omega) (by omega)
    have hM : ∀ p ∈ Pj, Nat.lcm p.1 p.2 < 2 ^ Kj := by
      intro p hp
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have h1 : 1 ≤ p.1 := by
        have := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).1).1
        omega
      have h2 : 1 ≤ p.2 := by
        have := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).2).1
        omega
      have h3 : 2 ^ j ≤ Nat.gcd p.1 p.2 := by
        have hlogj : Nat.log2 (gg p) = j := (Finset.mem_filter.mp hp).2
        have hpos : 0 < gg p := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
        rw [← hlogj]
        exact pow_log2_le_nat hpos
      have hdD : (p.1 : ℝ) ≤ 2 * D := by
        have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).1).2
        have h2' : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
        exact le_trans (by exact_mod_cast hh) h2'
      have hnN : (p.2 : ℝ) ≤ 2 * N := by
        have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).2).2
        have h2' : ((⌊2 * N⌋₊ : ℕ) : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
        exact le_trans (by exact_mod_cast hh) h2'
      exact lcm_lt_pow_bucket hD hN (by omega) (by omega) hdD hnN h3
    have hτ : ∀ p ∈ Pj, ((Nat.lcm p.1 p.2).divisors.card : ℝ) ^ 2 ≤ TT := by
      intro p hp
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hlcm_le : ((Nat.lcm p.1 p.2 : ℕ) : ℝ) ≤ 4 * X ^ 2 := by
        have hp1 : 0 < p.1 := by
          have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).1).1
          omega
        have hp2 : 0 < p.2 := by
          have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).2).1
          omega
        have hle : Nat.lcm p.1 p.2 ≤ p.1 * p.2 :=
          Nat.le_of_dvd (by positivity) (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
        have h1' : (p.1 : ℝ) ≤ 2 * D := by
          have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).1).2
          have h2' : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
          exact le_trans (by exact_mod_cast hh) h2'
        have h2' : (p.2 : ℝ) ≤ 2 * N := by
          have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hpP).2).2
          have h3' : ((⌊2 * N⌋₊ : ℕ) : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
          exact le_trans (by exact_mod_cast hh) h3'
        have h4 : (p.1 : ℝ) * (p.2 : ℝ) ≤ 4 * X ^ 2 := by nlinarith
        calc ((Nat.lcm p.1 p.2 : ℕ) : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; ring
          _ ≤ 4 * X ^ 2 := h4
      have := hbκ X (Nat.lcm p.1 p.2) (by linarith) hlcm_le
      simpa only [hTT] using this
    have hbB := bucket_le_pairCount_sum (α := α) (δ := δ) (D := D) (N := N)
      (Pj := Pj) (K := Kj) (T := TT) hTT0 hsub hMpos hM hτ
    have hpc : ∀ k ∈ Finset.range Kj,
        ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ) ≤
          C₂ * (2 : ℝ) ^ k * (1 / (q : ℝ) + q * δ + δ * (2 : ℝ) ^ k) := by
      intro k _
      exact hb2 α a q hq hc ha ((2 : ℝ) ^ k) δ (by positivity) hδ
    have hgeom := geom_pairCount_sum hC₂.le hq hδ.le Kj
    have hcorner : ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ) ≤
        C₂ * (1 / 2) * (1 / (q : ℝ) + q * δ + δ * (1 / 2)) := by
      have := hb2 α a q hq hc ha ((1 : ℝ) / 2) δ (by norm_num) hδ
      calc ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ)
          ≤ C₂ * ((1 : ℝ) / 2) * (1 / (q : ℝ) + q * δ + δ * ((1 : ℝ) / 2)) := this
        _ = C₂ * (1 / 2) * (1 / (q : ℝ) + q * δ + δ * (1 / 2)) := by ring
    have hinner : (∑ k ∈ Finset.range Kj,
        ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
        ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ) ≤
        C₂ * (((1 / (q : ℝ) + q * δ) * ((2 : ℝ) ^ Kj + 1 / 2)) +
          δ * (((2 : ℝ) ^ Kj) ^ 2 + 1 / 4)) := by
      have h1 : (∑ k ∈ Finset.range Kj,
          ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) ≤
          ∑ k ∈ Finset.range Kj, C₂ * (2 : ℝ) ^ k *
            (1 / (q : ℝ) + q * δ + δ * (2 : ℝ) ^ k) :=
        Finset.sum_le_sum (fun k hk => hpc k hk)
      have h2 : (∑ k ∈ Finset.range Kj, C₂ * (2 : ℝ) ^ k *
          (1 / (q : ℝ) + q * δ + δ * (2 : ℝ) ^ k)) ≤
          C₂ * ((1 / (q : ℝ) + q * δ) * 2 ^ Kj + δ * 4 ^ Kj) := hgeom
      have h4eq : ((4 : ℝ) ^ Kj) = ((2 : ℝ) ^ Kj) ^ 2 := by
        rw [pow_two, ← mul_pow]
        norm_num
      have hexp : C₂ * (1 / 2) * (1 / (q : ℝ) + q * δ + δ * (1 / 2)) =
          C₂ * ((1 / (q : ℝ) + q * δ) * (1 / 2) + δ * (1 / 4)) := by ring
      rw [h4eq] at h2
      rw [hexp] at hcorner
      nlinarith [h1, h2, hcorner]
    have hbB' : (∑ p ∈ Pj, FF p) ≤ TT * ((∑ k ∈ Finset.range Kj,
        ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
        ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ)) := by
      simpa only [hFF] using hbB
    have hPj' : P.filter (fun p => Nat.log2 (gg p) = j) = Pj := rfl
    calc (2 : ℝ) ^ j * (∑ p ∈ P.filter (fun p => Nat.log2 (gg p) = j), FF p)
        = (2 : ℝ) ^ j * (∑ p ∈ Pj, FF p) := by rw [hPj']
      _ ≤ (2 : ℝ) ^ j * (TT * ((∑ k ∈ Finset.range Kj,
            ((DiophantineCount.pairCount (-α) ((2 : ℝ) ^ k) δ : ℕ) : ℝ)) +
            ((DiophantineCount.pairCount (-α) ((1 : ℝ) / 2) δ : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hbB' (by positivity)
      _ ≤ (2 : ℝ) ^ j * (TT * (C₂ * (((1 / (q : ℝ) + q * δ) *
            ((2 : ℝ) ^ Kj + 1 / 2)) + δ * (((2 : ℝ) ^ Kj) ^ 2 + 1 / 4)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hTT0) (by positivity)
      _ = (2 : ℝ) ^ j * (TT * (C₂ * (((1 / (q : ℝ) + q * δ) *
            ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
            δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
          rw [hKj]

  have hsum_bucket : ∑ j ∈ Finset.range K, (2 : ℝ) ^ j *
      (∑ p ∈ P.filter (fun p => Nat.log2 (gg p) = j), FF p) ≤
      ∑ j ∈ Finset.range K, (2 : ℝ) ^ j * (TT * (C₂ * (((1 / (q : ℝ) + q * δ) *
        ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
        δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) :=
    Finset.sum_le_sum hbucket
  calc (count24 α D N δ : ℝ) ≤ ∑ p ∈ P, (gg p : ℝ) * FF p := hstep1
    _ ≤ 2 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j *
        ∑ p ∈ P.filter (fun p => Nat.log2 (gg p) = j), FF p := hstep2
    _ ≤ 2 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j * (TT * (C₂ * (((1 / (q : ℝ) + q * δ) *
        ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
        δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
        have := mul_le_mul_of_nonneg_left hsum_bucket (by norm_num : (0:ℝ) ≤ 2)
        linarith [this]
    _ = 2 * ∑ j ∈ Finset.range (Nat.log2 ⌊2 * N⌋₊ + 2),
        (2 : ℝ) ^ j * (κ * X ^ (ε / 2) * (C₂ * (((1 / (q : ℝ) + q * δ) *
          ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
          δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
        rw [hK, hTT]


set_option maxHeartbeats 2000000 in
/-- The scalar estimate closing `counting24_sparse`: the dyadic bucket budget is at most
`C X^ε N D (1/q + qδ + δND)`. -/
private theorem bucketed_sum_le {C₂ κ lam : ℝ} (hC₂ : 0 < C₂) (hκ : 0 < κ) (hlam : 0 ≤ lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ X D N δ : ℝ, 1 ≤ X → (1 / 2 : ℝ) ≤ D → (1 / 2 : ℝ) ≤ N →
      0 ≤ δ → ∀ q : ℕ, 1 ≤ q → ∀ L : ℕ,
      (2 : ℝ) ^ L ≤ 8 * N → (L : ℝ) ≤ (lam + 2) * X ^ (ε / 2) →
      2 * ∑ j ∈ Finset.range L,
        (2 : ℝ) ^ j * (κ * X ^ (ε / 2) * (C₂ * (((1 / (q : ℝ) + q * δ) *
          ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
          δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4))))
        ≤ 10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) * X ^ ε * N * D *
            (1 / (q : ℝ) + q * δ + δ * N * D) := by
  have hε2 : 0 < ε / 2 := by linarith
  intro X D N δ hX hD hN hδ q hq L h2L hKL
  have hX0 : 0 < X := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set Xp : ℝ := X ^ (ε / 2) with hXp
  set A : ℝ := 1 / (q : ℝ) + q * δ with hA
  have hXp1 : (1 : ℝ) ≤ Xp := Real.one_le_rpow hX hε2.le
  have hXp_le : Xp ≤ X ^ ε := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hXe : Xp * Xp = X ^ ε := by
    rw [hXp, ← Real.rpow_add hX0]
    congr 1
    ring
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hDN : (1 / 4 : ℝ) ≤ D * N := by nlinarith
  have hN_le : N ≤ 2 * (D * N) := by nlinarith
  have hN_le8 : N ≤ 8 * (D ^ 2 * N ^ 2) := by nlinarith
  have hDN_le : D * N ≤ 4 * (D ^ 2 * N ^ 2) := by nlinarith
  set Kl : ℝ := (lam + 2) * Xp with hKl
  have hKl0 : (0 : ℝ) ≤ Kl := by rw [hKl]; positivity
  -- per-bucket bound
  have hkey : ∀ j ∈ Finset.range L,
      2 ^ j * (κ * Xp * (C₂ * (A * ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2) +
        δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) ≤
      κ * Xp * C₂ * (A * (16 * D * N + 5 * (2 : ℝ) ^ j) +
        δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j)) := by
    intro j _
    set Y : ℝ := (2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) with hY
    have hYb := pow_bucket_le (show (0:ℝ) < D by linarith) (show (0:ℝ) < N by linarith) j
    rw [← hY] at hYb
    have hY0 : (0 : ℝ) ≤ Y := by positivity
    have hYpos : (0 : ℝ) < Y := by positivity
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hid1 : (2 : ℝ) ^ j * (16 * D * N / (2 : ℝ) ^ j) = 16 * D * N := by
      field_simp
    have hid2 : (2 : ℝ) ^ j * ((16 * D * N / (2 : ℝ) ^ j + 4) ^ 2) =
        256 * D ^ 2 * N ^ 2 / (2 : ℝ) ^ j + 128 * D * N + 16 * ((2 : ℝ) ^ j) := by
      field_simp
      ring
    have hY2 : Y ^ 2 ≤ (16 * D * N / (2 : ℝ) ^ j + 4) ^ 2 := pow_le_pow_left₀ hY0 hYb 2
    have h2jY : (2 : ℝ) ^ j * Y ≤ 16 * D * N + 4 * (2 : ℝ) ^ j := by
      have := mul_le_mul_of_nonneg_left hYb h2j.le
      linarith [hid1, this]
    have h2jY2 : (2 : ℝ) ^ j * Y ^ 2 ≤ 256 * D ^ 2 * N ^ 2 + 128 * D * N + 16 * ((2 : ℝ) ^ j) := by
      have h := mul_le_mul_of_nonneg_left hY2 h2j.le
      have hdiv : 256 * D ^ 2 * N ^ 2 / (2 : ℝ) ^ j ≤ 256 * D ^ 2 * N ^ 2 := by
        rw [div_le_iff₀ h2j]
        have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      linarith [hid2, h, hdiv]
    have hexp : 2 ^ j * (κ * Xp * (C₂ * (A * (Y + 1 / 2) + δ * (Y ^ 2 + 1 / 4)))) =
        κ * Xp * C₂ * (A * ((2 : ℝ) ^ j * Y + (2 : ℝ) ^ j * (1 / 2)) +
          δ * ((2 : ℝ) ^ j * Y ^ 2 + (2 : ℝ) ^ j * (1 / 4))) := by ring
    rw [hexp]
    have h5 : (2 : ℝ) ^ j * (1 / 2) ≤ (2 : ℝ) ^ j := by linarith
    have h17 : (2 : ℝ) ^ j * (1 / 4) ≤ (2 : ℝ) ^ j := by linarith
    have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h5 : (2 : ℝ) ^ j * (1 / 2) ≤ (2 : ℝ) ^ j := by nlinarith
    have h17 : (2 : ℝ) ^ j * (1 / 4) ≤ (2 : ℝ) ^ j := by nlinarith
    have ht1 : A * ((2 : ℝ) ^ j * Y + (2 : ℝ) ^ j * (1 / 2)) ≤
        A * (16 * D * N + 5 * (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      linarith [h2jY, h5]
    have ht2 : δ * ((2 : ℝ) ^ j * Y ^ 2 + (2 : ℝ) ^ j * (1 / 4)) ≤
        δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      linarith [h2jY2, h17]
    have hnn : (0 : ℝ) ≤ κ * Xp * C₂ := by positivity
    nlinarith [ht1, ht2, hnn]
  -- sum the buckets
  have hsum_le : (∑ j ∈ Finset.range L,
      2 ^ j * (κ * Xp * (C₂ * (A * ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2) +
        δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4))))) ≤
      ∑ j ∈ Finset.range L,
        κ * Xp * C₂ * (A * (16 * D * N + 5 * (2 : ℝ) ^ j) +
          δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j)) :=
    Finset.sum_le_sum hkey
  have hclosed : (∑ j ∈ Finset.range L,
        κ * Xp * C₂ * (A * (16 * D * N + 5 * (2 : ℝ) ^ j) +
          δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j))) =
      κ * Xp * C₂ * (A * (16 * D * N * L + 5 * ((2 : ℝ) ^ L - 1)) +
        δ * (256 * D ^ 2 * N ^ 2 * L + 128 * D * N * L + 17 * ((2 : ℝ) ^ L - 1))) := by
    have hexp : ∀ j : ℕ,
        κ * Xp * C₂ * (A * (16 * D * N + 5 * (2 : ℝ) ^ j) +
          δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j)) =
        (κ * Xp * C₂) * (A * (16 * D * N) + δ * (256 * D ^ 2 * N ^ 2) + δ * (128 * D * N)) +
          (κ * Xp * C₂) * (A * 5 + δ * 17) * (2 : ℝ) ^ j := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_two_pow]
    ring
  -- the final scalar estimate
  have hXKl : Xp * Kl = (lam + 2) * X ^ ε := by
    rw [hKl, show Xp * ((lam + 2) * Xp) = (lam + 2) * (Xp * Xp) by ring, hXe]
  have hXp_e : Xp ≤ X ^ ε := hXp_le
  have hfinal : κ * Xp * C₂ * (A * (16 * D * N * (L : ℝ) + 5 * ((2 : ℝ) ^ L - 1)) +
      δ * (256 * D ^ 2 * N ^ 2 * (L : ℝ) + 128 * D * N * (L : ℝ) + 17 * ((2 : ℝ) ^ L - 1))) ≤
      (4000 * (lam + 2)) * κ * C₂ * X ^ ε * (N * D * A + δ * (D ^ 2 * N ^ 2)) := by
    have h2Ln : (2 : ℝ) ^ L - 1 ≤ 2 * (2 : ℝ) ^ L := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
      linarith
    have h2Lpos : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
    -- replace `L` by the bucket count bound and `2^L` by `8N`
    have hL5 : 5 * ((2 : ℝ) ^ L - 1) ≤ 40 * N := by linarith [h2L, h2Ln]
    have hL17 : 17 * ((2 : ℝ) ^ L - 1) ≤ 136 * N := by linarith [h2L, h2Ln]
    have hstep1 : A * (16 * D * N * (L : ℝ) + 5 * ((2 : ℝ) ^ L - 1)) ≤
        A * (16 * D * N * Kl + 40 * N) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
      nlinarith [hKL, hL5, mul_nonneg (by positivity : (0:ℝ) ≤ 16 * D * N) hL0]
    have hstep2 : δ * (256 * D ^ 2 * N ^ 2 * (L : ℝ) + 128 * D * N * (L : ℝ) +
        17 * ((2 : ℝ) ^ L - 1)) ≤
        δ * (256 * D ^ 2 * N ^ 2 * Kl + 128 * D * N * Kl + 136 * N) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
      nlinarith [hKL, hL17, mul_nonneg (by positivity : (0:ℝ) ≤ 256 * D ^ 2 * N ^ 2) hL0,
        mul_nonneg (by positivity : (0:ℝ) ≤ 128 * D * N) hL0]
    have hnn : (0 : ℝ) ≤ κ * Xp * C₂ := by positivity
    have hstep : κ * Xp * C₂ * (A * (16 * D * N * (L : ℝ) + 5 * ((2 : ℝ) ^ L - 1)) +
        δ * (256 * D ^ 2 * N ^ 2 * (L : ℝ) + 128 * D * N * (L : ℝ) + 17 * ((2 : ℝ) ^ L - 1))) ≤
        κ * Xp * C₂ * (A * (16 * D * N * Kl + 40 * N) +
          δ * (256 * D ^ 2 * N ^ 2 * Kl + 128 * D * N * Kl + 136 * N)) := by
      have h1 := mul_le_mul_of_nonneg_left hstep1 hnn
      have h2 := mul_le_mul_of_nonneg_left hstep2 hnn
      linarith [h1, h2]
    refine hstep.trans ?_
    -- split into the five monomials
    have hsplit : κ * Xp * C₂ * (A * (16 * D * N * Kl + 40 * N) +
        δ * (256 * D ^ 2 * N ^ 2 * Kl + 128 * D * N * Kl + 136 * N)) =
        κ * Xp * C₂ * (A * (16 * D * N * Kl)) + κ * Xp * C₂ * (A * (40 * N)) +
          κ * Xp * C₂ * (δ * (256 * D ^ 2 * N ^ 2 * Kl)) +
          κ * Xp * C₂ * (δ * (128 * D * N * Kl)) + κ * Xp * C₂ * (δ * (136 * N)) := by ring
    rw [hsplit]
    -- each monomial against its share of the target
    have m1 : κ * Xp * C₂ * (A * (16 * D * N * Kl)) ≤
        (32 * (lam + 2)) * κ * C₂ * X ^ ε * (N * D * A) := by
      have he : κ * Xp * C₂ * (A * (16 * D * N * Kl)) =
          16 * ((lam + 2) * κ * C₂ * (X ^ ε * (A * (N * D)))) := by
        rw [show κ * Xp * C₂ * (A * (16 * D * N * Kl)) =
          16 * κ * C₂ * (Xp * Kl) * (A * (N * D)) from by ring, hXKl]
        ring
      rw [he]
      have hT : (0 : ℝ) ≤ (lam + 2) * κ * C₂ * (X ^ ε * (A * (N * D))) := by positivity
      nlinarith
    have m2 : κ * Xp * C₂ * (A * (40 * N)) ≤
        (80 * κ * C₂) * X ^ ε * (N * D * A) := by
      have he : κ * Xp * C₂ * (A * (40 * N)) = 40 * (κ * C₂ * Xp * (A * N)) := by ring
      rw [he]
      have h0 : (0 : ℝ) ≤ κ * C₂ * (A * N) := by positivity
      have h1 : Xp ≤ X ^ ε := hXp_e
      have h2 : N ≤ 2 * (N * D) := by nlinarith
      have h3 : (0 : ℝ) ≤ A := hA0
      have h4 : (0 : ℝ) ≤ κ * C₂ := by positivity
      have hstep1 : Xp * (A * N) ≤ X ^ ε * (A * N) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have hstep2 : A * N ≤ A * (2 * (N * D)) := mul_le_mul_of_nonneg_left h2 hA0
      have hXe0 : (0 : ℝ) ≤ X ^ ε := Real.rpow_nonneg hX0.le _
      have hcombined : Xp * (A * N) ≤ X ^ ε * (A * (2 * (N * D))) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hXe0)
      nlinarith [hcombined, h4]
    have m3 : κ * Xp * C₂ * (δ * (256 * D ^ 2 * N ^ 2 * Kl)) ≤
        (768 * (lam + 2)) * κ * C₂ * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by
      have he : κ * Xp * C₂ * (δ * (256 * D ^ 2 * N ^ 2 * Kl)) =
          256 * ((lam + 2) * κ * C₂ * (X ^ ε * (δ * (D ^ 2 * N ^ 2)))) := by
        rw [show κ * Xp * C₂ * (δ * (256 * D ^ 2 * N ^ 2 * Kl)) =
          256 * κ * C₂ * (Xp * Kl) * (δ * (D ^ 2 * N ^ 2)) from by ring, hXKl]
        ring
      rw [he]
      have hT : (0 : ℝ) ≤ (lam + 2) * κ * C₂ * (X ^ ε * (δ * (D ^ 2 * N ^ 2))) := by positivity
      nlinarith
    have m4 : κ * Xp * C₂ * (δ * (128 * D * N * Kl)) ≤
        (768 * (lam + 2)) * κ * C₂ * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by
      have he : κ * Xp * C₂ * (δ * (128 * D * N * Kl)) =
          128 * ((lam + 2) * κ * C₂ * (X ^ ε * (δ * (D * N)))) := by
        rw [show κ * Xp * C₂ * (δ * (128 * D * N * Kl)) =
          128 * κ * C₂ * (Xp * Kl) * (δ * (D * N)) from by ring, hXKl]
        ring
      rw [he]
      have h0 : (0 : ℝ) ≤ (lam + 2) * κ * C₂ * X ^ ε * δ := by positivity
      have hDN' : D * N ≤ 4 * (D ^ 2 * N ^ 2) := hDN_le
      have hlam2 : (0 : ℝ) ≤ lam + 2 := by linarith
      have h4 : (0 : ℝ) ≤ (lam + 2) * κ * C₂ * X ^ ε * (δ * (D * N)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hDN' h0]
    have m5 : κ * Xp * C₂ * (δ * (136 * N)) ≤
        (2176 * κ * C₂) * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by
      have he : κ * Xp * C₂ * (δ * (136 * N)) = 136 * (κ * C₂ * Xp * (δ * N)) := by ring
      rw [he]
      have h1 : Xp ≤ X ^ ε := hXp_e
      have h2 : N ≤ 8 * (D ^ 2 * N ^ 2) := hN_le8
      have h3 : (0 : ℝ) ≤ κ * C₂ * δ := by positivity
      have hstep1 : Xp * (δ * N) ≤ X ^ ε * (δ * N) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have hstep2 : δ * N ≤ 8 * (δ * (D ^ 2 * N ^ 2)) := by
        have := mul_le_mul_of_nonneg_left h2 hδ
        linarith [this]
      have hXe0 : (0 : ℝ) ≤ X ^ ε := Real.rpow_nonneg hX0.le _
      have hcombined : Xp * (δ * N) ≤ X ^ ε * (8 * (δ * (D ^ 2 * N ^ 2))) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hXe0)
      have hm : (136 : ℝ) * (κ * C₂) * (Xp * (δ * N)) ≤
          136 * (κ * C₂) * (X ^ ε * (8 * (δ * (D ^ 2 * N ^ 2)))) :=
        mul_le_mul_of_nonneg_left hcombined (by positivity)
      have hz : (0 : ℝ) ≤ κ * C₂ * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by positivity
      calc 136 * (κ * C₂ * Xp * (δ * N)) = 136 * (κ * C₂) * (Xp * (δ * N)) := by ring
        _ ≤ 136 * (κ * C₂) * (X ^ ε * (8 * (δ * (D ^ 2 * N ^ 2)))) := hm
        _ ≤ 2176 * κ * C₂ * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by nlinarith [hz]
    have hcomb : κ * Xp * C₂ * (A * (16 * D * N * Kl)) + κ * Xp * C₂ * (A * (40 * N)) +
          κ * Xp * C₂ * (δ * (256 * D ^ 2 * N ^ 2 * Kl)) +
          κ * Xp * C₂ * (δ * (128 * D * N * Kl)) + κ * Xp * C₂ * (δ * (136 * N)) ≤
        (4000 * (lam + 2)) * κ * C₂ * X ^ ε * (N * D * A + δ * (D ^ 2 * N ^ 2)) := by
      have hlam2 : (0 : ℝ) ≤ lam + 2 := by linarith
      have hXe0 : (0 : ℝ) ≤ X ^ ε := Real.rpow_nonneg hX0.le _
      have hT1 : (0 : ℝ) ≤ κ * C₂ * X ^ ε * (N * D * A) := by positivity
      have hT2 : (0 : ℝ) ≤ κ * C₂ * X ^ ε * (δ * (D ^ 2 * N ^ 2)) := by positivity
      nlinarith [m1, m2, m3, m4, m5, hT1, hT2, hlam2]
    linarith [hcomb]

  calc 2 * ∑ j ∈ Finset.range L,
        (2 : ℝ) ^ j * (κ * X ^ (ε / 2) * (C₂ * (((1 / (q : ℝ) + q * δ) *
          ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2)) +
          δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4))))
      = 2 * ∑ j ∈ Finset.range L,
        (2 : ℝ) ^ j * (κ * Xp * (C₂ * (A * ((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2) + 1 / 2) +
          δ * (((2 : ℝ) ^ (Nat.log2 ⌊4 * D * N / (2 : ℝ) ^ j⌋₊ + 2)) ^ 2 + 1 / 4)))) := by
        rw [hXp, hA]
    _ ≤ 2 * ∑ j ∈ Finset.range L,
        κ * Xp * C₂ * (A * (16 * D * N + 5 * (2 : ℝ) ^ j) +
          δ * (256 * D ^ 2 * N ^ 2 + 128 * D * N + 17 * (2 : ℝ) ^ j)) := by
        have := mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0:ℝ) ≤ 2)
        linarith
    _ = 2 * (κ * Xp * C₂ * (A * (16 * D * N * (L : ℝ) + 5 * ((2 : ℝ) ^ L - 1)) +
        δ * (256 * D ^ 2 * N ^ 2 * (L : ℝ) + 128 * D * N * (L : ℝ) + 17 * ((2 : ℝ) ^ L - 1)))) := by
        rw [hclosed]
    _ ≤ 2 * ((4000 * (lam + 2)) * κ * C₂ * X ^ ε * (N * D * A + δ * (D ^ 2 * N ^ 2))) := by
        have := mul_le_mul_of_nonneg_left hfinal (by norm_num : (0:ℝ) ≤ 2)
        linarith
    _ ≤ 10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) * X ^ ε * N * D *
          (1 / (q : ℝ) + q * δ + δ * N * D) := by
        rw [hA]
        have hκ1 : (0 : ℝ) < κ + 1 := by linarith
        have hC1 : (0 : ℝ) < C₂ + 1 := by linarith
        have hbase : (N * D * (1 / (q : ℝ) + q * δ) + δ * (D ^ 2 * N ^ 2)) =
            N * D * (1 / (q : ℝ) + q * δ + δ * N * D) := by ring
        rw [hbase]
        set B : ℝ := N * D * (1 / (q : ℝ) + q * δ + δ * N * D) with hB
        have hb0 : (0 : ℝ) ≤ X ^ ε * B := by rw [hB]; positivity
        have hlam0' : (0 : ℝ) ≤ lam + 2 := by linarith
        have hp : κ * C₂ ≤ (κ + 1) * (C₂ + 1) := by nlinarith
        have hlp : (lam + 2) * (κ * C₂) ≤ (lam + 2) * ((κ + 1) * (C₂ + 1)) :=
          mul_le_mul_of_nonneg_left hp hlam0'
        have h1 : (8000 : ℝ) * ((lam + 2) * κ * C₂) ≤
            10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) := by
          have e1 : (8000 : ℝ) * ((lam + 2) * κ * C₂) = 8000 * ((lam + 2) * (κ * C₂)) := by ring
          have e2 : 10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) =
              10 ^ 7 * ((lam + 2) * ((κ + 1) * (C₂ + 1))) := by ring
          rw [e1, e2]
          have hX : (0 : ℝ) ≤ (lam + 2) * (κ * C₂) := by positivity
          linarith [hlp, hX]
        have hmul := mul_le_mul_of_nonneg_right h1 hb0
        have e3 : 2 * ((4000 * (lam + 2)) * κ * C₂ * X ^ ε * B) =
            8000 * ((lam + 2) * κ * C₂) * (X ^ ε * B) := by ring
        have e4 : (10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1)) * (X ^ ε * B) =
            10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) * X ^ ε * N * D *
              (1 / (q : ℝ) + q * δ + δ * N * D) := by
          rw [hB]
          ring
        rw [e3]
        linarith [hmul, e4]


/-- The leaf `counting24_sparse` itself: page 5 equation 6 in the sparse case. -/
private theorem counting24_sparse_proof (h23 : DiophantineCount.Lemma23Bound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X D N α δ : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X → 0 ≤ α → α ≤ 1 →
        0 < δ → N * δ < 1 / 4 →
        ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
          |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
          (count24 α D N δ : ℝ) ≤
            C * X ^ ε * N * D * (1 / (q : ℝ) + q * δ + δ * N * D) := by
  intro ε hε
  obtain ⟨C₂, κ, lam, hC₂, hκ, hlam, hKb, hbucketed⟩ := counting24_le_bucketed h23 ε hε
  have hfinal := bucketed_sum_le hC₂ hκ hlam hε
  refine ⟨10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1), by positivity, ?_⟩
  intro X D N α δ hX hD hDX hN hNX hα0 hα1 hδ hNδ a q hq hc ha
  have hX0 : 0 < X := by linarith
  rcases Nat.eq_zero_or_pos ⌊2 * D⌋₊ with hDz | hDp
  · have hzero : count24 α D N δ = 0 := by
      rw [count24]
      apply Finset.sum_eq_zero
      intro d hd
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hd
      exfalso
      omega
    rw [hzero]
    push_cast
    have hXp : (0 : ℝ) ≤ X ^ ε := Real.rpow_nonneg hX0.le _
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) + q * δ := by positivity
    have hd0 : (0 : ℝ) ≤ δ := hδ.le
    have hnd : (0 : ℝ) ≤ N * D * (1 / (q : ℝ) + q * δ + δ * N * D) := by positivity
    have : (0 : ℝ) ≤ 10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) * X ^ ε * N * D *
        (1 / (q : ℝ) + q * δ + δ * N * D) := by positivity
    linarith
  rcases Nat.eq_zero_or_pos ⌊2 * N⌋₊ with hNz | hNp
  · have hpc0 : ∀ β : ℝ, DiophantineCount.pairCount β N δ = 0 := by
      intro β
      have hsum := pairCount_eq_sum_nat β N δ hN.le
      have hz : (∑ m ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          ((DiophantineCount.numeratorRange β δ (m : ℤ)).card : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
        exfalso
        omega
      have hcast : (DiophantineCount.pairCount β N δ : ℝ) = 0 := by rw [hsum, hz]
      exact_mod_cast hcast
    have hzero : count24 α D N δ = 0 := by
      rw [count24]
      apply Finset.sum_eq_zero
      intro d _
      apply Finset.sum_eq_zero
      intro b _
      exact hpc0 _
    rw [hzero]
    push_cast
    have hXp : (0 : ℝ) ≤ X ^ ε := Real.rpow_nonneg hX0.le _
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) + q * δ := by positivity
    have hd0 : (0 : ℝ) ≤ δ := hδ.le
    have : (0 : ℝ) ≤ 10 ^ 7 * (lam + 2) * (C₂ + 1) * (κ + 1) * X ^ ε * N * D *
        (1 / (q : ℝ) + q * δ + δ * N * D) := by positivity
    linarith
  have hDhalf : (1 / 2 : ℝ) ≤ D := by
    have h1 : (1 : ℝ) ≤ (⌊2 * D⌋₊ : ℝ) := by exact_mod_cast hDp
    have h2 : (⌊2 * D⌋₊ : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
    linarith
  have hNhalf : (1 / 2 : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ (⌊2 * N⌋₊ : ℝ) := by exact_mod_cast hNp
    have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
    linarith
  have hδ0 : (0 : ℝ) ≤ δ := hδ.le
  have h2L : (2 : ℝ) ^ (Nat.log2 ⌊2 * N⌋₊ + 2) ≤ 8 * N := by
    have h1 : (2 : ℝ) ^ (Nat.log2 ⌊2 * N⌋₊ + 2) = 4 * (2 : ℝ) ^ Nat.log2 ⌊2 * N⌋₊ := by
      rw [show Nat.log2 ⌊2 * N⌋₊ + 2 = Nat.log2 ⌊2 * N⌋₊ + 1 + 1 from by ring, pow_succ,
        pow_succ]
      ring
    rw [h1]
    have h2 : (2 : ℝ) ^ Nat.log2 ⌊2 * N⌋₊ ≤ (⌊2 * N⌋₊ : ℝ) := by
      have := pow_log2_le_nat hNp
      exact_mod_cast this
    have h3 : ((⌊2 * N⌋₊ : ℕ) : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
    linarith
  have hKL : ((Nat.log2 ⌊2 * N⌋₊ + 2 : ℕ) : ℝ) ≤ (lam + 2) * X ^ (ε / 2) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
    exact hKb X N hX hN hNX
  exact (hbucketed X D N α δ hX hD hDX hN hNX hα0 hα1 hδ hNδ a q hq hc ha).trans
    (hfinal X D N δ hX hDhalf hNhalf hδ0 q hq (Nat.log2 ⌊2 * N⌋₊ + 2) h2L hKL)


/-- LEAF. Page 5 equation 6. The remaining gcd grouping and divisor multiplicity bound.
CONDITIONAL ON the Lemma 2.3 input. -/
theorem counting24_sparse (h23 : DiophantineCount.Lemma23Bound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X D N α δ : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 < N → N ≤ X →
        0 ≤ α → α ≤ 1 → 0 < δ → N * δ < 1 / 4 →
        ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
          |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
          (count24 α D N δ : ℝ) ≤
            C * X ^ ε * N * D * (1 / (q : ℝ) + q * δ + δ * N * D) := by
  exact counting24_sparse_proof h23

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

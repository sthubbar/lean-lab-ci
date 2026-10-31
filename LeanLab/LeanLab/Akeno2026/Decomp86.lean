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
theorem typeI7 (hloc : Localization22) (hcount : Counting24) : TypeI7 := by sorry

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

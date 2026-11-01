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


/-- A continuous weight supported in `[0,1]` vanishes at `0`. -/
private theorem weightZero {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) : w 0 = 0 := by
  have hc : Continuous w := hw.continuous
  have hz : IsClosed {x : ℝ | w x = 0} := isClosed_eq hc continuous_const
  have hsub : Set.Iio (0 : ℝ) ⊆ {x : ℝ | w x = 0} := by
    intro x hx
    by_contra hh
    exact absurd (hs hh).1 (not_le.mpr hx)
  have hcl := closure_minimal hsub hz
  rw [closure_Iio] at hcl
  exact hcl (by simp)

/-- The natural range sum and the integer interval sum agree. -/
private theorem sum_range_eq_sum_Icc (f : ℤ → ℂ) {Y : ℝ} (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), f (n : ℤ)) =
      ∑ n ∈ Finset.Icc (0 : ℤ) ⌊Y⌋, f n := by
  apply Finset.sum_bij (fun (n : ℕ) (_ : n ∈ Finset.range (⌊Y⌋₊ + 1)) => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_Icc, Int.le_floor]
    exact ⟨by positivity, (Nat.le_floor_iff hY).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))⟩
  · intro a _ b _ hab
    exact_mod_cast hab
  · intro z hz
    obtain ⟨hz0, hzY⟩ := Finset.mem_Icc.mp hz
    refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_iff.mpr
    apply Nat.le_floor
    have : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz0
    rw [this]
    exact Int.le_floor.mp hzY
  · intro n _
    rfl

/-- Shifting the parameter by an integer does not change the numerator range count. -/
private theorem numeratorRange_card_add_intCast (α δ : ℝ) (m k : ℤ) :
    (DiophantineCount.numeratorRange (α + (k : ℝ)) δ m).card =
      (DiophantineCount.numeratorRange α δ m).card := by
  have h1 : ⌈(m : ℝ) * (α + (k : ℝ) - δ)⌉ = ⌈(m : ℝ) * (α - δ)⌉ + k * m := by
    rw [show (m : ℝ) * (α + (k : ℝ) - δ) = (m : ℝ) * (α - δ) + ((k * m : ℤ) : ℝ) by
      push_cast; ring]
    exact Int.ceil_add_intCast _ _
  have h2 : ⌊(m : ℝ) * (α + (k : ℝ) + δ)⌋ = ⌊(m : ℝ) * (α + δ)⌋ + k * m := by
    rw [show (m : ℝ) * (α + (k : ℝ) + δ) = (m : ℝ) * (α + δ) + ((k * m : ℤ) : ℝ) by
      push_cast; ring]
    exact Int.floor_add_intCast _ _
  unfold DiophantineCount.numeratorRange
  rw [h1, h2, Int.card_Icc, Int.card_Icc]
  congr 1
  ring

/-- Shifting the parameter by an integer does not change the pair count. -/
private theorem pairCount_add_intCast (α M δ : ℝ) (k : ℤ) :
    DiophantineCount.pairCount (α + (k : ℝ)) M δ =
      DiophantineCount.pairCount α M δ := by
  unfold DiophantineCount.pairCount
  apply Finset.sum_congr rfl
  intro m hm
  exact numeratorRange_card_add_intCast α δ m k

/-- The natural and integer dyadic denominator ranges agree. -/
private theorem sum_denominatorRange_eq {β : Type*} [AddCommMonoid β] (f : ℤ → β) {M : ℝ} (hM : 0 ≤ M) :
    (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, f (m : ℤ)) =
      ∑ m ∈ DiophantineCount.denominatorRange M, f m := by
  have h0 : ((⌊M⌋₊ : ℕ) : ℤ) = ⌊M⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    push_cast
    exact ⟨Nat.floor_le hM, Nat.lt_floor_add_one M⟩
  have h1 : ((⌊2 * M⌋₊ : ℕ) : ℤ) = ⌊2 * M⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    push_cast
    exact ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one (2 * M)⟩
  have hi : ∀ a ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      (a : ℤ) ∈ DiophantineCount.denominatorRange M := by
    intro a ha
    simp only [DiophantineCount.denominatorRange, Finset.mem_Ioc] at ha ⊢
    constructor
    · have : ((⌊M⌋₊ : ℕ) : ℤ) < (a : ℤ) := by exact_mod_cast ha.1
      rwa [h0] at this
    · have : ((a : ℕ) : ℤ) ≤ ((⌊2 * M⌋₊ : ℕ) : ℤ) := by exact_mod_cast ha.2
      rwa [h1] at this
  have hj : ∀ z ∈ DiophantineCount.denominatorRange M,
      z.toNat ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ := by
    intro z hz
    simp only [DiophantineCount.denominatorRange, Finset.mem_Ioc] at hz ⊢
    have hz0 : (0 : ℤ) ≤ z := by
      have : (0 : ℤ) ≤ ⌊M⌋ := Int.floor_nonneg.mpr hM
      linarith [hz.1]
    constructor
    · have hlt : ⌊M⌋ < z := hz.1
      rw [← h0] at hlt
      have h2 : (⌊M⌋₊ : ℤ) < (z.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hz0]
      exact_mod_cast h2
    · have hle : z ≤ ⌊2 * M⌋ := hz.2
      rw [← h1] at hle
      have h2 : (z.toNat : ℤ) ≤ (⌊2 * M⌋₊ : ℤ) := by rwa [Int.toNat_of_nonneg hz0]
      exact_mod_cast h2
  refine Finset.sum_nbij' (fun (n : ℕ) => (n : ℤ)) (fun (z : ℤ) => z.toNat) hi hj ?_ ?_ ?_
  · intro a _
    exact Int.toNat_natCast a
  · intro z hz
    have hz0 : (0 : ℤ) ≤ z := by
      simp only [DiophantineCount.denominatorRange, Finset.mem_Ioc] at hz
      have : (0 : ℤ) ≤ ⌊M⌋ := Int.floor_nonneg.mpr hM
      linarith [hz.1]
    exact Int.toNat_of_nonneg hz0
  · intro a _
    rfl

/-- The inner Type I sum as a smooth exponential sum with scale `X / m`. -/
private theorem inner_sum_eq_smoothSum (w : ℝ → ℝ) (hs : Function.support w ⊆ Set.Icc 0 1)
    {X : ℝ} (hX : 0 < X) {m : ℕ} (hm : 1 ≤ m) (β : ℝ) :
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ))
      = smoothSum w (X / m) (β * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hY : (0 : ℝ) < X / m := div_pos hX hm0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hYX : X / m ≤ X := by
    rw [div_le_iff₀ hm0]; nlinarith
  have hdrop : (∑ n ∈ Finset.range (⌊X / m⌋₊ + 1),
      e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)) =
      ∑ n ∈ Finset.range (⌊X⌋₊ + 1), e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ) := by
    apply Finset.sum_subset (Finset.range_mono (by have := Nat.floor_mono hYX; omega))
    intro n hn hnot
    have hn' : ⌊X / m⌋₊ < n := by simpa using hnot
    have h1 : X / m < (n : ℝ) := (Nat.floor_lt hY.le).mp hn'
    have h2 : X < (n : ℝ) * m := (div_lt_iff₀ hm0).mp h1
    have h3 : 1 < (m : ℝ) * n / X := (lt_div_iff₀ hX).mpr (by nlinarith)
    have hwv : w ((m : ℝ) * n / X) = 0 := by
      by_contra hc
      exact absurd (hs hc).2 (not_le.mpr h3)
    simp [hwv]
  rw [← hdrop]
  trans (∑ n ∈ Finset.Icc (0 : ℤ) ⌊X / m⌋,
      e ((β * (m : ℝ)) * (n : ℝ)) * (w ((n : ℝ) / (X / m)) : ℂ))
  · rw [← sum_range_eq_sum_Icc
      (fun n : ℤ => e ((β * (m : ℝ)) * (n : ℝ)) * (w ((n : ℝ) / (X / m)) : ℂ)) hY.le]
    apply Finset.sum_congr rfl
    intro n hn
    have harg : (m : ℝ) * (n : ℝ) / X = (n : ℝ) / (X / m) := by field_simp
    have hn2 : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
    simp only [harg, hn2]
  · simp only [smoothSum]



/-- `(X/m)^e/m = X^e * m^{-(e+1)}`. -/
private theorem rpow_div_div {X m : ℝ} (hX : 0 < X) (hm : 0 < m) (e : ℝ) :
    (X / m) ^ e / m = X ^ e * m ^ (-(e + 1)) := by
  rw [Real.div_rpow hX.le hm.le, div_div, ← Real.rpow_add_one (ne_of_gt hm)]
  rw [div_eq_mul_inv, ← Real.rpow_neg hm.le]

/-- The localization radius at scale `X/m`, divided by `m`, is at most `X^(ε'-1)`. -/
private theorem rpow_div_div_le_radius {X : ℝ} (hX : 1 ≤ X) {m : ℝ} (hm : 1 ≤ m) {ε' : ℝ} (hε' : 0 < ε') :
    (X / m) ^ (ε' - 1) / m ≤ X ^ (ε' - 1) := by
  have hX0 : 0 < X := by linarith
  have hm0 : 0 < m := by linarith
  rw [rpow_div_div hX0 hm0 (ε' - 1)]
  have hXe : 0 ≤ X ^ (ε' - 1) := Real.rpow_nonneg hX0.le _
  have hme : m ^ (-(ε' - 1 + 1)) ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_le hm (show -(ε' - 1 + 1) ≤ 0 by linarith)
    simpa using this
  calc X ^ (ε' - 1) * m ^ (-(ε' - 1 + 1)) ≤ X ^ (ε' - 1) * 1 :=
        mul_le_mul_of_nonneg_left hme hXe
    _ = X ^ (ε' - 1) := mul_one _



/-- The near-count is bounded by the numerator range count at a radius covering `ρ/m`. -/
private theorem nearCount_le_numeratorRange_card (β ρ δ : ℝ) (m : ℤ) (hm : 0 < (m : ℝ)) (_hρ : 0 ≤ ρ)
    (hρδ : ρ / (m : ℝ) ≤ δ) :
    nearCount (β * (m : ℝ)) ρ ≤ (DiophantineCount.numeratorRange (-β) δ m).card := by
  have hneg : ∀ z ∈ Finset.Icc ⌈β * (m : ℝ) - ρ⌉ ⌊β * (m : ℝ) + ρ⌋,
      -z ∈ DiophantineCount.numeratorRange (-β) δ m := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hz
    have hz1 : β * (m : ℝ) - ρ ≤ (z : ℝ) := Int.ceil_le.mp h1
    have hz2 : (z : ℝ) ≤ β * (m : ℝ) + ρ := Int.le_floor.mp h2
    have hb : |β * (m : ℝ) - (z : ℝ)| ≤ ρ := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [DiophantineCount.mem_numeratorRange hm]
    have heq : (-β : ℝ) - ((-z : ℤ) : ℝ) / (m : ℝ) = -(β - (z : ℝ) / (m : ℝ)) := by
      push_cast; ring
    rw [heq, abs_neg]
    have hstep : β - (z : ℝ) / (m : ℝ) = (β * (m : ℝ) - (z : ℝ)) / (m : ℝ) := by
      field_simp
    rw [hstep, abs_div, abs_of_pos hm]
    exact (div_le_div_of_nonneg_right hb hm.le).trans hρδ
  have hcard : ((Finset.Icc ⌈β * (m : ℝ) - ρ⌉ ⌊β * (m : ℝ) + ρ⌋).image (fun z : ℤ => -z)).card
      = (Finset.Icc ⌈β * (m : ℝ) - ρ⌉ ⌊β * (m : ℝ) + ρ⌋).card :=
    Finset.card_image_of_injOn (by intro a _ b _ hab; simpa using hab)
  calc nearCount (β * (m : ℝ)) ρ
      = (Finset.Icc ⌈β * (m : ℝ) - ρ⌉ ⌊β * (m : ℝ) + ρ⌋).card := rfl
    _ = ((Finset.Icc ⌈β * (m : ℝ) - ρ⌉ ⌊β * (m : ℝ) + ρ⌋).image (fun z : ℤ => -z)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_iff.mpr hneg)

/-- The localization bound holds at every positive scale. -/
private theorem norm_smoothSum_le {w : ℝ → ℝ} (hw0 : w 0 = 0) {ε' Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
    (hlocb : ∀ Y γ : ℝ, 1 ≤ Y →
      ‖smoothSum w Y γ‖ ≤ Cloc * (Y * (nearCount γ (Y ^ (ε' - 1)) : ℝ) + Y ^ (-(100 : ℝ))))
    {Y γ : ℝ} (hY : 0 < Y) :
    ‖smoothSum w Y γ‖ ≤ Cloc * (Y * (nearCount γ (Y ^ (ε' - 1)) : ℝ) + Y ^ (-(100 : ℝ))) := by
  by_cases h1 : 1 ≤ Y
  · exact hlocb Y γ h1
  · have hfl : ⌊Y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hY.le, not_le.mp h1⟩
    have hzero : smoothSum w Y γ = 0 := by
      simp only [smoothSum, hfl, Finset.Icc_self, Finset.sum_singleton]
      simp [hw0]
    rw [hzero, norm_zero]
    refine mul_nonneg hCloc0 ?_
    have h2' : 0 < Y ^ (-(100 : ℝ)) := Real.rpow_pos_of_pos hY _
    have h3' : (0 : ℝ) ≤ Y * (nearCount γ (Y ^ (ε' - 1)) : ℝ) :=
      mul_nonneg hY.le (Nat.cast_nonneg _)
    linarith

/-- The trivial bound for a smooth exponential sum with `|w| ≤ W` on its support. -/
private theorem norm_smoothSum_le_card {w : ℝ → ℝ} {W Y γ : ℝ} (_hW0 : 0 ≤ W)
    (hW : ∀ x ∈ Set.Icc 0 1, ‖w x‖ ≤ W) (hY : 0 < Y) :
    ‖smoothSum w Y γ‖ ≤ ((⌊Y⌋₊ : ℝ) + 1) * W := by
  have hpt : ∀ n ∈ Finset.Icc (0 : ℤ) ⌊Y⌋,
      ‖e (γ * (n : ℝ)) * (w ((n : ℝ) / Y) : ℂ)‖ ≤ W := by
    intro n hn
    obtain ⟨hn0, hn1⟩ := Finset.mem_Icc.mp hn
    have hn0' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    have hn1' : (n : ℝ) ≤ Y := Int.le_floor.mp hn1
    have he1 : ‖e (γ * (n : ℝ))‖ = 1 := by
      simp only [LeanLab.Akeno2026.e]
      rw [show 2 * (π : ℂ) * Complex.I * (((γ * (n : ℝ)) : ℝ) : ℂ)
          = (((2 * π * (γ * (n : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hmem : (n : ℝ) / Y ∈ Set.Icc 0 1 :=
      ⟨div_nonneg hn0' hY.le, (div_le_one hY).mpr hn1'⟩
    rw [norm_mul, he1, one_mul, Complex.norm_real]
    exact hW _ hmem
  have hc1 : (Finset.Icc (0 : ℤ) ⌊Y⌋).card = ⌊Y⌋₊ + 1 := by
    rw [Int.card_Icc]
    have h : ((⌊Y⌋₊ : ℕ) : ℤ) = ⌊Y⌋ := by
      rw [eq_comm, Int.floor_eq_iff]
      push_cast
      exact ⟨Nat.floor_le hY.le, Nat.lt_floor_add_one Y⟩
    rw [← h]
    simp
  unfold smoothSum
  calc ‖∑ n ∈ Finset.Icc (0 : ℤ) ⌊Y⌋, e (γ * (n : ℝ)) * (w ((n : ℝ) / Y) : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc (0 : ℤ) ⌊Y⌋, W := (norm_sum_le _ _).trans (Finset.sum_le_sum hpt)
    _ = ((Finset.Icc (0 : ℤ) ⌊Y⌋).card : ℝ) * W := by simp
    _ = ((⌊Y⌋₊ : ℝ) + 1) * W := by rw [hc1]; push_cast; ring

/-- A crude bound for the Type I sum, using only `|w| ≤ W`. -/
private theorem norm_typeISum_le_triv {w : ℝ → ℝ} {W X M : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ x ∈ Set.Icc 0 1, ‖w x‖ ≤ W) (hXs : Function.support w ⊆ Set.Icc 0 1)
    (hX : 0 < X) (hM : 0 < M) (hMX : M ≤ X)
    (A : ℕ → ℂ) (hA : ∀ m, ‖A m‖ ≤ 1) (β : ℝ) :
    ‖typeISum w A X M β‖ ≤ 4 * W * X := by
  have hMfl : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le hM.le
  have hcard : ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) ≤ 2 * M := by
    rw [Nat.card_Ioc]
    have h1 : ((⌊2 * M⌋₊ : ℕ) : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
    have h2 : ((⌊2 * M⌋₊ - ⌊M⌋₊ : ℕ) : ℝ) ≤ ((⌊2 * M⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (⌊2 * M⌋₊) (⌊M⌋₊)
    linarith
  have hterm : ∀ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), A m * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)‖
        ≤ ((⌊X / (m : ℝ)⌋₊ : ℝ) + 1) * W := by
    intro m hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1
      have := Nat.zero_le (⌊M⌋₊)
      omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hfac : (∑ n ∈ Finset.range (⌊X⌋₊ + 1), A m * e (β * m * n) *
        (w ((m : ℝ) * n / X) : ℂ))
        = A m * ∑ n ∈ Finset.range (⌊X⌋₊ + 1), e (β * m * n) *
          (w ((m : ℝ) * n / X) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hfac, norm_mul, inner_sum_eq_smoothSum w hXs hX hm1 β]
    have hY0 : (0 : ℝ) < X / (m : ℝ) := div_pos hX hmpos
    have h1 := norm_smoothSum_le_card hW0 hW hY0 (γ := β * (m : ℝ))
    have h2 : ‖A m‖ * ‖smoothSum w (X / (m : ℝ)) (β * (m : ℝ))‖
        ≤ 1 * (((⌊X / (m : ℝ)⌋₊ : ℝ) + 1) * W) :=
      mul_le_mul (hA m) h1 (norm_nonneg _) (by norm_num)
    linarith [h2]
  have hstep1 : ‖typeISum w A X M β‖ ≤
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ((⌊X / (m : ℝ)⌋₊ : ℝ) + 1) * W := by
    unfold typeISum
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hgeom : ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ((⌊X / (m : ℝ)⌋₊ : ℝ) + 1) * W
      ≤ ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (X / M + 1) * W := by
    apply Finset.sum_le_sum
    intro m hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1
      have := Nat.zero_le (⌊M⌋₊)
      omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmle : M < (m : ℝ) := by
      have h1 : M < ((⌊M⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one M
      have h2 : ((⌊M⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
        have h3 : (⌊M⌋₊ : ℕ) + 1 ≤ m := by
          have := (Finset.mem_Ioc.mp hm).1
          omega
        exact_mod_cast h3
      linarith
    have hfl : ((⌊X / (m : ℝ)⌋₊ : ℕ) : ℝ) ≤ X / (m : ℝ) :=
      Nat.floor_le (div_nonneg hX.le hmpos.le)
    have hsplit : X / (m : ℝ) ≤ X / M := by
      have h1 : 1 / (m : ℝ) ≤ 1 / M := one_div_le_one_div_of_le hM hmle.le
      calc X / (m : ℝ) = X * (1 / (m : ℝ)) := by ring
        _ ≤ X * (1 / M) := mul_le_mul_of_nonneg_left h1 hX.le
        _ = X / M := by ring
    have hle : ((⌊X / (m : ℝ)⌋₊ : ℝ) + 1) ≤ X / M + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle hW0
  refine hstep1.trans (hgeom.trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : 0 ≤ (X / M + 1) * W := by
    apply mul_nonneg _ hW0
    have h0 : 0 ≤ X / M := div_nonneg hX.le hM.le
    linarith
  refine (mul_le_mul_of_nonneg_right hcard h1).trans ?_
  have hMd : M * (X / M) = X := by field_simp
  nlinarith [hMd, hW0, hM.le, hMX, hX.le]

/-- The localization radius inside the Type I sum stays at most `X^(ε'-1)` after rescaling. -/
private theorem rpow_div_div_le_radius' {X : ℝ} (hX : 1 ≤ X) {m : ℕ} (hm : 1 ≤ m) {ε' : ℝ} (hε' : 0 < ε') :
    (X / (m : ℝ)) ^ (ε' - 1) / (m : ℝ) ≤ X ^ (ε' - 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact rpow_div_div_le_radius hX hm1 hε'

/-- Localisation bounds the Type I sum by the numerator range count at radius `X^(ε'-1)`. -/
private theorem norm_typeISum_le_localization {w : ℝ → ℝ} (hw0 : w 0 = 0)
    (hXs : Function.support w ⊆ Set.Icc 0 1) {X M : ℝ} (hX : 0 < X) (hM : 0 < M)
    (hX1 : 1 ≤ X) (hMX : M ≤ X) {ε' Cloc : ℝ} (hCloc0 : 0 ≤ Cloc) (hε' : 0 < ε')
    (hlocb : ∀ Y γ : ℝ, 1 ≤ Y →
      ‖smoothSum w Y γ‖ ≤ Cloc * (Y * (nearCount γ (Y ^ (ε' - 1)) : ℝ) + Y ^ (-(100 : ℝ))))
    (A : ℕ → ℂ) (hA : ∀ m, ‖A m‖ ≤ 1) (β : ℝ) :
    ‖typeISum w A X M β‖ ≤
      Cloc * ((X / M) * (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
          ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ))
        + 2 * M * 2 ^ (100 : ℕ)) := by
  have hmge : ∀ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, M < (m : ℝ) := by
    intro m hm
    have h1 : M < ((⌊M⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one M
    have h2 : ((⌊M⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      have h3 : (⌊M⌋₊ : ℕ) + 1 ≤ m := by
        have := (Finset.mem_Ioc.mp hm).1
        omega
      exact_mod_cast h3
    linarith
  have hmone : ∀ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, 1 ≤ m := by
    intro m hm
    have := (Finset.mem_Ioc.mp hm).1
    have := Nat.zero_le (⌊M⌋₊)
    omega
  have hjunk : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 2 * M →
      (X / (m : ℝ)) ^ (-(100 : ℝ)) ≤ 2 ^ (100 : ℕ) := by
    intro m hm hm2
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hY : (0 : ℝ) < X / (m : ℝ) := div_pos hX hmpos
    have hu : (1 / 2 : ℝ) ≤ X / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      nlinarith [hm2, hMX, hX.le]
    have hpow : (1 / 2 : ℝ) ^ 100 ≤ (X / (m : ℝ)) ^ 100 :=
      pow_le_pow_left₀ (by norm_num) hu 100
    have hpos : (0 : ℝ) < (X / (m : ℝ)) ^ 100 := pow_pos hY 100
    have hpos2 : (0 : ℝ) < (1 / 2 : ℝ) ^ 100 := by norm_num
    have hinv : ((X / (m : ℝ)) ^ 100)⁻¹ ≤ ((1 / 2 : ℝ) ^ 100)⁻¹ :=
      (inv_le_inv₀ hpos hpos2).mpr hpow
    have hhalf : ((1 / 2 : ℝ) ^ 100)⁻¹ = 2 ^ (100 : ℕ) := by norm_num
    rw [Real.rpow_neg hY.le]
    rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hinv.trans_eq hhalf
  have hterm : ∀ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), A m * e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)‖
        ≤ Cloc * ((X / M) *
            ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ)
          + (X / (m : ℝ)) ^ (-(100 : ℝ))) := by
    intro m hm
    have hm1 : 1 ≤ m := hmone m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmle : M < (m : ℝ) := hmge m hm
    have hfac : (∑ n ∈ Finset.range (⌊X⌋₊ + 1), A m * e (β * m * n) *
        (w ((m : ℝ) * n / X) : ℂ))
        = A m * ∑ n ∈ Finset.range (⌊X⌋₊ + 1), e (β * m * n) *
          (w ((m : ℝ) * n / X) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hfac, norm_mul, inner_sum_eq_smoothSum w hXs hX hm1 β]
    have hY : (0 : ℝ) < X / (m : ℝ) := div_pos hX hmpos
    have hloc := norm_smoothSum_le hw0 hCloc0 hlocb hY (γ := β * (m : ℝ))
    have hcardle : (nearCount (β * (m : ℝ)) ((X / (m : ℝ)) ^ (ε' - 1)) : ℝ) ≤
        ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ) := by
      have h := nearCount_le_numeratorRange_card β ((X / (m : ℝ)) ^ (ε' - 1)) (X ^ (ε' - 1)) (m : ℤ) hmpos
        (Real.rpow_nonneg hY.le _) (rpow_div_div_le_radius' hX1 hm1 hε')
      exact_mod_cast h
    have hYM : X / (m : ℝ) ≤ X / M := by
      have h1 : 1 / (m : ℝ) ≤ 1 / M := one_div_le_one_div_of_le hM hmle.le
      calc X / (m : ℝ) = X * (1 / (m : ℝ)) := by ring
        _ ≤ X * (1 / M) := mul_le_mul_of_nonneg_left h1 hX.le
        _ = X / M := by ring
    have hstep : (X / (m : ℝ)) * (nearCount (β * (m : ℝ)) ((X / (m : ℝ)) ^ (ε' - 1)) : ℝ)
        ≤ (X / M) * ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ) := by
      apply mul_le_mul hYM hcardle (Nat.cast_nonneg _) (div_nonneg hX.le hM.le)
    calc ‖A m‖ * ‖smoothSum w (X / (m : ℝ)) (β * (m : ℝ))‖
        ≤ 1 * (Cloc * ((X / (m : ℝ)) * (nearCount (β * (m : ℝ)) ((X / (m : ℝ)) ^ (ε' - 1)) : ℝ)
            + (X / (m : ℝ)) ^ (-(100 : ℝ)))) :=
          mul_le_mul (hA m) hloc (norm_nonneg _) (by norm_num)
      _ = Cloc * ((X / (m : ℝ)) * (nearCount (β * (m : ℝ)) ((X / (m : ℝ)) ^ (ε' - 1)) : ℝ)
            + (X / (m : ℝ)) ^ (-(100 : ℝ))) := by ring
      _ ≤ Cloc * ((X / M) *
            ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ)
          + (X / (m : ℝ)) ^ (-(100 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCloc0
          linarith [hstep]
  have hstep1 : ‖typeISum w A X M β‖ ≤
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, Cloc * ((X / M) *
            ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ)
          + (X / (m : ℝ)) ^ (-(100 : ℝ))) := by
    unfold typeISum
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  refine hstep1.trans ?_
  have hsplit : (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, Cloc * ((X / M) *
            ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ)
          + (X / (m : ℝ)) ^ (-(100 : ℝ))))
      = Cloc * ((X / M) * (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
            ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ))
          + ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (X / (m : ℝ)) ^ (-(100 : ℝ))) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ hCloc0
  have hdj : (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (X / (m : ℝ)) ^ (-(100 : ℝ)))
      ≤ 2 * M * 2 ^ (100 : ℕ) := by
    have hcard : ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) ≤ 2 * M := by
      rw [Nat.card_Ioc]
      have h1 : ((⌊2 * M⌋₊ : ℕ) : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
      have h2 : ((⌊2 * M⌋₊ - ⌊M⌋₊ : ℕ) : ℝ) ≤ ((⌊2 * M⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (⌊2 * M⌋₊) (⌊M⌋₊)
      linarith
    calc (∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (X / (m : ℝ)) ^ (-(100 : ℝ)))
        ≤ ∑ _m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (2 ^ (100 : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun m hm => hjunk m (hmone m hm) (by
            have h4 : (m : ℝ) ≤ ((⌊2 * M⌋₊ : ℕ) : ℝ) := by
              exact_mod_cast (Finset.mem_Ioc.mp hm).2
            have h5 : ((⌊2 * M⌋₊ : ℕ) : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
            linarith))
      _ = ((Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).card : ℝ) * 2 ^ (100 : ℕ) := by simp
      _ ≤ 2 * M * 2 ^ (100 : ℕ) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have hX0 : 0 ≤ X / M := div_nonneg hX.le hM.le
  have hP0 : 0 ≤ ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊,
      ((DiophantineCount.numeratorRange (-β) (X ^ (ε' - 1)) (m : ℤ)).card : ℝ) :=
    Finset.sum_nonneg (fun m _ => Nat.cast_nonneg _)
  nlinarith [hdj, hX0, hP0]

/-- LEAF. Page 6 proof of equation 7. Combine the trivial sum bound with localization.
CONDITIONAL ON equations 3 and 6. -/
theorem typeI7 (hloc : Localization22) (hcount : Counting24) : TypeI7 := by
  intro ε hε w hw hs
  have hw0 : w 0 = 0 := weightZero hw hs
  obtain ⟨Cloc, hCloc0, hlocb⟩ := hloc (ε / 2) (by positivity) w hw hs
  obtain ⟨Ccnt, hCcnt0, hcntb⟩ := hcount (ε / 2) (by positivity)
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (s := Set.Icc (0:ℝ) 1) (f := w) hw.continuous.continuousOn
  have hW0 : 0 ≤ W := (norm_nonneg (w 0)).trans (hW 0 (by constructor <;> norm_num))
  have htwo : (0:ℝ) ≤ 2 ^ (100 : ℕ) := by positivity
  refine ⟨4 * W * Cloc * Ccnt + 32 * 2 ^ (100 : ℕ) * W * Cloc, by positivity, ?_⟩
  intro X D M α hX hD hDX hM hMX hα0 hα1 a q hq hcop happ A hA
  have hX1 : 1 ≤ X := hX
  have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  set δ : ℝ := X ^ (ε / 2 - 1) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hXpos _
  set IocD : Finset ℕ := Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊ with hIocD
  set IocM : Finset ℕ := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ with hIocM
  set Pfun : ℕ → ℕ → ℝ := fun d b => ∑ m ∈ IocM,
      ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / d)) δ (m : ℤ)).card : ℝ) with hPfun
  -- per term bound
  have hA2 : ∀ d ∈ IocD, ∀ b ∈ Finset.range d,
      ‖typeISum w A X M (α + (b : ℝ) / d)‖ ^ 2 ≤
        4 * W * X * (Cloc * ((X / M) * Pfun d b + 2 * M * 2 ^ (100 : ℕ))) := by
    intro d hd b hb
    have hloc2 := norm_typeISum_le_localization (w := w) hw0 hs hXpos hM hX1 hMX (ε' := ε / 2) hCloc0
      (by linarith) hlocb A hA (α + (b : ℝ) / d)
    have htriv := norm_typeISum_le_triv hW0 hW hs hXpos hM hMX A hA (α + (b : ℝ) / d)
    have h4 : (0:ℝ) ≤ 4 * W * X := by positivity
    have hmul := mul_le_mul htriv hloc2 (norm_nonneg _) h4
    rw [pow_two]
    exact hmul
  -- energy bound
  have hB : energy (typeISum w A X M) D α ≤
      4 * W * X * ∑ d ∈ IocD, ∑ b ∈ Finset.range d,
        Cloc * ((X / M) * Pfun d b + 2 * M * 2 ^ (100 : ℕ)) := by
    simp only [energy]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b hb => hA2 d hd b hb)
  -- distribute
  have hC : (∑ d ∈ IocD, ∑ b ∈ Finset.range d,
        Cloc * ((X / M) * Pfun d b + 2 * M * 2 ^ (100 : ℕ)))
      = Cloc * ((X / M) * (∑ d ∈ IocD, ∑ b ∈ Finset.range d, Pfun d b)
          + (∑ d ∈ IocD, (d : ℝ)) * (2 * M * 2 ^ (100 : ℕ))) := by
    have h1 : ∀ d ∈ IocD, (∑ b ∈ Finset.range d,
          Cloc * ((X / M) * Pfun d b + 2 * M * 2 ^ (100 : ℕ)))
        = Cloc * ((X / M) * (∑ b ∈ Finset.range d, Pfun d b)
            + (d : ℝ) * (2 * M * 2 ^ (100 : ℕ))) := by
      intro d hd
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
  -- the pair count identity
  have hPv : ∀ d ∈ IocD, ∀ b : ℕ, Pfun d b =
      (DiophantineCount.pairCount (-(α + (b : ℝ) / d)) M δ : ℝ) := by
    intro d hd b
    have hM0 : (0:ℝ) ≤ M := hM.le
    have hcast : (∑ m ∈ IocM,
          ((DiophantineCount.numeratorRange (-(α + (b : ℝ) / d)) δ (m : ℤ)).card : ℝ))
        = ((∑ m ∈ IocM,
          (DiophantineCount.numeratorRange (-(α + (b : ℝ) / d)) δ (m : ℤ)).card : ℕ) : ℝ) := by
      push_cast
      rfl
    simp only [hPfun]
    rw [hcast]
    conv_rhs => rw [DiophantineCount.pairCount]
    rw [sum_denominatorRange_eq (M := M)
      (f := fun m : ℤ => (DiophantineCount.numeratorRange (-(α + (b : ℝ) / d)) δ m).card) hM0]
  -- the range versus residue class bound
  have hD1 : (∑ d ∈ IocD, ∑ b ∈ Finset.range d, Pfun d b) ≤
      (count24 α D M δ : ℝ) := by
    have hstep2 : ∀ d ∈ IocD, (∑ b ∈ Finset.range d, Pfun d b) ≤
        ∑ b ∈ Finset.Icc 1 d, (DiophantineCount.pairCount (-(α + (b : ℝ) / d)) M δ : ℝ) := by
      intro d hd
      have hd1 : 1 ≤ d := by
        have h1 : (⌊D⌋₊ : ℕ) < d := (Finset.mem_Ioc.mp hd).1
        have h2 := Nat.zero_le (⌊D⌋₊)
        omega
      set φ : ℕ → ℕ := fun b => if b = 0 then d else b with hφ
      have hφinj : Set.InjOn φ ((Finset.range d : Finset ℕ) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_range] at ha hb
        by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
        · rw [ha0, hb0]
        · simp only [hφ, ha0, if_true, hb0, if_false] at hab
          omega
        · simp only [hφ, ha0, if_true, hb0, if_false] at hab
          omega
        · simpa only [hφ, ha0, if_false, hb0] using hab
      have himage : ∀ b ∈ Finset.range d, φ b ∈ Finset.Icc 1 d := by
        intro b hb
        simp only [Finset.mem_range] at hb
        by_cases hb0 : b = 0
        · simp only [hφ, hb0, if_true, Finset.mem_Icc]
          omega
        · simp only [hφ, hb0, if_false, Finset.mem_Icc]
          omega
      have hImg : (∑ b ∈ Finset.range d, Pfun d b)
          = ∑ j ∈ (Finset.range d).image φ,
              (DiophantineCount.pairCount (-(α + (j : ℝ) / d)) M δ : ℝ) := by
        refine Eq.trans ?_ (Finset.sum_image
          (f := fun j : ℕ => (DiophantineCount.pairCount (-(α + (j : ℝ) / d)) M δ : ℝ))
          (s := Finset.range d) (g := φ) hφinj).symm
        apply Finset.sum_congr rfl
        intro b hb
        simp only [hPv d hd b]
        by_cases hb0 : b = 0
        · have hphi : φ b = d := by simp [hφ, hb0]
          rw [hphi, hb0]
          norm_num
          have harg : -(↑d / ↑d) + -α = (-α) + ((-1 : ℤ) : ℝ) := by
            have hd0 : (d : ℝ) ≠ 0 := by
              have hpos : (0:ℕ) < d := hd1
              exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
            field_simp
            ring
          rw [harg, (pairCount_add_intCast (-α) M δ (-1)).symm]
        · have hphi : φ b = b := by simp [hφ, hb0]
          rw [hphi]
      have hsub : (Finset.range d).image φ ⊆ Finset.Icc 1 d := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        exact himage b hb
      rw [hImg]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.cast_nonneg _)
    calc (∑ d ∈ IocD, ∑ b ∈ Finset.range d, Pfun d b)
        ≤ ∑ d ∈ IocD, ∑ b ∈ Finset.Icc 1 d,
            (DiophantineCount.pairCount (-(α + (b : ℝ) / d)) M δ : ℝ) :=
          Finset.sum_le_sum hstep2
      _ = (count24 α D M δ : ℝ) := by
          simp only [count24, hIocD]
          push_cast
          rfl
  -- sum of the moduli
  have hSd : (∑ d ∈ IocD, (d : ℝ)) ≤ 4 * D ^ 2 := by
    have hcard : ((IocD).card : ℝ) ≤ 2 * D := by
      rw [hIocD, Nat.card_Ioc]
      have h1 : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
      have h2 : ((⌊2 * D⌋₊ - ⌊D⌋₊ : ℕ) : ℝ) ≤ ((⌊2 * D⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (⌊2 * D⌋₊) (⌊D⌋₊)
      linarith
    have hb : ∀ d ∈ IocD, (d : ℝ) ≤ 2 * D := by
      intro d hd
      have h1 : d ≤ ⌊2 * D⌋₊ := (Finset.mem_Ioc.mp hd).2
      have h2 : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
      exact (Nat.cast_le.mpr h1).trans h2
    calc (∑ d ∈ IocD, (d : ℝ)) ≤ ∑ _d ∈ IocD, (2 * D) := Finset.sum_le_sum hb
      _ = (IocD.card : ℝ) * (2 * D) := by simp
      _ ≤ (2 * D) * (2 * D) := mul_le_mul_of_nonneg_right hcard (by linarith)
      _ = 4 * D ^ 2 := by ring
  -- apply the counting bound
  have hcnt := hcntb X D M α δ hX hD hDX hM hMX hα0 hα1 hδ0 a q hq hcop happ
  -- assemble
  have hX0 : (0:ℝ) < X := hXpos
  have hMX0 : 0 < M := hM
  have hstep1 : energy (typeISum w A X M) D α ≤ 4 * W * X *
      (Cloc * ((X / M) * (count24 α D M δ : ℝ) + (4 * D ^ 2) * (2 * M * 2 ^ (100 : ℕ)))) := by
    refine hB.trans ?_
    rw [hC]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 4 * W * X)
    refine mul_le_mul_of_nonneg_left ?_ hCloc0
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hD1 (by positivity)
    · exact mul_le_mul_of_nonneg_right hSd (by positivity)
  -- substitute the counting bound
  have hmono : 4 * W * X * (Cloc * ((X / M) * (count24 α D M δ : ℝ)
        + (4 * D ^ 2) * (2 * M * 2 ^ (100 : ℕ))))
      ≤ 4 * W * X * (Cloc * ((X / M) * (Ccnt * X ^ (ε/2) * M * D * (1/q + q*δ + δ*M*D))
        + (4 * D ^ 2) * (2 * M * 2 ^ (100 : ℕ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ hCloc0
    exact add_le_add (mul_le_mul_of_nonneg_left hcnt (by positivity)) le_rfl
  refine hstep1.trans (hmono.trans ?_)
  set Cc : ℝ := 4 * W * Cloc * Ccnt + 32 * 2 ^ (100 : ℕ) * W * Cloc with hCc
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hqa : (0:ℝ) < q := by exact_mod_cast hq
  have hcoef : 4 * W * Cloc * Ccnt ≤ Cc := by
    rw [hCc]
    nlinarith [hW0, hCloc0, hCcnt0, htwo]
  have hcoef4 : 32 * 2 ^ (100 : ℕ) * W * Cloc ≤ Cc := by
    rw [hCc]
    nlinarith [hW0, hCloc0, hCcnt0, htwo]
  have hsq : X * X * X ^ (ε/2) = X ^ (2 + ε/2) := by
    have h2 : X * X = X ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_two]
    rw [h2, ← Real.rpow_add hXpos]
  have hXa : X ^ (2 + ε/2) ≤ X ^ (2 + 2*ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXb : X ^ (2 + ε/2) * δ ≤ X ^ (1 + 2*ε) := by
    have hcomb : X ^ (2 + ε/2) * X ^ (ε/2 - 1) = X ^ (1 + ε) := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring
    rw [hδdef, hcomb]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXc : X ≤ X ^ (1 + 2*ε) := by
    calc X = X ^ (1:ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ (1 + 2*ε) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXfact : X ^ (2 + 2*ε) = X * X ^ (1 + 2*ε) := by
    rw [show 2 + 2*ε = 1 + (1 + 2*ε) by ring, Real.rpow_add hXpos, Real.rpow_one]
  have hsplit1 : X ^ (2 + 2*ε) * ((q:ℝ)*D/X) = X ^ (1 + 2*ε) * ((q:ℝ)*D) := by
    rw [hXfact]
    field_simp
  have hsplit2 : X ^ (2 + 2*ε) * (M*D^2/X) = X ^ (1 + 2*ε) * (M*D^2) := by
    rw [hXfact]
    field_simp
  have hDq : (0:ℝ) ≤ D/(q:ℝ) := le_of_lt (div_pos hD hqa)
  have hqD : (0:ℝ) ≤ (q:ℝ)*D := mul_nonneg hqa.le hD.le
  have hMD : (0:ℝ) ≤ M*D^2 := by positivity
  have hid1 : 4 * W * X * (Cloc * ((X / M) * (Ccnt * X ^ (ε/2) * M * D * (1/q + q*δ + δ*M*D))
        + (4 * D ^ 2) * (2 * M * 2 ^ (100 : ℕ))))
      = 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (D/q))
        + 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * ((q:ℝ)*δ) * D)
        + 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (δ*M*D) * D)
        + 32 * 2 ^ (100 : ℕ) * W * Cloc * (X*M*D^2) := by
    field_simp
    ring
  have hid2 : Cc * X ^ (2 + 2*ε) * (D/q + q*D/X + M*D^2/X)
      = Cc * (X ^ (2 + 2*ε) * (D/q)) + Cc * (X ^ (1 + 2*ε) * ((q:ℝ)*D))
        + Cc * (X ^ (1 + 2*ε) * (M*D^2)) := by
    have hq1 : Cc * X ^ (2 + 2*ε) * ((q:ℝ)*D/X) = Cc * (X ^ (1 + 2*ε) * ((q:ℝ)*D)) := by
      calc Cc * X ^ (2 + 2*ε) * ((q:ℝ)*D/X) = Cc * (X ^ (2 + 2*ε) * ((q:ℝ)*D/X)) := by ring
        _ = Cc * (X ^ (1 + 2*ε) * ((q:ℝ)*D)) := by rw [hsplit1]
    have hq2 : Cc * X ^ (2 + 2*ε) * (M*D^2/X) = Cc * (X ^ (1 + 2*ε) * (M*D^2)) := by
      calc Cc * X ^ (2 + 2*ε) * (M*D^2/X) = Cc * (X ^ (2 + 2*ε) * (M*D^2/X)) := by ring
        _ = Cc * (X ^ (1 + 2*ε) * (M*D^2)) := by rw [hsplit2]
    rw [mul_add, mul_add, hq1, hq2]
    ring
  rw [hid1, hid2]
  have e1 : 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (D/q)) ≤ Cc * (X ^ (2 + 2*ε) * (D/q)) := by
    rw [hsq]
    calc 4 * W * Cloc * Ccnt * (X ^ (2 + ε/2) * (D/q))
        ≤ Cc * (X ^ (2 + ε/2) * (D/q)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ Cc * (X ^ (2 + 2*ε) * (D/q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXa hDq) hCc0
  have e2 : 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * ((q:ℝ)*δ) * D)
      ≤ Cc * (X ^ (1 + 2*ε) * ((q:ℝ)*D)) := by
    rw [hsq]
    have hb : X ^ (2 + ε/2) * ((q:ℝ)*δ) * D ≤ X ^ (1 + 2*ε) * ((q:ℝ)*D) := by
      have h := mul_le_mul_of_nonneg_right hXb hqD
      calc X ^ (2 + ε/2) * ((q:ℝ)*δ) * D = (X ^ (2 + ε/2) * δ) * ((q:ℝ)*D) := by ring
        _ ≤ X ^ (1 + 2*ε) * ((q:ℝ)*D) := h
    calc 4 * W * Cloc * Ccnt * (X ^ (2 + ε/2) * ((q:ℝ)*δ) * D)
        ≤ Cc * (X ^ (2 + ε/2) * ((q:ℝ)*δ) * D) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ Cc * (X ^ (1 + 2*ε) * ((q:ℝ)*D)) := mul_le_mul_of_nonneg_left hb hCc0
  have e3 : 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (δ*M*D) * D)
      ≤ (4 * W * Cloc * Ccnt) * (X ^ (1 + 2*ε) * (M*D^2)) := by
    rw [hsq]
    have hb : X ^ (2 + ε/2) * (δ*M*D) * D ≤ X ^ (1 + 2*ε) * (M*D^2) := by
      have h := mul_le_mul_of_nonneg_right hXb hMD
      calc X ^ (2 + ε/2) * (δ*M*D) * D = (X ^ (2 + ε/2) * δ) * (M*D^2) := by ring
        _ ≤ X ^ (1 + 2*ε) * (M*D^2) := h
    have hcoef3 : (0:ℝ) ≤ 4 * W * Cloc * Ccnt := by positivity
    exact mul_le_mul_of_nonneg_left hb hcoef3
  have e4 : 32 * 2 ^ (100 : ℕ) * W * Cloc * (X*M*D^2)
      ≤ (32 * 2 ^ (100 : ℕ) * W * Cloc) * (X ^ (1 + 2*ε) * (M*D^2)) := by
    have h1 : X * M * D^2 ≤ X ^ (1 + 2*ε) * (M*D^2) := by
      calc X * M * D ^ 2 = X * (M*D^2) := by ring
        _ ≤ X ^ (1 + 2*ε) * (M*D^2) := mul_le_mul_of_nonneg_right hXc hMD
    have hcoef4' : (0:ℝ) ≤ 32 * 2 ^ (100 : ℕ) * W * Cloc := by positivity
    calc 32 * 2 ^ (100 : ℕ) * W * Cloc * (X*M*D^2)
        = (32 * 2 ^ (100 : ℕ) * W * Cloc) * (X*M*D^2) := by ring
      _ ≤ (32 * 2 ^ (100 : ℕ) * W * Cloc) * (X ^ (1 + 2*ε) * (M*D^2)) :=
          mul_le_mul_of_nonneg_left h1 hcoef4'
  have e34 : 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (δ*M*D) * D)
        + 32 * 2 ^ (100 : ℕ) * W * Cloc * (X*M*D^2)
      ≤ Cc * (X ^ (1 + 2*ε) * (M*D^2)) := by
    have h := add_le_add e3 e4
    calc 4 * W * Cloc * Ccnt * (X*X*X^(ε/2) * (δ*M*D) * D)
          + 32 * 2 ^ (100 : ℕ) * W * Cloc * (X*M*D^2)
        ≤ (4 * W * Cloc * Ccnt) * (X ^ (1 + 2*ε) * (M*D^2))
          + (32 * 2 ^ (100 : ℕ) * W * Cloc) * (X ^ (1 + 2*ε) * (M*D^2)) := h
      _ = (4 * W * Cloc * Ccnt + 32 * 2 ^ (100 : ℕ) * W * Cloc) * (X ^ (1 + 2*ε) * (M*D^2)) := by
          ring
      _ = Cc * (X ^ (1 + 2*ε) * (M*D^2)) := by rw [hCc]
  linarith [e1, e2, e34]

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

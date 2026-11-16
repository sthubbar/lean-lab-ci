/-
Independent split of the short coefficient replacement step of the periodic
kernel reduction.  The short block mass is read off the divisor type bound, the
replacement at a single even frequency is bounded by a logarithmic saving times
that mass, the number of even frequencies is counted, and the elementary
thresholds are collected separately.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561n

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Counting step.  The even frequencies form an arithmetic progression of
even numbers inside an interval whose length is the frequency height, so their
number is at most twice that height.  Only cardinality is used, with no analytic
input. -/
theorem leaf_short_frequency_card561 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ((frequencies512 ε x).card : ℝ) ≤
        2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  sorry

/-- LEAF. Mass of the short block.  From the divisor type bound alone, the sum of
the coefficient norms over the short support is at most a constant times the block
length times a single fixed power of the logarithm of x.  The exponent is returned
with the constant, because the divisor moment on a block of length about that
length costs a power of the logarithm growing with the divisor exponent. -/
theorem leaf_short_block_mass561 (B C₀ : ℝ) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M := by
  sorry

/-- LEAF. Replacement at a single frequency.  Assuming the prefix distribution of
b against every character of a small modulus, the error made by replacing the
actual short polynomial by its principal model at one even frequency is at most a
logarithmic saving times the mass of the short block.  The sum of squares over the
frequencies is not taken here. -/
theorem leaf_short_prefix_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Threshold step.  For small enough ε the block length is at least one, the
logarithm of x exceeds one, and the frequency height is at least one, from some
point onwards.  This produces the positive ε cut of the conclusion. -/
theorem leaf_short_length_bounds561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      1 ≤ length512 ε x ∧ 1 < Real.log x ∧
        1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  sorry

/-- The short coefficient replacement step, assembled from the frequency count, the
short block mass, the replacement at a single frequency and the elementary
thresholds.  CONDITIONAL ON those four separate inputs. -/
theorem leaf_short_coefficient561_split :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∃ C : ℝ, ∀ x k, ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          shortReplacementError561 ε D x (b x) u v ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨εp, hεp, hpre⟩ := leaf_short_prefix_replacement561
  obtain ⟨εl, hεl, hlen⟩ := leaf_short_length_bounds561
  refine ⟨min εp εl, lt_min hεp hεl, ?_⟩
  intro ε hε hεlt b u v
  dsimp only
  intro hcoef hdist A hA
  obtain ⟨C₀, hC₀⟩ := hcoef
  obtain ⟨K, M, hK, hM, hmass⟩ := leaf_short_block_mass561 B C₀
  obtain ⟨Kc, hcard⟩ := leaf_short_frequency_card561 ε hε
  obtain ⟨Xlen, hXlen⟩ := hlen ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  obtain ⟨Xmass, hXmass⟩ := hmass ε hε
  obtain ⟨Dp, hDp⟩ :=
    hpre ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) b u v hdist (A + 14 + M) (by linarith)
  refine ⟨Dp, fun D hD => ?_⟩
  obtain ⟨Cpre, hCpre⟩ := hDp D hD
  let P : ℝ := |Cpre| * K
  let C : ℝ := max (max (max (max Kc Xmass) Cpre) (max Xlen 3)) (2 * P ^ 2)
  refine ⟨C, fun x hx => ?_⟩
  have h1 : Kc ≤ max Kc Xmass := le_max_left _ _
  have h2 : max Kc Xmass ≤ max (max Kc Xmass) Cpre := le_max_left _ _
  have h3 : max (max Kc Xmass) Cpre ≤ max (max (max Kc Xmass) Cpre) (max Xlen 3) :=
    le_max_left _ _
  have h4 : max (max (max Kc Xmass) Cpre) (max Xlen 3) ≤ C := le_max_left _ _
  have hxKc : Kc ≤ x := le_trans (le_trans (le_trans h1 h2) h3) (le_trans h4 hx)
  have hXm1 : Xmass ≤ max Kc Xmass := le_max_right _ _
  have hxXm : Xmass ≤ x := le_trans (le_trans (le_trans hXm1 h2) h3) (le_trans h4 hx)
  have hCp1 : Cpre ≤ max (max Kc Xmass) Cpre := le_max_right _ _
  have hxCp : Cpre ≤ x := le_trans (le_trans (le_trans hCp1 h3) h4) hx
  have hXl1 : Xlen ≤ max Xlen 3 := le_max_left _ _
  have hXl2 : max Xlen 3 ≤ max (max (max Kc Xmass) Cpre) (max Xlen 3) := le_max_right _ _
  have hxXl : Xlen ≤ x := le_trans (le_trans hXl1 hXl2) (le_trans h4 hx)
  have h31 : (3 : ℝ) ≤ max Xlen 3 := le_max_right _ _
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans h31 hXl2) (le_trans h4 hx)
  have hxP : 2 * P ^ 2 ≤ C := le_max_right _ _
  obtain ⟨hL1, hlog1, hH1⟩ := hXlen x hxXl
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hL0 : (0 : ℝ) ≤ length512 ε x := le_trans zero_le_one hL1
  let S : ℝ := ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖
  have hmassx : S ≤ K * length512 ε x * Real.log x ^ M :=
    hXmass x hxXm (b x) (fun k => hC₀ x k)
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hmul : Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M = Real.log x ^ (-A - 14) := by
    rw [← Real.rpow_add hlogpos]
    congr 1
    ring
  have hper : ∀ N ∈ frequencies512 ε x,
      ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ≤
        P * length512 ε x * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hCpre x hxCp N hN
    have hlogA : (0 : ℝ) ≤ Real.log x ^ (-(A + 14 + M)) := Real.rpow_nonneg hlog0 _
    have habs : (0 : ℝ) ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) :=
      mul_nonneg (abs_nonneg _) hlogA
    calc ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖
        ≤ Cpre * Real.log x ^ (-(A + 14 + M)) * S := h1
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) * S :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cpre) hlogA) hS0
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            (K * length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_left hmassx habs
      _ = P * length512 ε x * (Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M) := by
          rw [show P = |Cpre| * K from rfl]
          ring
      _ = P * length512 ε x * Real.log x ^ (-A - 14) := by rw [hmul]
  have hsq : ∀ N ∈ frequencies512 ε x,
      ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ^ 2 ≤
        (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hper N hN
    have hq0 : (0 : ℝ) ≤ Real.log x ^ (-A - 14) := Real.rpow_nonneg hlog0 _
    have hq1 : Real.log x ^ (-A - 14) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ^ 2
        ≤ (P * length512 ε x * Real.log x ^ (-A - 14)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (P ^ 2 * length512 ε x ^ 2) * (Real.log x ^ (-A - 14)) ^ 2 := by ring
      _ ≤ (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hq0, hq1]
  have hsum1 : shortReplacementError561 ε D x (b x) u v ≤
      ∑ N ∈ frequencies512 ε x, (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    unfold shortReplacementError561
    exact Finset.sum_le_sum hsq
  have hconst : (∑ N ∈ frequencies512 ε x,
        (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) =
      ((frequencies512 ε x).card : ℝ) *
        ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardx := hcard x hxKc
  have hbase0 : (0 : ℝ) ≤ (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) :=
    mul_nonneg (mul_nonneg (sq_nonneg P) (sq_nonneg _)) (Real.rpow_nonneg hlog0 _)
  calc shortReplacementError561 ε D x (b x) u v
      ≤ ∑ N ∈ frequencies512 ε x, (P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) :=
        hsum1
    _ = ((frequencies512 ε x).card : ℝ) *
          ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := hconst
    _ ≤ (2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) *
          ((P ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) :=
        mul_le_mul_of_nonneg_right hcardx hbase0
    _ = (2 * P ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
            Real.log x ^ (-A - 14)) := by ring
    _ ≤ (2 * P ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
            Real.log x ^ (-A - 7)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg _))
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (2 * P ^ 2) * scale512 ε A x := by rw [scale512]
    _ ≤ C * scale512 ε A x :=
        mul_le_mul_of_nonneg_right hxP (by
          rw [scale512]
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg _))
            (Real.rpow_nonneg hlog0 _))

end LeanLab.BHP1997.Decomp561n

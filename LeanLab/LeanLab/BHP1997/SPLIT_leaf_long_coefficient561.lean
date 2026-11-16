/-
Independent split of the long coefficient replacement step of the periodic kernel
reduction. The replacement error is bounded at each even frequency by a logarithmic
saving times the mass of the short block, the mass itself is estimated from the
divisor type bound, the number of frequencies is counted, and the elementary
thresholds are collected separately.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561n

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Counting step. The even frequencies below the frequency height form an
arithmetic progression of even numbers inside an interval of length at most that
height plus two, so their number is at most twice the height. Only the cardinality of
that progression is used here, with no analytic input. -/
theorem leaf_long_frequency_card561 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ((frequencies512 ε x).card : ℝ) ≤
        2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  set H : ℝ := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) with hH
  have hHpos : 0 < H := by
    rw [hH]
    have h1 : (0 : ℝ) < 11 / 20 + ε := by linarith
    have h2 : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    exact mul_pos h1 h2
  refine ⟨1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := hx
  have hH1 : (1 : ℝ) ≤ x ^ H := Real.one_le_rpow hx1 (le_of_lt hHpos)
  have hdefeq : frequencies512 ε x = (Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).filter (fun N => Even N) := by
    rw [frequencies512, ← hH]
  have hfloor : x ≤ (⌊x + x ^ H⌋₊ : ℝ) := by
    have h1 : x + x ^ H < (⌊x + x ^ H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hle : ⌈x⌉₊ ≤ ⌊x + x ^ H⌋₊ + 1 :=
    le_trans (Nat.ceil_le.mpr hfloor) (Nat.le_succ _)
  have hfilter : (frequencies512 ε x).card ≤ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card := by
    rw [hdefeq]
    exact Finset.card_filter_le _ _
  have hcardIcc : ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card : ℝ)
      ≤ (⌊x + x ^ H⌋₊ : ℝ) + 1 - (⌈x⌉₊ : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    linarith
  calc ((frequencies512 ε x).card : ℝ)
      ≤ ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ H⌋₊).card : ℝ) := by exact_mod_cast hfilter
    _ ≤ (⌊x + x ^ H⌋₊ : ℝ) + 1 - (⌈x⌉₊ : ℝ) := hcardIcc
    _ ≤ x ^ H + 1 := by
        have hb : (⌊x + x ^ H⌋₊ : ℝ) ≤ x + x ^ H := Nat.floor_le (by positivity)
        have ha : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
        linarith
    _ ≤ 2 * x ^ H := by linarith

/-- LEAF. Mass of the short block. From the divisor type bound alone, the sum of the
coefficient norms over the short support is at most a constant times the block length
times a single fixed power of the logarithm of x. The exponent is not fixed in advance:
it is returned with the constant, because the divisor moment on a block of length
about Y costs a power of the logarithm that grows with the divisor exponent. -/
theorem leaf_long_short_mass561 (B C₀ : ℝ) :
    ∃ K M : ℝ, 1 ≤ K ∧ 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ b : ℕ → ℂ,
        (∀ k : ℕ, ‖b k‖ ≤ C₀ * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ ≤
          K * length512 ε x * Real.log x ^ M := by
  sorry

/-- LEAF. Replacement at a single frequency. Assuming the prefix distribution of a
against every character of a small modulus and the rough support of a, the error made
by replacing the long polynomial by its principal model at one even frequency is at
most a logarithmic saving times the mass of the short block. The sum of squares over
the frequencies is not taken here. -/
theorem leaf_long_prefix_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
              longPrincipal561 ε D x (b x) u N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Threshold step. For small enough ε the long interval length is at least one,
the logarithm of x exceeds one, and the frequency height is at least one, from some
point onwards. This produces the positive ε cut of the conclusion. -/
theorem leaf_long_length_bounds561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      1 ≤ length512 ε x ∧ 1 < Real.log x ∧
        1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  refine ⟨1, one_pos, fun ε hε _ => ⟨Real.exp 2, fun x hx => ?_⟩⟩
  have hexp : (1 : ℝ) ≤ Real.exp 2 := by
    have h := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans hexp hx
  have hxexp : Real.exp 2 ≤ x := hx
  have hlog : 1 < Real.log x := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos 2) hxexp
    rw [Real.log_exp] at h1
    linarith
  refine ⟨?_, hlog, ?_⟩
  · unfold length512
    exact Real.one_le_rpow hx1 (by positivity)
  · exact Real.one_le_rpow hx1 (by positivity)

/-- The long coefficient replacement step, assembled from the frequency count, the
short block mass, the replacement at a single frequency and the elementary thresholds.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_coefficient561_split :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
        ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          longReplacementError561 ε D x (a x) (b x) u ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨εp, hεp, hpre⟩ := leaf_long_prefix_replacement561
  obtain ⟨εl, hεl, hlen⟩ := leaf_long_length_bounds561
  refine ⟨min εp εl, lt_min hεp hεl, ?_⟩
  intro ε hε hεlt a b u
  dsimp only
  intro hdist hcoef hrough A hA
  obtain ⟨C₀, hC₀⟩ := hcoef
  obtain ⟨K, M, hK, hM, hmass⟩ := leaf_long_short_mass561 B C₀
  obtain ⟨Kc, hcard⟩ := leaf_long_frequency_card561 ε hε
  obtain ⟨Xlen, hXlen⟩ := hlen ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  obtain ⟨Xmass, hXmass⟩ := hmass ε hε
  obtain ⟨Dp, hDp⟩ :=
    hpre ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) a b u hdist hrough
      (A + 14 + M) (by linarith)
  refine ⟨Dp, fun D hD => ?_⟩
  obtain ⟨Cpre, hCpre⟩ := hDp D hD
  refine ⟨max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1), fun x hx => ?_⟩
  have hthr : max (max Kc Xmass) (max Cpre (max Xlen 3)) ≤
      max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) :=
    le_max_left _ _
  have hxKc : Kc ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans hthr hx))
  have hxXm : Xmass ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans hthr hx))
  have hxCp : Cpre ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans hthr hx))
  have hxXl : Xlen ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_trans hthr hx))
  have hx3 : (3 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_trans hthr hx))
  obtain ⟨hL1, hlog1, hH1⟩ := hXlen x hxXl
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hL0 : (0 : ℝ) ≤ length512 ε x := le_trans zero_le_one hL1
  have hH0 : (0 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    le_trans zero_le_one hH1
  have hmassx : ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ ≤
      K * length512 ε x * Real.log x ^ M :=
    hXmass x hxXm (fun k => b x k) (fun k => (hC₀ x k).2)
  have hmass0 : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hsplit : Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M = Real.log x ^ (-A - 14) := by
    rw [← Real.rpow_add hlogpos, show -(A + 14 + M) + M = -A - 14 by ring]
  have hper : ∀ N ∈ frequencies512 ε x,
      ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ≤
        (|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hCpre x hxCp N hN
    have hlogA : (0 : ℝ) ≤ Real.log x ^ (-(A + 14 + M)) := Real.rpow_nonneg hlog0 _
    have habs : (0 : ℝ) ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) :=
      mul_nonneg (abs_nonneg _) hlogA
    calc ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖
        ≤ Cpre * Real.log x ^ (-(A + 14 + M)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := h1
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cpre) hlogA) hmass0
      _ ≤ |Cpre| * Real.log x ^ (-(A + 14 + M)) *
            (K * length512 ε x * Real.log x ^ M) :=
          mul_le_mul_of_nonneg_left hmassx habs
      _ = (|Cpre| * K) * length512 ε x *
            (Real.log x ^ (-(A + 14 + M)) * Real.log x ^ M) := by ring
      _ = (|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14) := by rw [hsplit]
  have hsq : ∀ N ∈ frequencies512 ε x,
      ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ^ 2 ≤
        ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    intro N hN
    have h1 := hper N hN
    have hq0 : (0 : ℝ) ≤ Real.log x ^ (-A - 14) := Real.rpow_nonneg hlog0 _
    have hq1 : Real.log x ^ (-A - 14) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hbase : (0 : ℝ) ≤ (|Cpre| * K) ^ 2 * length512 ε x ^ 2 := by positivity
    calc ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
          longPrincipal561 ε D x (b x) u N‖ ^ 2
        ≤ ((|Cpre| * K) * length512 ε x * Real.log x ^ (-A - 14)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * (Real.log x ^ (-A - 14)) ^ 2 := by ring
      _ ≤ ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
          apply mul_le_mul_of_nonneg_left _ hbase
          nlinarith [hq0, hq1]
  have hconst : ∑ _N ∈ frequencies512 ε x,
        ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) =
      ((frequencies512 ε x).card : ℝ) *
        (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ℝ) ≤ ((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by
    positivity
  have hscale0 : (0 : ℝ) ≤ scale512 ε A x := by
    unfold scale512
    positivity
  have hcoefge : 2 * (|Cpre| * K) ^ 2 ≤
      max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) :=
    le_trans (by linarith) (le_max_right _ _)
  have hle : Real.log x ^ (-A - 14) ≤ Real.log x ^ (-A - 7) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  unfold longReplacementError561
  refine le_trans (Finset.sum_le_sum hsq) ?_
  rw [hconst]
  calc ((frequencies512 ε x).card : ℝ) *
        (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14))
      ≤ (2 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) *
          (((|Cpre| * K) ^ 2 * length512 ε x ^ 2) * Real.log x ^ (-A - 14)) :=
        mul_le_mul_of_nonneg_right (hcard x hxKc) hcard0
    _ = (2 * (|Cpre| * K) ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            length512 ε x ^ 2 * Real.log x ^ (-A - 14)) := by ring
    _ ≤ (2 * (|Cpre| * K) ^ 2) *
          (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            length512 ε x ^ 2 * Real.log x ^ (-A - 7)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
              length512 ε x ^ 2 * Real.log x ^ (-A - 14)
            = (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
                length512 ε x ^ 2) * Real.log x ^ (-A - 14) := by ring
          _ ≤ (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
                length512 ε x ^ 2) * Real.log x ^ (-A - 7) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (2 * (|Cpre| * K) ^ 2) * scale512 ε A x := by
        unfold scale512
        ring
    _ ≤ max (max (max Kc Xmass) (max Cpre (max Xlen 3))) (2 * (|Cpre| * K) ^ 2 + 1) *
          scale512 ε A x :=
        mul_le_mul_of_nonneg_right hcoefge hscale0

end LeanLab.BHP1997.Decomp561n

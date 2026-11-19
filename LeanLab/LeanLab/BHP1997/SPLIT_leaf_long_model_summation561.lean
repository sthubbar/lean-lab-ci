/-
Split of theorem leaf_long_model_summation561 in
LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561: the collection of the
single-arc budgets over the moduli of the major arcs of the long coefficient
replacement.  The double sum over the arcs is first written as the sum of the
individual arc errors, the operator norm of that sum is bounded by the sum of
the norms, and the per-arc budgets are then collected: the number of reduced
residues of a modulus cancels against the totient weight, the moduli are counted
by the cutoff, and the surplus logarithmic saving pays for both.  When the short
block is shorter than half a unit the block carries no mass at all and the whole
summation is vacuous.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

set_option autoImplicit false

/-- The logarithm of a number at least eight is at least two. -/
private lemma log_ge_two_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h : Real.log 8 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

/-- If a positive natural number is at most the natural floor of a real number then
it is at most that real number. -/
private lemma natCast_le_of_le_natFloor {a : ℝ} {q : ℕ} (hq : 1 ≤ q) (h : q ≤ ⌊a⌋₊) :
    (q : ℝ) ≤ a := by
  rcases le_or_gt 0 a with h0 | h0
  · exact le_trans (by exact_mod_cast h) (Nat.floor_le h0)
  · have hz : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hq0 : q ≤ 0 := by rw [← hz]; exact h
    omega

/-- LEAF: Telescoping step.  The principal model is, by its definition, the sum
over the same range of moduli and reduced residues of the model term multiplied by
the Moebius weight over the totient of the modulus and by the constant of the
principal density.  Subtracting that sum from the double sum of the actual arc
integrals and distributing the constant over the inner sum leaves exactly one
arc error per modulus and reduced residue.  This is an identity in the complex
numbers, with no analytic input and no side condition. -/
theorem leaf_long_model_difference561 (ε D x u : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)))) -
      longPrincipal561 ε D x (b x) u N =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))))) := by
  have key : longPrincipal561 ε D x (b x) u N
      = ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
              (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
                polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
                polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x) ((r : ℝ) / q + s) *
                @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))) := by
    simp only [longPrincipal561, Finset.mul_sum, mul_assoc]
  rw [key, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← Finset.sum_sub_distrib]


/-- LEAF: Triangle step.  The norm of the sum of the single arc errors is at most
the sum of their norms, and each of those is at most the per-arc budget supplied
by the single arc replacement, applied at that modulus and that reduced residue.
The moduli range over the cutoff of the model sum and the reduced residues over
the arc range of their modulus, so the passage from the index of a modulus to its
real value needs the nonnegativity of the arc parameter.  No coefficient
information enters. -/
theorem leaf_long_model_norm_le561 (ε D x u A C₀ : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ)
    (hA : 0 < A) (hD : 0 ≤ D)
    (h : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ‖((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))))‖ ≤ (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖))) :
    ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)))))‖ ≤
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖))) := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun q hq => ?_))
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun r hr => ?_))
  exact h q (Finset.mem_Icc.mp hq).1
    (natCast_le_of_le_natFloor (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2) r hr


/-- LEAF: Moduli collection step.  If the short block is at least half a unit long
and the block position is at least eight, then the double sum of the per-arc
budgets over all moduli up to the cutoff is at most the constant of the
conclusion times the required logarithmic saving times the mass of the short
block.  The residue count cancels the reciprocal of the modulus, the cutoff
bounds the number of moduli, and the surplus saving absorbs that power of the
logarithm.  Elementary summation and power arithmetic only. -/
theorem leaf_long_model_budget_collection561 (ε D x A C₀ : ℝ) (b : ℝ → ℕ → ℂ)
    (hA : 0 < A) (hD : 0 ≤ D) (hx : 8 ≤ x) (hY : 1 / 2 ≤ length512 ε x) :
    (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)))) ≤
      max 1 C₀ * Real.log x ^ (-A) * (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) := by
  set L := Real.log x with hLdef
  set len := length512 ε x with hldef
  set S := ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ with hSdef
  have hL2 : 2 ≤ L := by rw [hLdef]; exact log_ge_two_of_eight_le hx
  have hLpos : 0 < L := by linarith
  have hlen : 0 < len := by rw [hldef]; linarith
  have hY' : (1 / 2 : ℝ) ≤ len := by rw [hldef]; exact hY
  have hS : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hLa : 0 ≤ L ^ (-(A + 6 * D + 3)) := Real.rpow_nonneg hLpos.le _
  have hL4 : 0 ≤ L ^ (4 * D) := Real.rpow_nonneg hLpos.le _
  rcases le_or_gt C₀ 0 with hC | hC
  · have hterm : ∀ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊,
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        (C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * len)) * S) ≤ 0 := by
      intro q hq r hr
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hq).1
      have hden : (0 : ℝ) < (q : ℝ) * len := by positivity
      have hquot : 0 ≤ L ^ (4 * D) / ((q : ℝ) * len) := div_nonneg hL4 hden.le
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC hLa) hquot) hS
    refine le_trans (Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hterm q hq r hr))) ?_
    have hz : (∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (0 : ℝ)) = 0 := by simp
    rw [hz]
    have hmax : max 1 C₀ = 1 := max_eq_left (by linarith)
    rw [hmax, one_mul]
    exact mul_nonneg (Real.rpow_nonneg hLpos.le _) hS
  · have hB : 0 ≤ C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hLa) hL4) hS) hlen.le
    have hq_bound : ∀ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          (C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * len)) * S)) ≤
        C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
      have hlne : len ≠ 0 := ne_of_gt hlen
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ (q : ℝ) := by
        have h1 : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q := by
          refine le_trans (Finset.card_filter_le _ _) ?_
          simp
        exact_mod_cast h1
      have hT : 0 ≤ C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * len)) * S :=
        mul_nonneg (mul_nonneg (mul_nonneg hC.le hLa)
          (div_nonneg hL4 (by positivity))) hS
      refine le_trans (mul_le_mul_of_nonneg_right hcard hT) ?_
      have hkey : (q : ℝ) *
            (C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / ((q : ℝ) * len)) * S)
          = C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len := by
        field_simp
      exact hkey.le
    refine le_trans (Finset.sum_le_sum hq_bound) ?_
    have hsum : (∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊,
        C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len)
        = (⌊L ^ (2 * D)⌋₊ : ℝ) * (C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [hsum]
    have hQle : (⌊L ^ (2 * D)⌋₊ : ℝ) ≤ L ^ (2 * D) :=
      Nat.floor_le (Real.rpow_nonneg hLpos.le _)
    refine le_trans (mul_le_mul_of_nonneg_right hQle hB) ?_
    have hcomb : L ^ (2 * D) * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D)
        = L ^ (-A) * L ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      congr 1
      ring
    have hL3 : L ^ (-(3 : ℝ)) = (L ^ (3 : ℝ))⁻¹ := Real.rpow_neg hLpos.le 3
    have h8le : (8 : ℝ) ≤ L ^ (3 : ℝ) := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hL2 3
      norm_num at h
      simpa using h
    have hL3le : L ^ (-(3 : ℝ)) ≤ 1 / 8 := by
      rw [hL3, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h8le
    have hfrac : L ^ (-(3 : ℝ)) / len ≤ 1 := by
      have h2 : (1 : ℝ) / len ≤ 2 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hY'
        norm_num at h ⊢
        exact h
      have hmul := mul_le_mul hL3le h2 (by positivity : (0 : ℝ) ≤ 1 / len)
        (by norm_num : (0 : ℝ) ≤ 1 / 8)
      have hdiv : L ^ (-(3 : ℝ)) / len = L ^ (-(3 : ℝ)) * (1 / len) := by ring
      rw [hdiv]
      nlinarith [hmul]
    have hCX : C₀ * (L ^ (-(3 : ℝ)) / len) ≤ max 1 C₀ := by
      have hstep := mul_le_mul_of_nonneg_left hfrac hC.le
      rw [mul_one] at hstep
      rcases le_or_gt C₀ 1 with h1 | h1
      · rw [max_eq_left h1]
        exact le_trans hstep h1
      · rw [max_eq_right h1.le]
        exact hstep
    have hstep1 : L ^ (2 * D) * (C₀ * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D) * S / len)
        = (L ^ (2 * D) * L ^ (-(A + 6 * D + 3)) * L ^ (4 * D)) * (C₀ * S / len) := by ring
    rw [hstep1, hcomb]
    have hP2 : 0 ≤ L ^ (-A) * S := mul_nonneg (Real.rpow_nonneg hLpos.le _) hS
    have hmid : (C₀ * L ^ (-A) * S) * (L ^ (-(3 : ℝ)) / len) ≤ max 1 C₀ * L ^ (-A) * S := by
      have h := mul_le_mul_of_nonneg_right hCX hP2
      calc (C₀ * L ^ (-A) * S) * (L ^ (-(3 : ℝ)) / len)
          = (C₀ * (L ^ (-(3 : ℝ)) / len)) * (L ^ (-A) * S) := by ring
        _ ≤ max 1 C₀ * (L ^ (-A) * S) := h
        _ = max 1 C₀ * L ^ (-A) * S := by ring
    calc (L ^ (-A) * L ^ (-(3 : ℝ))) * (C₀ * S / len)
        = (C₀ * L ^ (-A) * S) * (L ^ (-(3 : ℝ)) / len) := by ring
      _ ≤ max 1 C₀ * L ^ (-A) * S := hmid


/-- LEAF: Degenerate block step.  If the block length is below one half then both
floors of the block range are zero, the range of indices of the short block is
empty, and the mass of the short block vanishes identically.  This is the case in
which the summation over the moduli is vacuous and no saving has to be paid
for. -/
theorem leaf_long_model_mass_degenerate561 (ε x : ℝ) (b : ℝ → ℕ → ℂ)
    (hY : length512 ε x < 1 / 2) :
    (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) = 0 := by
  have h2 : ⌊2 * length512 ε x⌋₊ = 0 := by
    apply Nat.floor_eq_zero.mpr
    linarith
  rw [h2, Finset.Ioc_eq_empty_of_le (b := 0) (a := ⌊length512 ε x⌋₊) (Nat.zero_le _)]
  simp


/-- The modulus summation of the long coefficient replacement, assembled from the
telescoping identity, the triangle step, the collection of the per-arc budgets
and the degenerate block step.  The threshold of the conclusion is eight.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_model_summation561_split (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (u A C₀ : ℝ) (N : ℕ),
      0 < A →
      ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x →
      N ∈ frequencies512 ε x →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))‖ ≤
          C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) →
      ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          longPrincipal561 ε D x (b x) u N‖ ≤
        max 1 C₀ * Real.log x ^ (-A) *
          ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  refine ⟨8, ?_⟩
  intro x hx a b u A C₀ N hA hord hN hhyp
  have hD0 : (0 : ℝ) ≤ D := hD
  rw [leaf_long_model_difference561 ε D x u a b N]
  by_cases hY : (1 / 2 : ℝ) ≤ length512 ε x
  · exact le_trans
      (leaf_long_model_norm_le561 ε D x u A C₀ a b N hA hD0
        (fun q hq hqL r hr => hhyp q hq hqL r hr))
      (leaf_long_model_budget_collection561 ε D x A C₀ b hA hD0 hx hY)
  · have hM0 : (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) = 0 :=
      leaf_long_model_mass_degenerate561 ε x b (lt_of_not_ge hY)
    refine le_trans
      (leaf_long_model_norm_le561 ε D x u A C₀ a b N hA hD0
        (fun q hq hqL r hr => hhyp q hq hqL r hr)) ?_
    simp [hM0]

end LeanLab.BHP1997.Decomp561n

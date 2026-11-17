/-
Independent split of the single frequency replacement of the long polynomial by its
principal model.  The major arc integral is written as the sum of its Farey arcs, the
modulus cutoff of the major arcs is dominated by the Farey order, a single arc is
compared with the corresponding model term at a cost of a logarithmic saving times the
window width, and the resulting modulus sum is collected with the elementary harmonic
bound.  The main term of each arc is the mass of the short block.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_coefficient561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Arc decomposition step.  The integrand is a finite sum of characters of the
circle, hence one periodic; the Farey arcs of the major arcs are eventually pairwise
disjoint, of width below the separation of neighbouring fractions with that denominator
cut, and every arc that leaves the fundamental period of the circle re-enters it shifted
by one.  Consequently the integral over the major arcs is the double sum over the
moduli and the reduced residues of the integral over the symmetric local arc around the
centre of that arc, in the local variable of the arc.  No distribution hypothesis and no
coefficient information is used. -/
theorem leaf_long_arc_decomposition561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  refine ⟨Real.exp 1, fun x hx a b N => ?_⟩
  have hx1 : 1 ≤ x := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      linarith
    linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpos : 0 < length512 ε x := by
    unfold length512
    exact Real.rpow_pos_of_pos (by linarith) _
  have hL_nonneg : 0 ≤ length512 ε x := le_of_lt hLpos
  have hlog_nonneg : 0 ≤ Real.log x := le_of_lt hlogpos
  set Q := min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ with hQ
  set W : ℕ → ℝ := fun q => Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x) with hW
  have hW_nonneg : ∀ q, 0 ≤ W q := by
    intro q
    rw [hW]
    refine div_nonneg (Real.rpow_nonneg hlog_nonneg _) ?_
    refine mul_nonneg (Nat.cast_nonneg _) hL_nonneg
  have h_periodic : ∀ t : ℝ, integrand512 ε x (a x) (b x) N (t + 1) = integrand512 ε x (a x) (b x) N t := by
    intro t
    unfold integrand512 polynomial512
    simp [fourier_add, AddCircle.add_comm]
  sorry

/-- LEAF. Order domination step.  The Farey order of the major arcs grows like the
square root of a positive power of the block length, while the modulus cutoff of the
major arcs is a fixed power of the logarithm; from some point on the order is at least
the cutoff, so that the union of arcs is taken over the full range of the model sum.
This is an elementary threshold on `x`, uniform in the arc parameter. -/
theorem leaf_long_order_domination561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := by
  set c : ℝ := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h1 : 0 < 11 / 20 + ε := by
      by_contra! h
      have : ε ≤ -(11 / 20) := by linarith
      linarith [hD]
    have h2 : 0 < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    exact mul_pos h1 h2
  have hc2pos : 0 < c / 2 := by linarith
  set δ : ℝ := c / (4 * (2 * D + 1)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    refine div_pos hc2pos (by linarith [hD])
  refine ⟨Real.exp 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      linarith
    linarith
  have hxpos : 0 ≤ x := by linarith
  have hlog_le : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hxpos hδpos
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpow_le : Real.log x ^ (2 * D) ≤ (x ^ δ / δ) ^ (2 * D) :=
    Real.rpow_le_rpow hlog_nonneg hlog_le (by linarith)
  have hdiv_le : (x ^ δ / δ) ^ (2 * D) ≤ x ^ (δ * (2 * D)) / δ ^ (2 * D) := by
    rw [div_rpow (Real.rpow_nonneg hxpos _) (by linarith)]
    have h1 : (x ^ δ) ^ (2 * D) = x ^ (δ * (2 * D)) := by
      rw [← Real.rpow_mul hxpos]
      ring
    rw [h1]
    exact le_rfl
  have hxpow_le : x ^ (δ * (2 * D)) ≤ x ^ (c / 2) := by
    apply Real.rpow_le_rpow hx1 ?_ (by linarith)
    rw [hδ]
    have : δ * (2 * D) = c / 4 * (2 * D) / (2 * D + 1) := by ring
    rw [this]
    have hpos : 0 < 2 * D + 1 := by linarith
    have hle : 2 * D / (2 * D + 1) ≤ 1 := by
      refine (div_le_one ?_).mpr ?_
      · linarith
      · linarith
    nlinarith
  have hfinal : Real.log x ^ (2 * D) ≤ x ^ (c / 2) := le_trans hpow_le (le_trans hdiv_le hxpow_le)
  have hfloor_le : (⌊Real.log x ^ (2 * D)⌋₊ : ℝ) ≤ Real.log x ^ (2 * D) :=
    Nat.floor_le (Real.rpow_nonneg hlog_nonneg _)
  have horder_lower : (x ^ (c / 2) / 2 : ℝ) ≤ (order512 ε x : ℝ) := by
    unfold order512
    have hpos' : 0 ≤ (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2 := by
      positivity
    have := Nat.floor_le hpos'
    have hlength : length512 ε x = x ^ (11 / 20 + ε) := rfl
    rw [hlength] at this
    have hcalc : (x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) = x ^ c := by
      rw [← Real.rpow_mul hxpos]
      rw [hc]
      ring
    rw [hcalc] at this
    have hsqrt : (x ^ c) ^ (1 / 2 : ℝ) = x ^ (c / 2) := by
      rw [← Real.rpow_mul hxpos]
      ring
    rw [hsqrt] at this
    exact this
  have hfinal' : (⌊Real.log x ^ (2 * D)⌋₊ : ℝ) ≤ (order512 ε x : ℝ) := by
    linarith
  exact_mod_cast hfinal'

/-- LEAF. Single arc replacement step.  On one reduced arc of the major arcs, the
actual long polynomial may be replaced by its principal model: the character expansion
of the phase at the centre of the arc, the prefix distribution of the long coefficients
against the characters of that modulus, the rough support that makes the coefficients
coprime to the modulus, and the total variation of the weight coming from the short
polynomial.  The cost is an arbitrary logarithmic saving times the width of the arc
times the mass of the short block, and it is uniform in the modulus and in the reduced
residue.  The saving is charged at an exponent strictly larger than the one required
later, which is what makes the modulus sum converge. -/
theorem leaf_long_arc_model_replacement561 :
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
      ∀ A : ℝ, 0 < A → ∃ C₀ : ℝ, ∀ x : ℝ, C₀ ≤ x → ∀ D : ℝ, 0 ≤ D →
        ∀ N ∈ frequencies512 ε x, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
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
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Modulus summation step.  If every single arc is within a logarithmic saving
times the width of the arc times the mass of the short block of its model term, then the
double sum over the moduli and the reduced residues is within a fixed constant times the
required saving times the mass of the short block.  There are at most one power of the
logarithm per unit of the arc parameter many moduli, the reduced residue count cancels
against the totient weight of the model, and the extra saving charged per arc pays for
both.  Elementary summation and power arithmetic only. -/
theorem leaf_long_model_summation561 (ε D : ℝ) (hD : 0 ≤ D) :
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
  refine ⟨Real.exp 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
      linarith
    linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_nonneg : 0 ≤ Real.log x := le_of_lt hlogpos
  intro a b u A C₀ N hA hord hN hbound
  set Q := ⌊Real.log x ^ (2 * D)⌋₊ with hQ
  set L := length512 ε x with hL
  set W : ℕ → ℝ := fun q => Real.log x ^ (4 * D) / ((q : ℝ) * L) with hW
  set M : ℝ := ∑ m ∈ Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊, ‖b x m‖ with hM
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hLpos : 0 < L := by
    rw [hL, length512]
    exact Real.rpow_pos_of_pos (by linarith) _
  have h_logpow_nonneg : ∀ (e : ℝ), 0 ≤ Real.log x ^ e := fun e => Real.rpow_nonneg hlog_nonneg e
  unfold longPrincipal561
  have h_diff : (∑ q ∈ Finset.Icc 1 Q,
      ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ s in (-(W q))..(W q), integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
      (u / Real.log x *
        ∑ q ∈ Finset.Icc 1 Q,
          (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) *
            ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
              ∫ t in (-(W q))..(W q),
                polynomial512 (Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊) (fun _ => 1) t *
                polynomial512 (Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊) (b x) ((r : ℝ) / q + t) *
                @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ))) =
      ∑ q ∈ Finset.Icc 1 Q,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ((∫ s in (-(W q))..(W q), integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
            (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
              ∫ s in (-(W q))..(W q),
                polynomial512 (Finset.Ioc ⌊x - 2 * L⌋₊ ⌊x⌋₊) (fun _ => 1) s *
                polynomial512 (Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊) (b x) ((r : ℝ) / q + s) *
                @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [h_diff]
  calc
    ‖∑ q ∈ Finset.Icc 1 Q,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), _‖ ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ‖(∫ s in (-(W q))..(W q), integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
              (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
                ∫ s in (-(W q))..(W q), _‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro q hq
      exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (C₀ * Real.log x ^ (-(A + 6 * D + 3)) * (W q) * M) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq_le : (q : ℝ) ≤ Real.log x ^ (2 * D) := by
        have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
        have hQ_le : (Q : ℝ) ≤ Real.log x ^ (2 * D) := Nat.floor_le (Real.rpow_nonneg hlog_nonneg _)
        exact le_trans (by exact_mod_cast hqQ) hQ_le
      apply Finset.sum_le_sum
      intro r hr
      exact hbound q hq1 hq_le r hr
    _ = C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M *
        (∑ q ∈ Finset.Icc 1 Q, ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card *
          (Real.log x ^ (4 * D) / ((q : ℝ) * L))) := by
      simp [hW, hM, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M *
        (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (Real.log x ^ (4 * D) / ((q : ℝ) * L))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply Finset.sum_le_sum
      intro q hq
      have hcard : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q :=
        Finset.card_filter_le _ _
      have hqpos : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      have hW_nonneg : 0 ≤ Real.log x ^ (4 * D) / ((q : ℝ) * L) := by
        refine div_nonneg (h_logpow_nonneg _) (mul_nonneg hqpos (le_of_lt hLpos))
      nlinarith [mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hW_nonneg]
    _ = C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M *
        (∑ q ∈ Finset.Icc 1 Q, Real.log x ^ (4 * D) / L) := by
      apply congrArg _
      apply Finset.sum_congr rfl
      intro q hq
      have hqpos : (q : ℝ) ≠ 0 := by
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        exact Nat.cast_ne_zero.mpr (by omega)
      field_simp [hqpos]
    _ = C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M *
        ((Q : ℝ) * (Real.log x ^ (4 * D) / L)) := by
      simp [Finset.sum_const, Finset.card_Icc, mul_comm]
    _ ≤ max 1 C₀ * Real.log x ^ (-A) * M := by
      have hQ_le' : (Q : ℝ) ≤ Real.log x ^ (2 * D) :=
        Nat.floor_le (Real.rpow_nonneg hlog_nonneg _)
      have hL_ge_one : 1 ≤ L := by
        rw [hL, length512]
        exact Real.one_le_rpow hx1 (by
          by_contra! h
          have : ε ≤ -(11 / 20) := by linarith
          linarith [hD])
      have hcalc : Real.log x ^ (-(A + 6 * D + 3)) * Real.log x ^ (2 * D) * Real.log x ^ (4 * D) =
          Real.log x ^ (-A - 3) := by
        rw [← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos]
        congr 1
        ring
      have hlog_le : Real.log x ^ (-A - 3) ≤ Real.log x ^ (-A) := by
        refine Real.rpow_le_rpow_of_exponent_le hlog_nonneg ?_
        linarith
      calc
        C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M * ((Q : ℝ) * (Real.log x ^ (4 * D) / L)) ≤
            C₀ * Real.log x ^ (-(A + 6 * D + 3)) * M * (Real.log x ^ (2 * D) * (Real.log x ^ (4 * D) / L)) := by
          gcongr
          exact hQ_le'
        _ = C₀ * M * (Real.log x ^ (-(A + 6 * D + 3)) * Real.log x ^ (2 * D) * Real.log x ^ (4 * D)) / L := by ring
        _ = C₀ * M * Real.log x ^ (-A - 3) / L := by rw [hcalc]
        _ ≤ C₀ * M * Real.log x ^ (-A - 3) := by
          refine (div_le_one hLpos).trans ?_
        _ ≤ C₀ * M * Real.log x ^ (-A) := by
          gcongr
          exact hlog_le
        _ ≤ max 1 C₀ * Real.log x ^ (-A) * M := by
          rw [mul_assoc]
          gcongr
          exact le_max_left _ _

/-- The single frequency long coefficient replacement, assembled from the arc
decomposition, the order domination, the single arc replacement and the modulus
summation.  CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_prefix_replacement561_split :
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
  obtain ⟨εR, hεR, hrep⟩ := leaf_long_arc_model_replacement561
  obtain ⟨εL, hεL, hlen⟩ := leaf_long_length_bounds561
  refine ⟨min εR εL, lt_min hεR hεL, ?_⟩
  intro ε hε hεlt a b u
  dsimp only
  intro hdist hrough A hA
  have hεR' : ε < εR := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεL' : ε < εL := lt_of_lt_of_le hεlt (min_le_right _ _)
  obtain ⟨Xl, hXl⟩ := hlen ε hε hεL'
  obtain ⟨C₀, hC₀⟩ := hrep ε hε hεR' a b u hdist hrough A hA
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : (0 : ℝ) ≤ D := hD
  obtain ⟨Xa, hXa⟩ := leaf_long_arc_decomposition561 ε D
  obtain ⟨Xo, hXo⟩ := leaf_long_order_domination561 ε D hD0
  obtain ⟨Xs, hXs⟩ := leaf_long_model_summation561 ε D hD0
  refine ⟨max (max (max (max Xa Xo) (max Xl C₀)) Xs + 3) (max 1 C₀), fun x hx => ?_⟩
  intro N hN
  have hthr : max (max (max Xa Xo) (max Xl C₀)) Xs + 3 ≤ x := le_trans (le_max_left _ _) hx
  have hthr' : max (max (max Xa Xo) (max Xl C₀)) Xs ≤ x := by linarith
  have hM1 : max (max Xa Xo) (max Xl C₀) ≤ x := le_trans (le_max_left _ _) hthr'
  have hAB : max Xa Xo ≤ x := le_trans (le_max_left _ _) hM1
  have hxa : Xa ≤ x := le_trans (le_max_left _ _) hAB
  have hxo : Xo ≤ x := le_trans (le_max_right _ _) hAB
  have hCD : max Xl C₀ ≤ x := le_trans (le_max_right _ _) hM1
  have hxl : Xl ≤ x := le_trans (le_max_left _ _) hCD
  have hxp : C₀ ≤ x := le_trans (le_max_right _ _) hCD
  have hxs : Xs ≤ x := le_trans (le_max_right _ _) hthr'
  obtain ⟨hL1, hlog1, -⟩ := hXl x hxl
  have hord : ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := hXo x hxo
  have hid : (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
    rw [hXa x hxa a b N, min_eq_right hord]
  rw [hid]
  have hlogpos : 0 < Real.log x := by linarith
  have hM0 : (0 : ℝ) ≤
      ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  refine le_trans (hXs x hxs a b u A C₀ N hA hord hN
    (fun q hq hqL r hr => hC₀ x hxp D hD0 N hN q hq hqL r hr)) ?_
  apply mul_le_mul_of_nonneg_right _ hM0
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (le_of_lt hlogpos) _)

end LeanLab.BHP1997.Decomp561n

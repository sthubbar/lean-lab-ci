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
  sorry

/-- LEAF. Order domination step.  The Farey order of the major arcs grows like the
square root of a positive power of the block length, while the modulus cutoff of the
major arcs is a fixed power of the logarithm; from some point on the order is at least
the cutoff, so that the union of arcs is taken over the full range of the model sum.
This is an elementary threshold on `x`, uniform in the arc parameter. -/
theorem leaf_long_order_domination561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := by
  sorry

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

/-- Summing a per-pair bound `K / q` over the reduced residues of every modulus up to
`Q`: the reduced residue count is at most `q`, so the double sum is at most `K * Q`. -/
private lemma norm_sum_diff_le561 {Q : ℕ} {S : ℕ → Finset ℕ} {F H : ℕ → ℕ → ℂ} {K : ℝ}
    (hK : ∀ q ∈ Finset.Icc 1 Q, ∀ r ∈ S q, ‖F q r - H q r‖ ≤ K / (q : ℝ))
    (hcard : ∀ q ∈ Finset.Icc 1 Q, (S q).card ≤ q) :
    ‖(∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ S q, F q r) -
        (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ S q, H q r)‖ ≤ max (K * (Q : ℝ)) 0 := by
  have hqpos : ∀ q ∈ Finset.Icc 1 Q, (0 : ℝ) < (q : ℝ) := by
    intro q hq
    have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have h2 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
    linarith
  rw [← Finset.sum_sub_distrib]
  rcases le_total K 0 with hK0 | hKpos
  · have hz : ∀ q ∈ Finset.Icc 1 Q, (∑ r ∈ S q, F q r) = (∑ r ∈ S q, H q r) := by
      intro q hq
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have h1 : ‖F q r - H q r‖ ≤ 0 := by
        refine le_trans (hK q hq r hr) ?_
        exact div_nonpos_of_nonpos_of_nonneg hK0 (le_of_lt (hqpos q hq))
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _)))
    have hz' : ∀ q ∈ Finset.Icc 1 Q, ((∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)) = 0 := by
      intro q hq
      rw [hz q hq, sub_self]
    rw [Finset.sum_congr rfl hz']
    simp only [Finset.sum_const_zero, norm_zero]
    exact le_max_right _ _
  · have hstep : ∀ q ∈ Finset.Icc 1 Q,
        ‖(∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)‖ ≤ (S q).card * (K / (q : ℝ)) := by
      intro q hq
      rw [← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ r ∈ S q, ‖F q r - H q r‖ ≤ ∑ r ∈ S q, K / (q : ℝ) :=
            Finset.sum_le_sum (fun r hr => hK q hq r hr)
        _ = (S q).card * (K / (q : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc ‖∑ q ∈ Finset.Icc 1 Q, ((∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r))‖
        ≤ ∑ q ∈ Finset.Icc 1 Q, ‖(∑ r ∈ S q, F q r) - (∑ r ∈ S q, H q r)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, (S q).card * (K / (q : ℝ)) := Finset.sum_le_sum hstep
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (K / (q : ℝ)) := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast hcard q hq
            · exact div_nonneg hKpos (le_of_lt (hqpos q hq))
      _ = ∑ _q ∈ Finset.Icc 1 Q, K := by
            refine Finset.sum_congr rfl (fun q hq => ?_)
            have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (hqpos q hq)
            field_simp
      _ = (Q : ℝ) * K := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ max (K * (Q : ℝ)) 0 := by
            rw [mul_comm]
            exact le_max_left _ _

/-- The scalar bookkeeping of the modulus summation: a per-arc saving
`log x ^ (-(A + 6D + 3))` multiplied by `log x ^ (2D)` moduli, `log x ^ (4D)` arc widths
and a block length at least one gives the required `log x ^ (-A)`. -/
private lemma scalar_bookkeeping561 {L len A C₀ M : ℝ} {Q : ℕ} {D : ℝ}
    (hL1 : 1 ≤ L) (hlen1 : 1 ≤ len) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hQ : (Q : ℝ) ≤ L ^ (2 * D)) :
    max (C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) 0
      ≤ max 1 C₀ * L ^ (-A) * M := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hlenpos : (0 : ℝ) < len := lt_of_lt_of_le zero_lt_one hlen1
  have hlnn : (0 : ℝ) ≤ L ^ (-A) := Real.rpow_nonneg hLpos.le _
  have hcore : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) ≤ L ^ (-A) * M := by
    have hexp : ∀ p q : ℝ, L ^ p * L ^ q = L ^ (p + q) := fun p q => (Real.rpow_add hLpos p q).symm
    have hcomb : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) * L ^ (2 * D)) =
        L ^ (-A) * L ^ (-(3 : ℝ)) := by
      rw [hexp (4 * D) (2 * D), hexp (-(A + 6 * D + 3)) (4 * D + 2 * D), hexp (-A) (-(3 : ℝ)),
        show -(A + 6 * D + 3) + (4 * D + 2 * D) = -A + -(3 : ℝ) by ring]
    have hstep1 : L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
        = (L ^ (-(A + 6 * D + 3)) * M) * ((L ^ (4 * D) / len) * (Q : ℝ)) := by ring
    have hstep2 : (L ^ (4 * D) / len) * (Q : ℝ) ≤ L ^ (4 * D) * L ^ (2 * D) / len := by
      calc (L ^ (4 * D) / len) * (Q : ℝ) ≤ (L ^ (4 * D) / len) * L ^ (2 * D) :=
            mul_le_mul_of_nonneg_left hQ (by positivity)
        _ = L ^ (4 * D) * L ^ (2 * D) / len := by ring
    have hKnn : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * M := by
      have h1 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) := Real.rpow_nonneg hLpos.le _
      positivity
    have hstep3 : (L ^ (-(A + 6 * D + 3)) * M) * (L ^ (4 * D) * L ^ (2 * D) / len)
        = L ^ (-A) * L ^ (-(3 : ℝ)) * M / len := by
      rw [← hcomb]
      ring
    have hstep4 : L ^ (-A) * L ^ (-(3 : ℝ)) * M / len ≤ L ^ (-A) * M := by
      have h3 : L ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have h4 : L ^ (-A) * L ^ (-(3 : ℝ)) * M ≤ L ^ (-A) * 1 * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        exact mul_le_mul_of_nonneg_left h3 hlnn
      have h5 : (0 : ℝ) ≤ L ^ (-A) * L ^ (-(3 : ℝ)) * M := by positivity
      calc L ^ (-A) * L ^ (-(3 : ℝ)) * M / len ≤ L ^ (-A) * L ^ (-(3 : ℝ)) * M :=
            div_le_self h5 hlen1
        _ ≤ L ^ (-A) * 1 * M := h4
        _ = L ^ (-A) * M := by ring
    calc L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
        = (L ^ (-(A + 6 * D + 3)) * M) * ((L ^ (4 * D) / len) * (Q : ℝ)) := hstep1
      _ ≤ (L ^ (-(A + 6 * D + 3)) * M) * (L ^ (4 * D) * L ^ (2 * D) / len) :=
            mul_le_mul_of_nonneg_left hstep2 hKnn
      _ = L ^ (-A) * L ^ (-(3 : ℝ)) * M / len := hstep3
      _ ≤ L ^ (-A) * M := hstep4
  have hXQ : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by
    have h2 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ L ^ (4 * D) / len :=
      div_nonneg (Real.rpow_nonneg hLpos.le _) hlenpos.le
    have h4 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
    have h6 : (0 : ℝ) ≤ L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M := by positivity
    exact mul_nonneg h6 h4
  have hsplit : C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
      = C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) := by ring
  rcases lt_trichotomy C₀ 0 with hC₀ | hC₀ | hC₀
  · have hKQ : C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) ≤ 0 := by
      calc C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)
          = C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) := hsplit
        _ ≤ 0 * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ)) :=
              mul_le_mul_of_nonneg_right hC₀.le hXQ
        _ = 0 := by ring
    rw [max_eq_right hKQ]
    have hfin : (0 : ℝ) ≤ max 1 C₀ * L ^ (-A) * M := by
      have h1 : (0 : ℝ) ≤ max 1 C₀ := le_trans zero_le_one (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ max 1 C₀ * L ^ (-A) := mul_nonneg h1 hlnn
      exact mul_nonneg h2 hM
    linarith
  · subst hC₀
    rw [max_eq_left zero_le_one]
    simp only [zero_mul, max_self, one_mul]
    exact mul_nonneg (Real.rpow_nonneg hLpos.le _) hM
  · have h1 : C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ))
        ≤ C₀ * (L ^ (-A) * M) := mul_le_mul_of_nonneg_left hcore hC₀.le
    have hprod : (0 : ℝ) ≤ L ^ (-A) * M := mul_nonneg hlnn hM
    have h2 : C₀ * (L ^ (-A) * M) ≤ max 1 C₀ * (L ^ (-A) * M) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hprod
    have h4 : C₀ * (L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ))
        = C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by ring
    have h5 : C₀ * (L ^ (-A) * M) = C₀ * L ^ (-A) * M := by ring
    have h6 : max 1 C₀ * (L ^ (-A) * M) = max 1 C₀ * L ^ (-A) * M := by ring
    have hKQnn : (0 : ℝ) ≤ C₀ * L ^ (-(A + 6 * D + 3)) * (L ^ (4 * D) / len) * M * (Q : ℝ) := by
      rw [hsplit]
      exact mul_nonneg hC₀.le hXQ
    rw [max_eq_left hKQnn]
    linarith [h1, h2, h4, h5, h6]

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

  by_cases hc : (0 : ℝ) < 11 / 20 + ε
  · refine ⟨max 1 (Real.exp 2) + 1, ?_⟩
    intro x hx a b u A C₀ N hA hord _hNfreq hhyp
    have hxe : Real.exp 2 ≤ x := by
      have h0 : Real.exp 2 ≤ max 1 (Real.exp 2) := le_max_right _ _
      linarith
    have hexp2 : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have hx1' : (1 : ℝ) < x := lt_of_lt_of_le hexp2 hxe
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx1'
    have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1'
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    have hlen1 : (1 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.one_le_rpow hx1 (le_of_lt hc)
    have hlenpos : (0 : ℝ) < length512 ε x := lt_of_lt_of_le zero_lt_one hlen1
    have hQle : ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (2 * D) :=
      Nat.floor_le (Real.rpow_nonneg hLpos.le _)
    have hMnn : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
      Finset.sum_nonneg (fun m _ => norm_nonneg _)
    have hmin : min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ = ⌊Real.log x ^ (2 * D)⌋₊ :=
      min_eq_right hord
    have hQcard : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q := by
      intro q hq
      have h1 : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ (Finset.Icc 1 q).card :=
        Finset.card_filter_le _ _
      have h2 : (Finset.Icc 1 q).card = q := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      omega
    have hKstep : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)))‖ ≤
          (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
              (Real.log x ^ (4 * D) / length512 ε x) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) / (q : ℝ) := by
      intro q hq r hr
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq2 : q ≤ ⌊Real.log x ^ (2 * D)⌋₊ := (Finset.mem_Icc.mp hq).2
      have hqle : (q : ℝ) ≤ Real.log x ^ (2 * D) := by
        have h2 : (q : ℝ) ≤ ((⌊Real.log x ^ (2 * D)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq2
        linarith
      have h1 := hhyp q hq1 hqle r hr
      refine le_trans h1 (le_of_eq ?_)
      have hq0 : (q : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        linarith
      have hlen0 : length512 ε x ≠ 0 := ne_of_gt hlenpos
      field_simp
    have hlp : longPrincipal561 ε D x (b x) u N =
        ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
              ∫ s in (-(Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)))..
                  (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)),
                polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
                polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                  ((r : ℝ) / q + s) *
                @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)) := by
      unfold longPrincipal561
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← mul_assoc, Finset.mul_sum]
    rw [hlp]
    refine le_trans (norm_sum_diff_le561 (S := fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
      (K := C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
        (Real.log x ^ (4 * D) / length512 ε x) *
        ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)
      hKstep hQcard) ?_
    exact scalar_bookkeeping561 (L := Real.log x) (len := length512 ε x) (A := A) (C₀ := C₀)
      (M := ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)
      (Q := ⌊Real.log x ^ (2 * D)⌋₊) (D := D) hL1 hlen1 hMnn hD hQle
  · push Not at hc
    refine ⟨max 1 (Real.exp 2), ?_⟩
    intro x hx a b u A C₀ N hA hord _hNfreq _hhyp
    exfalso
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left (1 : ℝ) (Real.exp 2)) hx
    have hxe : Real.exp 2 ≤ x := le_trans (le_max_right (1 : ℝ) (Real.exp 2)) hx
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 2) hxe
      rw [Real.log_exp] at h
      linarith
    have hlenle1 : length512 ε x ≤ 1 := by
      unfold length512
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 hc
    have hlen0 : (0 : ℝ) ≤ length512 ε x := by
      unfold length512
      exact Real.rpow_nonneg (le_trans zero_le_one hx1) _
    have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
    have hord0 : order512 ε x = 0 := by
      unfold order512
      have h1 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
        refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
        exact Real.rpow_le_one hlen0 hlenle1 hdelta
      have h2 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2 < 1 := by
        linarith
      exact Nat.floor_eq_zero.mpr h2
    have hge : (1 : ℕ) ≤ ⌊Real.log x ^ (2 * D)⌋₊ := by
      refine Nat.floor_pos.mpr ?_
      exact Real.one_le_rpow hL1 (by linarith)
    rw [hord0] at hord
    omega

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

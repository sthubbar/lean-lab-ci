/-
FALSE_local_arc_shoulder1622_arc_mean_value. AI wrote the Lean code. Binary Goldbach is open.

Split of a refutation. The leaf local_arc_shoulder1622_arc_mean_value of
SPLIT_local_arc_shoulder1622.lean is suspected false, and this file reduces its refutation
to one averaged lower bound, a LEAF below. The leaf file is not imported; its conclusion is
copied verbatim as a negated Prop. Unit S7-05 of route burst 20261124.

Why it fails. At modulus 1 the arc integral localArc1622 N 1 n is the modulus 1 piece of
the binary main term, of size about N over log squared N for n near N; an FFT evaluation
gave about 0.4 N over log squared N at N equal to 10^4, 10^5 and 10^6. The leaf allows only
about N^{13/14} log^13 N, which is smaller once log N is beyond about 1500.

Refutation route, unconditional and elementary, for the LEAF arc_average_lower1622:
1. Pairing. For weights h supported on n at most N, the sum of h n times localArc1622 N 1 n
   is the arc integral of S squared times H, with S the damped prime series and H the
   trigonometric polynomial with coefficients h.
2. Choice of H. H is the conjugate square of A, the damped prime series cut at N over 2
   minus M, times the Fejer kernel of degree M equal to about the square root of N; all
   frequencies are at most N and all coefficients are nonnegative, with sum about M N^2.
3. Circle energy. Over the whole circle the pairing has only nonnegative terms and is at
   least the fourth moment of A against the Fejer kernel, which on the window of half width
   1 over 8 N is at least a constant times M N^3 over log^4 N, by Chebyshev's lower bound.
4. Off arc. Off the arc of half width N^{-1/7} the Fejer kernel is at most N^{2/7} over 4 M,
   and Parseval bounds the rest by N^3 over log N times that, which is smaller.
Dividing by the coefficient sum gives the leaf with a constant over log^4 N.
-/
import LeanLab.Linnik1951.Data491
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.Linnik1951.FALSEshoulder1622

open Filter Asymptotics LeanLab.Linnik1951
open scoped Topology

/-- LEAF: refutation of the shoulder step of pages 159 to 161 at modulus 1, the averaged
singular integral lower bound, steps 1 to 4 of the route in the file header. A nonnegative
average of localArc1622 N 1 n over residuals n at most N has norm at least a constant times
the total weight times N over log^4 N. HARD. -/
theorem arc_average_lower1622 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop, ∃ s : Finset ℤ, ∃ h : ℤ → ℝ,
      (∀ n ∈ s, n ≤ (N : ℤ) ∧ 0 ≤ h n) ∧ 0 < ∑ n ∈ s, h n ∧
        κ * (∑ n ∈ s, h n) * (N : ℝ) / Real.log N ^ 4 ≤
          ‖∑ n ∈ s, ((h n : ℝ) : ℂ) * localArc1622 N 1 n‖ := by
  sorry

/-- Eventual size facts at the exponent one fourteenth with log to the 17. -/
theorem eventual_facts17 (K : ℝ) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      K * Real.log N ^ 17 < (N : ℝ) ^ (1 / 14 : ℝ) ∧ (1 : ℝ) ≤ (N : ℝ) ^ (1 / 14 : ℝ) ∧
        (1 : ℝ) < (N : ℝ) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h3 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ) ^ (1 / 14 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14)).comp hcast).eventually_ge_atTop 1
  have h4 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) < (N : ℝ) := hcast.eventually (eventually_gt_atTop 1)
  have h1 : ∀ᶠ N : ℕ in atTop, K * Real.log N ^ 17 < (N : ℝ) ^ (1 / 14 : ℝ) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (17 : ℝ) (by norm_num : (0 : ℝ) < 1 / 14)
    have hb := hlo.bound (show 0 < 1 / (K + 1) by positivity)
    filter_upwards [hcast.eventually hb, hcast.eventually (eventually_gt_atTop (1 : ℝ))]
      with N hN hN1
    have hl : 0 < Real.log N := Real.log_pos hN1
    have hp : 0 < (N : ℝ) ^ (1 / 14 : ℝ) := by positivity
    have hpow : Real.log N ^ (17 : ℝ) = Real.log N ^ (17 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (Real.log N) 17
    rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp,
      abs_of_pos (by positivity : 0 < Real.log N ^ 17)] at hN
    have hd : 0 < K + 1 := by positivity
    have h6 : (K + 1) * Real.log N ^ 17 ≤ (N : ℝ) ^ (1 / 14 : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd] at hN
      linarith
    have : 0 < Real.log N ^ 17 := by positivity
    nlinarith
  exact h1.and (h3.and h4) |>.mono fun N h => ⟨h.1, h.2.1, h.2.2⟩

/-- The bound of the leaf at modulus 1 is at most 2 c N log^13 N over N^{1/14}. -/
theorem shoulder_bound_q1_le (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : (1 : ℝ) < N) :
    c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      2 * c * (N : ℝ) * Real.log N ^ 13 / (N : ℝ) ^ (1 / 14 : ℝ) := by
  set σ := (N : ℝ) ^ (1 / 14 : ℝ) with hσ
  have hNr : (0 : ℝ) < N := by linarith
  have hσ1 : 1 ≤ σ := Real.one_le_rpow hN.le (by norm_num)
  have hσpos : 0 < σ := by linarith
  have h7 : (N : ℝ) ^ (1 / 7 : ℝ) = σ ^ 2 := by
    rw [hσ, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num
  rw [h7]
  have hsq : Real.sqrt (((1 : ℕ) : ℝ) * σ ^ 2) = σ := by
    rw [Nat.cast_one, one_mul, Real.sqrt_sq hσpos.le]
  rw [hsq]
  have hs1 : 1 / σ ^ 2 ≤ 1 / σ := one_div_le_one_div_of_le hσpos (by nlinarith)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN.le
  have hcoef : 0 ≤ c * (N : ℝ) * Real.log N ^ 13 := by positivity
  calc c * (N : ℝ) * Real.log N ^ 13 * (1 / σ ^ 2 + 1 / σ)
      ≤ c * (N : ℝ) * Real.log N ^ 13 * (1 / σ + 1 / σ) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef
    _ = 2 * c * (N : ℝ) * Real.log N ^ 13 / σ := by ring

/-- FALSE leaf refuted from the LEAF arc_average_lower1622. The conclusion of
local_arc_shoulder1622_arc_mean_value, copied verbatim, fails: at modulus 1 the averaged arc
integral is at least of order N over log^4 N, while the leaf bound is of order N^{13/14}
times log^13 N. The leaf file is not imported. -/
theorem not_local_arc_shoulder1622_arc_mean_value : ¬ (
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  rintro ⟨c, hc, N0, hb⟩
  obtain ⟨κ, hκ, hev⟩ := arc_average_lower1622
  obtain ⟨N, ⟨hlow, hN0⟩, hfin, hσ1, hN1⟩ :=
    ((hev.and (eventually_gt_atTop N0)).and
      (eventual_facts17 (2 * c / κ) (by positivity))).exists
  obtain ⟨s, h, hs, hpos, hge⟩ := hlow
  set ℓ := Real.log N with hℓ
  set σ := (N : ℝ) ^ (1 / 14 : ℝ) with hσ
  have hNr : (0 : ℝ) < N := by linarith
  have hℓ0 : 0 < ℓ := Real.log_pos hN1
  have hσpos : 0 < σ := by linarith
  have hq : ((1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [Nat.cast_one]; exact Real.one_le_rpow hN1.le (by norm_num)
  set B := c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
    with hB
  have hterm : ∀ n ∈ s, ‖((h n : ℝ) : ℂ) * localArc1622 N 1 n‖ ≤ h n * B := by
    intro n hn
    obtain ⟨hnN, hh⟩ := hs n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left (hb N hN0 1 le_rfl hq n hnN) hh
  have hup : ‖∑ n ∈ s, ((h n : ℝ) : ℂ) * localArc1622 N 1 n‖ ≤ (∑ n ∈ s, h n) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_mul]
  have hB2 : B ≤ 2 * c * (N : ℝ) * ℓ ^ 13 / σ := shoulder_bound_q1_le c hc N hN1
  have hchain : κ * (∑ n ∈ s, h n) * (N : ℝ) / ℓ ^ 4 ≤
      (∑ n ∈ s, h n) * (2 * c * (N : ℝ) * ℓ ^ 13 / σ) :=
    hge.trans (hup.trans (mul_le_mul_of_nonneg_left hB2 hpos.le))
  have hℓ4 : 0 < ℓ ^ 4 := by positivity
  rw [div_le_iff₀ hℓ4] at hchain
  have hkey : κ * σ ≤ 2 * c * ℓ ^ 17 := by
    have e1 : (∑ n ∈ s, h n) * (2 * c * (N : ℝ) * ℓ ^ 13 / σ) * ℓ ^ 4 =
        ((∑ n ∈ s, h n) * (N : ℝ)) * (2 * c * ℓ ^ 17) / σ := by
      field_simp
    rw [e1, le_div_iff₀ hσpos] at hchain
    have hSN : 0 < (∑ n ∈ s, h n) * (N : ℝ) := mul_pos hpos hNr
    have e2 : κ * (∑ n ∈ s, h n) * (N : ℝ) * σ = ((∑ n ∈ s, h n) * (N : ℝ)) * (κ * σ) := by
      ring
    rw [e2] at hchain
    exact le_of_mul_le_mul_left hchain hSN
  have hfin' : 2 * c / κ * ℓ ^ 17 < σ := hfin
  rw [div_mul_eq_mul_div, div_lt_iff₀ hκ] at hfin'
  linarith

end LeanLab.Linnik1951.FALSEshoulder1622

#print axioms LeanLab.Linnik1951.FALSEshoulder1622.eventual_facts17
#print axioms LeanLab.Linnik1951.FALSEshoulder1622.shoulder_bound_q1_le
#print axioms LeanLab.Linnik1951.FALSEshoulder1622.not_local_arc_shoulder1622_arc_mean_value

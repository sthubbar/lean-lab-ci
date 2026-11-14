/-
Jia 1996 pages 270, 274 and 275, Lemma 25 and display 65 on page 286.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The two source transfers remain OPEN. The assembly is CONDITIONAL.
-/
import LeanLab.Languasco2004.GroupSplit548
import LeanLab.Languasco2004.Numeric548
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.Decomp567a
open Finset Real Decomp279a Decomp316c GroupSplit548 Numeric548 Integral548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 48 and page 270: the integer model S of B_d and z.
The prime divisors used for this model are all primes below z. -/
def roughCount (Y : ℝ) (d : ℕ) (z : ℝ) : ℕ :=
  ((range (⌊2 * Y⌋₊ + 1)).filter (fun a : ℕ =>
    Y < (a : ℝ) ∧ (a : ℝ) ≤ 2 * Y ∧ d ∣ a ∧
    ∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a)).card

/-- Pages 270 and 274: the rough integer model for the selected region 47.
The finite caps and region selection are the caps of pieceSum. -/
def roughModel47 (N Y : ℝ) (n : ℕ) : ℝ :=
  singular n / Real.log N *
    ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
      Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
      ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
        if groupOf (regionIndex Y p q) = 2 ∧ regionIndex Y p q = 47
          then (roughCount Y (p * q) q : ℝ) else 0

/-- Page 275: the exact numerical coefficient before its printed rounding. -/
def integral47 : ℝ := ∫ t in (11 / 27 : ℝ)..(34 / 81), inner47 t

/-- LEAF. Jia page 274, Lemma 25, using Lemma 10 and Lemma 18,
display 32 on page 253 and the first comparison on page 270.
Only the prime count to rough integer comparison is asserted.
Its exceptional set has the logarithmic saving of page 263. -/
theorem prime_to_rough47 :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧
      ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n =>
          pieceSum 2 47 true N (localization N ε) n <
            roughModel47 N (localization N ε) n -
              K * ε * scale N (localization N ε) n)).card : ℝ) ≤
          C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 275, first integral of Lemma 25, using Lemma 21
on page 262 and the second and third comparisons on page 270.
This deterministic step evaluates the rough model. It asserts no
exceptional prime estimate and uses no printed decimal coefficient. -/
theorem rough_to_integral47 :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ n ∈ window N ε,
        (integral47 - K * ε) * scale N (localization N ε) n ≤
          roughModel47 N (localization N ε) n := by sorry

/-- Page 275: the certified integral leaves a reserve of four ten millionths. -/
theorem integral47_reserve : (0.0058884 : ℝ) ≤ integral47 :=
  region47_numeric_margin

/-- Pages 274 and 275: a nonnegative scale absorbs both relative errors.
This is the finite comparison used before counting exceptions. -/
theorem coefficient_comparison (I K L ε s model value : ℝ)
    (hI : (0.0058884 : ℝ) ≤ I) (hs : 0 ≤ s)
    (herr : (K + L) * ε ≤ 0.0000004)
    (hmodel : (I - L * ε) * s ≤ model)
    (hvalue : model - K * ε * s ≤ value) :
    0.005888 * s ≤ value := by
  have hc : (0.005888 : ℝ) ≤ I - (K + L) * ε := by linarith
  have hm := mul_le_mul_of_nonneg_right hc hs
  nlinarith

/-- Pages 274 and 275: the exact sealed region47_lower type follows
from the two strictly smaller source transfers. CONDITIONAL ON
prime_to_rough47 and rough_to_integral47. No admission occurs here. -/
theorem region47_lower_from_transfers :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 2 47 true N (localization N ε) n <
        0.005888 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨K, e1, hK, he1, h1⟩ := prime_to_rough47
  obtain ⟨L, e2, hL, he2, h2⟩ := rough_to_integral47
  let e3 : ℝ := 0.0000004 / (K + L + 1)
  have he3 : 0 < e3 := by dsimp [e3]; positivity
  refine ⟨min e1 (min e2 e3), lt_min he1 (lt_min he2 he3), ?_⟩
  intro ε B hε he hB
  have hε1 := he.trans_le (min_le_left e1 (min e2 e3))
  have hε2 := he.trans_le ((min_le_right e1 (min e2 e3)).trans (min_le_left e2 e3))
  have hε3 := he.trans_le ((min_le_right e1 (min e2 e3)).trans (min_le_right e2 e3))
  obtain ⟨C, N1, hN1⟩ := h1 ε B hε hε1 hB
  obtain ⟨N2, hN2⟩ := h2 ε hε hε2
  refine ⟨C, max 1 (max N1 N2), ?_⟩
  intro N hN
  have hN0 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN1' : N1 ≤ N := ((le_max_left N1 N2).trans (le_max_right 1 _)).trans hN
  have hN2' : N2 ≤ N := ((le_max_right N1 N2).trans (le_max_right 1 _)).trans hN
  have hY : 1 ≤ localization N ε := by
    unfold localization
    exact Real.one_le_rpow hN0 (by linarith)
  have herr : (K + L) * ε ≤ 0.0000004 := by
    have hh : ε * (K + L + 1) < 0.0000004 :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < K + L + 1)).mp hε3
    nlinarith
  have hsub : (window N ε).filter (fun n =>
      pieceSum 2 47 true N (localization N ε) n <
        0.005888 * scale N (localization N ε) n) ⊆
      (window N ε).filter (fun n =>
        pieceSum 2 47 true N (localization N ε) n <
          roughModel47 N (localization N ε) n -
            K * ε * scale N (localization N ε) n) := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨hnw, ?_⟩
    by_contra hnot
    have hv := le_of_not_gt hnot
    have hc := coefficient_comparison integral47 K L ε
      (scale N (localization N ε) n) (roughModel47 N (localization N ε) n)
      (pieceSum 2 47 true N (localization N ε) n) integral47_reserve
      (Decomp316a.scale_nonneg n hN0 hY) herr (hN2 N hN2' n hnw) hv
    exact (not_lt_of_ge hc) hbad
  exact (show (((window N ε).filter (fun n =>
      pieceSum 2 47 true N (localization N ε) n <
        0.005888 * scale N (localization N ε) n)).card : ℝ) ≤ _ from
      Nat.cast_le.mpr (card_le_card hsub)).trans (hN1 N hN1')

#print axioms integral47_reserve
#print axioms coefficient_comparison
#print axioms prime_to_rough47
#print axioms rough_to_integral47
#print axioms region47_lower_from_transfers
end
end LeanLab.Languasco2004.Decomp567a

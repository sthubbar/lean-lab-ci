import LeanLab.Ricci1937.CCounts
import LeanLab.Ricci1937.CErrorAbsorption
import LeanLab.Ricci1937.CTau
import LeanLab.Ricci1937.SigmaBar

/-!
Ricci 1937, Theorem C part 1, pages 74, 82 and 83.
The final assembly has exactly type TheoremC1 and depends on cited sieve leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.Ricci1937
open Finset Filter Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The fixed threshold survivor count in the proof on page 82. -/
def decomp87FixedRoughCount (P : Polynomial ℤ) (ω : ℝ) (ξ : ℕ) : ℕ :=
  #{n ∈ Icc (1 : ℕ) ξ | 1 ≤ Fval P n ∧
    ∀ p ∈ (Fval P n).primeFactorsList, (ξ : ℝ) ^ ω < (p : ℝ)}

/-- LEAF. Page 83, last lower display, with the gap from 2.4.
Theorem I and the Nagel product input used by its proof remain unresolved.
The coefficient bound is task67's larger uniform bound. -/
theorem decomp87_lower_sieve (P : Polynomial ℤ) (hP : CHyp P) (s : ℕ)
    (hs : P.natDegree + 1 ≤ s) (hs3 : s ≤ 3 * P.natDegree) :
    ∃ a A : ℝ, 0 < a ∧ ∀ᶠ ξ : ℕ in atTop,
      a * ξ / Real.log ξ - A * (ξ : ℝ) ^
        (1 - (0.0052 : ℝ) / ((P.natDegree : ℝ) + 1)) < c2SiftedCount P s ξ := by
  sorry

/-- LEAF. Page 82, application of 3.2 before removing the power error.
Theorem I and its cited Nagel product input remain unresolved. -/
theorem decomp87_upper_sieve (P : Polynomial ℤ) (hP : CHyp P) (ω : ℝ)
    (hω : 0 < ω) (herror : ω * (2 + 2 * ricciTau 1 + 0.01) < 1) :
    ∃ a A κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ᶠ ξ : ℕ in atTop,
      (decomp87FixedRoughCount P ω ξ : ℝ) ≤
        a * ξ / Real.log ξ + A * (ξ : ℝ) ^ (1 - κ) := by
  sorry

/-- LEAF. Page 82, monotonicity of the fixed prime threshold. -/
theorem decomp87_fixed_mono (P : Polynomial ℤ) {α β : ℝ} {ξ : ℕ}
    (hξ : 1 ≤ ξ) (hαβ : α ≤ β) :
    decomp87FixedRoughCount P β ξ ≤ decomp87FixedRoughCount P α ξ := by
  apply card_le_card
  intro n hn
  rcases mem_filter.mp hn with ⟨hn, hx, hp⟩
  refine mem_filter.mpr ⟨hn, hx, fun p hpm => ?_⟩
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hξ) hαβ) (hp p hpm)

/-- LEAF. Page 82, cutoff with eta equal to one half. -/
theorem decomp87_cutoff (P : Polynomial ℤ) {ω : ℝ} (hω : 0 < ω) (ξ : ℕ) :
    roughValueCount P ω ξ ≤ Nat.floor ((ξ : ℝ) ^ ((1 : ℝ) / 2)) +
      decomp87FixedRoughCount P (ω / 2) ξ := by
  let T := Nat.floor ((ξ : ℝ) ^ ((1 : ℝ) / 2))
  let S := {n ∈ Icc (1 : ℕ) ξ | 1 ≤ Fval P n ∧
    ∀ p ∈ (Fval P n).primeFactorsList, (ξ : ℝ) ^ (ω / 2) < (p : ℝ)}
  have hsub : {n ∈ Icc (1 : ℕ) ξ | 1 ≤ Fval P n ∧
      ∀ p ∈ (Fval P n).primeFactorsList, (n : ℝ) ^ ω < (p : ℝ)} ⊆ Icc 1 T ∪ S := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hnI, hx, hp⟩
    by_cases hsmall : n ≤ T
    · exact mem_union_left _ (mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, hsmall⟩)
    · apply mem_union_right
      refine mem_filter.mpr ⟨hnI, hx, fun p hpm => ?_⟩
      have hlarge : (ξ : ℝ) ^ ((1 : ℝ) / 2) < n :=
        (Nat.floor_lt (by positivity)).mp (by omega : T < n)
      have hpow : (ξ : ℝ) ^ (ω / 2) ≤ (n : ℝ) ^ ω := by
        rw [show ω / 2 = (1 / 2 : ℝ) * ω by ring, Real.rpow_mul (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hlarge.le hω.le
      exact hpow.trans_lt (hp p hpm)
  calc
    roughValueCount P ω ξ ≤ #(Icc 1 T ∪ S) := card_le_card hsub
    _ ≤ #(Icc 1 T) + #S := card_union_le _ _
    _ = T + decomp87FixedRoughCount P (ω / 2) ξ := by simp [S, decomp87FixedRoughCount]


/-- LEAF. Page 82, a smaller exponent giving a saved power upper error. -/
theorem decomp87_upper_parameter {ω : ℝ} (hω : 0 < ω) :
    0 < min (ω / 2) (1 / 8) ∧ min (ω / 2) (1 / 8) ≤ ω / 2 ∧
      min (ω / 2) (1 / 8) * (2 + 2 * ricciTau 1 + 0.01) < 1 := by
  have hpos : 0 < min (ω / 2) (1 / 8) := lt_min (by positivity) (by norm_num)
  refine ⟨hpos, min_le_left _ _, ?_⟩
  have hle : min (ω / 2) (1 / 8) ≤ (1 / 8 : ℝ) := min_le_right _ _
  have ht := ricciTau_one_lt
  nlinarith

/-- LEAF. Page 83, absorb the saved power lower remainder.
This implication is unconditional. Its application needs the lower sieve leaf. -/
theorem decomp87_lower_absorb (P : Polynomial ℤ) (s : ℕ) {a A : ℝ}
    (ha : 0 < a)
    (hbound : ∀ᶠ ξ : ℕ in atTop,
      a * ξ / Real.log ξ - A * (ξ : ℝ) ^
        (1 - (0.0052 : ℝ) / ((P.natDegree : ℝ) + 1)) < c2SiftedCount P s ξ) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      b * ξ / Real.log ξ < c2SiftedCount P s ξ := by
  exact ricci_lower_of_main_error ha (by positivity) A hbound

/-- LEAF. Page 82, absorb the cutoff and upper sieve power error.
This implication is unconditional. Its application needs the upper sieve leaf. -/
theorem decomp87_upper_absorb (P : Polynomial ℤ) {ω δ a A κ : ℝ}
    (hω : 0 < ω) (hδ : δ ≤ ω / 2) (ha : 0 < a) (hκ : 0 < κ)
    (hbound : ∀ᶠ ξ : ℕ in atTop,
      (decomp87FixedRoughCount P δ ξ : ℝ) ≤
        a * ξ / Real.log ξ + A * (ξ : ℝ) ^ (1 - κ)) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      (roughValueCount P ω ξ : ℝ) < b * ξ / Real.log ξ := by
  have hevent : ∀ᶠ ξ : ℕ in atTop,
      (roughValueCount P ω ξ : ℝ) < (a + 3) * ξ / Real.log ξ := by
    filter_upwards [hbound,
      ricci_power_error_absorb hκ (by norm_num : (0 : ℝ) < 2) A,
      ricci_power_error_absorb (κ := (1 : ℝ) / 2) (by norm_num)
        (by norm_num : (0 : ℝ) < 2) 1,
      eventually_ge_atTop 2] with ξ hb he hs hξ
    have hξ1 : 1 ≤ ξ := by omega
    have hcount : (roughValueCount P ω ξ : ℝ) ≤
        (Nat.floor ((ξ : ℝ) ^ ((1 : ℝ) / 2)) : ℝ) +
        decomp87FixedRoughCount P δ ξ := by
      exact_mod_cast (decomp87_cutoff P hω ξ).trans
        (Nat.add_le_add_left (decomp87_fixed_mono P hξ1 hδ) _)
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ (ξ : ℝ) ^ ((1 : ℝ) / 2) by positivity)
    have hlog : 0 < Real.log (ξ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ξ))
    have hmain : 0 < (ξ : ℝ) / Real.log ξ := div_pos (by positivity) hlog
    norm_num at he hs
    have halg : (a + 3) * (ξ : ℝ) / Real.log ξ = a * ξ / Real.log ξ + 3 * (ξ / Real.log ξ) := by ring
    rw [halg]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨a + 3, by positivity, N, fun ξ hξ => hN ξ (by omega)⟩


/-- LEAF. Page 83, elementary lower survivor inclusion from task67. -/
theorem decomp87_lower_inclusion (P : Polynomial ℤ) (hP : CHyp P) {s ξ : ℕ}
    (hs : P.natDegree < s) (hξ : 1 ≤ ξ) :
    c2SiftedCount P s ξ ≤ c2ValueCount P s ξ := by
  exact c2SiftedCount_le P hP hs hξ

/-- LEAF. Page 83, elementary upper inclusion from task67. -/
theorem decomp87_upper_inclusion (P : Polynomial ℤ) (s ξ : ℕ) :
    c2ValueCount P s ξ ≤ roughValueCount P (((s : ℝ) - P.natDegree) / (2 * s)) ξ := by
  exact c2ValueCount_le_rough P s ξ

/-- LEAF. Page 83, first display, exact count identity at s = 3g. -/
theorem decomp87_specialization (P : Polynomial ℤ) (hP : CHyp P) (ξ : ℕ) :
    #{n ∈ Icc (1 : ℕ) ξ | AlmostGT (3 * P.natDegree - 1)
      (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) (Fval P n)} = c2ValueCount P (3 * P.natDegree) ξ := by
  exact c1_count_eq_c2_three_mul P hP ξ

/-- LEAF. Page 81 formula 2.6, positivity of the full lower sieve constant. -/
theorem decomp87_sigma_positive : 0 < ricciSigmaBarLower := by
  exact lt_trans (by norm_num) ricciSigmaBarLower_gt

/-- CONDITIONAL ON decomp87_lower_sieve and decomp87_upper_sieve.
Page 83 assembles the leaves into exactly the cited proposition of ricciC1. -/
theorem ricciC1_decomp87 : TheoremC1 := by
  intro P hP
  let s := 3 * P.natDegree
  have hs : P.natDegree + 1 ≤ s := by dsimp [s]; have := hP.1; omega
  obtain ⟨a, A, ha, hraw⟩ := decomp87_lower_sieve P hP s hs le_rfl
  obtain ⟨b, hb, N₁, hlower⟩ := decomp87_lower_absorb P s ha hraw
  let ω : ℝ := ((s : ℝ) - P.natDegree) / (2 * s)
  have hsR : (P.natDegree : ℝ) < s := by exact_mod_cast (by omega : P.natDegree < s)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by have := hP.1; omega : 0 < s)
  have hω : 0 < ω := by dsimp [ω]; positivity
  obtain ⟨hδpos, hδle, hδerror⟩ := decomp87_upper_parameter hω
  obtain ⟨c, B, κ, hc, hκ, hrawupper⟩ :=
    decomp87_upper_sieve P hP (min (ω / 2) (1 / 8)) hδpos hδerror
  obtain ⟨d, hd, N₂, hupper⟩ := decomp87_upper_absorb P hω hδle hc hκ hrawupper
  refine ⟨b, d, hb, hd, max N₁ N₂, fun ξ hξ => ?_⟩
  rw [decomp87_specialization P hP ξ]
  constructor
  · apply lt_of_lt_of_le (hlower ξ (by omega))
    exact_mod_cast decomp87_lower_inclusion P hP (by omega : P.natDegree < s) (by omega)
  · apply lt_of_le_of_lt _ (hupper ξ (by omega))
    exact_mod_cast (show c2ValueCount P s ξ ≤ roughValueCount P ω ξ from
      decomp87_upper_inclusion P s ξ)

end
end LeanLab.Ricci1937

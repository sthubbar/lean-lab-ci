/-
Flag unit U-1737, run 20261120-flags3. Hu 2019, P0101, page 192 and page 194, Lemma 2.2.

Part 1. The Gemini flag says `Decomp570a.major_arc_singular_comparison` is false.
Its stated reason needs the power of two shift 2 to the L to be a fixed fraction of n.
The lab and the paper both set L to log of n over log n, divided by log 2, so
2 to the floor of L is at most n over log n. That is the shift lemma below.
Then each residual is n times one minus O of 1 over log n, and the drop is
absorbed by any positive tolerance. The flag is not established. No negation is proved.

Part 2. A named hypothesis def for the sealed leaf, a match theorem, and the
conditional route to `major_arc_lower` from the named hypotheses.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Hathi2021.Decomp570a

open Real

namespace LeanLab.Hathi2021.Flag1737

open Decomp319a Decomp570a

/-- Page 192. Twin: for n at least 3, two to the floor of L of n is at most n over log n.
So every shared shift of 82 powers of two is at most 82 n over log n. -/
theorem two_pow_floor_L_le (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ ⌊L n⌋₊ ≤ (n : ℝ) / Real.log n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hn'
  have hpos : 0 < (n : ℝ) / Real.log n := div_pos (by linarith) hlog
  have hL : L n = Real.log ((n : ℝ) / Real.log n) / Real.log 2 := rfl
  have hfl : ((⌊L n⌋₊ : ℕ) : ℝ) ≤ L n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) / Real.log n := by
      rw [le_div_iff₀ hlog]
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
      linarith
    apply Nat.floor_le
    rw [hL]
    exact div_nonneg (Real.log_nonneg h1) (Real.log_nonneg (by norm_num))
  have h2 : (2 : ℝ) ^ ⌊L n⌋₊ = Real.exp (Real.log 2 * (⌊L n⌋₊ : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  rw [h2]
  calc Real.exp (Real.log 2 * (⌊L n⌋₊ : ℝ))
      ≤ Real.exp (Real.log 2 * L n) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hfl (Real.log_nonneg (by norm_num))
    _ = (n : ℝ) / Real.log n := by
        rw [hL, mul_div_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))),
          Real.exp_log hpos]

/-- Page 194, proof of Lemma 2.2. Named hypothesis: the exact sealed statement of
`Decomp570a.major_arc_singular_comparison`. Twin: for every C above 1 and every
positive tolerance, eventually R1 is at least pi squared over 16 times n1 n2 times
the singular mass, minus the tolerance times the scale. -/
def MajorArcComparison1737 : Prop :=
  ∀ (C η : ℝ), 1 < C → 0 < η →
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) * singularMass n₁ n₂ -
        η * scale n₁ n₂ ≤ R1 n₁ n₂

/-- Page 193, Lemma 2.1. Named hypothesis: the exact sealed statement of
`Decomp570a.averaged_singular_mass`. -/
def AveragedMass1737 : Prop :=
  ∀ (C : ℝ), 1 < C →
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (566388 / 100000 : ℝ) * L n₁ ^ 82 ≤ singularMass n₁ n₂

/-- Match: the named comparison is the sealed leaf. -/
theorem majorArcComparison1737_match :
    MajorArcComparison1737 ↔ ∀ (C η : ℝ) (_hC : 1 < C) (_hη : 0 < η),
      ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) * singularMass n₁ n₂ -
        η * scale n₁ n₂ ≤ R1 n₁ n₂ := Iff.rfl

/-- Page 194, Lemma 2.2. CONDITIONAL on the two named hypotheses. -/
theorem major_arc_lower_of (hA : AveragedMass1737) (hM : MajorArcComparison1737)
    (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (556388 / 100000 * Real.pi ^ 2 / 16 - δ) * scale n₁ n₂ ≤ R1 n₁ n₂ := by
  obtain ⟨N₁, h₁⟩ := hA C hC
  obtain ⟨N₂, h₂⟩ := hM C δ hC hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have hm := h₁ n₁ n₂ ho₁ ho₂ ((le_max_left _ _).trans hn) hlt hratio
  have ha := h₂ n₁ n₂ ho₁ ho₂ ((le_max_right _ _).trans hn) hlt hratio
  have hc : 0 ≤ Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) := by positivity
  have hmass := mul_le_mul_of_nonneg_left hm hc
  have hs := scale_nonneg n₁ n₂
  unfold scale at *
  nlinarith [sq_nonneg Real.pi]

end LeanLab.Hathi2021.Flag1737

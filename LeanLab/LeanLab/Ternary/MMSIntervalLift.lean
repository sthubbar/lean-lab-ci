/-
P0028, arXiv 1610.02017, section 4.3, page 10.
Extension by zero and the structured pointwise bound from a Bohr set size estimate.
The set size estimate remains a hypothesis.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrMajorant

namespace LeanLab.Ternary.MMS
open Finset

/-- Extension by zero evaluated at a natural index. -/
theorem intervalLift_apply_nat (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    intervalLift N f n = if n ∈ Icc 1 N then f n else 0 := by
  simp [intervalLift, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Extension by zero vanishes at every negative integer. -/
theorem intervalLift_apply_neg (N : ℕ) (f : ℕ → ℝ) (n : ℤ) (hn : n < 0) :
    intervalLift N f n = 0 := by
  unfold intervalLift
  rw [Finsupp.finsetSum_apply]
  apply sum_eq_zero
  intro m hm
  simp only [Finsupp.single_apply]
  split_ifs with he
  · have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    omega
  · rfl

/-- Nonnegativity on the interval gives nonnegativity on every integer after extension. -/
theorem intervalLift_nonneg (N : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ Icc 1 N, 0 ≤ f n) (n : ℤ) : 0 ≤ intervalLift N f n := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with m
    rw [intervalLift_apply_nat]
    split_ifs with hm
    · exact hf m hm
    · rfl
  · rw [intervalLift_apply_neg N f n (lt_of_not_ge hn)]

/-- Extension by zero preserves comparison of two functions on the interval. -/
theorem intervalLift_mono (N : ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n ∈ Icc 1 N, f n ≤ g n) (n : ℤ) :
    intervalLift N f n ≤ intervalLift N g n := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with m
    rw [intervalLift_apply_nat, intervalLift_apply_nat]
    split_ifs with hm
    · exact hfg m hm
    · rfl
  · rw [intervalLift_apply_neg N f n (lt_of_not_ge hn),
      intervalLift_apply_neg N g n (lt_of_not_ge hn)]

/-- The extension of the interval indicator is at most one everywhere. -/
theorem intervalLift_one_le (N : ℕ) (n : ℤ) : intervalLift N (fun _ => 1) n ≤ 1 := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with m
    rw [intervalLift_apply_nat]
    split_ifs <;> norm_num
  · rw [intervalLift_apply_neg N (fun _ => 1) n (lt_of_not_ge hn)]
    norm_num

/-- Lemma 4.3 item 1, conditional on a positive linear lower bound for the averaging set. -/
theorem prop31Hyp_smooth_bounds {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : 0 ≤ η)
    (B : Finset ℤ) (hB : B.Nonempty) (κ : ℝ) (hκ : 0 < κ)
    (hsize : κ * N ≤ B.card) :
    ∀ n : ℤ, 0 ≤ intSmooth B (intervalLift N f) n ∧
      intSmooth B (intervalLift N f) n ≤ 1 + (1 / κ) * η := by
  obtain ⟨ν, hν, hh⟩ := hf.2.2.1
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hquot : η * N / B.card ≤ η / κ := by
    apply (div_le_div_iff₀ hc hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsize hη]
  intro n
  constructor
  · exact intSmooth_nonneg B _ (intervalLift_nonneg N f hf.1) n
  · have hub := intSmooth_majorant_le B hB (intervalLift N f) (intervalLift N ν)
      (intervalLift N (fun _ => 1)) (η * N) (intervalLift_mono N f ν hν)
      (intervalLift_one_le N) (fun γ => by simpa only [intHat_intervalLift] using hh γ) n
    have he : η / κ = (1 / κ) * η := by ring
    linarith

end LeanLab.Ternary.MMS

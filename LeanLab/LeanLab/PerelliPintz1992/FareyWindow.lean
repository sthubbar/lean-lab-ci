/-
P0070 Section 5, page 363, the uniform Farey window count 21.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A finite δ separated family in a closed real interval has at most its length divided by δ plus one points. -/
theorem separated_interval_card_le {ι : Type*} [DecidableEq ι] (F : Finset ι) (x : ι → ℝ)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hbounds : ∀ i ∈ F, a ≤ x i ∧ x i ≤ b)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → δ ≤ |x i - x j|) :
    (F.card : ℝ) ≤ (b - a) / δ + 1 := by
  let k : ι → ℕ := fun i => ⌊(x i - a) / δ⌋₊
  have hinj : Set.InjOn k F := by
    intro i hi j hj heq
    by_contra hne
    have hi0 : 0 ≤ (x i - a) / δ := div_nonneg (sub_nonneg.mpr (hbounds i hi).1) hδ.le
    have hj0 : 0 ≤ (x j - a) / δ := div_nonneg (sub_nonneg.mpr (hbounds j hj).1) hδ.le
    have hiL := Nat.floor_le hi0
    have hjL := Nat.floor_le hj0
    have hiU := Nat.lt_floor_add_one ((x i - a) / δ)
    have hjU := Nat.lt_floor_add_one ((x j - a) / δ)
    have heq' : (⌊(x i - a) / δ⌋₊ : ℝ) = ⌊(x j - a) / δ⌋₊ := by exact_mod_cast heq
    rw [le_div_iff₀ hδ] at hiL hjL
    rw [div_lt_iff₀ hδ] at hiU hjU
    have hclose : |x i - x j| < δ := by
      rw [abs_lt]
      constructor <;> nlinarith
    exact (not_lt_of_ge (hsep i hi j hj hne)) hclose
  have hc : F.card ≤ ⌊(b - a) / δ⌋₊ + 1 := by
    calc
      F.card ≤ (Finset.range (⌊(b - a) / δ⌋₊ + 1)).card := by
        apply Finset.card_le_card_of_injOn k _ hinj
        intro i hi
        apply Finset.mem_range.mpr
        have hh : k i ≤ ⌊(b - a) / δ⌋₊ := Nat.floor_mono
          (div_le_div_of_nonneg_right (by linarith [(hbounds i hi).2]) hδ.le)
        omega
      _ = ⌊(b - a) / δ⌋₊ + 1 := Finset.card_range _
  have hc' : (F.card : ℝ) ≤ (⌊(b - a) / δ⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  have hf := Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hδ.le)
  linarith

#print axioms separated_interval_card_le


/-- Distinct rational centres have the separation displayed before equation 21. -/
theorem rat_centres_separated (x y : ℚ) (hne : x ≠ y) :
    1 / ((x.den : ℝ) * y.den) ≤ |(x : ℝ) - y| := by
  have hx : 0 < (x.den : ℝ) := by exact_mod_cast x.pos
  have hy : 0 < (y.den : ℝ) := by exact_mod_cast y.pos
  let j : ℤ := x.num * y.den - y.num * x.den
  have hj : j ≠ 0 := by
    intro hj0
    have hh : x.num * (y.den : ℤ) = y.num * x.den := sub_eq_zero.mp hj0
    have he : (x : ℝ) = (y : ℝ) := by
      rw [Rat.cast_def, Rat.cast_def, div_eq_div_iff hx.ne' hy.ne']
      exact_mod_cast hh
    exact hne (by exact_mod_cast he)
  have hdiff : (x : ℝ) - y = (j : ℝ) / ((x.den : ℝ) * y.den) := by
    rw [Rat.cast_def, Rat.cast_def]
    dsimp [j]
    push_cast
    field_simp
  have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  rw [hdiff, abs_div, abs_of_pos (mul_pos hx hy)]
  exact div_le_div_of_nonneg_right h1 (mul_pos hx hy).le

#print axioms rat_centres_separated


/-- Count rational centres of bounded denominator in any real window. -/
theorem rat_window_card_le (F : Finset ℚ) {D : ℕ} (hD : 1 ≤ D) (ξ w : ℝ) (hw : 0 ≤ w)
    (hden : ∀ x ∈ F, x.den ≤ D) (hwin : ∀ x ∈ F, |(x : ℝ) - ξ| ≤ w) :
    (F.card : ℝ) ≤ 2 * w * (D : ℝ) ^ 2 + 1 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      1 / (D : ℝ) ^ 2 ≤ |(x : ℝ) - y| := by
    intro x hx y hy hne
    have hxD : (x.den : ℝ) ≤ D := by exact_mod_cast hden x hx
    have hyD : (y.den : ℝ) ≤ D := by exact_mod_cast hden y hy
    have hx0 : (0 : ℝ) < x.den := by exact_mod_cast x.pos
    have hy0 : (0 : ℝ) < y.den := by exact_mod_cast y.pos
    have hprod : (x.den : ℝ) * y.den ≤ (D : ℝ) ^ 2 := by nlinarith
    exact (one_div_le_one_div_of_le (mul_pos hx0 hy0) hprod).trans
      (rat_centres_separated x y hne)
  have hbounds : ∀ x ∈ F, ξ - w ≤ (x : ℝ) ∧ (x : ℝ) ≤ ξ + w := by
    intro x hx
    have hh := abs_le.mp (hwin x hx)
    constructor <;> linarith
  have hp := separated_interval_card_le F (fun x : ℚ => (x : ℝ))
    (show ξ - w ≤ ξ + w by linarith) (show 0 < 1 / (D : ℝ) ^ 2 by positivity) hbounds hsep
  calc
    (F.card : ℝ) ≤ ((ξ + w) - (ξ - w)) / (1 / (D : ℝ) ^ 2) + 1 := hp
    _ = 2 * w * (D : ℝ) ^ 2 + 1 := by field_simp; ring

#print axioms rat_window_card_le


/-- Equation 21 with an explicit absolute constant, uniformly in every real ξ. -/
theorem farey_arcs_card_le (F : Finset ℚ) (M : ℕ) (hM : 1 ≤ M) (Q H ξ : ℝ)
    (hMQ : (M : ℝ) ≤ Q) (hH : 0 < H)
    (hden : ∀ x ∈ F, M ≤ x.den ∧ x.den ≤ 2 * M)
    (hmeet : ∀ x ∈ F, ∃ α : ℝ,
      |(x : ℝ) - α| ≤ 1 / ((x.den : ℝ) * Q) ∧ |α - ξ| ≤ 1 / H) :
    (F.card : ℝ) ≤ 9 * ((M : ℝ) ^ 2 / H + 1) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hQp : 0 < Q := hMp.trans_le hMQ
  have hwin : ∀ x ∈ F, |(x : ℝ) - ξ| ≤ 1 / H + 1 / ((M : ℝ) * Q) := by
    intro x hx
    obtain ⟨α, hα, hαξ⟩ := hmeet x hx
    have hMden : (M : ℝ) ≤ x.den := by exact_mod_cast (hden x hx).1
    have hrad : 1 / ((x.den : ℝ) * Q) ≤ 1 / ((M : ℝ) * Q) :=
      one_div_le_one_div_of_le (mul_pos hMp hQp) (mul_le_mul_of_nonneg_right hMden hQp.le)
    have ht := abs_sub_le (x : ℝ) α ξ
    linarith
  have hp := rat_window_card_le F (D := 2 * M) (by omega) ξ
    (1 / H + 1 / ((M : ℝ) * Q)) (by positivity)
    (fun x hx => (hden x hx).2) hwin
  have heq : 2 * (1 / H + 1 / ((M : ℝ) * Q)) * ((2 * M : ℕ) : ℝ) ^ 2 + 1 =
      8 * (M : ℝ) ^ 2 / H + 8 * (M : ℝ) / Q + 1 := by
    push_cast
    field_simp [hH.ne', hQp.ne', hMp.ne'] ; ring
  rw [heq] at hp
  have hratio : (M : ℝ) / Q ≤ 1 := (div_le_one hQp).mpr hMQ
  have hnonneg : 0 ≤ (M : ℝ) ^ 2 / H := div_nonneg (sq_nonneg _) hH.le
  have hp' : (F.card : ℝ) ≤ 8 * ((M : ℝ) ^ 2 / H) + 8 * ((M : ℝ) / Q) + 1 := by
    convert hp using 1 ; ring
  linarith only [hp', hratio, hnonneg]

#print axioms farey_arcs_card_le

end
end LeanLab.PerelliPintz1992.Section6

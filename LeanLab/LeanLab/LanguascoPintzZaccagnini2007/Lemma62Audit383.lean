import LeanLab.LanguascoPintzZaccagnini2007.Singular383
import LeanLab.LanguascoPintzZaccagnini2007.Audit1608

/-!
Journal page 778 Lemma 6.2 and the recorded Q2 about the missing lower cutoff on r.
The repaired Lemma62 already in this folder is unchanged.
At r equal to 1 the average is bounded below by a fixed fraction of L.
This formalizes the existing QUESTION and makes no new finding claim.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Journal page 778 Lemma 6.2, Q2. At X and m equal to 2 to power t squared
and r equal to 1, the sum is at least t squared divided by 2 for every t at least 2. -/
theorem Amr_one_square_lower383 (t : ℕ) (ht : 2 ≤ t) :
    (t : ℝ) ^ 2 / 2 ≤ Amr (2 ^ (t ^ 2)) (2 ^ (t ^ 2)) 1 := by
  classical
  let X := 2 ^ (t ^ 2)
  let M := t ^ 2 - t
  have ht0 : 0 < t := by omega
  have ha0 : 0 < t ^ 2 := pow_pos ht0 _
  have hta : t ≤ t ^ 2 := by nlinarith
  have hMlt : M < t ^ 2 := by dsimp [M]; omega
  have hL : Lg X = (t : ℝ) ^ 2 := by
    dsimp [X]
    rw [Lg_two_pow1608, Nat.cast_pow]
  have hcut : ⌊Lg X - √(Lg X)⌋₊ = M := by
    rw [hL, Real.sqrt_sq (Nat.cast_nonneg t), ← Nat.cast_pow,
      ← Nat.cast_sub hta, Nat.floor_natCast]
  have hpow : ∀ a ∈ Icc 1 M, 2 ^ a < X := by
    intro a ha
    exact Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt (mem_Icc.mp ha).2 hMlt)
  have hXe : Even X := Nat.even_pow.mpr ⟨even_two, by dsimp [X]; omega⟩
  have hterm : ∀ a ∈ Icc 1 M, (1 : ℝ) ≤ Sing (X - 2 ^ a) := by
    intro a ha
    have hae : Even (2 ^ a) := Nat.even_pow.mpr ⟨even_two, by have := (mem_Icc.mp ha).1; omega⟩
    have hne : X - 2 ^ a ≠ 0 := by have := hpow a ha; omega
    have hev : Even (X - 2 ^ a) := (Nat.even_sub (hpow a ha).le).mpr (iff_of_true hXe hae)
    have hc : (1 : ℝ) ≤ 2 * LeanLab.ChenExplicit.twinC := by
      have := LeanLab.ChenExplicit.twinC_ge_065
      linarith
    exact hc.trans (singular_even_lower383 hev hne)
  have hsum : (M : ℝ) ≤ Amr X X 1 := by
    unfold Amr
    rw [hcut, filter_true_of_mem (fun a ha => ⟨hpow a ha, one_dvd _⟩)]
    calc (M : ℝ) = ∑ _a ∈ Icc 1 M, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum hterm
  have htr : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hMr : (M : ℝ) = (t : ℝ) ^ 2 - t := by dsimp [M]; rw [Nat.cast_sub hta, Nat.cast_pow]
  have hquad := mul_nonneg (by linarith : 0 ≤ (t : ℝ) - 2) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  change (t : ℝ) ^ 2 / 2 ≤ Amr X X 1
  nlinarith

/-- Journal page 778 Lemma 6.2, the already recorded Q2.
The eventual bound for every positive odd r is false without an r cutoff.
The witnesses have r equal to 1, m equal to X, and X equal to 2 to power t squared. -/
theorem printed_lemma62_without_r0_false383 :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ m r : ℕ,
      (X : ℝ) / 2 ≤ m → m ≤ X → 0 < r → Odd r → Amr X m r ≤ ε * Lg X) := by
  intro h
  obtain ⟨X₀, hX₀⟩ := h (1 / 4) (by norm_num)
  let t := X₀ + 4
  let X := 2 ^ (t ^ 2)
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hX : X₀ ≤ X := by
    have hp : t ^ 2 < 2 ^ (t ^ 2) := Nat.lt_two_pow_self
    have hta : X₀ ≤ t ^ 2 := by dsimp [t]; nlinarith
    exact hta.trans hp.le
  have hlarge := hX₀ X hX X 1
    (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg X; linarith)
    le_rfl one_pos odd_one
  have hlower := Amr_one_square_lower383 t ht
  have hL : Lg X = (t : ℝ) ^ 2 := by
    dsimp [X]
    rw [Lg_two_pow1608, Nat.cast_pow]
  rw [hL] at hlarge
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  change (t : ℝ) ^ 2 / 2 ≤ Amr X X 1 at hlower
  nlinarith [sq_pos_of_pos htpos]

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.Amr_one_square_lower383
#print axioms LeanLab.LPZ2007.printed_lemma62_without_r0_false383

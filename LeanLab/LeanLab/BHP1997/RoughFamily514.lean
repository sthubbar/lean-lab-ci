/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 50 and 51, displays 5.15 and 5.17 with
page 3, display 1.8.

The subtracted sums of 5.15 have the shape: a sum over outer prime factors with product `d`,
of the rough indicator of the cofactor `m / d` at a level `z`. This file sums the rough
variable estimate of `Rough514` over the outer factors, which is how page 51 passes from
Siegel Walfisz in the rough variable to 5.17 for each subtracted sum.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Rough514

namespace LeanLab.BHP1997.Rough514
open Classical Complex Decomp132
open scoped BigOperators

/-- P0069 page 51 display 5.17. Reindexing of one subtracted sum of 5.15 by the cofactor: the
multiples `m = d * n` of an outer product `d ≥ 1` in `(L, U]` correspond to the cofactors `n`
in `(L / d, U / d]`. -/
theorem sum_dvd_reindex {d : ℕ} (hd : 1 ≤ d) (L U : ℕ) (g : ℕ → ℂ) :
    ∑ m ∈ Finset.Ioc L U, (if d ∣ m then g m else 0) =
      ∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) := by
  have hd0 : 0 < d := hd
  have hinj : ∀ x ∈ Finset.Ioc (L / d) (U / d), ∀ y ∈ Finset.Ioc (L / d) (U / d),
      d * x = d * y → x = y := fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd0 h
  have h1 : ∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) =
      ∑ m ∈ (Finset.Ioc (L / d) (U / d)).image (fun n => d * n),
        (if d ∣ m then g m else 0) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨(Nat.div_lt_iff_lt_mul hd0).mp hn.1 |>.trans_eq (Nat.mul_comm n d),
      (Nat.mul_comm d n).trans_le ((Nat.le_div_iff_mul_le hd0).mp hn.2)⟩
  · intro m hm hnot
    by_cases hdm : d ∣ m
    · exfalso
      apply hnot
      rcases hdm with ⟨n, rfl⟩
      rw [Finset.mem_Ioc] at hm
      refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
      rw [Finset.mem_Ioc]
      exact ⟨(Nat.div_lt_iff_lt_mul hd0).mpr (hm.1.trans_eq (Nat.mul_comm d n)),
        (Nat.le_div_iff_mul_le hd0).mpr ((Nat.mul_comm n d).trans_le hm.2)⟩
    · simp [hdm]

/-- P0069 page 51 display 5.17. Summation of the rough variable estimate over the outer
prime factors of a subtracted sum of 5.15. Each index `i` carries an outer product `d i ≤ L`
and a roughness level `z i ≥ X ^ c`; the character factors as `χ (d i) * χ (m / d i)` and the
inner sum over the cofactor is bounded by `rough_character_interval`. -/
theorem rough_family_character_sum {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ {ι : Type} (I : Finset ι) (d z : ι → ℕ) (L U : ℕ) (M : ℝ),
        (∀ i ∈ I, 1 ≤ d i ∧ d i ≤ L ∧ X ^ c ≤ (z i : ℝ)) → (U : ℝ) ≤ X →
        ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) ≤ M →
        ‖∑ m ∈ Finset.Ioc L U,
            ((∑ i ∈ I, if d i ∣ m then Task308.roughIndicator (m / d i) (z i) else 0 : ℝ) : ℂ) *
              χ (m : ZMod q)‖ ≤ C * M * U * Real.log X ^ (-A) := by
  obtain ⟨C0, hC0, hmain⟩ := rough_character_interval hc A hA
  refine ⟨max C0 1, lt_max_of_lt_left hC0, ?_⟩
  intro X hX q hq hqX χ hχ ι I d z L U M hI hU hM
  have hX0 : C0 ≤ X := (le_max_left _ _).trans hX
  have hX1 : (1 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hlog : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  -- swap the two finite sums
  have hswap : ∑ m ∈ Finset.Ioc L U,
      ((∑ i ∈ I, if d i ∣ m then Task308.roughIndicator (m / d i) (z i) else 0 : ℝ) : ℂ) *
        χ (m : ZMod q) =
      ∑ i ∈ I, ∑ m ∈ Finset.Ioc L U,
        (if d i ∣ m then ((Task308.roughIndicator (m / d i) (z i) : ℝ) : ℂ) * χ (m : ZMod q)
          else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rfl
    · simp
  rw [hswap]
  -- bound each outer factor
  have hterm : ∀ i ∈ I, ‖∑ m ∈ Finset.Ioc L U,
        (if d i ∣ m then ((Task308.roughIndicator (m / d i) (z i) : ℝ) : ℂ) * χ (m : ZMod q)
          else 0)‖ ≤ C0 * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) := by
    intro i hi
    obtain ⟨hd1, hdL, hz⟩ := hI i hi
    have hd0 : 0 < d i := hd1
    have hdR : (0 : ℝ) < (d i : ℝ) := Nat.cast_pos.mpr hd0
    rw [sum_dvd_reindex hd1 L U
      (fun m => ((Task308.roughIndicator (m / d i) (z i) : ℝ) : ℂ) * χ (m : ZMod q))]
    have hre : ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
        ((Task308.roughIndicator (d i * n / d i) (z i) : ℝ) : ℂ) * χ ((d i * n : ℕ) : ZMod q) =
        χ ((d i : ℕ) : ZMod q) * ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          ((Task308.roughIndicator n (z i) : ℝ) : ℂ) * χ (n : ZMod q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n hd0, Nat.cast_mul, map_mul]
      ring
    rw [hre, norm_mul]
    have hcast : ((U / d i : ℕ) : ℝ) ≤ (U : ℝ) / (d i : ℝ) := Nat.cast_div_le
    have hUd : (U : ℝ) / (d i : ℝ) ≤ U :=
      div_le_self hUnn (by exact_mod_cast hd1)
    have hb := hmain X hX0 q hq hqX χ hχ (z i) hz (L / d i) (U / d i)
      (Nat.div_pos hdL hd0) (hcast.trans (hUd.trans hU))
    calc ‖χ ((d i : ℕ) : ZMod q)‖ * ‖∑ n ∈ Finset.Ioc (L / d i) (U / d i),
            ((Task308.roughIndicator n (z i) : ℝ) : ℂ) * χ (n : ZMod q)‖
        ≤ 1 * (C0 * ((U / d i : ℕ) : ℝ) * Real.log X ^ (-A)) :=
          mul_le_mul (DirichletCharacter.norm_le_one χ _) hb (norm_nonneg _) zero_le_one
      _ ≤ C0 * ((U : ℝ) / (d i : ℝ)) * Real.log X ^ (-A) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hC0.le) hlog
      _ = C0 * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) := by ring
  have hS : 0 ≤ ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hK : 0 ≤ C0 * U * Real.log X ^ (-A) := mul_nonneg (mul_nonneg hC0.le hUnn) hlog
  calc ‖∑ i ∈ I, ∑ m ∈ Finset.Ioc L U,
        (if d i ∣ m then ((Task308.roughIndicator (m / d i) (z i) : ℝ) : ℂ) * χ (m : ZMod q)
          else 0)‖
      ≤ ∑ i ∈ I, C0 * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = C0 * U * Real.log X ^ (-A) * ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C0 * U * Real.log X ^ (-A) * M := mul_le_mul_of_nonneg_left hM hK
    _ = C0 * (M * U * Real.log X ^ (-A)) := by ring
    _ ≤ max C0 1 * (M * U * Real.log X ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg (mul_nonneg (hS.trans hM) hUnn) hlog)
    _ = max C0 1 * M * U * Real.log X ^ (-A) := by ring

end LeanLab.BHP1997.Rough514

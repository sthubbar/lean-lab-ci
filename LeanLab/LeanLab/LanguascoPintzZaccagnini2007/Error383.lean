import LeanLab.LanguascoPintzZaccagnini2007.Decomp383a
import LeanLab.LanguascoPintzZaccagnini2007.Product383

/-!
Journal page 777 display 20 with the explicit support error of display 30.
These quantitative bounds retain the Romanov tail and the logarithmic remainder.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Journal pages 778 and 779, displays 27 to 30. The weighted single exponent
count is at most its period main bound plus 5 exp 27 log L. -/
theorem weighted_one_log383 (F : Finset ℕ) (M m : ℕ) {X L : ℝ}
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m)
    (hX : 0 < X) (hL : 2 ≤ L) (hlog : log X = L * log 2)
    (hmX : (m : ℝ) ≤ X) (hM : (M : ℝ) ≤ L) :
    ∑ d ∈ F, fd d * (Tail383.oneCount d M m : ℝ) ≤
      (M : ℝ) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * log L := by
  have hp := product_weight_log383 (Icc 1 M) (fun a => m - 2 ^ a) hX hL hlog
    (fun a ha => by have := hpow a ha; omega)
    (fun a _ => (show ((m - 2 ^ a : ℕ) : ℝ) ≤ m by exact_mod_cast Nat.sub_le m (2 ^ a)).trans hmX)
    (by simpa using hM)
  have hb := Tail383.weighted_one_le F M m hF hpow
  linarith

/-- Journal page 777 display 20. Fix j exponents and bound the final exponent.
The logarithmic error is paid M to power j times, without any asymptotic notation. -/
theorem tuple_weight_log383 (F : Finset ℕ) (j M N : ℕ) {X L : ℝ}
    (hF : ∀ d ∈ F, OddSqf d)
    (hsmall : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν < N)
    (hX : 0 < X) (hL : 2 ≤ L) (hlog : log X = L * log 2)
    (hNX : (N : ℝ) ≤ X) (hM : (M : ℝ) ≤ L) :
    ∑ d ∈ F, fd d * (#{ν ∈ exponentTuples131 (j + 1) M | d ∣ N - tuplePower131 ν} : ℝ) ≤
      (M : ℝ) ^ (j + 1) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * (M : ℝ) ^ j * log L := by
  have hsingle : ∀ t ∈ exponentTuples131 j M,
      ∑ d ∈ F, fd d * (Tail383.oneCount d M (N - tuplePower131 t) : ℝ) ≤
        (M : ℝ) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * log L := by
    intro t ht
    have hpow : ∀ a ∈ Icc 1 M, 2 ^ a < N - tuplePower131 t := by
      intro a ha
      have hcons : (Fin.cons a t : Fin (j + 1) → ℕ) ∈ exponentTuples131 (j + 1) M := by
        simp only [exponentTuples131, Fintype.mem_piFinset] at ht ⊢
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa using ha
        · simpa using ht i
      have hp := hsmall _ hcons
      have he : tuplePower131 (Fin.cons a t) = 2 ^ a + tuplePower131 t := by
        simp [tuplePower131, Fin.sum_univ_succ]
      rw [he] at hp
      omega
    exact weighted_one_log383 F M (N - tuplePower131 t) hF hpow hX hL hlog
      ((show ((N - tuplePower131 t : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.sub_le N _).trans hNX) hM
  simp_rw [Tail383.count_succ_eq, mul_sum]
  rw [sum_comm]
  calc ∑ t ∈ exponentTuples131 j M, ∑ d ∈ F, fd d * (Tail383.oneCount d M (N - tuplePower131 t) : ℝ)
      ≤ ∑ _t ∈ exponentTuples131 j M,
        ((M : ℝ) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * log L) := sum_le_sum hsingle
    _ = (M : ℝ) ^ j * ((M : ℝ) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * log L) := by
      rw [sum_const, nsmul_eq_mul, exponentTuples_card131, Nat.cast_pow]
    _ = (M : ℝ) ^ (j + 1) * ∑ d ∈ F, seriesTerm d + 5 * exp 27 * (M : ℝ) ^ j * log L := by ring
    _ = (∑ d ∈ F, (M : ℝ) ^ (j + 1) * seriesTerm d) + 5 * exp 27 * (M : ℝ) ^ j * log L := by
      rw [mul_sum]

/-- Journal page 777 displays 20 and 22, with page 779 display 30.
At an explicit tuple window, the actual divisor tail is bounded by L to power k
 times the Romanov tail plus 5 exp 27 L to power k minus one times log L. -/
theorem divisor_tail_error383 (j X N D : ℕ) (hN : N ∈ evenJ131 X) (hL : 2 ≤ Lg X)
    (hw : 6 * (j + 1) * 2 ^ ⌊Lg X - √(Lg X)⌋₊ ≤ X) :
    ∑ d ∈ (Ico (D + 1) (N + 1)).filter OddSqf,
      fd d * (residueTupleCount131 d (j + 1) ⌊Lg X - √(Lg X)⌋₊ N : ℝ) ≤
      Lg X ^ (j + 1) * ∑' n, seriesTerm (n + (D + 1)) +
        5 * exp 27 * Lg X ^ j * log (Lg X) := by
  let M := ⌊Lg X - √(Lg X)⌋₊
  let F := (Ico (D + 1) (N + 1)).filter OddSqf
  have hF : ∀ d ∈ F, OddSqf d := fun d hd => (mem_filter.mp hd).2
  obtain ⟨hN1, hNX, _, hNJ⟩ := evenJ_nat131 hN
  have hsmall : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν < N := by
    intro ν hν
    have hp := tuplePower_le131 hν
    have h6 : 6 * tuplePower131 ν ≤ X := by
      calc 6 * tuplePower131 ν ≤ 6 * ((j + 1) * 2 ^ M) := Nat.mul_le_mul_left _ hp
        _ = 6 * (j + 1) * 2 ^ M := by ring
        _ ≤ X := hw
    omega
  have hM : (M : ℝ) ≤ Lg X := by
    have hs : √(Lg X) ≤ Lg X := (sqrt_le_left (by linarith)).mpr (by nlinarith)
    have hf : (M : ℝ) ≤ Lg X - √(Lg X) := Nat.floor_le (by linarith)
    linarith [sqrt_nonneg (Lg X)]
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlog : log (X : ℝ) = Lg X * log 2 := by unfold Lg Real.logb; field_simp
  have hcoeff := tail_le D F (fun d hd => by have := (mem_Ico.mp (mem_filter.mp hd).1).1; omega)
  have hcoeff0 : 0 ≤ ∑ d ∈ F, seriesTerm d := sum_nonneg fun d _ => seriesTerm_nonneg d
  have hlog0 : 0 ≤ log (Lg X) := log_nonneg (by linarith)
  have hq0 : 0 ≤ Lg X := by linarith
  have hb := tuple_weight_log383 F j M N hF hsmall hXpos hL hlog
    (by exact_mod_cast hNX) hM
  have he : (∑ d ∈ F, fd d * (residueTupleCount131 d (j + 1) M N : ℝ)) =
      ∑ d ∈ F, fd d * (#{ν ∈ exponentTuples131 (j + 1) M | d ∣ N - tuplePower131 ν} : ℝ) := by
    apply sum_congr rfl
    intro d _
    rw [residueTupleCount_nat383 d (j + 1) M N (fun ν hν => (hsmall ν hν).le)]
  change (∑ d ∈ F, fd d * (residueTupleCount131 d (j + 1) M N : ℝ)) ≤ _
  rw [he]
  refine hb.trans (add_le_add ?_ ?_)
  · exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hM _) hcoeff hcoeff0 (pow_nonneg hq0 _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hM _) (by positivity)) hlog0

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.weighted_one_log383
#print axioms LeanLab.LPZ2007.tuple_weight_log383
#print axioms LeanLab.LPZ2007.divisor_tail_error383

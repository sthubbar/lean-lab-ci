/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 178 Lemma 5. The zero column follows the convention recorded in STATEMENTS.md.
-/
import LeanLab.PlattTrudgian2014.Transfer380

namespace LeanLab.PlattTrudgian2014

open Finset

/-- P0026 page 178, selecting a single routed frequency in the finite cosine sum. -/
theorem cosine_route_sum380 (q : ℕ) (hq : q < 16) (x : ℝ) :
    (∑ j : Fin 16, (if (j : ℕ) = q then (1 : ℝ) else 0) * Real.cos (2 * (j : ℝ) * x)) =
      Real.cos (2 * (q : ℝ) * x) := by
  rw [sum_eq_single (⟨q, hq⟩ : Fin 16)]
  · simp
  · intro j _ hj
    have hne : (j : ℕ) ≠ q := fun h => hj (Fin.ext h)
    simp [hne]
  · simp

set_option maxRecDepth 10000 in
/-- P0026 page 178 h star, the surviving half frequencies stay in the closed vector. -/
theorem half_frequency_arithmetic380 : ∀ i : Fin 16, ∀ k : Fin 17,
    Even ((i : ℕ) + (k : ℕ)) →
      ((i : ℕ) + (k : ℕ)) / 2 < 16 ∧ Int.natAbs ((i : ℤ) - k) / 2 < 16 ∧
        2 * (((i : ℕ) + (k : ℕ)) / 2) = (i : ℕ) + (k : ℕ) ∧
          ((i : ℤ) - k = 2 * (Int.natAbs ((i : ℤ) - k) / 2 : ℕ) ∨
            (i : ℤ) - k = -(2 * (Int.natAbs ((i : ℤ) - k) / 2 : ℕ) : ℤ)) := by
  decide +kernel

/-- P0026 page 178 h star, one cosine product regrouped using the finite routing certificate. -/
theorem half_mode_cosine380 (i : Fin 16) (k : Fin 17) (x : ℝ) :
    (Real.cos ((i : ℝ) * x) * Real.cos ((k : ℝ) * x) +
      Real.cos ((i : ℝ) * (x + Real.pi)) * Real.cos ((k : ℝ) * (x + Real.pi))) / 2 =
        ∑ j : Fin 16, (halfMode380 i k j : ℝ) * Real.cos (2 * (j : ℝ) * x) := by
  rw [cos_product_half_average125, neg_one_pow_eq_ite]
  by_cases hp : Even ((i : ℕ) + (k : ℕ))
  · rw [if_pos hp]
    obtain ⟨hq, hr, hplus, hsign⟩ := half_frequency_arithmetic380 i k hp
    let q := ((i : ℕ) + (k : ℕ)) / 2
    let r := Int.natAbs ((i : ℤ) - k) / 2
    have hm (j : Fin 16) : (halfMode380 i k j : ℝ) =
        ((if (j : ℕ) = q then 1 else 0) + (if (j : ℕ) = r then 1 else 0)) / 2 := by
      rw [half_mode_routing380 i k j, if_pos hp]
      dsimp [q, r]
      split_ifs <;> norm_num
    have hs : (∑ j : Fin 16, (halfMode380 i k j : ℝ) * Real.cos (2 * (j : ℝ) * x)) =
        (Real.cos (2 * (q : ℝ) * x) + Real.cos (2 * (r : ℝ) * x)) / 2 := by
      simp_rw [hm]
      calc
        _ = ((∑ j : Fin 16, (if (j : ℕ) = q then (1 : ℝ) else 0) * Real.cos (2 * (j : ℝ) * x)) +
            (∑ j : Fin 16, (if (j : ℕ) = r then (1 : ℝ) else 0) * Real.cos (2 * (j : ℝ) * x))) / 2 := by
          rw [← sum_add_distrib, sum_div]
          apply sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [cosine_route_sum380 q hq x, cosine_route_sum380 r hr x]
    have hcplus : Real.cos (2 * (q : ℝ) * x) = Real.cos (((i : ℕ) + (k : ℕ) : ℕ) * x) := by
      have he : 2 * (q : ℝ) = ((i : ℕ) + (k : ℕ) : ℕ) := by exact_mod_cast hplus
      rw [he]
    have hcminus : Real.cos (2 * (r : ℝ) * x) = Real.cos (((i : ℝ) - k) * x) := by
      rcases hsign with h | h
      · have he : (i : ℝ) - k = 2 * (r : ℝ) := by
          have hR := congrArg (fun z : ℤ => (z : ℝ)) h
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
            Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, r] using hR
        rw [he]
      · have he : (i : ℝ) - k = -(2 * (r : ℝ)) := by
          have hR := congrArg (fun z : ℤ => (z : ℝ)) h
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
            Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, r] using hR
        rw [he, neg_mul, Real.cos_neg]
    rw [hs, hcplus, hcminus]
    ring
  · simp [half_mode_routing380, hp]

/-- P0026 page 178 Lemma 5, the full first factor average from the single mode identities. -/
theorem half_transfer_cosine_proved380 (i : Fin 16) (y : ℝ) :
    (Real.cos ((i : ℝ) * y) * halfCosPoly125 y +
      Real.cos ((i : ℝ) * (y + Real.pi)) * halfCosPoly125 (y + Real.pi)) / 2 =
        ∑ j : Fin 16, (halfTransfer125 i j : ℝ) * Real.cos (2 * (j : ℝ) * y) := by
  have he :
      (Real.cos ((i : ℝ) * y) * halfCosPoly125 y +
        Real.cos ((i : ℝ) * (y + Real.pi)) * halfCosPoly125 (y + Real.pi)) / 2 =
      ∑ k : Fin 17, (halfCoeff125 k : ℝ) *
        ((Real.cos ((i : ℝ) * y) * Real.cos ((k : ℝ) * y) +
          Real.cos ((i : ℝ) * (y + Real.pi)) * Real.cos ((k : ℝ) * (y + Real.pi))) / 2) := by
    simp only [halfCosPoly125, mul_sum, ← sum_add_distrib, sum_div]
    apply sum_congr rfl
    intro k _
    ring
  rw [he]
  simp_rw [half_mode_cosine380, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [half_transfer_mode_sum380]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro k _
  ring

#print axioms cosine_route_sum380
#print axioms half_frequency_arithmetic380
#print axioms half_mode_cosine380
#print axioms half_transfer_cosine_proved380

end LeanLab.PlattTrudgian2014

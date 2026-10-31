/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 9, display 3.5.
A shifted collision count is bounded by the unshifted collision count.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Elementary115
import LeanLab.Hathi2021.FalsifierU6830

open Finset

namespace LeanLab.Hathi2021.Collision115

/-- The finite fiber inequality used for the left inequality of display 3.5, page 9.
For any map to a finite additive group, a shifted collision count is at most
its unshifted collision count. -/
theorem shifted_pairs_le_zero {A G : Type*} [Fintype A] [Fintype G] [AddCommGroup G] [DecidableEq G]
    (f : A → G) (r : G) :
    (univ.filter (fun x : A × A => f x.1 - f x.2 = r)).card ≤
      (univ.filter (fun x : A × A => f x.1 = f x.2)).card := by
  classical
  let c (a : G) : ℕ := (univ.filter (fun x : A => f x = a)).card
  have fiber (s : G) :
      (univ.filter (fun x : A × A => f x.1 - f x.2 = s)).card =
        ∑ a : G, c (a + s) * c a := by
    rw [card_eq_sum_card_fiberwise (f := fun x : A × A => f x.2)
      (t := univ) (by simp)]
    apply sum_congr rfl
    intro a _
    have hset :
        (univ.filter (fun x : A × A => f x.1 - f x.2 = s)).filter
          (fun x => f x.2 = a) =
        (univ.filter (fun x : A => f x = a + s)) ×ˢ
          (univ.filter (fun x : A => f x = a)) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, mem_product]
      constructor
      · rintro ⟨hxy, hy⟩
        refine ⟨?_, hy⟩
        rw [hy, sub_eq_iff_eq_add] at hxy
        simpa only [add_comm] using hxy
      · rintro ⟨hx, hy⟩
        refine ⟨?_, hy⟩
        rw [hx, hy]
        abel
    rw [hset, card_product]
  have htranslate : (∑ a : G, c (a + r) ^ 2) = ∑ a : G, c a ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight r) _ _ (fun _ => rfl)
  have hi : (∑ a : G, 2 * c (a + r) * c a) ≤
      ∑ a : G, (c (a + r) ^ 2 + c a ^ 2) := by
    apply sum_le_sum
    intro a _
    exact two_mul_le_add_sq _ _
  rw [sum_add_distrib, htranslate] at hi
  simp_rw [mul_assoc] at hi
  rw [← mul_sum] at hi
  rw [fiber r]
  have hzero := fiber 0
  simp only [sub_eq_zero, add_zero, ← pow_two] at hzero
  rw [hzero]
  omega

/-- Display 3.1, page 9. Separate a tuple of pairs into two exponent vectors.
The offset r is moved to the other side of the congruence. -/
theorem cntF_eq_pairs (l d ρ : ℕ) (r : ℤ) :
    FalsifierU6830.cntF l (d : ℤ)
      (fun x : Fin ρ × Fin ρ => (2 : ℤ) ^ (x.1.val + 1) - 2 ^ (x.2.val + 1)) r =
    (univ.filter (fun x : (Fin l → Fin ρ) × (Fin l → Fin ρ) =>
      (∑ j, (2 : ZMod d) ^ ((x.1 j).val + 1)) -
        (∑ j, (2 : ZMod d) ^ ((x.2 j).val + 1)) = -(r : ZMod d))).card := by
  classical
  unfold FalsifierU6830.cntF
  apply Finset.card_equiv (Equiv.arrowProdEquivProdArrow (Fin l)
    (fun _ => Fin ρ) (fun _ => Fin ρ))
  intro x
  simp only [mem_filter, mem_univ, true_and]
  change (r + ∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) -
      2 ^ ((x j).2.val + 1))) % (d : ℤ) = 0 ↔
    (∑ j, (2 : ZMod d) ^ ((x j).1.val + 1)) -
      (∑ j, (2 : ZMod d) ^ ((x j).2.val + 1)) = -(r : ZMod d)
  rw [← Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Finset.sum_sub_distrib]
  constructor <;> intro h <;> linear_combination h

/-- Page 9, the shifted solution count bound underlying display 3.5. -/
theorem cntF_le_zero (l d ρ : ℕ) (hd : Odd d) (r : ℤ) :
    FalsifierU6830.cntF l (d : ℤ)
      (fun x : Fin ρ × Fin ρ => (2 : ℤ) ^ (x.1.val + 1) - 2 ^ (x.2.val + 1)) r ≤
    FalsifierU6830.cntF l (d : ℤ)
      (fun x : Fin ρ × Fin ρ => (2 : ℤ) ^ (x.1.val + 1) - 2 ^ (x.2.val + 1)) 0 := by
  classical
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  haveI : NeZero d := ⟨hd0⟩
  rw [cntF_eq_pairs, cntF_eq_pairs]
  simpa only [Int.cast_zero, neg_zero, sub_eq_zero] using
    shifted_pairs_le_zero
      (fun x : Fin l → Fin ρ => ∑ j, (2 : ZMod d) ^ ((x j).val + 1)) (-(r : ZMod d))

/-- Page 9, proof of display 3.5. One more pair increases N by at most ρ squared. -/
theorem Nl_succ_le (l d ρ : ℕ) (hd : Odd d) :
    PairLinnik.Nl (l + 1) d ρ ≤ ρ ^ 2 * PairLinnik.Nl l d ρ := by
  classical
  let w : Fin ρ × Fin ρ → ℤ :=
    fun x => (2 : ℤ) ^ (x.1.val + 1) - 2 ^ (x.2.val + 1)
  have hNl (k : ℕ) : PairLinnik.Nl k d ρ = FalsifierU6830.cntF k (d : ℤ) w 0 := by
    simp only [PairLinnik.Nl, FalsifierU6830.cntF, zero_add, w]
  rw [hNl (l + 1), FalsifierU6830.cntF_succ]
  calc
    (∑ b : Fin ρ × Fin ρ, FalsifierU6830.cntF l (d : ℤ) w (0 + w b)) ≤
        ∑ _ : Fin ρ × Fin ρ, FalsifierU6830.cntF l (d : ℤ) w 0 := by
      apply sum_le_sum
      intro b _
      simpa only [zero_add, w] using cntF_le_zero l d ρ hd (w b)
    _ = ρ ^ 2 * PairLinnik.Nl l d ρ := by
      rw [← hNl l]
      simp [pow_two]

/-- Page 9, display 3.5, beta is nondecreasing with the number of pairs.
At l equal to zero this uses the natural empty tuple extension of display 2.8. -/
theorem beta_le_beta_succ (l d : ℕ) (hd : Odd d) :
    (Rho.rho d : ℝ) ^ (2 * l) / (PairLinnik.Nl l d (Rho.rho d) : ℝ) ≤
    (Rho.rho d : ℝ) ^ (2 * (l + 1)) /
      (PairLinnik.Nl (l + 1) d (Rho.rho d) : ℝ) := by
  have hN : (0 : ℝ) < PairLinnik.Nl l d (Rho.rho d) := by
    exact_mod_cast Elementary115.Nl_pos l d hd
  have hN' : (0 : ℝ) < PairLinnik.Nl (l + 1) d (Rho.rho d) := by
    exact_mod_cast Elementary115.Nl_pos (l + 1) d hd
  have hcount : (PairLinnik.Nl (l + 1) d (Rho.rho d) : ℝ) ≤
      (Rho.rho d : ℝ) ^ 2 * PairLinnik.Nl l d (Rho.rho d) := by
    exact_mod_cast Nl_succ_le l d (Rho.rho d) hd
  rw [div_le_div_iff₀ hN hN']
  calc
    (Rho.rho d : ℝ) ^ (2 * l) * PairLinnik.Nl (l + 1) d (Rho.rho d) ≤
        (Rho.rho d : ℝ) ^ (2 * l) *
          ((Rho.rho d : ℝ) ^ 2 * PairLinnik.Nl l d (Rho.rho d)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (Rho.rho d : ℝ) ^ (2 * (l + 1)) * PairLinnik.Nl l d (Rho.rho d) := by
      rw [show 2 * (l + 1) = 2 * l + 2 by omega, pow_add]
      ring

end LeanLab.Hathi2021.Collision115

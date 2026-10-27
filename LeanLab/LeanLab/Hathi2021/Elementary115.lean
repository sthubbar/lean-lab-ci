/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 9, displays 3.1 and 3.2.
The existing Rho module proves the order bound. This file addresses the count bound.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Rho
import LeanLab.Hathi2021.PairLinnik

open Finset

namespace LeanLab.Hathi2021.Elementary115

/-- Page 9, uniqueness of a power in one complete multiplicative period. -/
theorem period_power_injective {d : ℕ} (hd : Odd d) :
    Function.Injective (fun i : Fin (Rho.rho d) => (2 : ZMod d) ^ (i.val + 1)) := by
  intro i j hij
  apply Fin.ext
  have hm := (Rho.isOfFinOrder_two hd).pow_inj_mod.mp hij
  change (i.val + 1) % Rho.rho d = (j.val + 1) % Rho.rho d at hm
  have hc := Nat.ModEq.add_right_cancel' 1 hm
  change i.val % Rho.rho d = j.val % Rho.rho d at hc
  simpa only [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hc

/-- Page 9, display 3.1. Fixing all but one exponent gives at most one solution.
There are 2l plus 1 free exponents for l plus 1 pairs. -/
theorem Nl_le_period_power (l d : ℕ) (hd : Odd d) :
    PairLinnik.Nl (l + 1) d (Rho.rho d) ≤ Rho.rho d ^ (2 * l + 1) := by
  classical
  let S := {x : Fin (l + 1) → Fin (Rho.rho d) × Fin (Rho.rho d) //
    (∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (d : ℤ) = 0}
  let f : S → (Fin l → Fin (Rho.rho d) × Fin (Rho.rho d)) × Fin (Rho.rho d) :=
    fun x => (Fin.tail x.val, (x.val 0).1)
  have hz (x : S) :
      ∑ j, ((2 : ZMod d) ^ ((x.val j).1.val + 1) -
        2 ^ ((x.val j).2.val + 1)) = 0 := by
    have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ j, ((2 : ℤ) ^ ((x.val j).1.val + 1) - 2 ^ ((x.val j).2.val + 1))) d).mpr
        (Int.dvd_of_emod_eq_zero x.property)
    push_cast at hcast
    exact hcast
  have hf : Function.Injective f := by
    intro x y hxy
    have ht := congrArg Prod.fst hxy
    have hu := congrArg Prod.snd hxy
    change Fin.tail x.val = Fin.tail y.val at ht
    change (x.val 0).1 = (y.val 0).1 at hu
    have hs :
        ∑ j : Fin l, ((2 : ZMod d) ^ ((x.val j.succ).1.val + 1) -
          2 ^ ((x.val j.succ).2.val + 1)) =
        ∑ j : Fin l, ((2 : ZMod d) ^ ((y.val j.succ).1.val + 1) -
          2 ^ ((y.val j.succ).2.val + 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have he := congrFun ht j
      change x.val j.succ = y.val j.succ at he
      rw [he]
    have hx := hz x
    have hy := hz y
    rw [Fin.sum_univ_succ] at hx hy
    rw [hu, hs] at hx
    have hv : (2 : ZMod d) ^ ((x.val 0).2.val + 1) =
        2 ^ ((y.val 0).2.val + 1) := by linear_combination hy - hx
    have hzero : x.val 0 = y.val 0 := Prod.ext hu (period_power_injective hd hv)
    apply Subtype.ext
    funext j
    exact Fin.cases hzero (fun i => congrFun ht i) j
  have hcard := Fintype.card_le_of_injective f hf
  have hcount : PairLinnik.Nl (l + 1) d (Rho.rho d) = Fintype.card S := by
    simp only [S, Fintype.card_subtype, PairLinnik.Nl]
  rw [← hcount] at hcard
  calc
    PairLinnik.Nl (l + 1) d (Rho.rho d) ≤
        Fintype.card ((Fin l → Fin (Rho.rho d) × Fin (Rho.rho d)) × Fin (Rho.rho d)) := hcard
    _ = Rho.rho d ^ (2 * l + 1) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_two, ← pow_mul, pow_add, pow_one]

/-- Display 2.7 on page 6. A diagonal tuple always gives a solution. -/
theorem Nl_pos (l d : ℕ) (hd : Odd d) : 0 < PairLinnik.Nl l d (Rho.rho d) := by
  classical
  unfold PairLinnik.Nl
  apply Finset.card_pos.mpr
  let i : Fin (Rho.rho d) := ⟨0, Rho.rho_pos hd⟩
  refine ⟨fun _ => (i, i), ?_⟩
  simp

/-- Display 3.2 on page 9, the beta half, using the definition in display 2.8. -/
theorem rho_le_beta (l d : ℕ) (hd : Odd d) :
    (Rho.rho d : ℝ) ≤ (Rho.rho d : ℝ) ^ (2 * (l + 1)) /
      (PairLinnik.Nl (l + 1) d (Rho.rho d) : ℝ) := by
  have hr : (0 : ℝ) < Rho.rho d := by exact_mod_cast Rho.rho_pos hd
  have hN : (0 : ℝ) < PairLinnik.Nl (l + 1) d (Rho.rho d) := by
    exact_mod_cast Nl_pos (l + 1) d hd
  have hbound : (PairLinnik.Nl (l + 1) d (Rho.rho d) : ℝ) ≤
      (Rho.rho d : ℝ) ^ (2 * l + 1) := by
    exact_mod_cast Nl_le_period_power l d hd
  rw [le_div_iff₀ hN]
  calc
    (Rho.rho d : ℝ) * PairLinnik.Nl (l + 1) d (Rho.rho d) ≤
        (Rho.rho d : ℝ) * (Rho.rho d : ℝ) ^ (2 * l + 1) :=
      mul_le_mul_of_nonneg_left hbound hr.le
    _ = (Rho.rho d : ℝ) ^ (2 * (l + 1)) := by
      rw [← pow_succ']
      congr 1

/-- Display 3.2 on page 9, the logarithmic half of the lower bound. -/
theorem log_div_log_two_le_rho (d : ℕ) (hd : Odd d) (hd1 : 1 < d) :
    Real.log ((d : ℝ) + 1) / Real.log 2 ≤ (Rho.rho d : ℝ) := by
  have hpow : (d : ℝ) + 1 ≤ (2 : ℝ) ^ Rho.rho d := by
    exact_mod_cast Rho.two_pow_rho_ge hd hd1
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < d + 1) hpow
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact hlog

/-- Page 9, the diagonal extension in the proof of display 3.5.
This counting inequality holds for every chosen period length. -/
theorem Nl_succ_ge_diagonal (l d ρ : ℕ) :
    ρ * PairLinnik.Nl l d ρ ≤ PairLinnik.Nl (l + 1) d ρ := by
  classical
  let S₀ := {x : Fin l → Fin ρ × Fin ρ //
    (∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (d : ℤ) = 0}
  let S₁ := {x : Fin (l + 1) → Fin ρ × Fin ρ //
    (∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (d : ℤ) = 0}
  let g : Fin ρ × S₀ → S₁ := fun x =>
    ⟨Fin.cons (x.1, x.1) x.2.val, by
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, zero_add]
        using x.2.property⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    have hzero := congrFun hval 0
    change (x.1, x.1) = (y.1, y.1) at hzero
    have ht : x.2.val = y.2.val := by
      funext i
      exact congrFun hval i.succ
    apply Prod.ext
    · exact congrArg (fun z : Fin ρ × Fin ρ => z.1) hzero
    · exact Subtype.ext ht
  have hcard := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_prod, Fintype.card_fin, S₀, S₁,
    Fintype.card_subtype, PairLinnik.Nl] using hcard

/-- Page 9, display 3.5, the inequality obtained from diagonal extension. -/
theorem beta_succ_div_rho_le_beta (l d : ℕ) (hd : Odd d) :
    ((Rho.rho d : ℝ) ^ (2 * (l + 1)) /
      (PairLinnik.Nl (l + 1) d (Rho.rho d) : ℝ)) / Rho.rho d ≤
    (Rho.rho d : ℝ) ^ (2 * l) / (PairLinnik.Nl l d (Rho.rho d) : ℝ) := by
  have hr : (0 : ℝ) < Rho.rho d := by exact_mod_cast Rho.rho_pos hd
  have hN : (0 : ℝ) < PairLinnik.Nl l d (Rho.rho d) := by
    exact_mod_cast Nl_pos l d hd
  have hN' : (0 : ℝ) < PairLinnik.Nl (l + 1) d (Rho.rho d) := by
    exact_mod_cast Nl_pos (l + 1) d hd
  have hcount : (Rho.rho d : ℝ) * PairLinnik.Nl l d (Rho.rho d) ≤
      PairLinnik.Nl (l + 1) d (Rho.rho d) := by
    exact_mod_cast Nl_succ_ge_diagonal l d (Rho.rho d)
  rw [div_div, div_le_div_iff₀ (mul_pos hN' hr) hN]
  rw [show 2 * (l + 1) = 2 * l + 2 by omega, pow_add]
  calc
    (Rho.rho d : ℝ) ^ (2 * l) * (Rho.rho d : ℝ) ^ 2 *
        PairLinnik.Nl l d (Rho.rho d) =
      ((Rho.rho d : ℝ) ^ (2 * l) * Rho.rho d) *
        ((Rho.rho d : ℝ) * PairLinnik.Nl l d (Rho.rho d)) := by ring
    _ ≤ ((Rho.rho d : ℝ) ^ (2 * l) * Rho.rho d) *
        PairLinnik.Nl (l + 1) d (Rho.rho d) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

end LeanLab.Hathi2021.Elementary115

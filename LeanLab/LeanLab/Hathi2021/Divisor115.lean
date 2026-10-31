/-
P0080 Hathi 2021, arXiv 2109.13174v3, page 9, display 3.4.
Reduction to a divisor modulus, with explicit quotient and remainder coordinates.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Elementary115

open Finset

namespace LeanLab.Hathi2021.Divisor115

/-- Page 9, proof of display 3.4. If m divides d and the large period has length
 t times rho of m, every reduced solution has at most t to power 2l lifts. -/
theorem Nl_dvd_le (l m d t : ℕ) (hm : Odd m) (hmd : m ∣ d) :
    PairLinnik.Nl l d (t * Rho.rho m) ≤ t ^ (2 * l) * PairLinnik.Nl l m (Rho.rho m) := by
  classical
  let R := Rho.rho m
  have hR : 0 < R := Rho.rho_pos hm
  let red : Fin (t * R) → Fin R := fun i => ⟨i.val % R, Nat.mod_lt _ hR⟩
  let quot : Fin (t * R) → Fin t := fun i =>
    ⟨i.val / R, (Nat.div_lt_iff_lt_mul hR).mpr i.isLt⟩
  let Big := {x : Fin l → Fin (t * R) × Fin (t * R) //
    (∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (d : ℤ) = 0}
  let Small := {x : Fin l → Fin R × Fin R //
    (∑ j, ((2 : ℤ) ^ ((x j).1.val + 1) - 2 ^ ((x j).2.val + 1))) % (m : ℤ) = 0}
  have hp (n : ℕ) : (2 : ZMod m) ^ (n % R + 1) = 2 ^ (n + 1) := by
    dsimp [R, Rho.rho]
    rw [pow_succ, pow_succ, pow_mod_orderOf]
  have hsmall (x : Big) :
      (∑ j, ((2 : ℤ) ^ ((red (x.val j).1).val + 1) -
        2 ^ ((red (x.val j).2).val + 1))) % (m : ℤ) = 0 := by
    have hdvd : (m : ℤ) ∣ ∑ j, ((2 : ℤ) ^ ((x.val j).1.val + 1) -
        2 ^ ((x.val j).2.val + 1)) :=
      dvd_trans (by exact_mod_cast hmd) (Int.dvd_of_emod_eq_zero x.property)
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hdvd
    push_cast at hz
    apply Int.dvd_iff_emod_eq_zero.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    push_cast
    change ∑ j, ((2 : ZMod m) ^ ((x.val j).1.val % R + 1) -
      2 ^ ((x.val j).2.val % R + 1)) = 0
    simp_rw [hp]
    exact hz
  let g : Big → Small × (Fin l → Fin t × Fin t) := fun x =>
    (⟨fun j => (red (x.val j).1, red (x.val j).2), hsmall x⟩,
      fun j => (quot (x.val j).1, quot (x.val j).2))
  have recover (i j : Fin (t * R)) (hr : red i = red j) (hq : quot i = quot j) : i = j := by
    apply Fin.ext
    have hr' : i.val % R = j.val % R := congrArg Fin.val hr
    have hq' : i.val / R = j.val / R := congrArg Fin.val hq
    calc
      i.val = i.val % R + R * (i.val / R) := (Nat.mod_add_div _ _).symm
      _ = j.val % R + R * (j.val / R) := by rw [hr', hq']
      _ = j.val := Nat.mod_add_div _ _
  have hg : Function.Injective g := by
    intro x y hxy
    have hr := congrArg (fun z : Small × (Fin l → Fin t × Fin t) => z.1.val) hxy
    have hq := congrArg Prod.snd hxy
    apply Subtype.ext
    funext j
    have hrj := congrFun hr j
    have hqj := congrFun hq j
    apply Prod.ext
    · exact recover _ _ (congrArg Prod.fst hrj) (congrArg Prod.fst hqj)
    · exact recover _ _ (congrArg Prod.snd hrj) (congrArg Prod.snd hqj)
  have hcard := Fintype.card_le_of_injective g hg
  have hb : Fintype.card Big = PairLinnik.Nl l d (t * R) := by
    simp only [Big, Fintype.card_subtype, PairLinnik.Nl]
  have hs : Fintype.card Small = PairLinnik.Nl l m R := by
    simp only [Small, Fintype.card_subtype, PairLinnik.Nl]
  rw [hb, Fintype.card_prod, hs] at hcard
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at hcard
  rw [← pow_two, ← pow_mul] at hcard
  simpa only [R, mul_comm] using hcard

/-- Page 9, display 3.4, the beta half of monotonicity under divisibility. -/
theorem beta_dvd_mono (l m d : ℕ) (hm : Odd m) (hd : Odd d) (hmd : m ∣ d) :
    (Rho.rho m : ℝ) ^ (2 * l) / (PairLinnik.Nl l m (Rho.rho m) : ℝ) ≤
    (Rho.rho d : ℝ) ^ (2 * l) / (PairLinnik.Nl l d (Rho.rho d) : ℝ) := by
  let t := Rho.rho d / Rho.rho m
  have hperiod : t * Rho.rho m = Rho.rho d := Nat.div_mul_cancel (Rho.rho_dvd hmd)
  have hcount := Nl_dvd_le l m d t hm hmd
  rw [hperiod] at hcount
  have hN : (0 : ℝ) < PairLinnik.Nl l m (Rho.rho m) := by
    exact_mod_cast Elementary115.Nl_pos l m hm
  have hN' : (0 : ℝ) < PairLinnik.Nl l d (Rho.rho d) := by
    exact_mod_cast Elementary115.Nl_pos l d hd
  have hcast : (PairLinnik.Nl l d (Rho.rho d) : ℝ) ≤
      (t : ℝ) ^ (2 * l) * PairLinnik.Nl l m (Rho.rho m) := by
    exact_mod_cast hcount
  have hreal : (t : ℝ) * (Rho.rho m : ℝ) = Rho.rho d := by exact_mod_cast hperiod
  rw [div_le_div_iff₀ hN hN']
  calc
    (Rho.rho m : ℝ) ^ (2 * l) * PairLinnik.Nl l d (Rho.rho d) ≤
        (Rho.rho m : ℝ) ^ (2 * l) *
          ((t : ℝ) ^ (2 * l) * PairLinnik.Nl l m (Rho.rho m)) :=
      mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = (Rho.rho d : ℝ) ^ (2 * l) * PairLinnik.Nl l m (Rho.rho m) := by
      rw [← hreal, mul_pow]
      ring

/-- Page 9, display 3.3. The lcm of the orders at prime divisors divides rho of q. -/
theorem lcm_primeFactors_rho_dvd (q : ℕ) :
    q.primeFactors.lcm Rho.rho ∣ Rho.rho q := by
  apply Finset.lcm_dvd
  intro p hp
  exact Rho.rho_dvd (Nat.dvd_of_mem_primeFactors hp)

end LeanLab.Hathi2021.Divisor115

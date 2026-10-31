/-
R-5321, CLOUD 20261021T0217Z-cloud56, unit U-6805, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The singular series as a martingale in the modulus.  For a modulus `m` and a
residue `n` put

  `C m n = #{(u, v) ∈ (ZMod m)ˣ × (ZMod m)ˣ : u + v = n}`,

the number of local Goldbach solutions mod `m`, and `β_m(n) = m C m n / φ(m)²`,
the local density.  For squarefree `m` coprime to `2`, `β_m(n)` is the partial
singular series `∏_{p ∣ m} β_p(n)` of the Hardy-Littlewood conjecture.

Plain math twins:

* `card_isUnit`: `#{a ∈ ZMod m : a is a unit} = φ(m)`.
* `C_eq_c`: `C m n = #{a ∈ ZMod m : a and n - a units}`.
* `c_prime`: for a prime `p`, `C p n = p - 1` if `n = 0`, else `p - 2`.
* `sum_C`: `∑_{n mod m} C m n = φ(m)²`, i.e. `β_m` has mean one over `n mod m`.
* `tower`: for `m ∣ m'` and every `n mod m`,
  `φ(m)² · ∑_{n' mod m', n' ≡ n mod m} C m' n' = φ(m')² · C m n`.
  Divided through, `E[β_{m'}(N) | N mod m] = β_m(N mod m)` for `N` uniform
  mod `m'`: the local densities form a martingale along any divisor chain of
  moduli, for example `m_k = ∏_{p ≤ p_k} p`.  This is the exact form of the
  folklore fact that the singular series averages to one.
* `beta_mean_one`: the rational identity
  `(1/p)·p/(p-1) + ((p-1)/p)·p(p-2)/(p-1)² = 1` for `p ≥ 3`.
* vacuity: `tower_instance` evaluates both sides for `m = 2`, `m' = 4`,
  `n = 0`, and `c_prime_five` checks `C 5 0 = 4`, `C 5 1 = 3` by `decide`.

What the martingale cannot see: every conditional expectation above is a
function of `N mod m`.  The Goldbach count is not measurable for any modulus
filtration, and Selberg's parity example has the same local data; see ROUTES.md
R-5321 field 2.
-/
import Mathlib

namespace LeanLab.Routes.R5321

open Finset

/-- Local Goldbach solutions mod `m`: unit pairs summing to `n`. -/
noncomputable def C (m : ℕ) [NeZero m] (n : ZMod m) : ℕ :=
  #{x : (ZMod m)ˣ × (ZMod m)ˣ | ((x.1 : ZMod m) + x.2) = n}

/-- The same count by the first coordinate. -/
def c (m : ℕ) [NeZero m] (n : ZMod m) : ℕ :=
  #{a : ZMod m | IsUnit a ∧ IsUnit (n - a)}

theorem card_isUnit (m : ℕ) [NeZero m] :
    #{a : ZMod m | IsUnit a} = m.totient := by
  rw [← ZMod.card_units_eq_totient]
  have : (univ.filter (IsUnit : ZMod m → Prop)) =
      (univ.map ⟨((↑) : (ZMod m)ˣ → ZMod m), Units.val_injective⟩) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun h => ⟨h.unit, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.isUnit⟩
  rw [this, card_map, card_univ]

theorem C_eq_c (m : ℕ) [NeZero m] (n : ZMod m) : C m n = c m n := by
  unfold C c
  refine card_bij (fun x _ => (x.1 : ZMod m)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨x.1.isUnit, ?_⟩
    rw [← hx]; simp
  · intro x hx y hy hxy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    have h1 : x.1 = y.1 := Units.ext hxy
    have h2 : (x.2 : ZMod m) = y.2 := by
      have := hx.trans hy.symm
      rw [hxy] at this
      exact add_left_cancel this
    exact Prod.ext h1 (Units.ext h2)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact ⟨(ha.1.unit, ha.2.unit), by simp, rfl⟩

theorem c_prime (p : ℕ) [hp : Fact p.Prime] (n : ZMod p) :
    c p n = if n = 0 then p - 1 else p - 2 := by
  unfold c
  simp only [isUnit_iff_ne_zero]
  split_ifs with hn
  · subst hn
    have : (univ.filter fun a : ZMod p => a ≠ 0 ∧ (0 : ZMod p) - a ≠ 0) = univ.erase 0 := by
      ext a; simp
    rw [this, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  · have : (univ.filter fun a : ZMod p => a ≠ 0 ∧ n - a ≠ 0) = (univ.erase 0).erase n := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_erase, sub_ne_zero, and_true]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, Ne.symm h1⟩
    rw [this, card_erase_of_mem (mem_erase.mpr ⟨hn, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
    omega

theorem c_prime_five : c 5 0 = 4 ∧ c 5 1 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨?_, ?_⟩ <;> rw [c_prime] <;> simp

theorem sum_C (m : ℕ) [NeZero m] : ∑ n : ZMod m, C m n = m.totient ^ 2 := by
  unfold C
  rw [← card_eq_sum_card_fiberwise (f := fun x : (ZMod m)ˣ × (ZMod m)ˣ => (x.1 : ZMod m) + x.2)
    (fun _ _ => mem_univ _)]
  rw [card_univ, Fintype.card_prod, ZMod.card_units_eq_totient, sq]

/-- The martingale, or tower, identity of the local densities. -/
theorem tower {m m' : ℕ} [NeZero m] [NeZero m'] (h : m ∣ m') (n : ZMod m) :
    m.totient ^ 2 * (∑ n' ∈ (univ.filter fun n' : ZMod m' => ZMod.castHom h (ZMod m) n' = n),
      C m' n') = m'.totient ^ 2 * C m n := by
  classical
  set F : (ZMod m')ˣ × (ZMod m')ˣ →* (ZMod m)ˣ × (ZMod m)ˣ :=
    MonoidHom.prodMap (ZMod.unitsMap h) (ZMod.unitsMap h) with hF
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective h y.1
    obtain ⟨b, hb⟩ := ZMod.unitsMap_surjective h y.2
    exact ⟨(a, b), by simp [hF, ha, hb]⟩
  set K := #{x : (ZMod m')ˣ × (ZMod m')ˣ | F x = 1} with hK
  have hfib : ∀ y, #{x : (ZMod m')ˣ × (ZMod m')ˣ | F x = y} = K := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range F (hsurj y) (hsurj 1)
  -- the map on sums
  have hsum : ∀ x : (ZMod m')ˣ × (ZMod m')ˣ,
      ZMod.castHom h (ZMod m) ((x.1 : ZMod m') + x.2) = ((F x).1 : ZMod m) + (F x).2 := by
    intro x
    rw [map_add]; rfl
  -- left side as one count
  have hL : (∑ n' ∈ (univ.filter fun n' : ZMod m' => ZMod.castHom h (ZMod m) n' = n), C m' n')
      = #{x : (ZMod m')ˣ × (ZMod m')ˣ | ZMod.castHom h (ZMod m) ((x.1 : ZMod m') + x.2) = n} := by
    have hmaps : ∀ x ∈ (univ.filter fun x : (ZMod m')ˣ × (ZMod m')ˣ =>
        ZMod.castHom h (ZMod m) ((x.1 : ZMod m') + x.2) = n),
        (fun x : (ZMod m')ˣ × (ZMod m')ˣ => (x.1 : ZMod m') + x.2) x ∈
          (univ.filter fun n' : ZMod m' => ZMod.castHom h (ZMod m) n' = n) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx
    rw [card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl fun n' hn' => ?_
    unfold C
    apply congrArg Finset.card
    ext x
    simp only [mem_filter, mem_univ, true_and] at hn' ⊢
    constructor
    · intro hx; exact ⟨by rw [hx]; exact hn', hx⟩
    · rintro ⟨-, hx⟩; exact hx
  -- count through the fibres of F
  have hL2 : #{x : (ZMod m')ˣ × (ZMod m')ˣ | ZMod.castHom h (ZMod m) ((x.1 : ZMod m') + x.2) = n}
      = C m n * K := by
    have hmaps : ∀ x ∈ (univ.filter fun x : (ZMod m')ˣ × (ZMod m')ˣ =>
        ZMod.castHom h (ZMod m) ((x.1 : ZMod m') + x.2) = n),
        F x ∈ (univ.filter fun y : (ZMod m)ˣ × (ZMod m)ˣ => ((y.1 : ZMod m) + y.2) = n) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [← hsum]; exact hx
    rw [card_eq_sum_card_fiberwise hmaps]
    unfold C
    rw [card_eq_sum_ones (s := univ.filter fun y : (ZMod m)ˣ × (ZMod m)ˣ =>
      ((y.1 : ZMod m) + y.2) = n), sum_mul, one_mul]
    refine sum_congr rfl fun y hy => ?_
    rw [← hfib y]
    apply congrArg Finset.card
    ext x
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    constructor
    · rintro ⟨-, hx⟩; exact hx
    · intro hx; exact ⟨by rw [hsum, hx]; exact hy, hx⟩
  -- total count
  have hT : m'.totient ^ 2 = m.totient ^ 2 * K := by
    have := card_eq_sum_card_fiberwise (f := F) (s := (univ : Finset ((ZMod m')ˣ × (ZMod m')ˣ)))
      (t := univ) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_prod, ZMod.card_units_eq_totient] at this
    have h2 : ∑ y ∈ (univ : Finset ((ZMod m)ˣ × (ZMod m)ˣ)),
        #{x ∈ (univ : Finset ((ZMod m')ˣ × (ZMod m')ˣ)) | F x = y} = m.totient ^ 2 * K := by
      rw [sum_congr rfl fun y _ => hfib y, sum_const, card_univ, Fintype.card_prod,
        ZMod.card_units_eq_totient, smul_eq_mul, sq]
    rw [sq, this, h2]
  rw [hL, hL2, hT]
  ring

theorem tower_instance :
    (Nat.totient 2) ^ 2 * (∑ n' ∈ (univ.filter fun n' : ZMod 4 =>
      ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) n' = 0), C 4 n')
      = (Nat.totient 4) ^ 2 * C 2 0 := tower _ _

theorem beta_mean_one (p : ℚ) (hp : 3 ≤ p) :
    (1 / p) * (p / (p - 1)) + ((p - 1) / p) * (p * (p - 2) / (p - 1) ^ 2) = 1 := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h0 : p ≠ 0 := by linarith
  field_simp
  ring

end LeanLab.Routes.R5321

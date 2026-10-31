/-
P0046 Li and Pan 2007, Theorem 1.2 for every q coprime to 6: lift from d = rad q to q by
averaging over the fibers of Z/q → Z/d. Over a fiber triple, x₁ and x₂ run freely and
x₃ = n - x₁ - x₂ runs over its fiber, so the average of f₁ x₁ + f₂ x₂ + f₃ x₃ is the sum of the
fiber averages. This replaces the paper's prime-power step by one uniform argument.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0128.
-/
import LeanLab.DensityGoldbach.LiPanLocal

open Finset

namespace LeanLab.DensityGoldbach

section lift

variable {q d : ℕ} [NeZero q] [NeZero d] (hdq : d ∣ q)

/-- The fiber of `Z/q → Z/d` over `v`. -/
noncomputable def fib (v : ZMod d) : Finset (ZMod q) :=
  (univ : Finset (ZMod q)).filter (fun x => ZMod.castHom hdq (ZMod d) x = v)

omit [NeZero q] in
lemma lift_spec (v : ZMod d) : ZMod.castHom hdq (ZMod d) ((v.val : ℕ) : ZMod q) = v := by
  rw [map_natCast, ZMod.natCast_zmod_val]

lemma card_fib (v : ZMod d) : #(fib hdq v) = #(fib hdq (0 : ZMod d)) := by
  set w : ZMod q := ((v.val : ℕ) : ZMod q)
  refine card_nbij' (fun x => x - w) (fun x => x + w) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [fib, mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hx ⊢
    rw [map_sub, hx, lift_spec, sub_self]
  · intro x hx
    simp only [fib, mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hx ⊢
    rw [map_add, hx, lift_spec, zero_add]
  · intro x _; simp
  · intro x _; simp

lemma card_fib_pos (v : ZMod d) : 0 < #(fib hdq v) := by
  rw [card_pos]
  exact ⟨((v.val : ℕ) : ZMod q), by simp only [fib, mem_filter, mem_univ, true_and, lift_spec]⟩

/-- Over a fiber triple the pair sum is `c² (g₁ v₁ + g₂ v₂ + g₃ v₃)` in sums form. -/
lemma sum_pairs (f₁ f₂ f₃ : ZMod q → ℝ) (n : ZMod q) (v₁ v₂ v₃ : ZMod d)
    (hv : v₁ + v₂ + v₃ = ZMod.castHom hdq (ZMod d) n) :
    ∑ x₁ ∈ fib hdq v₁, ∑ x₂ ∈ fib hdq v₂, (f₁ x₁ + f₂ x₂ + f₃ (n - x₁ - x₂)) =
      (#(fib hdq (0 : ZMod d)) : ℝ) * ((∑ x ∈ fib hdq v₁, f₁ x) + (∑ x ∈ fib hdq v₂, f₂ x)
        + (∑ x ∈ fib hdq v₃, f₃ x)) := by
  have hinner : ∀ x₁ ∈ fib hdq v₁, ∑ x₂ ∈ fib hdq v₂, f₃ (n - x₁ - x₂) =
      ∑ x ∈ fib hdq v₃, f₃ x := by
    intro x₁ hx₁
    simp only [fib, mem_filter, mem_univ, true_and] at hx₁
    refine sum_nbij' (fun x₂ => n - x₁ - x₂) (fun x => n - x₁ - x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [fib, mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hx ⊢
      rw [map_sub, map_sub, hx₁, hx, ← hv]; ring
    · intro x hx
      simp only [fib, mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hx ⊢
      rw [map_sub, map_sub, hx₁, hx, ← hv]; ring
    · intro x _; ring
    · intro x _; ring
    · intro x _; ring_nf
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul, ← mul_sum, card_fib hdq v₁,
    card_fib hdq v₂]
  ring

variable (hU : ∀ x : ZMod q, IsUnit x ↔ IsUnit (ZMod.castHom hdq (ZMod d) x))
include hU

lemma sum_units_fib (f : ZMod q → ℝ) :
    ∑ x ∈ unitsMod q, f x = ∑ v ∈ unitsMod d, ∑ x ∈ fib hdq v, f x := by
  rw [← sum_fiberwise_of_maps_to (s := unitsMod q) (t := unitsMod d)
    (g := ZMod.castHom hdq (ZMod d)) (fun x hx => by
      rw [mem_unitsMod] at hx ⊢; exact (hU x).1 hx)]
  refine sum_congr rfl fun v hv => ?_
  congr 1
  ext x
  simp only [fib, mem_filter, mem_univ, true_and, mem_unitsMod]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨(hU x).2 ?_, h⟩; rw [h]; exact (mem_unitsMod v).1 hv

/-- **The lift**: `LiPan12 d` gives `LiPan12 q` when units of `Z/q` are the preimages of units
of `Z/d`. -/
theorem liPan12_lift (h : LiPan12 d) : LiPan12 q := by
  intro f₁ f₂ f₃ n
  set c : ℝ := ((#(fib hdq (0 : ZMod d)) : ℕ) : ℝ) with hc
  have hc0 : 0 < c := by rw [hc]; exact_mod_cast card_fib_pos hdq 0
  set g : (ZMod q → ℝ) → ZMod d → ℝ := fun f v => (∑ x ∈ fib hdq v, f x) / c
  have hφ : (q.totient : ℝ) = c * d.totient := by
    have h1 := sum_units_fib hdq hU (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_one] at h1
    have hcard : ∀ m : ℕ, [NeZero m] → #(unitsMod m) = m.totient := by
      intro m _
      rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
      exact Fintype.card_congr
        { toFun := fun u => IsUnit.unit (mem_filter.1 u.2).2
          invFun := fun u => ⟨(u : ZMod m), mem_filter.2 ⟨mem_univ _, u.isUnit⟩⟩
          left_inv := fun u => by simp
          right_inv := fun u => by ext; simp }
    rw [hcard q] at h1
    rw [h1, sum_congr rfl (fun v _ => by rw [card_fib hdq v]), sum_const, hcard d, nsmul_eq_mul,
      mul_comm]
  have hsum : ∀ f : ZMod q → ℝ, ∑ x ∈ unitsMod q, f x = c * ∑ v ∈ unitsMod d, g f v := by
    intro f
    rw [sum_units_fib hdq hU f, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [g]; field_simp
  obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, hv, hK⟩ := h (g f₁) (g f₂) (g f₃)
    (ZMod.castHom hdq (ZMod d) n)
  -- some pair in the fiber triple reaches the average
  have hpairs := sum_pairs hdq f₁ f₂ f₃ n v₁ v₂ v₃ hv
  rw [← hc] at hpairs
  have hcard2 : (#(fib hdq v₁ ×ˢ fib hdq v₂) : ℝ) = c * c := by
    rw [card_product, card_fib hdq v₁, card_fib hdq v₂]; push_cast; rfl
  have hne : (fib hdq v₁ ×ˢ fib hdq v₂).Nonempty := by
    rw [← card_pos, card_product]; exact Nat.mul_pos (card_fib_pos hdq v₁) (card_fib_pos hdq v₂)
  set K := ((∑ a ∈ unitsMod q, f₁ a) + (∑ a ∈ unitsMod q, f₂ a) + (∑ a ∈ unitsMod q, f₃ a))
    / (q.totient : ℝ) with hKdef
  have hKg : K = ((∑ v ∈ unitsMod d, g f₁ v) + (∑ v ∈ unitsMod d, g f₂ v)
      + (∑ v ∈ unitsMod d, g f₃ v)) / d.totient := by
    rw [hKdef, hsum f₁, hsum f₂, hsum f₃, hφ]
    have : (d.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
    field_simp
  obtain ⟨⟨x₁, x₂⟩, hx, hge⟩ := exists_le_of_sum_le (s := fib hdq v₁ ×ˢ fib hdq v₂)
    (f := fun _ => K) (g := fun p => f₁ p.1 + f₂ p.2 + f₃ (n - p.1 - p.2)) hne (by
      rw [sum_product (fib hdq v₁) (fib hdq v₂) (fun p => f₁ p.1 + f₂ p.2 + f₃ (n - p.1 - p.2)),
        hpairs, sum_const, nsmul_eq_mul, hcard2]
      have : K ≤ g f₁ v₁ + g f₂ v₂ + g f₃ v₃ := hKg ▸ hK
      simp only [g] at this
      have e : (∑ x ∈ fib hdq v₁, f₁ x) + (∑ x ∈ fib hdq v₂, f₂ x) + (∑ x ∈ fib hdq v₃, f₃ x)
          = c * ((∑ x ∈ fib hdq v₁, f₁ x) / c + (∑ x ∈ fib hdq v₂, f₂ x) / c
            + (∑ x ∈ fib hdq v₃, f₃ x) / c) := by field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left this hc0.le])
  obtain ⟨hx₁, hx₂⟩ := mem_product.1 hx
  simp only [fib, mem_filter, mem_univ, true_and] at hx₁ hx₂
  refine ⟨x₁, ?_, x₂, ?_, n - x₁ - x₂, ?_, by ring, hge⟩
  · rw [mem_unitsMod, hU, hx₁]; exact (mem_unitsMod v₁).1 hv₁
  · rw [mem_unitsMod, hU, hx₂]; exact (mem_unitsMod v₂).1 hv₂
  · rw [mem_unitsMod, hU, map_sub, map_sub, hx₁, hx₂, ← hv]
    ring_nf; exact (mem_unitsMod v₃).1 hv₃

end lift

lemma coprime_iff_primes (a n : ℕ) : a.Coprime n ↔ ∀ p, p.Prime → p ∣ n → ¬ p ∣ a :=
  ⟨fun h p hp hpn hpa => hp.not_dvd_one (h ▸ Nat.dvd_gcd hpa hpn),
    fun h => Nat.coprime_of_dvd fun p hp hpa hpn => h p hp hpn hpa⟩

/-- **Li-Pan Theorem 1.2 in full**: every `q` coprime to `6`. -/
theorem liPan12_full (q : ℕ) [NeZero q] (h6 : q.Coprime 6) : LiPan12 q := by
  set d := ∏ p ∈ q.primeFactors, p with hd
  have hq0 : q ≠ 0 := NeZero.ne q
  have hdq : d ∣ q := Nat.prod_primeFactors_dvd q
  have hd0 : NeZero d := ⟨fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hdq))⟩
  have hprime : ∀ p ∈ q.primeFactors, p.Prime ∧ 5 ≤ p := fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    have hc : p.Coprime 6 := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) h6
    by_contra hlt
    push Not at hlt
    have := hpp.two_le
    interval_cases p <;> revert hpp hc <;> decide
  have hLd : LiPan12 d := liPan12_prod q.primeFactors hprime d hd hd0
  have hdiv : ∀ p, p.Prime → (p ∣ q ↔ p ∣ d) := fun p hp =>
    ⟨fun h => dvd_prod_of_mem _ (Nat.mem_primeFactors.2 ⟨hp, h, hq0⟩), fun h => h.trans hdq⟩
  refine liPan12_lift hdq (fun x => ?_) hLd
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, map_natCast,
    ZMod.isUnit_iff_coprime, coprime_iff_primes, coprime_iff_primes]
  exact forall_congr' fun p => imp_congr_right fun hp => by rw [hdiv p hp]

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.liPan12_full

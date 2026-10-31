/-
P0046 Li and Pan 2007, arXiv math/0701240, Theorem 1.2, the local averaging lemma: for q with
gcd(q, 6) = 1 and any real f₁, f₂, f₃ on the reduced residues mod q, every n mod q is
x + y + z with reduced x, y, z and f₁ x + f₂ y + f₃ z at least the average
(S₁ + S₂ + S₃)/φ(q). Here: the prime case p ≥ 5 by the paper's double counting, then the
CRT product step, giving every squarefree q coprime to 6.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0127.
-/
import LeanLab.DensityGoldbach.Prop31Step

open Finset

namespace LeanLab.DensityGoldbach

/-- Li-Pan Theorem 1.2 at one modulus `q`. -/
def LiPan12 (q : ℕ) [NeZero q] : Prop := ∀ f₁ f₂ f₃ : ZMod q → ℝ, ∀ n : ZMod q,
  ∃ x ∈ unitsMod q, ∃ y ∈ unitsMod q, ∃ z ∈ unitsMod q, x + y + z = n ∧
    ((∑ a ∈ unitsMod q, f₁ a) + (∑ a ∈ unitsMod q, f₂ a) + (∑ a ∈ unitsMod q, f₃ a))
      / q.totient ≤ f₁ x + f₂ y + f₃ z

section prime

variable (p : ℕ) [hp : Fact p.Prime]

lemma mem_unitsMod_prime (z : ZMod p) : z ∈ unitsMod p ↔ z ≠ 0 := by
  rw [mem_unitsMod, isUnit_iff_ne_zero]

/-- `y ↦ m - y` permutes the nonzero residues other than `m`. -/
lemma sum_sub_erase (g : ZMod p → ℝ) (m : ZMod p) :
    ∑ y ∈ (unitsMod p).erase m, g (m - y) = ∑ y ∈ (unitsMod p).erase m, g y := by
  refine sum_nbij' (fun y => m - y) (fun y => m - y) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_erase, mem_unitsMod_prime] at hy ⊢
    exact ⟨fun h => hy.2 (by linear_combination -h), fun h => hy.1 (by linear_combination -h)⟩
  · intro y hy
    rw [mem_erase, mem_unitsMod_prime] at hy ⊢
    exact ⟨fun h => hy.2 (by linear_combination -h), fun h => hy.1 (by linear_combination -h)⟩
  · intro y _; ring
  · intro y _; ring
  · intro y _; rfl

/-- The pair count, Li-Pan (2.2): for `x ≠ 0`, `m = n - x ≠ 0`. -/
lemma lp_D (f₁ f₂ f₃ : ZMod p → ℝ) (n : ZMod p) (K : ℝ)
    (H : ∀ x ∈ unitsMod p, ∀ y ∈ unitsMod p, ∀ z ∈ unitsMod p, x + y + z = n →
      f₁ x + f₂ y + f₃ z < K) (hp5 : 5 ≤ p)
    (x : ZMod p) (hx : x ∈ unitsMod p) (hm : n - x ≠ 0) :
    ((p : ℝ) - 2) * f₁ x + ((∑ a ∈ unitsMod p, f₂ a) - f₂ (n - x))
      + ((∑ a ∈ unitsMod p, f₃ a) - f₃ (n - x)) < ((p : ℝ) - 2) * K := by
  set m := n - x with hmdef
  have hmU : m ∈ unitsMod p := (mem_unitsMod_prime p m).2 hm
  have hcard : (#((unitsMod p).erase m) : ℝ) = (p : ℝ) - 2 := by
    rw [card_erase_of_mem hmU, card_unitsMod_prime, Nat.cast_sub (by omega),
      Nat.cast_sub hp.out.one_le]
    push_cast; ring
  have hne : ((unitsMod p).erase m).Nonempty := by
    rw [← card_pos]; have := card_unitsMod_prime p
    rw [card_erase_of_mem hmU]; omega
  have hlt := sum_lt_sum_of_nonempty hne (f := fun y => f₁ x + f₂ y + f₃ (m - y))
    (g := fun _ => K) (fun y hy => by
      have hy' := mem_erase.1 hy
      apply H x hx y hy'.2 (m - y) ?_ (by rw [hmdef]; ring)
      rw [mem_unitsMod_prime]; intro h; exact hy'.1 (by linear_combination -h))
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hcard] at hlt
  rw [sum_sub_erase p f₃ m, sum_erase_eq_sub hmU, sum_erase_eq_sub hmU] at hlt
  linarith

/-- Li-Pan (2.3): the solutions with `x = n`. -/
lemma lp_D0 (f₁ f₂ f₃ : ZMod p → ℝ) (n : ZMod p) (K : ℝ)
    (H : ∀ x ∈ unitsMod p, ∀ y ∈ unitsMod p, ∀ z ∈ unitsMod p, x + y + z = n →
      f₁ x + f₂ y + f₃ z < K) (hn : n ≠ 0) :
    ((p : ℝ) - 1) * f₁ n + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a)
      < ((p : ℝ) - 1) * K := by
  have hnU : n ∈ unitsMod p := (mem_unitsMod_prime p n).2 hn
  have hcard : (#(unitsMod p) : ℝ) = (p : ℝ) - 1 := by
    rw [card_unitsMod_prime, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have hne : (unitsMod p).Nonempty := ⟨n, hnU⟩
  have hlt := sum_lt_sum_of_nonempty hne (f := fun y => f₁ n + f₂ y + f₃ (-y))
    (g := fun _ => K) (fun y hy => by
      apply H n hnU y hy (-y) ?_ (by ring)
      rw [mem_unitsMod_prime] at hy ⊢; exact neg_ne_zero.2 hy)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hcard] at hlt
  have hneg : ∑ y ∈ unitsMod p, f₃ (-y) = ∑ y ∈ unitsMod p, f₃ y := by
    refine sum_nbij' (fun y => -y) (fun y => -y) ?_ ?_ ?_ ?_ ?_ <;>
      simp [mem_unitsMod_prime]
  rw [hneg] at hlt
  linarith

/-- `x ↦ n - x` and the sum over `x ≠ 0, n`. -/
lemma sum_erase_sub (g : ZMod p → ℝ) (n : ZMod p) :
    ∑ x ∈ (unitsMod p).erase n, g (n - x) = ∑ x ∈ (unitsMod p).erase n, g x :=
  sum_sub_erase p g n

/-- Summed (2.2) over `x ≠ 0, n`, in the normalized form `E`. -/
lemma lp_E (f₁ f₂ f₃ : ZMod p → ℝ) (n : ZMod p)
    (H : ∀ x ∈ unitsMod p, ∀ y ∈ unitsMod p, ∀ z ∈ unitsMod p, x + y + z = n →
      f₁ x + f₂ y + f₃ z <
        ((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a))
          / ((p : ℝ) - 1)) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    -((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a))
      + ((p : ℝ) - 1) * (∑ a ∈ unitsMod p, f₁ a) - ((p : ℝ) - 1) * ((p : ℝ) - 2) * f₁ n
      + ((p : ℝ) - 1) * (f₂ n + f₃ n) < 0 := by
  have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnU : n ∈ unitsMod p := (mem_unitsMod_prime p n).2 hn
  have hcard : (#((unitsMod p).erase n) : ℝ) = (p : ℝ) - 2 := by
    rw [card_erase_of_mem hnU, card_unitsMod_prime, Nat.cast_sub (by omega),
      Nat.cast_sub hp.out.one_le]
    push_cast; ring
  have hne : ((unitsMod p).erase n).Nonempty := by
    rw [← card_pos, card_erase_of_mem hnU, card_unitsMod_prime]; omega
  have hlt := sum_lt_sum_of_nonempty hne
    (f := fun x => ((p : ℝ) - 2) * f₁ x + ((∑ a ∈ unitsMod p, f₂ a) - f₂ (n - x))
      + ((∑ a ∈ unitsMod p, f₃ a) - f₃ (n - x)))
    (g := fun _ => ((p : ℝ) - 2) *
      (((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a))
          / ((p : ℝ) - 1))) (fun x hx => by
      have hx' := mem_erase.1 hx
      exact lp_D p f₁ f₂ f₃ n _ H hp5 x hx'.2 (sub_ne_zero.2 (Ne.symm hx'.1)))
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← mul_sum]
    at hlt
  rw [sum_erase_sub p f₂ n, sum_erase_sub p f₃ n, sum_erase_eq_sub hnU, sum_erase_eq_sub hnU,
    sum_erase_eq_sub hnU] at hlt
  have hKe : ((p : ℝ) - 1) * (((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a)
      + (∑ a ∈ unitsMod p, f₃ a)) / ((p : ℝ) - 1)) =
      (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a) := by
    field_simp
  have := mul_lt_mul_of_pos_left hlt hp1
  generalize (∑ a ∈ unitsMod p, f₁ a) = S₁ at *
  generalize (∑ a ∈ unitsMod p, f₂ a) = S₂ at *
  generalize (∑ a ∈ unitsMod p, f₃ a) = S₃ at *
  generalize (S₁ + S₂ + S₃) / ((p : ℝ) - 1) = K at *
  generalize (p : ℝ) = q at *
  have hK2 : (q - 1) * ((q - 2) * ((q - 2) * K)) = (q - 2) ^ 2 * (S₁ + S₂ + S₃) := by
    rw [← hKe]; ring
  linarith

/-- **Li-Pan Theorem 1.2 for a prime `p ≥ 5`.** -/
theorem liPan12_prime (hp5 : 5 ≤ p) : LiPan12 p := by
  intro f₁ f₂ f₃ n
  by_contra hne
  push Not at hne
  have htot : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [htot] at hne
  have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have H := hne
  by_cases hn : n = 0
  · have hcard : (#(unitsMod p) : ℝ) = (p : ℝ) - 1 := by
      rw [card_unitsMod_prime, Nat.cast_sub hp.out.one_le, Nat.cast_one]
    have hne' : (unitsMod p).Nonempty := ⟨1, (mem_unitsMod_prime p 1).2 one_ne_zero⟩
    have hlt := sum_lt_sum_of_nonempty hne'
      (f := fun x => ((p : ℝ) - 2) * f₁ x + ((∑ a ∈ unitsMod p, f₂ a) - f₂ (n - x))
        + ((∑ a ∈ unitsMod p, f₃ a) - f₃ (n - x)))
      (g := fun _ => ((p : ℝ) - 2) *
        (((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a))
          / ((p : ℝ) - 1)))
      (fun x hx => lp_D p f₁ f₂ f₃ n _ H hp5 x hx (by
        rw [hn, zero_sub, neg_ne_zero]; exact (mem_unitsMod_prime p x).1 hx))
    have hneg : ∀ g : ZMod p → ℝ, ∑ x ∈ unitsMod p, g (n - x) = ∑ x ∈ unitsMod p, g x := by
      intro g
      refine sum_nbij' (fun x => n - x) (fun x => n - x) ?_ ?_ ?_ ?_ ?_ <;>
        simp [mem_unitsMod_prime, hn]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← mul_sum,
      hneg] at hlt
    have hKe : ((p : ℝ) - 1) * (((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a)
        + (∑ a ∈ unitsMod p, f₃ a)) / ((p : ℝ) - 1)) =
        (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a) := by
      field_simp
    have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    generalize (∑ a ∈ unitsMod p, f₁ a) = S₁ at *
    generalize (∑ a ∈ unitsMod p, f₂ a) = S₂ at *
    generalize (∑ a ∈ unitsMod p, f₃ a) = S₃ at *
    generalize (S₁ + S₂ + S₃) / ((p : ℝ) - 1) = K at *
    generalize (p : ℝ) = q at *
    nlinarith
  · have E₁ := lp_E p f₁ f₂ f₃ n H hp5 hn
    have E₂ := lp_E p f₂ f₁ f₃ n (fun x hx y hy z hz e => by
      have := H y hy x hx z hz (by rw [← e]; ring)
      have e2 : (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₃ a)
        = (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a) := by
        ring
      rw [e2]; linarith) hp5 hn
    have E₃ := lp_E p f₃ f₂ f₁ n (fun x hx y hy z hz e => by
      have := H z hz y hy x hx (by rw [← e]; ring)
      have e3 : (∑ a ∈ unitsMod p, f₃ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₁ a)
        = (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a) := by
        ring
      rw [e3]; linarith) hp5 hn
    have E₀ := lp_D0 p f₁ f₂ f₃ n _ H hn
    have hKe : ((p : ℝ) - 1) * (((∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a)
        + (∑ a ∈ unitsMod p, f₃ a)) / ((p : ℝ) - 1)) =
        (∑ a ∈ unitsMod p, f₁ a) + (∑ a ∈ unitsMod p, f₂ a) + (∑ a ∈ unitsMod p, f₃ a) := by
      field_simp
    have h3 : (0 : ℝ) < (p : ℝ) - 3 := by linarith
    have h4 : (0 : ℝ) < (p : ℝ) - 4 := by linarith
    generalize (∑ a ∈ unitsMod p, f₁ a) = S₁ at *
    generalize (∑ a ∈ unitsMod p, f₂ a) = S₂ at *
    generalize (∑ a ∈ unitsMod p, f₃ a) = S₃ at *
    generalize (S₁ + S₂ + S₃) / ((p : ℝ) - 1) = K at *
    generalize (p : ℝ) = q at *
    -- `(q - 3) E₁ + E₂ + E₃` gives `(q - 1)(q - 4)(S₁ - (q - 1) f₁ n) < 0`; `E₀` the reverse.
    have hc : (q - 1) * (q - 4) * (S₁ - (q - 1) * f₁ n) < 0 := by
      nlinarith [mul_lt_mul_of_pos_left E₁ h3]
    have hE0 : (q - 1) * f₁ n < S₁ := by linarith
    have : 0 < (q - 1) * (q - 4) * (S₁ - (q - 1) * f₁ n) := by
      apply mul_pos (mul_pos hp1 h4); linarith
    linarith

end prime

lemma liPan12_congr {m n : ℕ} (h : m = n) {_ : NeZero m} {_ : NeZero n} (hm : LiPan12 m) :
    LiPan12 n := by
  subst h; exact hm

lemma liPan12_one : LiPan12 1 := by
  intro f₁ f₂ f₃ n
  have hU : (0 : ZMod 1) ∈ unitsMod 1 := mem_filter.2 ⟨mem_univ _, isUnit_of_subsingleton _⟩
  have hUe : unitsMod 1 = {0} := by
    ext u; rw [mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ hU⟩
  refine ⟨0, hU, 0, hU, 0, hU, Subsingleton.elim _ _, ?_⟩
  rw [hUe, sum_singleton, sum_singleton, sum_singleton, Nat.totient_one, Nat.cast_one, div_one]

/-- **The CRT step**: `LiPan12 m` and a prime `p ≥ 5` coprime to `m` give `LiPan12 (m p)`. -/
theorem liPan12_step (m p : ℕ) [NeZero m] [hp : Fact p.Prime] [NeZero (m * p)] (hp5 : 5 ≤ p)
    (hcop : m.Coprime p) (hm : LiPan12 m) : LiPan12 (m * p) := by
  intro f₁ f₂ f₃ n
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set e := ZMod.chineseRemainder hcop with he
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  have htp : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have hφm : (0 : ℝ) < (m.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))
  -- fiber averages
  let F : (ZMod (m * p) → ℝ) → ZMod m → ZMod p → ℝ := fun f u v => f (e.symm (u, v))
  let av : (ZMod (m * p) → ℝ) → ZMod m → ℝ := fun f u =>
    (∑ v ∈ unitsMod p, F f u v) / ((p : ℝ) - 1)
  have hav : ∀ f : ZMod (m * p) → ℝ, ∑ u ∈ unitsMod m, av f u =
      (∑ z ∈ unitsMod (m * p), f z) / ((p : ℝ) - 1) := by
    intro f
    rw [sum_unitsMod_crt hcop, sum_div]
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx1, hK1⟩ := hm (av f₁) (av f₂) (av f₃) (e n).1
  obtain ⟨s, hs, t, ht, r, hr, hx2, hK2⟩ := liPan12_prime p hp5 (F f₁ a₁) (F f₂ a₂) (F f₃ a₃)
    (e n).2
  refine ⟨e.symm (a₁, s), ?_, e.symm (a₂, t), ?_, e.symm (a₃, r), ?_, ?_, ?_⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₁, hs⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₂, ht⟩
  · rw [mem_unitsMod_crt hcop, RingEquiv.apply_symm_apply]; exact ⟨ha₃, hr⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, hx1, hx2]
  · rw [hav, hav, hav] at hK1
    rw [htp] at hK2
    rw [Nat.totient_mul hcop, Nat.cast_mul, htp]
    have hK2' : av f₁ a₁ + av f₂ a₂ + av f₃ a₃ ≤ F f₁ a₁ s + F f₂ a₂ t + F f₃ a₃ r := by
      have : av f₁ a₁ + av f₂ a₂ + av f₃ a₃ =
          ((∑ v ∈ unitsMod p, F f₁ a₁ v) + (∑ v ∈ unitsMod p, F f₂ a₂ v)
            + (∑ v ∈ unitsMod p, F f₃ a₃ v)) / ((p : ℝ) - 1) := by
        simp only [av]; ring
      rw [this]; exact hK2
    have heq : ((∑ z ∈ unitsMod (m * p), f₁ z) + (∑ z ∈ unitsMod (m * p), f₂ z)
        + (∑ z ∈ unitsMod (m * p), f₃ z)) / ((m.totient : ℝ) * ((p : ℝ) - 1)) =
        ((∑ z ∈ unitsMod (m * p), f₁ z) / ((p : ℝ) - 1)
          + (∑ z ∈ unitsMod (m * p), f₂ z) / ((p : ℝ) - 1)
          + (∑ z ∈ unitsMod (m * p), f₃ z) / ((p : ℝ) - 1)) / (m.totient : ℝ) := by
      field_simp
    rw [heq]
    exact hK1.trans hK2'

/-- Induction over a finset of primes `≥ 5`. -/
theorem liPan12_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    ∀ n (_ : n = ∏ p ∈ S, p) (_ : NeZero n), LiPan12 n := by
  induction S using Finset.induction_on with
  | empty =>
    intro n hn _
    exact liPan12_congr (by simp [hn]) liPan12_one
  | insert a s ha ih =>
    intro n hn _
    have hprod : 0 < ∏ p ∈ s, p := prod_pos fun p hp => (hS p (mem_insert_of_mem hp)).1.pos
    set k := ∏ p ∈ s, p with hk
    have hk0 : NeZero k := ⟨hprod.ne'⟩
    have ih' : LiPan12 k := ih (fun p hp => hS p (mem_insert_of_mem hp)) k rfl hk0
    obtain ⟨hap, ha5⟩ := hS a (mem_insert_self a s)
    have : Fact a.Prime := ⟨hap⟩
    have : NeZero (k * a) := ⟨(Nat.mul_pos hprod hap.pos).ne'⟩
    have hc : k.Coprime a := Nat.Coprime.prod_left fun p hp =>
      (Nat.coprime_primes (hS p (mem_insert_of_mem hp)).1 hap).2 (fun h => ha (h ▸ hp))
    exact liPan12_congr (by rw [hn, prod_insert ha, hk]; ring) (liPan12_step k a ha5 hc ih')

/-- **Li-Pan Theorem 1.2 for every squarefree `q` coprime to `6`.** -/
theorem liPan12_squarefree (q : ℕ) [NeZero q] (hsq : Squarefree q) (h6 : q.Coprime 6) :
    LiPan12 q := by
  refine liPan12_prod q.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩) q
    (Nat.prod_primeFactors_of_squarefree hsq).symm inferInstance
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hc : p.Coprime 6 := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) h6
  by_contra hlt
  push Not at hlt
  have := hpp.two_le
  interval_cases p <;> revert hpp hc <;> decide

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.liPan12_squarefree

import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Factorization.Basic

/-!
Deepening of the MEDIUM leaf `hyperbola_identity` of Feed1122VoronoiDivisorSumAsymptotic.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
The real variable identity reduces to its integer form at N equal to floor x,
since floor of x over m is floor x divided by m and floor of root x is the integer square root of floor x.
The reduction is proved here; the integer hyperbola identity is the remaining leaf.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

open Finset

/-! Helpers for the integer hyperbola identity: the divisor sum counts lattice points
under the hyperbola a b at most N, split by a at most root N or b at most root N. -/

lemma card_mul_le_row (N a : ℕ) (ha : 1 ≤ a) :
    #{b ∈ Icc 1 N | a * b ≤ N} = N / a := by
  have e : ({b ∈ Icc 1 N | a * b ≤ N} : Finset ℕ) = Icc 1 (N / a) := by
    ext b
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le ha]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by rw [mul_comm]; exact h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, by rw [mul_comm]; exact h3⟩
      calc b ≤ b * a := Nat.le_mul_of_pos_right b ha
        _ ≤ N := h3
  rw [e, Nat.card_Icc, Nat.add_sub_cancel]

lemma card_left (N K : ℕ) :
    #{p ∈ Icc 1 K ×ˢ Icc 1 N | p.1 * p.2 ≤ N} = ∑ a ∈ Icc 1 K, N / a := by
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun a ha => ?_)
  rw [← card_filter, card_mul_le_row N a (mem_Icc.mp ha).1]

lemma card_right (N K : ℕ) :
    #{p ∈ Icc 1 N ×ˢ Icc 1 K | p.1 * p.2 ≤ N} = ∑ b ∈ Icc 1 K, N / b := by
  rw [card_filter, sum_product_right]
  refine sum_congr rfl (fun b hb => ?_)
  rw [← card_filter]
  have : ({a ∈ Icc 1 N | a * b ≤ N} : Finset ℕ) = {a ∈ Icc 1 N | b * a ≤ N} := by
    ext a; simp [mul_comm]
  rw [this, card_mul_le_row N b (mem_Icc.mp hb).1]

lemma sum_card_divisors (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, N / a := by
  have h1 : ∀ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, if a ∣ n then 1 else 0 := by
    intro n hn
    rw [← card_filter]
    congr 1
    ext a
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    obtain ⟨hn1, hn2⟩ := mem_Icc.mp hn
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn1, (Nat.le_of_dvd hn1 hd).trans hn2⟩, hd⟩
    · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← card_filter]
  have : Icc 1 N = Ioc 0 N := by ext x; simp [mem_Icc, mem_Ioc]; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma nat_identity (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card + Nat.sqrt N ^ 2 =
      2 * ∑ m ∈ Icc 1 (Nat.sqrt N), N / m := by
  set s := Nat.sqrt N with hs
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hs2 : s * s ≤ N := Nat.sqrt_le N
  have hlt : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  set PA := ({p ∈ Icc 1 s ×ˢ Icc 1 N | p.1 * p.2 ≤ N} : Finset (ℕ × ℕ)) with hPA
  set PB := ({p ∈ Icc 1 N ×ˢ Icc 1 s | p.1 * p.2 ≤ N} : Finset (ℕ × ℕ)) with hPB
  have hU : PA ∪ PB = {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 * p.2 ≤ N} := by
    ext ⟨a, b⟩
    simp only [hPA, hPB, mem_union, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro (⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ | ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩)
      · exact ⟨⟨⟨h1, h2.trans hsN⟩, h3, h4⟩, h5⟩
      · exact ⟨⟨⟨h1, h2⟩, h3, h4.trans hsN⟩, h5⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      by_cases ha : a ≤ s
      · exact Or.inl ⟨⟨⟨h1, ha⟩, h3, h4⟩, h5⟩
      · by_cases hb : b ≤ s
        · exact Or.inr ⟨⟨⟨h1, h2⟩, h3, hb⟩, h5⟩
        · exfalso
          have : (s + 1) * (s + 1) ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
          omega
  have hI : PA ∩ PB = Icc 1 s ×ˢ Icc 1 s := by
    ext ⟨a, b⟩
    simp only [hPA, hPB, mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, ⟨⟨h6, h7⟩, h8, h9⟩, h10⟩
      exact ⟨⟨h1, h2⟩, h3, h9⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have : a * b ≤ N := (Nat.mul_le_mul h2 h4).trans hs2
      exact ⟨⟨⟨⟨h1, h2⟩, h3, h4.trans hsN⟩, this⟩, ⟨⟨h1, h2.trans hsN⟩, h3, h4⟩, this⟩
  have key := card_union_add_card_inter PA PB
  rw [hU, hI, card_product, Nat.card_Icc, Nat.add_sub_cancel, hPA, hPB, card_left, card_right,
    card_left, ← sum_card_divisors] at key
  rw [sq, key]; ring

/-- Formerly LEAF, now proved: integer Dirichlet hyperbola identity, the first step of the classical proof of the
Voronoi formula cited on Halupczok page 337. For every natural N, the sum of d of n for n up to N
equals twice the sum over m up to the integer square root of N of N divided by m,
minus the square of that integer square root.
Class MEDIUM: an exact finite lattice point count by the symmetry of the hyperbola. -/
theorem nat_hyperbola_identity :
    ∀ N : ℕ, (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) =
      2 * ∑ m ∈ Icc 1 (Nat.sqrt N), ((N / m : ℕ) : ℝ) - (Nat.sqrt N : ℝ) ^ 2 := by
  intro N
  have h := nat_identity N
  have h' : ((∑ n ∈ Icc 1 N, n.divisors.card + Nat.sqrt N ^ 2 : ℕ) : ℝ) =
      ((2 * ∑ m ∈ Icc 1 (Nat.sqrt N), N / m : ℕ) : ℝ) := by rw [h]
  push_cast at h'
  linarith


/-- For x at least 0, the floor of root x is the integer square root of floor x. -/
theorem floor_sqrt_eq (x : ℝ) (hx : 0 ≤ x) : ⌊Real.sqrt x⌋₊ = Nat.sqrt ⌊x⌋₊ := by
  set N := ⌊x⌋₊
  rw [Nat.floor_eq_iff (Real.sqrt_nonneg x)]
  have h1 : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ x := by
    have := Nat.sqrt_le' N
    have h2 : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at h2
    exact h2.trans (Nat.floor_le hx)
  have h3 : x < ((Nat.sqrt N : ℕ) + 1 : ℝ) ^ 2 := by
    have h4 : N + 1 ≤ (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
    have h5 : ((N + 1 : ℕ) : ℝ) ≤ (((Nat.sqrt N + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    linarith [Nat.lt_floor_add_one x]
  constructor
  · exact Real.le_sqrt_of_sq_le h1
  · rw [Real.sqrt_lt' (by positivity)]; exact h3

/-- The real variable hyperbola identity, assembled from the integer leaf.
Statement identical to `hyperbola_identity`. -/
theorem hyperbola_identity_of_leaves :
    ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) =
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 := by
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  rw [floor_sqrt_eq x hx0, nat_hyperbola_identity ⌊x⌋₊]
  congr 2
  apply sum_congr rfl
  intro m _
  rw [Nat.floor_div_natCast]

end LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.nat_hyperbola_identity
#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.floor_sqrt_eq
#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.hyperbola_identity_of_leaves

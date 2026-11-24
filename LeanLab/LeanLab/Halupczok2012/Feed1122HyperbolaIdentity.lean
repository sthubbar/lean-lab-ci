import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield

/-!
Deepening of the MEDIUM leaf `hyperbola_identity` of Feed1122VoronoiDivisorSumAsymptotic.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
The real variable identity reduces to its integer form at N equal to floor x,
since floor of x over m is floor x divided by m and floor of root x is the integer square root of floor x.
The reduction is proved here, and the integer hyperbola identity is proved too, by session S91.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

open Finset

/-- The lattice points `(a, b)` of `[1, N]²` under the hyperbola `ab ≤ N` number `∑_{n ≤ N} d(n)`. -/
theorem card_ab (N : ℕ) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)).card =
      ∑ n ∈ Icc 1 N, n.divisors.card := by
  have hS : (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) =
      (Icc 1 N).biUnion (fun n => n.divisorsAntidiagonal) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_biUnion, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hab⟩
      exact ⟨a * b, ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hab⟩, rfl, by positivity⟩
    · rintro ⟨n, ⟨hn1, hnN⟩, rfl, hn0⟩
      have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul hn0)
      have hb : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul hn0)
      refine ⟨⟨⟨ha, ?_⟩, hb, ?_⟩, hnN⟩
      · exact le_trans (Nat.le_mul_of_pos_right a hb) hnN
      · exact le_trans (Nat.le_mul_of_pos_left b ha) hnN
  rw [hS, card_biUnion]
  · refine sum_congr rfl (fun n _ => ?_)
    rw [← Nat.map_div_right_divisors, card_map]
  · intro x _ y _ hxy
    rw [Function.onFun, disjoint_left]
    intro p hx hy
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    exact hxy (hx.1.symm.trans hy.1)

/-- The lattice points under the hyperbola with `a ≤ s` number `∑_{a ≤ s} ⌊N/a⌋`. -/
theorem card_left (N s : ℕ) (hs : s ≤ N) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N ∧ p.1 ≤ s)).card =
      ∑ a ∈ Icc 1 s, N / a := by
  rw [card_filter, sum_product]
  rw [← sum_subset (Icc_subset_Icc_right hs)]
  · refine sum_congr rfl (fun a ha => ?_)
    have ha' := mem_Icc.mp ha
    rw [← card_filter]
    have : (Icc 1 N).filter (fun b => a * b ≤ N ∧ a ≤ s) = Icc 1 (N / a) := by
      ext b
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hb1, _⟩, hab, _⟩
        exact ⟨hb1, (Nat.le_div_iff_mul_le ha'.1).mpr (by linarith [mul_comm a b])⟩
      · rintro ⟨hb1, hb⟩
        have hab : b * a ≤ N := (Nat.le_div_iff_mul_le ha'.1).mp hb
        refine ⟨⟨hb1, le_trans (Nat.le_mul_of_pos_right b ha'.1) hab⟩, by linarith [mul_comm a b], ha'.2⟩
    rw [this]; simp
  · intro a haN ha
    have haN' := (mem_Icc.mp haN).1
    rw [mem_Icc, not_and_or] at ha
    apply sum_eq_zero
    intro b _
    rw [ite_eq_right_iff]; intro hh; exfalso; revert hh
    rintro ⟨_, h⟩
    rcases ha with h1 | h1
    · omega
    · exact h1 h

/-- Integer hyperbola identity in `ℕ`: the points split into `a ≤ √N` or `b ≤ √N`, the overlap is the `√N × √N` square. -/
theorem nat_key (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card + Nat.sqrt N ^ 2 = 2 * ∑ m ∈ Icc 1 (Nat.sqrt N), N / m := by
  set s := Nat.sqrt N with hsdef
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hss : s * s ≤ N := Nat.sqrt_le N
  set S := (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) with hS
  set A := S.filter (fun p => p.1 ≤ s)
  set B := S.filter (fun p => p.2 ≤ s)
  have hunion : A ∪ B = S := by
    ext ⟨a, b⟩
    simp only [A, B, mem_union, mem_filter, S]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_contra hc
      push Not at hc
      have h1 : s < a := hc.1 h
      have h2 : s < b := hc.2 h
      have : (s + 1) * (s + 1) ≤ a * b := Nat.mul_le_mul h1 h2
      have h3 : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
      omega
  have hinter : A ∩ B = Icc 1 s ×ˢ Icc 1 s := by
    ext ⟨a, b⟩
    simp only [A, B, S, mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · intro h; omega
    · intro h
      have : a * b ≤ s * s := Nat.mul_le_mul h.1.2 h.2.2
      omega
  have hA : A.card = ∑ a ∈ Icc 1 s, N / a := by
    rw [← card_left N s hsN]; simp only [A, S, filter_filter]
  have hB : B.card = A.card := by
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [A, B, S, mem_filter, mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [Prod.fst_swap, Prod.snd_swap, mul_comm]; exact hp.1.2⟩, hp.2⟩
    · intro p _ q _ h; exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [A, B, S, mem_filter, mem_product] at hq ⊢
      exact ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, by rw [Prod.fst_swap, Prod.snd_swap, mul_comm]; exact hq.1.2⟩, hq.2⟩
  have hcu := card_union_add_card_inter A B
  rw [hunion, hinter, card_product, Nat.card_Icc, hB, hA] at hcu
  rw [← card_ab N, ← hS]
  simp only [Nat.add_sub_cancel] at hcu
  rw [sq]; omega

/-- Integer Dirichlet hyperbola identity, formerly a LEAF, PROVED by session S91, the first step of the classical proof of the
Voronoi formula cited on Halupczok page 337. For every natural N, the sum of d of n for n up to N
equals twice the sum over m up to the integer square root of N of N divided by m,
minus the square of that integer square root.
Proved by the exact finite lattice point count by the symmetry of the hyperbola. -/
theorem nat_hyperbola_identity :
    ∀ N : ℕ, (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) =
      2 * ∑ m ∈ Icc 1 (Nat.sqrt N), ((N / m : ℕ) : ℝ) - (Nat.sqrt N : ℝ) ^ 2 := by
  intro N
  have h := nat_key N
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

#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.floor_sqrt_eq
#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.hyperbola_identity_of_leaves
#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.nat_hyperbola_identity

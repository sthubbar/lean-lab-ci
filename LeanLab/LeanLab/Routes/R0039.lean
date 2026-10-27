import Mathlib

/-
# R-0039, T3 MOONSHOT: the polynomial method, Cauchy-Davenport and the Combinatorial
# Nullstellensatz, for N in P + P

Unit U-1353, PC run 20261021T0503Z-11296. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it. KNOWN mathematics in
substance: Alon 1999, Alon-Nathanson-Ruzsa 1996, Karasev-Petrov 2012, Lason 2010.

The route: reduce A = primes up to N modulo a prime m > N, where a congruence a + b = N mod m
with a, b ≤ N lifts to the equation a + b = N, `lift_eq`, and then show N ∈ A + A in ZMod m by
the polynomial method. With size only, the polynomial method gives Cauchy-Davenport and the
pigeonhole cover, `pigeon_cover`, which needs #A + #A > m. The primes never meet it,
`pigeon_never`, and no size-only statement can work, since a set of every size up to N / 3
misses N, `decoy_of_card`.
-/

namespace LeanLab.Routes.R0039

open Finset
open scoped Pointwise

/-- Pigeonhole cover: in a finite additive group, `#A + #B > |G|` forces `A + B = G`.
This is the case of the Combinatorial Nullstellensatz with `f = ∏_{c ≠ n} (x + y - c)`. -/
theorem pigeon_cover {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (h : Fintype.card G < #A + #B) (n : G) : n ∈ A + B := by
  by_contra hn
  have hdisj : Disjoint A (B.image (fun b => n - b)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hb
    exact hn (Finset.mem_add.mpr ⟨n - b, ha, b, hbB, by abel⟩)
  have hinj : #(B.image (fun b => n - b)) = #B :=
    Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy)
  have := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (A ∪ B.image (fun b => n - b))
  omega

/-- The lift: for `a, b ≤ N < m`, a congruence `a + b ≡ N mod m` is the equation `a + b = N`. -/
theorem lift_eq (a b N m : ℕ) (ha : a ≤ N) (hb : b ≤ N) (hm : N < m)
    (h : ((a + b : ℕ) : ZMod m) = (N : ZMod m)) : a + b = N := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hN : N % m = N := Nat.mod_eq_of_lt hm
  have hd := Nat.div_add_mod (a + b) m
  have hq : (a + b) / m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
  interval_cases hq' : (a + b) / m <;> omega

/-- The primes up to `N` number at most `(N + 1) / 2`: map `p ↦ (p - 1) / 2`. -/
theorem primes_card_le (N : ℕ) (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime ∧ p ≤ N) :
    #A ≤ (N + 1) / 2 := by
  have hmaps : ∀ p ∈ A, (fun p => (p - 1) / 2) p ∈ range ((N + 1) / 2) := by
    intro p hp
    obtain ⟨hpr, hpN⟩ := hA p hp
    have := hpr.two_le
    simp only [mem_range]; omega
  have hinj : Set.InjOn (fun p => (p - 1) / 2) A := by
    intro p hp q hq hpq
    obtain ⟨hp1, -⟩ := hA p hp
    obtain ⟨hq1, -⟩ := hA q hq
    simp only at hpq
    rcases hp1.eq_two_or_odd' with rfl | ⟨k, rfl⟩ <;>
      rcases hq1.eq_two_or_odd' with rfl | ⟨j, rfl⟩
    · rfl
    · have := hq1.two_le; omega
    · have := hp1.two_le; omega
    · omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- The pigeonhole hypothesis never holds for the primes at a lift modulus `m > N`. -/
theorem pigeon_never (N m : ℕ) (hm : N < m) (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime ∧ p ≤ N) :
    ¬ m < #A + #A := by
  have := primes_card_le N A hA
  omega

/-- Size barrier: for `3 ∣ N`, every size `k ≤ N / 3` is the size of a set in `[0, N]`
with `N ∉ D + D`, the class `1 mod 3`. So no statement using only `#A` decides `N ∈ A + A`
at sizes up to `N / 3`, which covers `π(N)` for `N ≥ 30`, by the numerics. -/
theorem decoy_of_card (N k : ℕ) (h3 : 3 ∣ N) (hk : k ≤ N / 3) :
    ∃ D ⊆ range (N + 1), #D = k ∧ ∀ a ∈ D, ∀ b ∈ D, a + b ≠ N := by
  set D0 := (range (N / 3)).image (fun i => 3 * i + 1) with hD0
  have hcard : #D0 = N / 3 :=
    (Finset.card_image_of_injective _ (fun x y hxy => by
      have h' : 3 * x + 1 = 3 * y + 1 := hxy
      omega)).trans
      (Finset.card_range _)
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq (hcard ▸ hk : k ≤ #D0)
  refine ⟨D, ?_, hDcard, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hDsub hx)
    simp only [mem_range] at hi ⊢; omega
  · intro a ha b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hDsub ha)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hDsub hb)
    obtain ⟨c, rfl⟩ := h3
    omega

/-- Cauchy-Davenport for the record, Mathlib's `ZMod.cauchy_davenport`: the most a
size-only polynomial argument gives in `ZMod m`. -/
theorem cd_size_only {m : ℕ} (hm : m.Prime) {s t : Finset (ZMod m)} (hs : s.Nonempty)
    (ht : t.Nonempty) : min m (#s + #t - 1) ≤ #(s + t) :=
  ZMod.cauchy_davenport hm hs ht

/-! Vacuity checks: the hypotheses are satisfiable. -/

example : (2 : ZMod 5) ∈ ({0, 1, 2} : Finset (ZMod 5)) + {0, 1, 2} :=
  pigeon_cover _ _ (by decide) 2

example : ∃ D ⊆ range 31, #D = 10 ∧ ∀ a ∈ D, ∀ b ∈ D, a + b ≠ 30 :=
  decoy_of_card 30 10 (by norm_num) (by norm_num)

example : (3 + 7 : ℕ) = 10 := lift_eq 3 7 10 11 (by norm_num) (by norm_num) (by norm_num) rfl

end LeanLab.Routes.R0039

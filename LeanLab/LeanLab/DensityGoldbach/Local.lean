/-
P0038 Shao 2012, local facts mod 15 and the link Proposition 1.4 to Corollary 1.5.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0081.
-/
import LeanLab.DensityGoldbach.Statements

open Finset

namespace LeanLab.DensityGoldbach

/-- Shao's sharpness residues `{1, 2, 4, 7, 13} mod 15`. -/
def S15 : Finset (ZMod 15) := {1, 2, 4, 7, 13}

lemma S15_sub_units : S15 ⊆ unitsMod 15 := by decide

lemma card_units15 : #(unitsMod 15) = 8 := by decide

lemma card_S15 : #S15 = 5 := by decide

/-- `5 = 5/8 · φ(15)`: the example sits exactly at density `5/8`. -/
lemma totient15 : Nat.totient 15 = 8 := by decide

/-- No three elements of `S15` sum to `14 mod 15`. -/
theorem S15_misses_14 : ∀ a ∈ S15, ∀ b ∈ S15, ∀ c ∈ S15, a + b + c ≠ 14 := by decide

/-- Lifted to integers: if `a, b, c` are each `≡ 1, 2, 4, 7, 13 mod 15`, then
`a + b + c ≢ 14 mod 15`. So `N ≡ 14 mod 15` is never a sum of three primes of Shao's set. -/
theorem shao_example (a b c : ℕ) (ha : (a : ZMod 15) ∈ S15) (hb : (b : ZMod 15) ∈ S15)
    (hc : (c : ZMod 15) ∈ S15) : (a + b + c) % 15 ≠ 14 := by
  intro h
  have : ((a + b + c : ℕ) : ZMod 15) = 14 := by
    rw [← ZMod.natCast_mod, h]; rfl
  push_cast at this
  exact S15_misses_14 _ ha _ hb _ hc this

/-- The set of naturals in Shao's residue classes misses every `N ≡ 14 mod 15`. -/
theorem shao_example_set (n : ℕ) (hn : n % 15 = 14) :
    ¬ IsSum3 {p | p.Prime ∧ (p : ZMod 15) ∈ S15} {p | p.Prime ∧ (p : ZMod 15) ∈ S15}
      {p | p.Prime ∧ (p : ZMod 15) ∈ S15} n := by
  rintro ⟨a, ha, b, hb, c, hc, rfl⟩
  exact shao_example a b c ha.2 hb.2 hc.2 hn

/-! ### Corollary 1.5 for `m = 15` by a disjoint certificate

For each `x mod 15` three triples of reduced residues summing to `x` whose underlying sets are
pairwise disjoint. Removing at most two of the eight reduced residues kills at most two. -/

/-- Certificate triples. -/
def t1 (x : ZMod 15) : ZMod 15 × ZMod 15 × ZMod 15 := (show Fin 15 → ZMod 15 × ZMod 15 × ZMod 15 from ![(1, 1, 13), (1, 1, 14), (1, 8, 8), (1, 1, 1), (1, 1, 2), (1, 2, 2), (1, 1, 4), (1, 2, 4), (1, 11, 11), (1, 1, 7), (1, 1, 8), (1, 2, 8), (1, 4, 7), (1, 1, 11), (1, 14, 14)]) x
/-- Certificate triples. -/
def t2 (x : ZMod 15) : ZMod 15 × ZMod 15 × ZMod 15 := (show Fin 15 → ZMod 15 × ZMod 15 × ZMod 15 from ![(2, 2, 11), (2, 7, 7), (2, 2, 13), (2, 2, 14), (4, 4, 11), (4, 8, 8), (2, 2, 2), (7, 7, 8), (2, 2, 4), (2, 8, 14), (2, 4, 4), (4, 11, 11), (2, 2, 8), (2, 13, 13), (2, 4, 8)]) x
/-- Certificate triples. -/
def t3 (x : ZMod 15) : ZMod 15 × ZMod 15 × ZMod 15 := (show Fin 15 → ZMod 15 × ZMod 15 × ZMod 15 from ![(4, 4, 7), (4, 4, 8), (4, 14, 14), (4, 7, 7), (7, 13, 14), (7, 14, 14), (7, 7, 7), (11, 13, 13), (7, 8, 8), (13, 13, 13), (7, 7, 11), (13, 14, 14), (14, 14, 14), (7, 7, 14), (7, 11, 11)]) x

/-- The underlying set of a triple. -/
def tset (t : ZMod 15 × ZMod 15 × ZMod 15) : Finset (ZMod 15) := {t.1, t.2.1, t.2.2}

lemma cert_sum : ∀ x : ZMod 15, (t1 x).1 + (t1 x).2.1 + (t1 x).2.2 = x ∧
    (t2 x).1 + (t2 x).2.1 + (t2 x).2.2 = x ∧
    (t3 x).1 + (t3 x).2.1 + (t3 x).2.2 = x := by decide

lemma cert_units : ∀ x : ZMod 15, tset (t1 x) ⊆ unitsMod 15 ∧ tset (t2 x) ⊆ unitsMod 15 ∧
    tset (t3 x) ⊆ unitsMod 15 := by decide

lemma cert_disj : ∀ x : ZMod 15, Disjoint (tset (t1 x)) (tset (t2 x)) ∧
    Disjoint (tset (t1 x)) (tset (t3 x)) ∧ Disjoint (tset (t2 x)) (tset (t3 x)) := by decide

/-- If at most two elements of `U` are missing from `A`, one of three pairwise disjoint
subsets of `U` lies inside `A`. -/
lemma one_survives {α : Type*} [DecidableEq α] {A U S₁ S₂ S₃ : Finset α} (hAU : A ⊆ U)
    (hc : #U ≤ #A + 2) (h1 : S₁ ⊆ U) (h2 : S₂ ⊆ U) (h3 : S₃ ⊆ U)
    (d12 : Disjoint S₁ S₂) (d13 : Disjoint S₁ S₃) (d23 : Disjoint S₂ S₃) :
    S₁ ⊆ A ∨ S₂ ⊆ A ∨ S₃ ⊆ A := by
  by_contra hn
  simp only [not_or, not_subset] at hn
  obtain ⟨⟨y₁, hy₁, hA₁⟩, ⟨y₂, hy₂, hA₂⟩, ⟨y₃, hy₃, hA₃⟩⟩ := hn
  have n12 : y₁ ≠ y₂ := fun h => Finset.disjoint_left.1 d12 hy₁ (h ▸ hy₂)
  have n13 : y₁ ≠ y₃ := fun h => Finset.disjoint_left.1 d13 hy₁ (h ▸ hy₃)
  have n23 : y₂ ≠ y₃ := fun h => Finset.disjoint_left.1 d23 hy₂ (h ▸ hy₃)
  have hsub : ({y₁, y₂, y₃} : Finset α) ⊆ U \ A := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_sdiff.2 ⟨h1 hy₁, hA₁⟩
    · exact mem_sdiff.2 ⟨h2 hy₂, hA₂⟩
    · exact mem_sdiff.2 ⟨h3 hy₃, hA₃⟩
  have hcard : #({y₁, y₂, y₃} : Finset α) = 3 := by
    rw [card_insert_of_notMem (by simp [n12, n13]), card_pair n23]
  have := card_le_card hsub
  rw [card_sdiff_of_subset hAU, hcard] at this
  omega

lemma triple_of_sub {A : Finset (ZMod 15)} {t : ZMod 15 × ZMod 15 × ZMod 15}
    (h : tset t ⊆ A) : t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A :=
  ⟨h (by simp [tset]), h (by simp [tset]), h (by simp [tset])⟩

/-- Corollary 1.5 for `m = 15`: a set of at least 6 of the 8 reduced residues mod 15 has
`A + A + A = Z/15`. -/
theorem cor15_fifteen : Cor15 15 := by
  intro A hA hcard x
  rw [totient15] at hcard
  have h6 : 6 ≤ #A := by
    have : (5 : ℝ) < #A := by linarith
    exact_mod_cast this
  have hc : #(unitsMod 15) ≤ #A + 2 := by rw [card_units15]; omega
  obtain ⟨s1, s2, s3⟩ := cert_sum x
  obtain ⟨u1, u2, u3⟩ := cert_units x
  obtain ⟨d12, d13, d23⟩ := cert_disj x
  rcases one_survives hA hc u1 u2 u3 d12 d13 d23 with h | h | h
  · obtain ⟨a, b, c⟩ := triple_of_sub h; exact ⟨_, a, _, b, _, c, s1⟩
  · obtain ⟨a, b, c⟩ := triple_of_sub h; exact ⟨_, a, _, b, _, c, s2⟩
  · obtain ⟨a, b, c⟩ := triple_of_sub h; exact ⟨_, a, _, b, _, c, s3⟩

/-- **Proposition 1.4 implies Corollary 1.5**, with `f` the indicator of `A`. -/
theorem cor15_of_prop14 (m : ℕ) [NeZero m] (h : Prop14 m) : Cor15 m := by
  intro A hA hcard x
  let f : ZMod m → ℝ := fun a => if a ∈ A then 1 else 0
  have hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1 := fun a => by
    by_cases ha : a ∈ A <;> simp [f, ha]
  have hsum : ∑ a ∈ unitsMod m, f a = #A := by
    simp only [f]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext a; simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  obtain ⟨a₁, -, a₂, -, a₃, -, hx, hpos, -⟩ := h f hf (by rw [hsum]; exact hcard) x
  have mem : ∀ a, 0 < f a → a ∈ A := fun a ha => by
    by_contra hn; simp [f, hn] at ha
  have h1 : 0 ≤ f a₁ := (hf a₁).1
  have h2 : 0 ≤ f a₂ := (hf a₂).1
  have h3 : 0 ≤ f a₃ := (hf a₃).1
  have p1 : 0 < f a₁ := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  have p2 : 0 < f a₂ := by
    rcases h2.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  have p3 : 0 < f a₃ := by
    rcases h3.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  exact ⟨a₁, mem _ p1, a₂, mem _ p2, a₃, mem _ p3, hx.symm⟩

end LeanLab.DensityGoldbach

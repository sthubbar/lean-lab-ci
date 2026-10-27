/-
P0085 A. Alsetri 2025, Density ternary Goldbach for primes in a fixed residue class,
arXiv 2505.09648 v2, read 2026-10-17.
Theorem 1.1: A ⊆ primes ≡ 1 mod 3 with relative lower density > 1/2 in that class; then
A + A + A contains every sufficiently large odd n with n ≡ 0 mod 3. 1/2 is best possible.
Theorem 1.2, local: m odd squarefree, 3 | m, f : Z_m^* → [0,1] supported on classes ≡ 1 mod 3,
Σ f > φ(m)/4; then every x ≡ 0 mod 3 is a1 + a2 + a3 with f(ai) > 0 and Σ f(ai) > 3/2.
Sharpness: A = {1, 7} ⊆ Z_15^*, 12 mod 15 ∉ A + A + A, Σ f = φ(15)/4.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0203Z-18204, unit U-0162.
Checked only by the Lean kernel. Ternary Goldbach is a theorem; binary Goldbach is OPEN.
-/
import LeanLab.DensityGoldbach.Statements

open Finset

namespace LeanLab.DensityGoldbach

/-- P0085 Theorem 1.1. Since `A` lies in the class `1 mod 3`, `lowerDensityRes A 1 3` is the
paper's `liminf |A ∩ [1,N]| / |P_{1,3} ∩ [1,N]|`. -/
def Alsetri11 : Prop := ∀ A : Set ℕ, A ⊆ P → (∀ a ∈ A, a % 3 = 1) →
  1 / 2 < lowerDensityRes A 1 3 →
  ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → Odd n → n % 3 = 0 → IsSum3 A A A n

theorem alsetri_1_1 : Alsetri11 := by sorry

/-- The conclusion of P0085 Theorem 1.2 for `f` and modulus `m`. -/
def AlsetriConcl (m : ℕ) [NeZero m] (f : ZMod m → ℝ) : Prop :=
  ∀ x : ZMod m, x.val % 3 = 0 → ∃ a₁ ∈ unitsMod m, ∃ a₂ ∈ unitsMod m, ∃ a₃ ∈ unitsMod m,
    x = a₁ + a₂ + a₃ ∧ 0 < f a₁ ∧ 0 < f a₂ ∧ 0 < f a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃

/-- P0085 Theorem 1.2 at modulus `m`. Supported on the classes `≡ 1 mod 3` is written as
`f a = 0` whenever `a.val % 3 ≠ 1`; for `3 ∣ m` this is the class of `a` mod 3. -/
def Alsetri12 (m : ℕ) [NeZero m] : Prop := ∀ f : ZMod m → ℝ,
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) → (∀ a, a.val % 3 ≠ 1 → f a = 0) →
  (m.totient : ℝ) / 4 < ∑ a ∈ unitsMod m, f a → AlsetriConcl m f

theorem alsetri_1_2 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) (h3 : 3 ∣ m) :
    Alsetri12 m := by sorry

/-! ### Proved, zero sorry -/

lemma units15_eq : unitsMod 15 = {1, 2, 4, 7, 8, 11, 13, 14} := by decide

/-- The sharpness example: `A = {1, 7}` misses `12 mod 15`. -/
theorem alsetri_sharp_set : ∀ a ∈ ({1, 7} : Finset (ZMod 15)), ∀ b ∈ ({1, 7} : Finset (ZMod 15)),
    ∀ c ∈ ({1, 7} : Finset (ZMod 15)), a + b + c ≠ 12 := by decide

/-- The indicator of `{1, 7}`. -/
noncomputable def fSharp (a : ZMod 15) : ℝ := if a = 1 ∨ a = 7 then 1 else 0

lemma fSharp_sum : ∑ a ∈ unitsMod 15, fSharp a = 2 := by
  have e : ∀ a : ZMod 15, fSharp a = if a = 1 ∨ a = 7 then 1 else 0 := fun _ => rfl
  rw [units15_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [e]
  rw [if_pos (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  norm_num

/-- The threshold `φ(m)/4` cannot be lowered to `≥`: at `m = 15` the indicator of `{1, 7}`
has `Σ f = φ(15)/4 = 2`, is supported on classes `≡ 1 mod 3`, and fails the conclusion. -/
theorem alsetri_sharp :
    (∀ a, 0 ≤ fSharp a ∧ fSharp a ≤ 1) ∧ (∀ a : ZMod 15, a.val % 3 ≠ 1 → fSharp a = 0) ∧
      ((Nat.totient 15 : ℝ) / 4 = ∑ a ∈ unitsMod 15, fSharp a) ∧ ¬ AlsetriConcl 15 fSharp := by
  refine ⟨fun a => ?_, fun a ha => ?_, ?_, ?_⟩
  · unfold fSharp; split_ifs <;> norm_num
  · unfold fSharp
    rw [if_neg]
    rintro (rfl | rfl) <;> exact ha (by decide)
  · rw [fSharp_sum, show Nat.totient 15 = 8 by decide]; norm_num
  · intro h
    obtain ⟨a, -, b, -, c, -, hx, ha, hb, hc, -⟩ := h 12 (by decide)
    have mem : ∀ y : ZMod 15, 0 < fSharp y → y ∈ ({1, 7} : Finset (ZMod 15)) := by
      intro y hy
      unfold fSharp at hy
      split_ifs at hy with h1
      · rcases h1 with rfl | rfl <;> decide
      · exact absurd hy (lt_irrefl 0)
    exact alsetri_sharp_set a (mem a ha) b (mem b hb) c (mem c hc) hx.symm

/-- Lifted to integers: primes `≡ 1, 7 mod 15` are all `≡ 1 mod 3`, and no three of them sum
to any `n ≡ 12 mod 15`, for example the odd `n = 27, 57, 87, …`. Their relative density in
the primes `≡ 1 mod 3` is `1/2` by Dirichlet equidistribution, not proved here. -/
theorem alsetri_example_set (n : ℕ) (hn : n % 15 = 12) :
    ¬ IsSum3 {p | p.Prime ∧ (p % 15 = 1 ∨ p % 15 = 7)} {p | p.Prime ∧ (p % 15 = 1 ∨ p % 15 = 7)}
      {p | p.Prime ∧ (p % 15 = 1 ∨ p % 15 = 7)} n := by
  rintro ⟨a, ha, b, hb, c, hc, rfl⟩
  rcases ha.2 with h1 | h1 <;> rcases hb.2 with h2 | h2 <;> rcases hc.2 with h3 | h3 <;> omega

theorem alsetri_example_mod3 (p : ℕ) (h : p % 15 = 1 ∨ p % 15 = 7) : p % 3 = 1 := by omega

/-- Theorem 1.2 at `m = 3`: the only unit `≡ 1 mod 3` is `1`, and `0 = 1 + 1 + 1`. -/
theorem alsetri12_three : Alsetri12 3 := by
  intro f hf hsupp hsum x hx
  have hu : unitsMod 3 = {1, 2} := by decide
  have h2 : f 2 = 0 := hsupp 2 (by decide)
  rw [hu, Finset.sum_pair (by decide), h2, show Nat.totient 3 = 2 by decide] at hsum
  have hx0 : x = 0 := by
    fin_cases x
    · rfl
    · exact absurd hx (by decide)
    · exact absurd hx (by decide)
  subst hx0
  refine ⟨1, by rw [hu]; simp, 1, by rw [hu]; simp, 1, by rw [hu]; simp, by decide,
    by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 2000000

/-! ### Theorem 1.2 at `m = 15`, proved outright

The units `≡ 1 mod 3` are `1, 4, 7, 13`; write `a, b, c, d` for `f` there. For each target
`x ∈ {0, 3, 6, 9, 12}` there are four triples from `{1, 4, 7, 13}` summing to `x`. -/

lemma real15_0 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hd1 : d ≤ 1) (hs : 2 < a + b + c + d) :
    (0 < a ∧ 0 < a ∧ 0 < d ∧ 3 / 2 < a + a + d) ∨
      (0 < a ∧ 0 < c ∧ 0 < c ∧ 3 / 2 < a + c + c) ∨
      (0 < b ∧ 0 < b ∧ 0 < c ∧ 3 / 2 < b + b + c) ∨
      (0 < b ∧ 0 < d ∧ 0 < d ∧ 3 / 2 < b + d + d) := by
  rcases ha.lt_or_eq with h1 | h1 <;> rcases hb.lt_or_eq with h2 | h2 <;>
  rcases hc.lt_or_eq with h3 | h3 <;> rcases hd.lt_or_eq with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | (rcases lt_or_ge (3 / 2) (a + a + d) with s1 | s1 <;>
        rcases lt_or_ge (3 / 2) (a + c + c) with s2 | s2 <;>
        rcases lt_or_ge (3 / 2) (b + b + c) with s3 | s3 <;>
        rcases lt_or_ge (3 / 2) (b + d + d) with s4 | s4 <;>
        first
        | exact Or.inl ⟨by linarith, by linarith, by linarith, s1⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s3⟩))
        | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, s4⟩))
        | (exfalso; linarith))

lemma real15_3 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hd1 : d ≤ 1) (hs : 2 < a + b + c + d) :
    (0 < a ∧ 0 < a ∧ 0 < a ∧ 3 / 2 < a + a + a) ∨
      (0 < a ∧ 0 < b ∧ 0 < d ∧ 3 / 2 < a + b + d) ∨
      (0 < b ∧ 0 < c ∧ 0 < c ∧ 3 / 2 < b + c + c) ∨
      (0 < c ∧ 0 < d ∧ 0 < d ∧ 3 / 2 < c + d + d) := by
  rcases ha.lt_or_eq with h1 | h1 <;> rcases hb.lt_or_eq with h2 | h2 <;>
  rcases hc.lt_or_eq with h3 | h3 <;> rcases hd.lt_or_eq with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | (rcases lt_or_ge (3 / 2) (a + a + a) with s1 | s1 <;>
        rcases lt_or_ge (3 / 2) (a + b + d) with s2 | s2 <;>
        rcases lt_or_ge (3 / 2) (b + c + c) with s3 | s3 <;>
        rcases lt_or_ge (3 / 2) (c + d + d) with s4 | s4 <;>
        first
        | exact Or.inl ⟨by linarith, by linarith, by linarith, s1⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s3⟩))
        | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, s4⟩))
        | (exfalso; linarith))

lemma real15_6 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hd1 : d ≤ 1) (hs : 2 < a + b + c + d) :
    (0 < a ∧ 0 < a ∧ 0 < b ∧ 3 / 2 < a + a + b) ∨
      (0 < a ∧ 0 < c ∧ 0 < d ∧ 3 / 2 < a + c + d) ∨
      (0 < b ∧ 0 < b ∧ 0 < d ∧ 3 / 2 < b + b + d) ∨
      (0 < c ∧ 0 < c ∧ 0 < c ∧ 3 / 2 < c + c + c) := by
  rcases ha.lt_or_eq with h1 | h1 <;> rcases hb.lt_or_eq with h2 | h2 <;>
  rcases hc.lt_or_eq with h3 | h3 <;> rcases hd.lt_or_eq with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | (rcases lt_or_ge (3 / 2) (a + a + b) with s1 | s1 <;>
        rcases lt_or_ge (3 / 2) (a + c + d) with s2 | s2 <;>
        rcases lt_or_ge (3 / 2) (b + b + d) with s3 | s3 <;>
        rcases lt_or_ge (3 / 2) (c + c + c) with s4 | s4 <;>
        first
        | exact Or.inl ⟨by linarith, by linarith, by linarith, s1⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s3⟩))
        | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, s4⟩))
        | (exfalso; linarith))

lemma real15_9 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hd1 : d ≤ 1) (hs : 2 < a + b + c + d) :
    (0 < a ∧ 0 < a ∧ 0 < c ∧ 3 / 2 < a + a + c) ∨
      (0 < a ∧ 0 < b ∧ 0 < b ∧ 3 / 2 < a + b + b) ∨
      (0 < b ∧ 0 < c ∧ 0 < d ∧ 3 / 2 < b + c + d) ∨
      (0 < d ∧ 0 < d ∧ 0 < d ∧ 3 / 2 < d + d + d) := by
  rcases ha.lt_or_eq with h1 | h1 <;> rcases hb.lt_or_eq with h2 | h2 <;>
  rcases hc.lt_or_eq with h3 | h3 <;> rcases hd.lt_or_eq with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | (rcases lt_or_ge (3 / 2) (a + a + c) with s1 | s1 <;>
        rcases lt_or_ge (3 / 2) (a + b + b) with s2 | s2 <;>
        rcases lt_or_ge (3 / 2) (b + c + d) with s3 | s3 <;>
        rcases lt_or_ge (3 / 2) (d + d + d) with s4 | s4 <;>
        first
        | exact Or.inl ⟨by linarith, by linarith, by linarith, s1⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s3⟩))
        | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, s4⟩))
        | (exfalso; linarith))

lemma real15_12 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) (hd1 : d ≤ 1) (hs : 2 < a + b + c + d) :
    (0 < a ∧ 0 < b ∧ 0 < c ∧ 3 / 2 < a + b + c) ∨
      (0 < a ∧ 0 < d ∧ 0 < d ∧ 3 / 2 < a + d + d) ∨
      (0 < b ∧ 0 < b ∧ 0 < b ∧ 3 / 2 < b + b + b) ∨
      (0 < c ∧ 0 < c ∧ 0 < d ∧ 3 / 2 < c + c + d) := by
  rcases ha.lt_or_eq with h1 | h1 <;> rcases hb.lt_or_eq with h2 | h2 <;>
  rcases hc.lt_or_eq with h3 | h3 <;> rcases hd.lt_or_eq with h4 | h4
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩))
    | (rcases lt_or_ge (3 / 2) (a + b + c) with s1 | s1 <;>
        rcases lt_or_ge (3 / 2) (a + d + d) with s2 | s2 <;>
        rcases lt_or_ge (3 / 2) (b + b + b) with s3 | s3 <;>
        rcases lt_or_ge (3 / 2) (c + c + d) with s4 | s4 <;>
        first
        | exact Or.inl ⟨by linarith, by linarith, by linarith, s1⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s2⟩)
        | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, s3⟩))
        | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, s4⟩))
        | (exfalso; linarith))

theorem alsetri12_fifteen : Alsetri12 15 := by
  intro f hf hsupp hsum x hx
  have z2 : f 2 = 0 := hsupp 2 (by decide)
  have z8 : f 8 = 0 := hsupp 8 (by decide)
  have z11 : f 11 = 0 := hsupp 11 (by decide)
  have z14 : f 14 = 0 := hsupp 14 (by decide)
  rw [units15_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    z2, z8, z11, z14, show Nat.totient 15 = 8 by decide] at hsum
  have hs : 2 < f 1 + f 4 + f 7 + f 13 := by push_cast at hsum; linarith
  have U : ∀ y : ZMod 15, y ∈ ({1, 4, 7, 13} : Finset (ZMod 15)) → y ∈ unitsMod 15 := by
    rw [units15_eq]; decide
  have u1 := U 1 (by decide)
  have u4 := U 4 (by decide)
  have u7 := U 7 (by decide)
  have u13 := U 13 (by decide)
  have b := fun y => hf y
  fin_cases x
  · rcases real15_0 (f 1) (f 4) (f 7) (f 13) (b 1).1 (b 4).1 (b 7).1 (b 13).1 (b 1).2 (b 4).2
      (b 7).2 (b 13).2 hs with h | h | h | h
    · exact ⟨1, u1, 1, u1, 13, u13, by rfl, h⟩
    · exact ⟨1, u1, 7, u7, 7, u7, by rfl, h⟩
    · exact ⟨4, u4, 4, u4, 7, u7, by rfl, h⟩
    · exact ⟨4, u4, 13, u13, 13, u13, by rfl, h⟩
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · rcases real15_3 (f 1) (f 4) (f 7) (f 13) (b 1).1 (b 4).1 (b 7).1 (b 13).1 (b 1).2 (b 4).2
      (b 7).2 (b 13).2 hs with h | h | h | h
    · exact ⟨1, u1, 1, u1, 1, u1, by rfl, h⟩
    · exact ⟨1, u1, 4, u4, 13, u13, by rfl, h⟩
    · exact ⟨4, u4, 7, u7, 7, u7, by rfl, h⟩
    · exact ⟨7, u7, 13, u13, 13, u13, by rfl, h⟩
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · rcases real15_6 (f 1) (f 4) (f 7) (f 13) (b 1).1 (b 4).1 (b 7).1 (b 13).1 (b 1).2 (b 4).2
      (b 7).2 (b 13).2 hs with h | h | h | h
    · exact ⟨1, u1, 1, u1, 4, u4, by rfl, h⟩
    · exact ⟨1, u1, 7, u7, 13, u13, by rfl, h⟩
    · exact ⟨4, u4, 4, u4, 13, u13, by rfl, h⟩
    · exact ⟨7, u7, 7, u7, 7, u7, by rfl, h⟩
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · rcases real15_9 (f 1) (f 4) (f 7) (f 13) (b 1).1 (b 4).1 (b 7).1 (b 13).1 (b 1).2 (b 4).2
      (b 7).2 (b 13).2 hs with h | h | h | h
    · exact ⟨1, u1, 1, u1, 7, u7, by rfl, h⟩
    · exact ⟨1, u1, 4, u4, 4, u4, by rfl, h⟩
    · exact ⟨4, u4, 7, u7, 13, u13, by rfl, h⟩
    · exact ⟨13, u13, 13, u13, 13, u13, by rfl, h⟩
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · rcases real15_12 (f 1) (f 4) (f 7) (f 13) (b 1).1 (b 4).1 (b 7).1 (b 13).1 (b 1).2 (b 4).2
      (b 7).2 (b 13).2 hs with h | h | h | h
    · exact ⟨1, u1, 4, u4, 7, u7, by rfl, h⟩
    · exact ⟨1, u1, 13, u13, 13, u13, by rfl, h⟩
    · exact ⟨4, u4, 4, u4, 4, u4, by rfl, h⟩
    · exact ⟨7, u7, 7, u7, 13, u13, by rfl, h⟩
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)

end LeanLab.DensityGoldbach

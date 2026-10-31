/-
P0086 D. Basak, R. N. Bhat, A. Dong, A. Zaharescu, "Almost all primes are not needed in
ternary Goldbach", arXiv 2409.08968 (v1, 13 Sep 2024).
Theorem 1.1 and Lemma 3.1 are cited Prop definitions. Lemma 4.1 has a proof.
Asymptotic notation: the limit in Theorem 1.1 (a) is a `Filter.Tendsto` over real `X → ∞`;
"there exists `u_A`" in Lemma 3.1 is an explicit existential, ineffective, real threshold.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
Cited results are Prop definitions. They are not asserted as theorems in this file.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary.Statements

open Finset Filter Topology
open scoped Classical

namespace LeanLab.SparseTernary

/-! ### Basic notions -/

/-- `m = p₁ + p₂ + p₃` with all three `pᵢ ∈ P`. -/
def IsSum3In (P : Set ℕ) (m : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁ ∈ P ∧ p₂ ∈ P ∧ p₃ ∈ P ∧ p₁ + p₂ + p₃ = m

/-- `#{p ∈ P : p ≤ X}` for real `X`. For `X ≥ 0`, `p ≤ X ↔ p ≤ ⌊X⌋₊`. -/
noncomputable def countLe (P : Set ℕ) (X : ℝ) : ℕ := #{p ∈ range (⌊X⌋₊ + 1) | p ∈ P}

/-- `#{p ∈ P : p ≤ x}` for natural `x`. -/
noncomputable def countUpTo (P : Set ℕ) (x : ℕ) : ℕ := #{p ∈ range (x + 1) | p ∈ P}

/-- Condition (a) of Theorem 1.1 for one exponent `B`:
`(log X)^B · #{p ∈ P : p ≤ X} / X → 0` as real `X → ∞`. -/
def SparseB (P : Set ℕ) (B : ℕ) : Prop :=
  Tendsto (fun X : ℝ => Real.log X ^ B * (countLe P X : ℝ) / X) atTop (𝓝 0)

/-! ### Theorem 1.1 -/

/-- Theorem 1.1: there is a set `P` of primes such that (a) for every positive integer `B`,
`lim_{X→∞} (log X)^B · #{p ∈ P : p ≤ X} / X = 0`, and (b) every odd `m ≥ 7` is a sum of
three primes in `P`. -/
def Theorem11 : Prop :=
  ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ B : ℕ, 0 < B → SparseB P B) ∧
    ∀ m : ℕ, Odd m → 7 ≤ m → IsSum3In P m

/- The cited assertion is represented by `Theorem11` above.
The former unproved declaration `theorem_1_1` had no consumers. -/

/-! ### Lemma 3.1 -/

/-- Lemma 3.1: fix a positive integer `A`. There is `u_A > 0` such that for all real `u ≥ u_A`:
(a) there is a set `P_u` of primes in `[u, 2u]` with `#P_u ≤ u / (log u)^A`, and
(b) every odd `m ∈ [4u, 5u]` is `p₁ + p₂ + p₃` with `pᵢ ∈ P_u`.
`P_u` is finite, being inside `[u, 2u]`; it is chosen after `u`, before `m`. -/
def Lemma31 (A : ℕ) : Prop :=
  ∃ uA : ℝ, 0 < uA ∧ ∀ u : ℝ, uA ≤ u → ∃ Pu : Finset ℕ,
    (∀ p ∈ Pu, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ 2 * u) ∧
    (Pu.card : ℝ) ≤ u / Real.log u ^ A ∧
    ∀ m : ℕ, Odd m → 4 * u ≤ m → (m : ℝ) ≤ 5 * u → IsSum3In (↑Pu : Set ℕ) m

/- The cited assertion is represented by `Lemma31 A` above.
The former unproved declaration `lemma_3_1` had no consumers. -/

/-! ### Lemma 4.1, proved -/

/-- The paper's `a_j = ⌈p_j^{1/3}⌉ + 1`, (4.4). -/
noncomputable def aOf (p : ℕ) : ℕ := ⌈(p : ℝ) ^ ((1 : ℝ) / 3)⌉₊ + 1

/-- `R_j = {1, …, a} ∪ {a, 2a, …, a²} ∪ {a², 2a², …, a³}`, (4.5) and (4.6). -/
def Rset (a : ℕ) : Finset ℕ :=
  Icc 1 a ∪ (Icc 1 a).image (· * a) ∪ (Icc 1 a).image (· * a ^ 2)

/-- Core of Lemma 4.1: if `q ≤ a³` then every `n` is congruent mod `q` to `r + w₁a + w₂a²`
with `1 ≤ r, w₁, w₂ ≤ a`. Such sums fill the `a³` consecutive integers
`[1 + a + a², a + a² + a³]`, a mixed radix argument, shorter than the paper's case split. -/
theorem three_digits {q a : ℕ} (hq : 0 < q) (hqa : q ≤ a ^ 3) (n : ℕ) :
    ∃ r ∈ Icc 1 a, ∃ w₁ ∈ Icc 1 a, ∃ w₂ ∈ Icc 1 a, r + w₁ * a + w₂ * a ^ 2 ≡ n [MOD q] := by
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hqa; omega
    · exact h
  set s := 1 + a + a ^ 2 with hs
  set M := (n + q * s - s) % q with hM
  have hMq : M < q := Nat.mod_lt _ hq
  have hMa : M < a * a * a := by
    have : a ^ 3 = a * a * a := by ring
    omega
  refine ⟨M % a + 1, ?_, M / a % a + 1, ?_, M / a / a + 1, ?_, ?_⟩
  · have := Nat.mod_lt M ha; simp only [mem_Icc]; omega
  · have := Nat.mod_lt (M / a) ha; simp only [mem_Icc]; omega
  · have : M / a / a < a := by
      rw [Nat.div_lt_iff_lt_mul ha, Nat.div_lt_iff_lt_mul ha]; exact hMa
    simp only [mem_Icc]; exact ⟨Nat.le_add_left _ _, this⟩
  · have e1 := Nat.mod_add_div M a
    have e2 := Nat.mod_add_div (M / a) a
    have hsum : M % a + 1 + (M / a % a + 1) * a + (M / a / a + 1) * a ^ 2 = s + M := by
      have : M = M % a + a * (M / a % a + a * (M / a / a)) := by
        conv_lhs => rw [← e1, ← e2]
      rw [hs]; nth_rewrite 4 [this]; ring
    rw [hsum]
    have hqs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    have h1 : M ≡ n + q * s - s [MOD q] := Nat.mod_modEq _ _
    have h2 : s + M ≡ s + (n + q * s - s) [MOD q] := Nat.ModEq.add_left s h1
    have h3 : s + (n + q * s - s) = n + q * s := by omega
    rw [h3] at h2
    refine h2.trans ?_
    show (n + q * s) % q = n % q
    simp [Nat.add_mul_mod_self_left]

theorem le_aOf_cube (p : ℕ) : p ≤ aOf p ^ 3 := by
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcube : ((p : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hc : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (aOf p : ℝ) := by
    unfold aOf; push_cast
    linarith [Nat.le_ceil ((p : ℝ) ^ ((1 : ℝ) / 3))]
  have : (p : ℝ) ≤ (aOf p : ℝ) ^ 3 := by
    rw [← hcube]; exact pow_le_pow_left₀ hx hc 3
  exact_mod_cast this

/-- Lemma 4.1: for every `n` and prime `p`, there are `r₁, r₂, r₃ ∈ R_p` with
`n ≡ r₁ + r₂ + r₃ (mod p)`, where `R_p` is built from `a = ⌈p^{1/3}⌉ + 1`. Proved for every
positive modulus `p`, prime or not. -/
theorem lemma_4_1 (p : ℕ) (hp : 0 < p) (n : ℕ) :
    ∃ r₁ ∈ Rset (aOf p), ∃ r₂ ∈ Rset (aOf p), ∃ r₃ ∈ Rset (aOf p), n ≡ r₁ + r₂ + r₃ [MOD p] := by
  obtain ⟨r, hr, w₁, hw₁, w₂, hw₂, h⟩ := three_digits hp (le_aOf_cube p) n
  refine ⟨r, ?_, w₁ * aOf p, ?_, w₂ * aOf p ^ 2, ?_, h.symm⟩
  · unfold Rset; simp only [mem_union]; exact Or.inl (Or.inl hr)
  · unfold Rset; simp only [mem_union, mem_image]; exact Or.inl (Or.inr ⟨w₁, hw₁, rfl⟩)
  · unfold Rset; simp only [mem_union, mem_image]; exact Or.inr ⟨w₂, hw₂, rfl⟩

/-! ### Links, zero sorry -/

theorem isSum3In_mono {P Q : Set ℕ} (h : P ⊆ Q) {m : ℕ} (hm : IsSum3In P m) : IsSum3In Q m := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hm
  exact ⟨a, b, c, h ha, h hb, h hc, e⟩

theorem isTernarySum_of_isSum3In {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) {m : ℕ}
    (h : IsSum3In P m) : IsTernarySum m := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := h
  exact ⟨a, b, c, hP a ha, hP b hb, hP c hc, e⟩

/-- Theorem 1.1 implies the ternary Goldbach theorem. -/
theorem ternaryGoldbach_of_theorem11 (h : Theorem11) : TernaryGoldbach := by
  obtain ⟨P, hP, -, hb⟩ := h
  exact fun m ho h7 => isTernarySum_of_isSum3In hP (hb m ho h7)

/-- Theorem 1.1 implies the lab's `TernaryAbove C` for every `C ≥ 7`. -/
theorem ternaryAbove_of_theorem11 (h : Theorem11) (C : ℝ) (hC : 7 ≤ C) :
    LeanLab.Ternary.TernaryAbove C :=
  LeanLab.Ternary.ternaryAbove_of_ternaryGoldbach (ternaryGoldbach_of_theorem11 h) C hC

/-- Lemma 3.1 for one `A` already gives Vinogradov's theorem in the lab's form: odd `m ≥ 4u_A`
lies in `[4u, 5u]` for `u = m/4`. -/
theorem ternaryAbove_of_lemma31 {A : ℕ} (h : Lemma31 A) : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := by
  obtain ⟨uA, -, hu⟩ := h
  refine ⟨4 * uA, fun m ho hm => ?_⟩
  obtain ⟨Pu, hPu, -, hb⟩ := hu (m / 4) (by linarith)
  have hs := hb m ho (by linarith) (by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  exact isTernarySum_of_isSum3In (fun p hp => (hPu p hp).1) hs

/-- Lemma 3.1 is monotone in `A`: a larger `A` gives a smaller set. -/
theorem lemma31_mono {A A' : ℕ} (hAA : A' ≤ A) (h : Lemma31 A) : Lemma31 A' := by
  obtain ⟨uA, huA, hu⟩ := h
  refine ⟨max uA 3, by positivity, fun u hu' => ?_⟩
  obtain ⟨Pu, h1, h2, h3⟩ := hu u (le_trans (le_max_left _ _) hu')
  refine ⟨Pu, h1, le_trans h2 ?_, h3⟩
  have hu3 : 3 ≤ u := le_trans (le_max_right _ _) hu'
  have hlog : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : Real.log u ^ A' ≤ Real.log u ^ A := pow_le_pow_right₀ hlog hAA
  have hpos : 0 < Real.log u ^ A' := by positivity
  exact div_le_div_of_nonneg_left (by linarith) hpos hpow

/-- Condition (a) of Theorem 1.1 is monotone in `B`: the `B` statement gives every
smaller exponent. -/
theorem sparseB_mono {P : Set ℕ} {B B' : ℕ} (hBB : B' ≤ B) (h : SparseB P B) : SparseB P B' := by
  unfold SparseB at *
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
    have hlog : 1 ≤ Real.log X := by rwa [Real.le_log_iff_exp_le hX0]
    have hpow : Real.log X ^ B' ≤ Real.log X ^ B := pow_le_pow_right₀ hlog hBB
    have hc : (0 : ℝ) ≤ countLe P X := Nat.cast_nonneg _
    gcongr

/-- "Almost all primes are not needed": the `B = 1` case says
`#{p ∈ P : p ≤ X} = o(X / log X)`, which is `o(π(X))` by Chebyshev's lower bound. -/
theorem sparse_one_of_theorem11 (h : Theorem11) :
    ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ SparseB P 1 ∧ SparseB P 0 ∧ TernaryGoldbach := by
  obtain ⟨P, hP, ha, hb⟩ := h
  exact ⟨P, hP, ha 1 one_pos, sparseB_mono (Nat.zero_le 1) (ha 1 one_pos),
    fun m ho h7 => isTernarySum_of_isSum3In hP (hb m ho h7)⟩

/-! ### A ternary basis cannot be too thin -/

/-- Counting: if every odd `m` in `T` is a sum of three elements of a finite set `S`, then
`#T ≤ #S³`. -/
theorem card_le_cube {S T : Finset ℕ} (h : ∀ m ∈ T, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a + b + c = m) :
    T.card ≤ S.card ^ 3 := by
  have hsub : T ⊆ (S ×ˢ S ×ˢ S).image (fun t => t.1 + t.2.1 + t.2.2) := by
    intro m hm
    obtain ⟨a, ha, b, hb, c, hc, e⟩ := h m hm
    exact mem_image.mpr ⟨(a, b, c), by simp [ha, hb, hc], e⟩
  calc T.card ≤ ((S ×ˢ S ×ˢ S).image (fun t => t.1 + t.2.1 + t.2.2)).card := card_le_card hsub
    _ ≤ (S ×ˢ S ×ˢ S).card := card_image_le
    _ = S.card ^ 3 := by simp [card_product]; ring

/-- At least `(x - 7)/2 + 1` odd numbers lie in `[7, x]`. -/
theorem odd_count (x : ℕ) (hx : 7 ≤ x) :
    (x - 7) / 2 + 1 ≤ #{m ∈ Icc 7 x | Odd m} := by
  have : (range ((x - 7) / 2 + 1)).image (fun k => 2 * k + 7) ⊆ {m ∈ Icc 7 x | Odd m} := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
    simp only [mem_range] at hk
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨k + 3, by ring⟩⟩
  calc (x - 7) / 2 + 1 = ((range ((x - 7) / 2 + 1)).image (fun k => 2 * k + 7)).card := by
        rw [card_image_of_injective _ (fun a b h => by omega), card_range]
    _ ≤ _ := card_le_card this

/-- If every odd `m ∈ [7, x]` is a sum of three elements of a set `P` of naturals, then
`x ≤ 14 · #(P ∩ [0, x])³`, so `#(P ∩ [0, x]) ≫ x^{1/3}`. -/
theorem cube_lower_bound (P : Set ℕ) (x : ℕ) (hx : 7 ≤ x)
    (h : ∀ m : ℕ, Odd m → 7 ≤ m → m ≤ x → IsSum3In P m) : x ≤ 14 * countUpTo P x ^ 3 := by
  have hT : #{m ∈ Icc 7 x | Odd m} ≤ countUpTo P x ^ 3 := by
    unfold countUpTo
    apply card_le_cube
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    obtain ⟨a, b, c, ha, hb, hc, e⟩ := h m hm.2 hm.1.1 hm.1.2
    refine ⟨a, ?_, b, ?_, c, ?_, e⟩ <;> simp only [mem_filter, mem_range] <;>
      refine ⟨by omega, by assumption⟩
  have := odd_count x hx
  omega

/-- The same bound as a real cube root: `x^{1/3} ≤ 3 · #(P ∩ [0, x])`. -/
theorem cbrt_lower_bound (P : Set ℕ) (x : ℕ) (hx : 7 ≤ x)
    (h : ∀ m : ℕ, Odd m → 7 ≤ m → m ≤ x → IsSum3In P m) :
    (x : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 * (countUpTo P x : ℝ) := by
  have h1 := cube_lower_bound P x hx h
  have h2 : (x : ℝ) ≤ (3 * (countUpTo P x : ℝ)) ^ (3 : ℕ) := by
    have : (x : ℝ) ≤ 14 * (countUpTo P x : ℝ) ^ 3 := by exact_mod_cast h1
    nlinarith [pow_nonneg (Nat.cast_nonneg (countUpTo P x) : (0 : ℝ) ≤ countUpTo P x) 3]
  have h3 : 0 ≤ 3 * (countUpTo P x : ℝ) := by positivity
  calc (x : ℝ) ^ ((1 : ℝ) / 3) ≤ ((3 * (countUpTo P x : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h2 (by norm_num)
    _ = 3 * (countUpTo P x : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h3]; norm_num

/-- For the set of Theorem 1.1, the count is at least `x^{1/3}/3` for every `x ≥ 7`, against
the paper's upper bound `o(X / (log X)^B)` for each `B`. The two are compatible. -/
theorem theorem11_two_sided (h : Theorem11) :
    ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ B : ℕ, 0 < B → SparseB P B) ∧
      ∀ x : ℕ, 7 ≤ x → (x : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 * (countUpTo P x : ℝ) := by
  obtain ⟨P, hP, ha, hb⟩ := h
  exact ⟨P, hP, ha, fun x hx => cbrt_lower_bound P x hx (fun m ho h7 _ => hb m ho h7)⟩

/-- Small kernel fact: any set of primes that represents every odd `m ≥ 7` contains 2 and 3,
since `7 = 2 + 2 + 3` is the only way to write 7 as a sum of three primes. -/
theorem two_three_mem {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) (h7 : IsSum3In P 7) :
    2 ∈ P ∧ 3 ∈ P := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := h7
  have pa := (hP a ha).two_le
  have pb := (hP b hb).two_le
  have pc := (hP c hc).two_le
  have qa := hP a ha
  have qb := hP b hb
  have qc := hP c hc
  have : a ≤ 3 := by omega
  have : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b
  · exact ⟨ha, by have : c = 3 := by omega
                  subst this; exact hc⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩
  · exfalso; have : c = 1 := by omega
    subst this; exact Nat.not_prime_one qc

end LeanLab.SparseTernary

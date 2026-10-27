/-
P0046 Li and Pan 2007, Corollary 2.1: q odd squarefree, f₁, f₂, f₃ from the reduced residues
to [0, 1] with Σ (f₁ + f₂ + f₃) > 2 φ(q); every n mod q is x + y + z, reduced, with
f₁ x + f₂ y + f₃ z > 5/3 and f₁ x f₂ y f₃ z ≠ 0. Shao cites it in Lemma 2.3.
As in the paper: Theorem 1.2 when 3 ∤ q, the case q = 3 by hand, here by 64 positivity cases
and linarith, and q = 3 q' by Theorem 1.2 mod q' first and then the case q = 3.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0129.
-/
import LeanLab.DensityGoldbach.LiPanFull
import LeanLab.DensityGoldbach.Prop16

open Finset

namespace LeanLab.DensityGoldbach

/-- Li-Pan Corollary 2.1 at one modulus. -/
def LiPanCor21 (q : ℕ) [NeZero q] : Prop := ∀ f₁ f₂ f₃ : ZMod q → ℝ,
  (∀ a, 0 ≤ f₁ a ∧ f₁ a ≤ 1) → (∀ a, 0 ≤ f₂ a ∧ f₂ a ≤ 1) → (∀ a, 0 ≤ f₃ a ∧ f₃ a ≤ 1) →
  2 * (q.totient : ℝ) < ∑ a ∈ unitsMod q, (f₁ a + f₂ a + f₃ a) →
  ∀ n : ZMod q, ∃ x ∈ unitsMod q, ∃ y ∈ unitsMod q, ∃ z ∈ unitsMod q, x + y + z = n ∧
    5 / 3 < f₁ x + f₂ y + f₃ z ∧ f₁ x * f₂ y * f₃ z ≠ 0

lemma prod_ne_of_gt_two {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (hc1 : c ≤ 1) (h : 2 < a + b + c) : a * b * c ≠ 0 := by
  have : 0 < a := by by_contra h'; push Not at h'; linarith
  have : 0 < b := by by_contra h'; push Not at h'; linarith
  have : 0 < c := by by_contra h'; push Not at h'; linarith
  positivity

/-- The case `3 ∤ q`, from Theorem 1.2. -/
theorem liPanCor21_coprime (q : ℕ) [NeZero q] (h6 : q.Coprime 6) : LiPanCor21 q := by
  intro f₁ f₂ f₃ hf₁ hf₂ hf₃ hsum n
  obtain ⟨x, hx, y, hy, z, hz, e, hK⟩ := liPan12_full q h6 f₁ f₂ f₃ n
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [← sum_add_distrib, ← sum_add_distrib] at hK
  have h2 : 2 < f₁ x + f₂ y + f₃ z := by
    refine lt_of_lt_of_le ?_ hK
    rw [lt_div_iff₀ hφ]; linarith
  exact ⟨x, hx, y, hy, z, hz, e, by linarith, prod_ne_of_gt_two (hf₁ x).1 (hf₂ y).1 (hf₃ z).1
    (hf₁ x).2 (hf₂ y).2 (hf₃ z).2 h2⟩

lemma zmod3_cases : ∀ z : ZMod 3, (z ≠ 0 ↔ z = 1 ∨ z = 2) := by decide

lemma unitsMod_three : unitsMod 3 = {1, 2} := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  ext z
  rw [mem_unitsMod, isUnit_iff_ne_zero, mem_insert, mem_singleton]
  exact zmod3_cases z

/-- **The case `q = 3`, by hand.** -/
theorem liPanCor21_three : LiPanCor21 3 := by
  intro f₁ f₂ f₃ hf₁ hf₂ hf₃ hsum n
  rw [unitsMod_three, sum_pair (by decide)] at hsum
  rw [show Nat.totient 3 = 2 by decide] at hsum
  push_cast at hsum
  have m1 : (1 : ZMod 3) ∈ unitsMod 3 := by rw [unitsMod_three]; simp
  have m2 : (2 : ZMod 3) ∈ unitsMod 3 := by rw [unitsMod_three]; simp
  obtain ⟨a0, a1⟩ := hf₁ 1; obtain ⟨b0, b1⟩ := hf₁ 2
  obtain ⟨c0, c1⟩ := hf₂ 1; obtain ⟨d0, d1⟩ := hf₂ 2
  obtain ⟨e0, e1⟩ := hf₃ 1; obtain ⟨g0, g1⟩ := hf₃ 2
  have key : ∀ x y z : ZMod 3, x ∈ unitsMod 3 → y ∈ unitsMod 3 → z ∈ unitsMod 3 →
      x + y + z = n → (5 / 3 < f₁ x + f₂ y + f₃ z ∧ 0 < f₁ x ∧ 0 < f₂ y ∧ 0 < f₃ z) →
      ∃ x ∈ unitsMod 3, ∃ y ∈ unitsMod 3, ∃ z ∈ unitsMod 3, x + y + z = n ∧
        5 / 3 < f₁ x + f₂ y + f₃ z ∧ f₁ x * f₂ y * f₃ z ≠ 0 :=
    fun x y z hx hy hz e ⟨h, p, q', r⟩ => ⟨x, hx, y, hy, z, hz, e, h, by positivity⟩
  by_contra hne
  have H : ∀ x y z : ZMod 3, x ∈ unitsMod 3 → y ∈ unitsMod 3 → z ∈ unitsMod 3 →
      x + y + z = n → 0 < f₁ x → 0 < f₂ y → 0 < f₃ z → f₁ x + f₂ y + f₃ z ≤ 5 / 3 := by
    intro x y z hx hy hz e p q' r
    by_contra h; push Not at h
    exact hne (key x y z hx hy hz e ⟨h, p, q', r⟩)
  have hn : ∀ m : ZMod 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rcases hn n with rfl | rfl | rfl
  · have h0 := H 1 1 1 m1 m1 m1 (by decide)
    have h1 := H 2 2 2 m2 m2 m2 (by decide)
    rcases a0.eq_or_lt with ha | ha <;> rcases b0.eq_or_lt with hb | hb <;>
    rcases c0.eq_or_lt with hc | hc <;> rcases d0.eq_or_lt with hd | hd <;>
    rcases e0.eq_or_lt with he | he <;> rcases g0.eq_or_lt with hg | hg
    all_goals ((try have := h0 (by assumption) (by assumption) (by assumption)) <;>
      (try have := h1 (by assumption) (by assumption) (by assumption)) <;>
      linarith)
  · have h0 := H 1 1 2 m1 m1 m2 (by decide)
    have h1 := H 1 2 1 m1 m2 m1 (by decide)
    have h2 := H 2 1 1 m2 m1 m1 (by decide)
    rcases a0.eq_or_lt with ha | ha <;> rcases b0.eq_or_lt with hb | hb <;>
    rcases c0.eq_or_lt with hc | hc <;> rcases d0.eq_or_lt with hd | hd <;>
    rcases e0.eq_or_lt with he | he <;> rcases g0.eq_or_lt with hg | hg
    all_goals ((try have := h0 (by assumption) (by assumption) (by assumption)) <;>
      (try have := h1 (by assumption) (by assumption) (by assumption)) <;>
      (try have := h2 (by assumption) (by assumption) (by assumption)) <;>
      linarith)
  · have h0 := H 1 2 2 m1 m2 m2 (by decide)
    have h1 := H 2 1 2 m2 m1 m2 (by decide)
    have h2 := H 2 2 1 m2 m2 m1 (by decide)
    rcases a0.eq_or_lt with ha | ha <;> rcases b0.eq_or_lt with hb | hb <;>
    rcases c0.eq_or_lt with hc | hc <;> rcases d0.eq_or_lt with hd | hd <;>
    rcases e0.eq_or_lt with he | he <;> rcases g0.eq_or_lt with hg | hg
    all_goals ((try have := h0 (by assumption) (by assumption) (by assumption)) <;>
      (try have := h1 (by assumption) (by assumption) (by assumption)) <;>
      (try have := h2 (by assumption) (by assumption) (by assumption)) <;>
      linarith)

/-- The case `q = 3 k`, `k` coprime to `6`: Theorem 1.2 mod `k` on the 3-fiber sums, then the
case `q = 3`. -/
theorem liPanCor21_mul3 (k : ℕ) [NeZero k] [NeZero (3 * k)] (hk : Nat.Coprime 3 k)
    (h6 : k.Coprime 6) : LiPanCor21 (3 * k) := by
  intro f₁ f₂ f₃ hf₁ hf₂ hf₃ hsum n
  have : NeZero 3 := ⟨by norm_num⟩
  set e := ZMod.chineseRemainder hk
  let G : (ZMod (3 * k) → ℝ) → ZMod k → ℝ := fun f u => ∑ b ∈ unitsMod 3, f (e.symm (b, u))
  have hG : ∀ f : ZMod (3 * k) → ℝ, ∑ u ∈ unitsMod k, G f u = ∑ a ∈ unitsMod (3 * k), f a := by
    intro f; rw [sum_unitsMod_crt hk, sum_comm]
  obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, hn2, hK⟩ := liPan12_full k h6 (G f₁) (G f₂) (G f₃) (e n).2
  rw [hG, hG, hG] at hK
  have hφ : ((3 * k).totient : ℝ) = 2 * k.totient := by
    rw [Nat.totient_mul hk, show Nat.totient 3 = 2 by decide]; push_cast; ring
  have hφk : (0 : ℝ) < k.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  rw [hφ, sum_add_distrib, sum_add_distrib] at hsum
  have h4 : 2 * ((Nat.totient 3 : ℕ) : ℝ) < ∑ b ∈ unitsMod 3,
      (f₁ (e.symm (b, u₁)) + f₂ (e.symm (b, u₂)) + f₃ (e.symm (b, u₃))) := by
    rw [show Nat.totient 3 = 2 by decide, sum_add_distrib, sum_add_distrib]
    have : 4 < G f₁ u₁ + G f₂ u₂ + G f₃ u₃ := by
      refine lt_of_lt_of_le ?_ hK
      rw [lt_div_iff₀ hφk]; linarith
    norm_num
    exact this
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, hn3, h53, hne⟩ := liPanCor21_three
    (fun b => f₁ (e.symm (b, u₁))) (fun b => f₂ (e.symm (b, u₂))) (fun b => f₃ (e.symm (b, u₃)))
    (fun _ => hf₁ _) (fun _ => hf₂ _) (fun _ => hf₃ _) h4 (e n).1
  have hunit : ∀ b ∈ unitsMod 3, ∀ u ∈ unitsMod k, e.symm (b, u) ∈ unitsMod (3 * k) := by
    intro b hb u hu
    rw [mem_unitsMod_crt hk, RingEquiv.apply_symm_apply]; exact ⟨hb, hu⟩
  refine ⟨e.symm (b₁, u₁), hunit b₁ hb₁ u₁ hu₁, e.symm (b₂, u₂), hunit b₂ hb₂ u₂ hu₂,
    e.symm (b₃, u₃), hunit b₃ hb₃ u₃ hu₃, ?_, h53, hne⟩
  apply e.injective
  rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, hn3, hn2]

/-- **Li-Pan Corollary 2.1** for every odd squarefree `q`. -/
theorem liPanCor21_odd (q : ℕ) [NeZero q] (hodd : Odd q) (hsq : Squarefree q) :
    LiPanCor21 q := by
  have h2 : ¬ 2 ∣ q := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hodd
  by_cases h3 : 3 ∣ q
  · obtain ⟨k, rfl⟩ := h3
    have hk0 : k ≠ 0 := by rintro rfl; exact NeZero.ne (3 * 0) rfl
    have : NeZero k := ⟨hk0⟩
    have hk3 : Nat.Coprime 3 k := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro h
      exact Nat.prime_three.one_lt.ne' (Nat.isUnit_iff.1 (hsq 3 (mul_dvd_mul_left 3 h)))
    have hk6 : k.Coprime 6 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
      refine ⟨?_, hk3.symm⟩
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact fun h => h2 (dvd_mul_of_dvd_right h 3)
    exact liPanCor21_mul3 k hk3 hk6
  · apply liPanCor21_coprime
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact ⟨h2, h3⟩

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.liPanCor21_odd

namespace LeanLab.DensityGoldbach

/-- Shao's route for Lemma 2.3 when `|A| + |B| + |C| > 16`, by Li-Pan Cor 2.1 at `q = 15` with
indicator functions; a cross-check of the kernel computation in Lemma23.lean. -/
theorem lemma23_big_of_liPan (A B C : Finset (ZMod 15))
    (hA : A ⊆ unitsMod 15) (hB : B ⊆ unitsMod 15) (hC : C ⊆ unitsMod 15)
    (h : 16 < #A + #B + #C) (z : ZMod 15) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x + y + w = z := by
  classical
  let ind : Finset (ZMod 15) → ZMod 15 → ℝ := fun S a => if a ∈ S then 1 else 0
  have hb : ∀ S a, 0 ≤ ind S a ∧ ind S a ≤ 1 := by
    intro S a; simp only [ind]; split_ifs <;> norm_num
  have hs : ∀ S, S ⊆ unitsMod 15 → ∑ a ∈ unitsMod 15, ind S a = #S := by
    intro S hS
    simp only [ind]
    rw [sum_boole, Nat.cast_inj, filter_mem_eq_inter, inter_eq_right.2 hS]
  have hsum : 2 * ((Nat.totient 15 : ℕ) : ℝ) <
      ∑ a ∈ unitsMod 15, (ind A a + ind B a + ind C a) := by
    rw [sum_add_distrib, sum_add_distrib, hs A hA, hs B hB, hs C hC,
      show Nat.totient 15 = 8 by decide]
    have : (16 : ℝ) < #A + #B + #C := by exact_mod_cast h
    push_cast; linarith
  have : NeZero 15 := ⟨by norm_num⟩
  obtain ⟨x, -, y, -, w, -, e, -, hne⟩ := liPanCor21_odd 15 (by decide)
    (by rw [show (15 : ℕ) = 3 * 5 from rfl]
        exact (Nat.squarefree_mul (by norm_num)).2
          ⟨Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩)
    (ind A) (ind B) (ind C) (hb A) (hb B) (hb C) hsum z
  have mem : ∀ S a, ind S a ≠ 0 → a ∈ S := by
    intro S a h; by_contra h'; exact h (by simp [ind, h'])
  exact ⟨x, mem A x (left_ne_zero_of_mul (left_ne_zero_of_mul hne)),
    y, mem B y (right_ne_zero_of_mul (left_ne_zero_of_mul hne)),
    w, mem C w (right_ne_zero_of_mul hne), e⟩

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.lemma23_big_of_liPan

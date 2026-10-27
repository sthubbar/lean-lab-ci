/-
DISCOVER I-0060, from P0082 Brüdern-Perelli 1998 and the even Goldbach verifications.
Below a verified height M, the inequality abs(p₁ + p₂ − F(n)) < 1 in odd primes is solvable
exactly when F(n) is not an odd integer, provided 5 < F(n) < M. So below the height
4 · 10^18 the exceptions of Theorem 1 are only the n with F(n) ≤ 5 and the n with F(n) an
odd integer; the analytic content of Theorem 1 is about F(n) beyond every verification.
Elementary; KNOWN in method.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.ExceptionalSet.BrudernPerelli1998

namespace LeanLab.ExceptionalSet.BrudernPerelli1998
open Real

attribute [local instance] Classical.propDecidable

/-- `x` is an odd integer. -/
def IsOddInt (x : ℝ) : Prop := ∃ k : ℤ, x = 2 * k + 1

/-- No even integer lies within distance 1 of an odd integer. -/
theorem no_even_near_odd {x : ℝ} (hx : IsOddInt x) {m : ℤ} (hm : Even m) :
    ¬ |(m : ℝ) - x| < 1 := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := hm
  intro h
  have h1 := abs_lt.mp h
  push_cast at h1
  have e1 : ((a : ℝ) + a) - (2 * k + 1) < 1 := h1.2
  have e2 : -1 < ((a : ℝ) + a) - (2 * k + 1) := h1.1
  have f1 : a + a - (2 * k + 1) < 1 := by exact_mod_cast e1
  have f2 : -1 < a + a - (2 * k + 1) := by exact_mod_cast e2
  omega

/-- Away from odd integers there is an even integer within distance 1. -/
theorem even_near_of_not_oddInt {x : ℝ} (hx : ¬ IsOddInt x) :
    ∃ m : ℤ, Even m ∧ |(m : ℝ) - x| < 1 := by
  set t := (x - 1) / 2 with ht
  refine ⟨2 * ⌈t⌉, even_two_mul _, ?_⟩
  have hc1 : t ≤ ⌈t⌉ := Int.le_ceil t
  have hc2 : (⌈t⌉ : ℝ) < t + 1 := Int.ceil_lt_add_one t
  have hne : (⌈t⌉ : ℝ) ≠ t := by
    intro h
    apply hx
    refine ⟨⌈t⌉, ?_⟩
    linarith
  have hlt : t < ⌈t⌉ := lt_of_le_of_ne hc1 (Ne.symm hne)
  rw [abs_lt]
  push_cast
  constructor <;> linarith [ht]

/-- An even `m ≥ 6` that is a sum of two primes is a sum of two odd primes. -/
theorem odd_primes_of_goldbach {m : ℕ} (hm : Even m) (h6 : 6 ≤ m) (h : IsGoldbachSum m) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = m := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hqe : Even q := by
      obtain ⟨r, hr⟩ := hm
      exact ⟨r - 1, by omega⟩
    have := hq.even_iff.mp hqe
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hpe : Even p := by
      obtain ⟨r, hr⟩ := hm
      exact ⟨r - 1, by omega⟩
    have := hp.even_iff.mp hpe
    omega
  exact ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, hpq⟩

/-- **I-0060.** Below a verified height, solvability is exactly "F(n) is not an odd integer". -/
theorem solvable_iff_of_upTo {M : ℕ} (hE : EvenGoldbachUpTo M) {γ : ℝ} {n : ℕ}
    (h5 : 5 < F γ n) (hM : F γ n < M) : Solvable γ n ↔ ¬ IsOddInt (F γ n) := by
  constructor
  · rintro ⟨p₁, p₂, -, -, ho₁, ho₂, hlt⟩ hodd
    have hev : Even ((p₁ + p₂ : ℕ) : ℤ) := (Int.even_coe_nat _).mpr (ho₁.add_odd ho₂)
    exact no_even_near_odd hodd hev (by exact_mod_cast hlt)
  · intro hno
    obtain ⟨m, hm, hlt⟩ := even_near_of_not_oddInt hno
    have h1 := abs_lt.mp hlt
    have hm4 : (4 : ℝ) < m := by linarith [h1.1]
    have hmpos : 0 ≤ m := by
      have : (0 : ℝ) ≤ m := by linarith
      exact_mod_cast this
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' := ⟨m.toNat, (Int.toNat_of_nonneg hmpos).symm⟩
    have hm' : Even m' := by exact_mod_cast hm
    have h4' : 4 < m' := by exact_mod_cast hm4
    have h6 : 6 ≤ m' := by
      obtain ⟨r, hr⟩ := hm'; omega
    have hleM : m' ≤ M := by
      have : (m' : ℝ) < M + 1 := by push_cast at h1; linarith [h1.2]
      have : m' < M + 1 := by exact_mod_cast this
      omega
    obtain ⟨p, q, hp, hq, hop, hoq, hpq⟩ :=
      odd_primes_of_goldbach hm' h6 (hE m' hm' (by omega) hleM)
    refine ⟨p, q, hp, hq, hop, hoq, ?_⟩
    rw [hpq]; exact_mod_cast hlt

/-- `F γ` is monotone on `n ≥ 1` for `γ > 0`. -/
theorem F_mono {γ : ℝ} (hγ : 0 < γ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    F γ a ≤ F γ b := by
  unfold F
  apply Real.exp_le_exp.mpr
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply Real.rpow_le_rpow (Real.log_nonneg ha')
    (Real.log_le_log (by linarith) hab') hγ.le

/-- Below the height `M`, every exception has `F(n) ≤ 5` or `F(n)` an odd integer. -/
theorem Eγ_le_of_upTo {M : ℕ} (hE : EvenGoldbachUpTo M) {γ : ℝ} (hγ : 0 < γ) {N : ℕ}
    (hN : F γ N < M) :
    Eγ γ N ≤ ((Finset.Icc 1 N).filter (fun n : ℕ => F γ n ≤ 5 ∨ IsOddInt (F γ n))).card := by
  unfold Eγ
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  refine ⟨hn.1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hFM : F γ n < M := lt_of_le_of_lt (F_mono hγ hn.1.1 hn.1.2) hN
  exact hn.2 ((solvable_iff_of_upTo hE hcon.1 hFM).mpr hcon.2)

/-- And conversely every such `n` with `F(n)` an odd integer is an exception, at any height. -/
theorem not_solvable_of_oddInt {γ : ℝ} {n : ℕ} (h : IsOddInt (F γ n)) : ¬ Solvable γ n := by
  rintro ⟨p₁, p₂, -, -, ho₁, ho₂, hlt⟩
  have hev : Even ((p₁ + p₂ : ℕ) : ℤ) := (Int.even_coe_nat _).mpr (ho₁.add_odd ho₂)
  exact no_even_near_odd h hev (by exact_mod_cast hlt)

end LeanLab.ExceptionalSet.BrudernPerelli1998

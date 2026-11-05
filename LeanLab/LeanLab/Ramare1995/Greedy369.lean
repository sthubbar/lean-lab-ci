/-
An alternative bounded descent for the lower DecompJ1133 range.
Ramaré 1995 p. 704 supplies the greedy method. Ramaré and Saouter 2003 pp. 11 to 13
supply stronger interval ratios for large arguments. The hypotheses below isolate the
three interval inputs and a finite Goldbach input through 10^9. No input is asserted here.
The additive allowance 400 in the small interval input is a lab relaxation.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Greedy

namespace LeanLab.Ramare1995.Greedy369
open LeanLab LeanLab.SchnirelmannConstant

/-- A prime from the relaxed small interval is odd in the range used by the descent.
Auxiliary parity step for Ramaré 1995 p. 704 and the 2003 p. 13 interval input. -/
theorem odd_of_relaxed_gap {y p : ℕ} (hp : p.Prime) (hy : 10 ^ 9 - 3 < y)
    (hg : 28314000 * (y - p) < y + 28314000 * 400) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | ho
  · subst h2
    omega
  · exact ho

/-- Stronger interval ratios reduce the terminal Goldbach input to 10^9.
CONDITIONAL ON finite Goldbach and all three displayed prime interval inputs.
This does not assert a proof of those inputs or rebuild the finite verification. -/
theorem lower_of_stronger_intervals
    (hG : EvenGoldbachUpTo (10 ^ 9))
    (hL : ∀ y : ℕ, 10 ^ 29 ≤ y → y ≤ 4 * 10 ^ 32 →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 209257759 * (y - p) < y)
    (hM : ∀ y : ℕ, 10 ^ 20 ≤ y → y ≤ 4 * 10 ^ 32 →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 81353847 * (y - p) < y)
    (hS : ∀ y : ℕ, 10 ^ 9 - 3 < y → y ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 28314000 * (y - p) < y + 28314000 * 400)
    (N : ℕ) (hN : Even N) (hlo : 10 ^ 30 < N) (hhi : N ≤ 4 * 10 ^ 32) :
    AtMostPrimes 6 N := by
  have hN2 := Nat.even_iff.mp hN
  have P3 := AtMostPrimes.prime Nat.prime_three
  obtain ⟨p1, hp1, hp1le, h1⟩ := hL (N - 3) (by omega) (by omega)
  have o1 := Greedy.odd_of_big hp1 (by omega) (by omega) hp1le
  set x1 := N - 3 - p1 with hx1
  rcases le_or_gt x1 (10 ^ 9) with s1 | b1
  · have hx := atMost2_of_even hG (Nat.even_iff.mpr (by omega)) s1
    have ht := (P3.add (AtMostPrimes.prime hp1)).add hx
    rw [show 3 + p1 + x1 = N by omega] at ht
    exact ht.mono (by norm_num)
  have hnext : ∃ p2 : ℕ, p2.Prime ∧ p2 ≤ x1 ∧
      ((81353847 * (x1 - p2) < x1 ∧ 10 ^ 20 ≤ x1) ∨
       (28314000 * (x1 - p2) < x1 + 28314000 * 400 ∧ x1 < 10 ^ 20)) := by
    rcases le_or_gt (10 ^ 20) x1 with hm | hs
    · obtain ⟨p2, hp2, hp2le, h2⟩ := hM x1 hm (by omega)
      exact ⟨p2, hp2, hp2le, Or.inl ⟨h2, hm⟩⟩
    · obtain ⟨p2, hp2, hp2le, h2⟩ := hS x1 (by omega) hs.le
      exact ⟨p2, hp2, hp2le, Or.inr ⟨h2, hs⟩⟩
  obtain ⟨p2, hp2, hp2le, h2⟩ := hnext
  have o2 : p2 % 2 = 1 := by
    rcases h2 with h2 | h2
    · exact Greedy.odd_of_big hp2 (by omega) (by omega) hp2le
    · exact odd_of_relaxed_gap hp2 (by omega) h2.1
  set x2 := x1 - p2 with hx2
  rcases le_or_gt x2 (10 ^ 9 - 3) with s2 | b2
  · have hx := atMost2_of_even hG (m := x2 + 3) (Nat.even_iff.mpr (by omega)) (by omega)
    have ht := ((AtMostPrimes.prime hp1).add (AtMostPrimes.prime hp2)).add hx
    rw [show p1 + p2 + (x2 + 3) = N by omega] at ht
    exact ht.mono (by norm_num)
  have x2upper : x2 ≤ 10 ^ 20 := by
    rcases h2 with h2 | h2 <;> omega
  obtain ⟨p3, hp3, hp3le, h3⟩ := hS x2 b2 x2upper
  have o3 := odd_of_relaxed_gap hp3 b2 h3
  set x3 := x2 - p3 with hx3
  have s3 : x3 ≤ 10 ^ 9 := by
    rcases h2 with h2 | h2 <;> omega
  have hx := atMost2_of_even hG (m := x3) (Nat.even_iff.mpr (by omega)) s3
  have ht := ((((P3.add (AtMostPrimes.prime hp1)).add (AtMostPrimes.prime hp2)).add
    (AtMostPrimes.prime hp3)).add hx)
  rw [show 3 + p1 + p2 + p3 + x3 = N by omega] at ht
  exact ht

/-- Natural subtraction translates the real prime interval inequality into a gap bound.
Auxiliary conversion for Ramaré and Saouter 2003 Theorems 2 and 3 on pp. 12 to 13. -/
theorem interval_nat_bound {D y p : ℕ} (hD : 0 < D) (hu : (p : ℝ) ≤ y)
    (hl : (y : ℝ) * (1 - 1 / (D : ℝ)) < p) :
    p ≤ y ∧ D * (y - p) < y := by
  have hpy : p ≤ y := by exact_mod_cast hu
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have he : (y : ℝ) * (1 - 1 / (D : ℝ)) = y - y / D := by ring
  rw [he] at hl
  have hg : (y : ℝ) - p < y / D := by linarith
  have hmul := (lt_div_iff₀ hD0).mp hg
  refine ⟨hpy, ?_⟩
  have hc : ((D * (y - p) : ℕ) : ℝ) < y := by
    rw [Nat.cast_mul, Nat.cast_sub hpy]
    nlinarith
  exact_mod_cast hc

/-- The Table 1 row 59 applies from the laboratory cutoff 10^29.
Auxiliary threshold for the large interval query, 2003 p. 11. -/
theorem exp59_le : Real.exp 59 ≤ (10 ^ 29 : ℝ) := by
  have h67 := Section9.exp67_le
  have h8 := Real.add_one_le_exp (8 : ℝ)
  have hp := Real.exp_pos 59
  have hm := mul_le_mul_of_nonneg_left h8 hp.le
  have he : Real.exp 67 = Real.exp 59 * Real.exp 8 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at h67
  nlinarith

/-- The Table 1 row 46 applies from the laboratory cutoff 10^20.
Auxiliary threshold for the medium interval query, 2003 p. 11. -/
theorem exp46_le : Real.exp 46 ≤ (10 ^ 20 : ℝ) := by
  have he : Real.exp 46 = Real.exp 1 ^ 46 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  calc
    Real.exp 1 ^ 46 ≤ (2.7182818286 : ℝ) ^ 46 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 46
    _ ≤ 10 ^ 20 := by norm_num

/-- Source input bridge for the stronger descent.
CONDITIONAL ON finite Goldbach through 10^9, Table 1 rows 59 and 46, Theorem 3,
and the explicit prime gap bound 400 below its threshold. All inputs stay visible. -/
theorem lower_of_table_inputs
    (hG : EvenGoldbachUpTo (10 ^ 9))
    (h59 : ∀ x : ℝ, Real.exp 59 ≤ x → ∃ p : ℕ,
      p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x)
    (h46 : ∀ x : ℝ, Real.exp 46 ≤ x → (10 ^ 20 : ℝ) ≤ x → ∃ p : ℕ,
      p.Prime ∧ x * (1 - 1 / 81353847) < p ∧ (p : ℝ) ≤ x)
    (h3 : LeanLab.Tao2012.RSShortIntervals)
    (h400 : ∀ y : ℕ, 10 ^ 9 - 3 < y → y ≤ 10726905041 →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ y - p ≤ 400)
    (N : ℕ) (hN : Even N) (hlo : 10 ^ 30 < N) (hhi : N ≤ 4 * 10 ^ 32) :
    AtMostPrimes 6 N := by
  apply lower_of_stronger_intervals hG ?_ ?_ ?_ N hN hlo hhi
  · intro y hy hu
    have hy' : (10 ^ 29 : ℝ) ≤ y := by exact_mod_cast hy
    obtain ⟨p, hp, hl, hu'⟩ := h59 y (exp59_le.trans hy')
    obtain ⟨hpy, hg⟩ := interval_nat_bound (D := 209257759) (by norm_num) hu' hl
    exact ⟨p, hp, hpy, hg⟩
  · intro y hy hu
    have hy' : (10 ^ 20 : ℝ) ≤ y := by exact_mod_cast hy
    obtain ⟨p, hp, hl, hu'⟩ := h46 y (exp46_le.trans hy') hy'
    obtain ⟨hpy, hg⟩ := interval_nat_bound (D := 81353847) (by norm_num) hu' hl
    exact ⟨p, hp, hpy, hg⟩
  · intro y hy hu
    by_cases hb : 10726905041 < y
    · obtain ⟨p, hp, hpy, hg⟩ := h3 y hb
      simp only [LeanLab.Tao2012.Δ] at hg
      exact ⟨p, hp, hpy, by omega⟩
    · obtain ⟨p, hp, hpy, hg⟩ := h400 y hy (by omega)
      exact ⟨p, hp, hpy, by omega⟩

end LeanLab.Ramare1995.Greedy369

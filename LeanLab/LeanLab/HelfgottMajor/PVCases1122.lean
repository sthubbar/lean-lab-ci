import Mathlib
import LeanLab.HelfgottMajor.PV420Split1122

/-!
Route burst S58 round two, burst-20261122, tag pomerance-cases.
Split of the HARD case LEAFs `PV420Split1122.pomerance_even_case` and
`PV420Split1122.pomerance_odd_case`, Pomerance 2011 Theorem 1, along the structure that
Frolenkov arXiv 1107.0381 Sections 3 and 5 follows: Fourier expansion of the interval
indicator, display 12; truncation at a parameter, display 15 and 16; reduction through
Pomerance display 10, Frolenkov display 14, and |τ(χ)| = √q, display 13, to the sum of
|sin| or of |cos mα - cos mβ|, displays 17 and 22; application of Pomerance Lemma 3 or
Section 4; and, for even χ, the doubling S_χ = 2 T_χ of Frolenkov display 1.

Pomerance's own truncation error and choice of H are not quoted by Frolenkov, who uses
Bykovskii smoothing instead, and the Integers PDF is not reachable. So the truncation step
is a LEAF that asserts: at Pomerance's H, the truncated expansion with its error fits the
part of the final bound not used by Lemma 3 or Section 4. Everything else is PROVED here:
the even reduction of intervals to initial segments, the application of Lemma 3 and of
Section 4, and the final arithmetic.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVCases1122

open Real Finset

/-- Frolenkov display 1, the easy half, used by Pomerance for even χ: an interval sum is a
difference of two initial segment sums, so it is at most the sum of their norms. PROVED. -/
theorem interval_le_two_initial {q : ℕ} (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      ‖∑ m ∈ range (N + 1), χ (m : ZMod q)‖ + ‖∑ m ∈ range M, χ (m : ZMod q)‖ := by
  by_cases h : M ≤ N + 1
  · have : ∑ m ∈ Icc M N, χ (m : ZMod q) =
        ∑ m ∈ range (N + 1), χ (m : ZMod q) - ∑ m ∈ range M, χ (m : ZMod q) := by
      have hI : Icc M N = Ico M (N + 1) := by ext x; simp
      rw [← Finset.sum_Ico_eq_sub _ h, hI]
    rw [this]; exact norm_sub_le _ _
  · have : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, sum_empty, norm_zero]; positivity

/-- LEAF: Pomerance 2011, proof of Theorem 1 for even χ, the steps before Lemma 3:
the Polya Fourier expansion of the initial segment indicator, Frolenkov display 12 with M = 0,
truncated at Pomerance's parameter H with his explicit truncation error, Frolenkov displays 15
and 16, then reduced through display 10 and |τ(χ)| = √q, Frolenkov displays 13, 14 and 17, to
√q/π times the sum of |sin(j x)|/j at x = 2πK/q; with Pomerance's choice of H the truncation
error fits in what the final bound leaves after Lemma 3. Class HARD. -/
theorem even_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  sorry

/-- Pomerance even case, initial segments: Lemma 3 applied to the truncated sum, then the
final arithmetic, giving T_χ at most half of Pomerance's even bound. PROVED from the LEAF
`even_truncated` and the hypothesis Lemma 3. -/
theorem even_initial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL3 : ∀ (x : ℝ) (n : ℕ), 1 ≤ n → ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n))
    (htr : ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)))
    (K : ℕ) :
    ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
      1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q := by
  obtain ⟨H, hH, hK⟩ := htr
  have h1 := hK K
  have h2 := (hL3 (2 * π * K / q) H hH).le
  have hc : 0 ≤ sqrt q / π := div_nonneg (sqrt_nonneg _) pi_pos.le
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  have hpi : π ≠ 0 := pi_pos.ne'
  have e : sqrt q / π * (2 / π * log H + 2 / π * (eulerMascheroniConstant + log 2 + 3 / H)) =
      2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
    field_simp; ring
  linarith

/-- LEAF: Pomerance 2011, proof of Theorem 1 for odd χ, the steps before Section 4: the Polya
Fourier expansion of the interval indicator, Frolenkov display 12, truncated at Pomerance's
parameter H with his explicit truncation error, Frolenkov displays 15 and 21, then reduced
through display 10 and |τ(χ)| = √q, Frolenkov displays 13, 14 and 22, to √q/π times the sum of
|cos mα - cos mβ|/m at α = 2πM/q, β = 2π(N+1)/q; with Pomerance's choice of H the truncation
error fits in what the final bound leaves after Section 4. Class HARD.
REPAIR S58: 7 ≤ q added; FALSE without it at q = 3, M = N = 1, see the notes. -/
theorem odd_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  sorry

/-- Pomerance odd case: Section 4 applied to the truncated sum, then the final arithmetic.
PROVED from the LEAF `odd_truncated` and the hypothesis Section 4. -/
theorem odd_from_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (htr : ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)))
    (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  obtain ⟨H, hH, hK⟩ := htr
  have h1 := hK M N
  have h2 := (hS4 (2 * π * M / q) (2 * π * (N + 1) / q) H hH).le
  have hc : 0 ≤ sqrt q / π := div_nonneg (sqrt_nonneg _) pi_pos.le
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- Assembly: exactly `PV420Split1122.pomerance_even_case`, from `interval_le_two_initial`,
`even_initial` and the LEAF `even_truncated`. -/
theorem pomerance_even_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hL3 : ∀ (x : ℝ) (n : ℕ), 1 ≤ n → ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n))
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) + ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (heven : χ (-1) = 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  have htr := even_truncated χ hχ hq heven
  have a := even_initial χ hL3 htr (N + 1)
  have b := even_initial χ hL3 htr M
  have c := interval_le_two_initial χ M N
  have e : 2 * (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q) =
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by ring
  linarith

example : type_of% @pomerance_even_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_even_case := rfl

/-! ### Private helpers for `odd_small`

The bound is proved by periodicity: partial sums of a nontrivial character are `q`-periodic, so
every interval sum is at most twice the largest partial sum over one period, and for `q < 7` the
partial sums are read off the values of `χ` on the units. -/

/-- A product that vanishes against a nonzero element has a non-unit first factor. -/
private lemma not_isUnit_of_mul_eq_zero {q : ℕ} [NeZero q] {a b : ZMod q}
    (hab : a * b = 0) (hb : b ≠ 0) : ¬ IsUnit a := by
  rintro ⟨u, hu⟩
  apply hb
  have h1 : b = ↑u⁻¹ * (↑u * b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [h1, hu, hab, mul_zero]

/-- The sum of a nontrivial character over the `q` consecutive integers starting at `K` is zero. -/
private lemma block_sum_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (K : ℕ) :
    ∑ j ∈ range q, χ ((K + j : ℕ) : ZMod q) = 0 := by
  have hshift : ∑ j ∈ range q, χ ((j : ZMod q) + (K : ZMod q)) = ∑ a : ZMod q, χ a := by
    rw [← LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range (fun a => χ (a + (K : ZMod q)))]
    rw [show (∑ a : ZMod q, χ (a + (K : ZMod q))) = ∑ a : ZMod q, χ ((K : ZMod q) + a) from by
      exact sum_congr rfl fun a _ => by rw [add_comm]]
    exact Equiv.sum_comp (Equiv.addLeft (K : ZMod q)) (fun a => χ a)
  calc ∑ j ∈ range q, χ ((K + j : ℕ) : ZMod q)
      = ∑ j ∈ range q, χ ((j : ZMod q) + (K : ZMod q)) := by
        refine sum_congr rfl fun j _ => ?_
        rw [Nat.cast_add, add_comm]
    _ = ∑ a : ZMod q, χ a := hshift
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hne

/-- The sum of a nontrivial character over one complete period is zero. -/
private lemma period_sum_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    ∑ c ∈ range q, χ (c : ZMod q) = 0 := by
  simpa using block_sum_zero χ hne 0

/-- Partial sums of a nontrivial character are periodic with period `q`. -/
private lemma partial_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (K : ℕ) :
    ∑ m ∈ range (K + q), χ (m : ZMod q) = ∑ m ∈ range K, χ (m : ZMod q) := by
  rw [Finset.sum_range_add, block_sum_zero χ hne K, add_zero]

/-- Partial sums of a nontrivial character are periodic with period `q`, iterated. -/
private lemma partial_add_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (a t : ℕ) :
    ∑ m ∈ range (a + q * t), χ (m : ZMod q) = ∑ m ∈ range a, χ (m : ZMod q) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show a + q * (t + 1) = (a + q * t) + q from by ring, partial_period χ hne, ih]

/-- Every partial sum is bounded by the largest partial sum over one period. -/
private lemma partial_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    {B : ℝ} (hB : ∀ j < q, ‖∑ m ∈ range j, χ (m : ZMod q)‖ ≤ B) (K : ℕ) :
    ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤ B := by
  rw [show K = K % q + q * (K / q) from (Nat.mod_add_div K q).symm,
    partial_add_mul χ hne]
  exact hB _ (Nat.mod_lt _ (NeZero.pos q))

/-- An interval sum is at most twice the largest partial sum over one period. -/
private lemma interval_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    {B : ℝ} (hB : ∀ j < q, ‖∑ m ∈ range j, χ (m : ZMod q)‖ ≤ B) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤ 2 * B := by
  have h1 := interval_le_two_initial χ M N
  have h2 := partial_bound χ hne hB (N + 1)
  have h3 := partial_bound χ hne hB M
  linarith

/-- `χ(2)^2 = -1` modulo `5`. -/
private lemma five_sq (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    χ (2 : ZMod 5) * χ (2 : ZMod 5) = -1 := by
  have h1 : (-1 : ZMod 5) * (-1) = 1 := by simp
  have hmul : χ (-1) ^ 2 = 1 := by rw [sq, ← map_mul, h1, map_one]
  have hneg : χ (-1) = -1 := by
    rcases sq_eq_one_iff.mp hmul with h | h
    · exact absurd h hodd
    · exact h
  rw [← map_mul, show ((2 : ZMod 5) * 2) = -1 from by decide, hneg]

/-- `χ(2)χ(3) = 1` modulo `5`. -/
private lemma five_mul (χ : DirichletCharacter ℂ 5) :
    χ (2 : ZMod 5) * χ (3 : ZMod 5) = 1 := by
  rw [← map_mul, show ((2 : ZMod 5) * 3) = 1 from by decide, map_one]

/-- `χ(2)` is nonzero modulo `5`. -/
private lemma five_ne_zero (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    χ (2 : ZMod 5) ≠ 0 := by
  intro h
  have h1 := five_sq χ hodd
  rw [h, mul_zero] at h1
  exact absurd h1.symm (by norm_num)

/-- `χ(3) = -χ(2)` modulo `5`. -/
private lemma five_three (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    χ (3 : ZMod 5) = -χ (2 : ZMod 5) := by
  have ha := five_sq χ hodd
  have hb := five_mul χ
  have hne := five_ne_zero χ hodd
  have h1 : χ (2 : ZMod 5) * (-χ (2 : ZMod 5)) = 1 := by
    rw [mul_neg, ha]; ring
  exact mul_left_cancel₀ hne (by rw [hb, h1])

/-- `‖χ(2)‖ = 1` modulo `5`. -/
private lemma five_norm (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    ‖χ (2 : ZMod 5)‖ = 1 := by
  have ha := five_sq χ hodd
  have h2 : ‖χ (2 : ZMod 5)‖ ^ 2 = 1 := by
    rw [← norm_pow, sq, ha]; norm_num
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact h
  · have := norm_nonneg (χ (2 : ZMod 5)); rw [h] at this; norm_num at this

/-- `‖1 + χ(2)‖ = √2` modulo `5`. -/
private lemma five_one_add (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    ‖1 + χ (2 : ZMod 5)‖ = Real.sqrt 2 := by
  have ha := five_sq χ hodd
  have hsq2 : χ (2 : ZMod 5) ^ 2 = -1 := by rw [sq, ha]
  have hsq : (1 + χ (2 : ZMod 5)) ^ 2 = 2 * χ (2 : ZMod 5) := by
    calc (1 + χ (2 : ZMod 5)) ^ 2 = 1 + 2 * χ (2 : ZMod 5) + χ (2 : ZMod 5) ^ 2 := by ring
      _ = 2 * χ (2 : ZMod 5) := by rw [hsq2]; ring
  have h2 : ‖1 + χ (2 : ZMod 5)‖ ^ 2 = 2 := by
    rw [← norm_pow, hsq, norm_mul, five_norm χ hodd]
    norm_num
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- A primitive-looking evaluation of a partial sum with no dependence on `q`. -/
private lemma sum_range_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range 2, f m = f 0 + f 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

private lemma sum_range_three {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range 3, f m = f 0 + f 1 + f 2 := by
  rw [Finset.sum_range_succ, sum_range_two]

private lemma sum_range_four {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range 4, f m = f 0 + f 1 + f 2 + f 3 := by
  rw [Finset.sum_range_succ, sum_range_three]

private lemma sum_range_five {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range 5, f m = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [Finset.sum_range_succ, sum_range_four]

/-- `χ` vanishes at zero. -/
private lemma chi_zero {q : ℕ} [Nontrivial (ZMod q)] (χ : DirichletCharacter ℂ q) :
    χ (0 : ZMod q) = 0 :=
  MulChar.map_nonunit χ not_isUnit_zero

private lemma hB_three (χ : DirichletCharacter ℂ 3) :
    ∀ j < 3, ‖∑ m ∈ range j, χ (m : ZMod 3)‖ ≤ (1 : ℝ) := by
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  have h0 : χ (0 : ZMod 3) = 0 := chi_zero χ
  have h1 : χ (1 : ZMod 3) = 1 := MulChar.map_one χ
  intro j hj
  interval_cases j
  · rw [Finset.sum_range_zero, norm_zero]; norm_num
  · rw [Finset.sum_range_one, show ((0 : ℕ) : ZMod 3) = 0 from Nat.cast_zero, h0, norm_zero]
    norm_num
  · rw [sum_range_two, show ((0 : ℕ) : ZMod 3) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 3) = 1 from Nat.cast_one, h0, h1]
    simp

private lemma hB_four (χ : DirichletCharacter ℂ 4) :
    ∀ j < 4, ‖∑ m ∈ range j, χ (m : ZMod 4)‖ ≤ (1 : ℝ) := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  have h0 : χ (0 : ZMod 4) = 0 := chi_zero χ
  have h1 : χ (1 : ZMod 4) = 1 := MulChar.map_one χ
  have h2 : χ (2 : ZMod 4) = 0 :=
    MulChar.map_nonunit _ (not_isUnit_of_mul_eq_zero (a := 2) (b := 2)
      (by decide) (by decide))
  intro j hj
  interval_cases j
  · rw [Finset.sum_range_zero, norm_zero]; norm_num
  · rw [Finset.sum_range_one, show ((0 : ℕ) : ZMod 4) = 0 from Nat.cast_zero, h0, norm_zero]
    norm_num
  · rw [sum_range_two, show ((0 : ℕ) : ZMod 4) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 4) = 1 from Nat.cast_one, h0, h1]
    simp
  · rw [sum_range_three, show ((0 : ℕ) : ZMod 4) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 4) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 4) = 2 from Nat.cast_ofNat, h0, h1, h2]
    simp

private lemma hB_six (χ : DirichletCharacter ℂ 6) :
    ∀ j < 6, ‖∑ m ∈ range j, χ (m : ZMod 6)‖ ≤ (1 : ℝ) := by
  haveI : Fact (1 < 6) := ⟨by norm_num⟩
  have h0 : χ (0 : ZMod 6) = 0 := chi_zero χ
  have h1 : χ (1 : ZMod 6) = 1 := MulChar.map_one χ
  have h2 : χ (2 : ZMod 6) = 0 :=
    MulChar.map_nonunit _ (not_isUnit_of_mul_eq_zero (a := 2) (b := 3)
      (by decide) (by decide))
  have h3 : χ (3 : ZMod 6) = 0 :=
    MulChar.map_nonunit _ (not_isUnit_of_mul_eq_zero (a := 3) (b := 2)
      (by decide) (by decide))
  have h4 : χ (4 : ZMod 6) = 0 :=
    MulChar.map_nonunit _ (not_isUnit_of_mul_eq_zero (a := 4) (b := 3)
      (by decide) (by decide))
  intro j hj
  interval_cases j
  · rw [Finset.sum_range_zero, norm_zero]; norm_num
  · rw [Finset.sum_range_one, show ((0 : ℕ) : ZMod 6) = 0 from Nat.cast_zero, h0, norm_zero]
    norm_num
  · rw [sum_range_two, show ((0 : ℕ) : ZMod 6) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 6) = 1 from Nat.cast_one, h0, h1]
    simp
  · rw [sum_range_three, show ((0 : ℕ) : ZMod 6) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 6) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 6) = 2 from Nat.cast_ofNat, h0, h1, h2]
    simp
  · rw [sum_range_four, show ((0 : ℕ) : ZMod 6) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 6) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 6) = 2 from Nat.cast_ofNat,
      show ((3 : ℕ) : ZMod 6) = 3 from Nat.cast_ofNat, h0, h1, h2, h3]
    simp
  · rw [sum_range_five, show ((0 : ℕ) : ZMod 6) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 6) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 6) = 2 from Nat.cast_ofNat,
      show ((3 : ℕ) : ZMod 6) = 3 from Nat.cast_ofNat,
      show ((4 : ℕ) : ZMod 6) = 4 from Nat.cast_ofNat, h0, h1, h2, h3, h4]
    simp

private lemma hB_five (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) :
    ∀ j < 5, ‖∑ m ∈ range j, χ (m : ZMod 5)‖ ≤ Real.sqrt 2 := by
  haveI : Fact (1 < 5) := ⟨by norm_num⟩
  have h3 := five_three χ hodd
  have h1 := five_one_add χ hodd
  have h0 : χ (0 : ZMod 5) = 0 := chi_zero χ
  have hone : χ (1 : ZMod 5) = 1 := MulChar.map_one χ
  have h12 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  intro j hj
  interval_cases j
  · rw [Finset.sum_range_zero, norm_zero]; exact hnn
  · rw [Finset.sum_range_one, show ((0 : ℕ) : ZMod 5) = 0 from Nat.cast_zero, h0, norm_zero]
    exact hnn
  · rw [sum_range_two, show ((0 : ℕ) : ZMod 5) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 5) = 1 from Nat.cast_one, h0, hone]
    simp only [zero_add, norm_one]
    exact h12
  · rw [sum_range_three, show ((0 : ℕ) : ZMod 5) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 5) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 5) = 2 from Nat.cast_ofNat, h0, hone, zero_add]
    exact h1.le
  · rw [sum_range_four, show ((0 : ℕ) : ZMod 5) = 0 from Nat.cast_zero,
      show ((1 : ℕ) : ZMod 5) = 1 from Nat.cast_one,
      show ((2 : ℕ) : ZMod 5) = 2 from Nat.cast_ofNat,
      show ((3 : ℕ) : ZMod 5) = 3 from Nat.cast_ofNat, h0, hone, h3, zero_add]
    rw [show 1 + χ (2 : ZMod 5) + -χ (2 : ZMod 5) = 1 by ring, norm_one]
    exact h12

private lemma sqrt3_lb : (1.732 : ℝ) ≤ Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

private lemma sqrt5_lb : (2.236 : ℝ) ≤ Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]

private lemma inv_two_pi_lb : (0.159 : ℝ) ≤ 1 / (2 * π) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]

private lemma inv_pi_lb : (0.318 : ℝ) ≤ 1 / π := by
  rw [le_div_iff₀ pi_pos]
  nlinarith [Real.pi_lt_d4]

private lemma sqrt2_ub : 2 * Real.sqrt 2 ≤ (2.829 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

private lemma two_le_rhs_three :
    (2 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 3 * Real.log 3 +
      1 / π * Real.sqrt 3 * Real.log (Real.log 3) + Real.sqrt 3 := by
  have hlog3 : (1 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
  have hll : (0 : ℝ) ≤ Real.log (Real.log 3) := Real.log_nonneg hlog3.le
  have h1 := inv_two_pi_lb
  have hs := sqrt3_lb
  have hprod : (0.159 : ℝ) * 1.732 ≤ 1 / (2 * π) * Real.sqrt 3 :=
    mul_le_mul h1 hs (by norm_num) (by positivity)
  have hT2 : (0 : ℝ) ≤ 1 / π * Real.sqrt 3 * Real.log (Real.log 3) :=
    mul_nonneg (mul_nonneg (by linarith [inv_pi_lb]) (Real.sqrt_nonneg 3)) hll
  have hstep : (0.159 : ℝ) * 1.732 * 1 ≤ 1 / (2 * π) * Real.sqrt 3 * Real.log 3 := by
    calc (0.159 : ℝ) * 1.732 * 1 = (0.159 * 1.732) * 1 := by norm_num
      _ ≤ (1 / (2 * π) * Real.sqrt 3) * Real.log 3 :=
          mul_le_mul hprod hlog3.le (by norm_num) (by positivity)
  nlinarith [hstep, hT2, hs]

private lemma two_le_rhs_four :
    (2 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 4 * Real.log 4 +
      1 / π * Real.sqrt 4 * Real.log (Real.log 4) + Real.sqrt 4 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_gt_d9]
  have hll : (0 : ℝ) ≤ Real.log (Real.log 4) := Real.log_nonneg hlog4
  have hT1 : (0 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 4 * Real.log 4 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg 4)) (by linarith)
  have hT2 : (0 : ℝ) ≤ 1 / π * Real.sqrt 4 * Real.log (Real.log 4) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg 4)) hll
  linarith [hs]

private lemma two_le_rhs_six :
    (2 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 6 * Real.log 6 +
      1 / π * Real.sqrt 6 * Real.log (Real.log 6) + Real.sqrt 6 := by
  have hs : (2 : ℝ) ≤ Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_nonneg 6]
  have hlog6 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlog6_1 : (1 : ℝ) ≤ Real.log 6 := by
    have h : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
    have h46 : Real.log 4 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [Real.log_two_gt_d9, h, h46]
  have hll6 : (0 : ℝ) ≤ Real.log (Real.log 6) := Real.log_nonneg hlog6_1
  have hT1 : (0 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 6 * Real.log 6 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg 6)) hlog6
  have hT2 : (0 : ℝ) ≤ 1 / π * Real.sqrt 6 * Real.log (Real.log 6) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg 6)) hll6
  linarith

private lemma two_sqrt_two_le_rhs_five :
    (2 * Real.sqrt 2 : ℝ) ≤ 1 / (2 * π) * Real.sqrt 5 * Real.log 5 +
      1 / π * Real.sqrt 5 * Real.log (Real.log 5) + Real.sqrt 5 := by
  have hlog5 : (1.6 : ℝ) ≤ Real.log 5 := lt_trans (by norm_num) Real.log_five_gt_d9 |>.le
  have hpos5 : (0 : ℝ) < Real.log 5 := by linarith
  have hll : (0.37 : ℝ) ≤ Real.log (Real.log 5) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / Real.log 5 by positivity)
    rw [Real.log_div one_ne_zero hpos5.ne', Real.log_one] at h
    have h2 : 1 / Real.log 5 ≤ 1 / 1.6 := one_div_le_one_div_of_le (by norm_num) hlog5
    linarith
  have hs := sqrt5_lb
  have hA : (2.236 : ℝ) * 1.6 ≤ Real.sqrt 5 * Real.log 5 :=
    mul_le_mul hs hlog5 (by norm_num) (by positivity)
  have hB : (2.236 : ℝ) * 0.37 ≤ Real.sqrt 5 * Real.log (Real.log 5) :=
    mul_le_mul hs hll (by norm_num) (by positivity)
  have h1 := inv_two_pi_lb
  have h2 := inv_pi_lb
  have hT1 : (0.159 : ℝ) * (2.236 * 1.6) ≤ 1 / (2 * π) * (Real.sqrt 5 * Real.log 5) :=
    mul_le_mul h1 hA (by norm_num) (by positivity)
  have hT2 : (0.318 : ℝ) * (2.236 * 0.37) ≤
      1 / π * (Real.sqrt 5 * Real.log (Real.log 5)) :=
    mul_le_mul h2 hB (by norm_num) (by positivity)
  have hab : 2 * Real.sqrt 2 ≤ (2.829 : ℝ) := sqrt2_ub
  nlinarith [hT1, hT2, hs, hab]

/-- LEAF: Pomerance 2011 Theorem 1, odd case, for the small moduli q below 7 left out of
`odd_truncated`: q = 3, 4, 5, since q = 6 has no primitive character. A finite check of the
interval sums over one period, the largest norm being at most 2 against a bound above 2.08.
Class EASY. -/
theorem odd_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (hq7 : q < 7) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  have hq0 : 0 < q := NeZero.pos q
  have hq2 : 2 ≤ q := by omega
  have hne : χ ≠ 1 := by
    intro h
    rw [h] at hodd
    exact hodd (MulChar.one_apply (isUnit_one.neg))
  interval_cases q
  · refine absurd ?_ hodd
    rw [show (-1 : ZMod 2) = 1 from by decide]
    exact MulChar.map_one χ
  · push_cast
    have hb := interval_bound χ hne (hB_three χ) M N
    have hnum := two_le_rhs_three
    linarith
  · push_cast
    have hb := interval_bound χ hne (hB_four χ) M N
    have hnum := two_le_rhs_four
    linarith
  · push_cast
    have hb := interval_bound χ hne (hB_five χ hodd) M N
    have hnum := two_sqrt_two_le_rhs_five
    linarith
  · push_cast
    have hb := interval_bound χ hne (hB_six χ) M N
    have hnum := two_le_rhs_six
    linarith

/-- Assembly: exactly `PV420Split1122.pomerance_odd_case`, from `odd_from_truncated` and the
LEAF `odd_truncated` for q at least 7, and the LEAF `odd_small` below 7. -/
theorem pomerance_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q :=
  if h7 : 7 ≤ q then odd_from_truncated χ hS4 (odd_truncated χ hχ h7 hodd) M N
  else odd_small χ hχ hq (by omega) hodd M N

example : type_of% @pomerance_odd_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_odd_case := rfl

end LeanLab.HelfgottMajor.PVCases1122

#print axioms LeanLab.HelfgottMajor.PVCases1122.interval_le_two_initial
#print axioms LeanLab.HelfgottMajor.PVCases1122.even_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.even_initial
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_small
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_from_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.pomerance_even_case
#print axioms LeanLab.HelfgottMajor.PVCases1122.pomerance_odd_case

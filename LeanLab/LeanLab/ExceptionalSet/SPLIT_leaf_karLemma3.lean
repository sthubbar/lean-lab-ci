/-
Split of the sealed statement `leaf_karLemma3` of `LeanLab.ExceptionalSet.KaracubaSplit`,
Karacuba's Lemma 3: for `U > 0`, `q ≥ 1`, `α = a/q + θ/q²` with `(a, q) = 1`, `|θ| ≤ 1`
and every real `β`,

  `Σ_{x=1}^{P} min(U, 1/‖(α x + β)‖) ≤ 6 (U + q log q) (P/q + 1)`,

`‖·‖` being `nint`, the distance to the nearest integer, and `P/q` the integer quotient.

The split keeps the conclusion and cuts the parameters into the four ranges that need
different arguments:

* `leaf_karLemma3_unit`, `q = 1`: `α x + β` is then an integer shift of `θ x + β`, so every
  summand is at most `U` and the right side is `6 U (P + 1)`; the trivial bound `U P` gives it.
* `leaf_karLemma3_few`, `2 ≤ q` and `P < q`: there are fewer than `q` summands and the right
  side is `6 (U + q log q)` because `P/q = 0`. For `0 < |x - x'| < q` the number `a (x - x')/q`
  is at least `1/q` from an integer, so the distances to the nearest integer are `(1/4q)`
  separated and a spacing bound on `P` points of the circle gives the result.
* `leaf_karLemma3_many_large_U`, `2 ≤ q ≤ P` and `q log q ≤ U`: the `U` term of the right side
  dominates, `6 (U + q log q) ≤ 12 U`, so counting the `x` with `‖α x + β‖ < 1/(2U)`, at most
  `4q` per residue class modulo `q`, finishes.
* `leaf_karLemma3_many_small_U`, `2 ≤ q ≤ P` and `U < q log q`: the log term dominates. Read
  `x = r + q j` with `1 ≤ r ≤ q`. Then `α x + β = a j + (a r/q + β) + θ (r + q j)/q²`, the
  integer `a j` drops out of the distance, the `θ` term moves the point by at most `P/q²`, and
  the `q` centres `a r/q + β` are `1/q` apart; the sum is `(P/q + 1)` times a lattice sum
  bounded by `2U + 2q(1 + log q)`.

`leaf_karLemma3_split` is the statement of `leaf_karLemma3`, from these four leaves, with no
`sorry` and without using `leaf_karLemma3`; `sorry` sits on the four LEAF leaves only.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- Toolkit: elementary properties of `nint`. -/

private lemma nint_nonneg (y : ℝ) : 0 ≤ nint y :=
  le_min (Int.fract_nonneg y) (by linarith [Int.fract_lt_one y])

private lemma nint_le_half (y : ℝ) : nint y ≤ 1 / 2 := by
  unfold nint
  rcases le_total (Int.fract y) (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

private lemma nint_add_intCast (y : ℝ) (m : ℤ) : nint (y + m) = nint y := by
  unfold nint; rw [Int.fract_add_intCast]

private lemma nint_intCast_add (m : ℤ) (y : ℝ) : nint (m + y) = nint y := by
  rw [add_comm]; exact nint_add_intCast y m

private lemma self_eq_floor_add_fract (y : ℝ) : y = (⌊y⌋ : ℝ) + Int.fract y := by
  linarith [Int.self_sub_floor y]

private lemma exists_int_eq_abs_nint (y : ℝ) : ∃ m : ℤ, nint y = |y - m| := by
  have h0 : (0 : ℝ) ≤ Int.fract y := Int.fract_nonneg y
  have h1 : Int.fract y < 1 := Int.fract_lt_one y
  have hA : y - ((⌊y⌋ : ℤ) : ℝ) = Int.fract y := by
    push_cast; exact Int.self_sub_floor y
  have hB : y - (((⌊y⌋ + 1 : ℤ)) : ℝ) = Int.fract y - 1 := by
    push_cast; linarith [Int.self_sub_floor y]
  rcases le_total (Int.fract y) (1 / 2) with h | h
  · refine ⟨⌊y⌋, ?_⟩
    unfold nint
    rw [min_eq_left (by linarith : Int.fract y ≤ 1 - Int.fract y), hA, abs_of_nonneg h0]
  · refine ⟨⌊y⌋ + 1, ?_⟩
    unfold nint
    rw [min_eq_right (by linarith : 1 - Int.fract y ≤ Int.fract y), hB, abs_of_neg (by linarith)]
    ring

private lemma nint_le_abs_sub (y : ℝ) (m : ℤ) : nint y ≤ |y - m| := by
  have h0 : (0 : ℝ) ≤ Int.fract y := Int.fract_nonneg y
  have h1 : Int.fract y < 1 := Int.fract_lt_one y
  have hval : y - m = ((⌊y⌋ - m : ℤ) : ℝ) + Int.fract y := by
    have hy : y = (⌊y⌋ : ℝ) + Int.fract y := self_eq_floor_add_fract y
    conv_lhs => rw [hy]
    push_cast; ring
  rw [hval]
  unfold nint
  rcases le_or_gt 0 (⌊y⌋ - m) with hk0 | hk0
  · have hk0' : (0 : ℝ) ≤ ((⌊y⌋ - m : ℤ) : ℝ) := by exact_mod_cast hk0
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have hk1 : ⌊y⌋ - m ≤ -1 := by omega
    have hk1' : ((⌊y⌋ - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hk1
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

private lemma nint_sub_abs_le (a b : ℝ) : nint a - |b| ≤ nint (a + b) := by
  obtain ⟨m, hm⟩ := exists_int_eq_abs_nint (a + b)
  have h1 : nint a ≤ |a - m| := nint_le_abs_sub a m
  have h2 : |a - m| ≤ |a + b - m| + |b| := by
    have h3 : a - m = (a + b - m) + (-b) := by ring
    calc |a - m| = |(a + b - m) + (-b)| := by rw [h3]
      _ ≤ |a + b - m| + |-b| := abs_add_le _ _
      _ = |a + b - m| + |b| := by rw [abs_neg]
  rw [← hm] at h2
  linarith

/-- Toolkit: a rational `m/q` with `q ∤ m` is at distance at least `1/q` from every integer. -/
private lemma one_div_le_nint_int_div (m : ℤ) {q : ℕ} (hq : 2 ≤ q) (hm : ¬ (q : ℤ) ∣ m) :
    1 / (q : ℝ) ≤ nint ((m : ℝ) / q) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (show 0 < q by omega)
  have hfac : Int.fract ((m : ℝ) / q) = (((m % q : ℤ)) : ℝ) / q :=
    Int.fract_div_intCast_eq_div_intCast_mod
  have hmod0 : 0 ≤ m % q := Int.emod_nonneg m hqZ.ne'
  have hmod1 : m % q < (q : ℤ) := Int.emod_lt_of_pos m hqZ
  have hne : m % q ≠ 0 := by
    intro h
    apply hm
    refine ⟨m / q, ?_⟩
    calc m = m % (q : ℤ) + (q : ℤ) * (m / (q : ℤ)) := (Int.emod_add_mul_ediv m (q : ℤ)).symm
      _ = (q : ℤ) * (m / (q : ℤ)) := by rw [h, zero_add]
  have hr1 : (1 : ℤ) ≤ m % q := by omega
  have hrq : m % q ≤ (q : ℤ) - 1 := by omega
  have hr1' : (1 : ℝ) ≤ (((m % q : ℤ)) : ℝ) := by exact_mod_cast hr1
  have hrq' : (((m % q : ℤ)) : ℝ) ≤ (q : ℝ) - 1 := by
    have : (((m % q : ℤ)) : ℝ) ≤ (((q : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hrq
    push_cast at this; linarith
  rw [nint, hfac, le_min_iff]
  constructor
  · rw [div_le_div_iff_of_pos_right hq0]; linarith
  · have h4 : ((q : ℝ) - 1) / (q : ℝ) = 1 - 1 / (q : ℝ) := by
      field_simp
    have h5 : (((m % q : ℤ)) : ℝ) / (q : ℝ) ≤ ((q : ℝ) - 1) / (q : ℝ) := by
      rw [div_le_div_iff_of_pos_right hq0]; exact hrq'
    rw [h4] at h5
    linarith

/-- Toolkit: for `(a,q) = 1` and `0 < d < q` the fraction `a d / q` is at distance at least
`1/q` from every integer. -/
private lemma one_div_le_nint_gcd_mul (a : ℤ) {q : ℕ} (hq : 2 ≤ q) (hgcd : Int.gcd a q = 1)
    {d : ℕ} (hd0 : 0 < d) (hdq : d < q) :
    1 / (q : ℝ) ≤ nint (((a : ℝ) * (d : ℝ)) / q) := by
  have hnot : ¬ (q : ℤ) ∣ a * (d : ℤ) := by
    intro hdvd
    have hgcd' : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact hgcd
    have hqdvd : (q : ℤ) ∣ (d : ℤ) := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hgcd'
    obtain ⟨c, hc⟩ := hqdvd
    have hq1 : (1 : ℤ) ≤ (q : ℤ) := by omega
    have hd0' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd0
    have hdq' : (d : ℤ) < (q : ℤ) := by exact_mod_cast hdq
    rcases lt_or_gt_of_ne (show c ≠ 0 by intro h; rw [h, mul_zero] at hc; omega) with hc0 | hc0
    · nlinarith
    · nlinarith
  have h := one_div_le_nint_int_div (a * (d : ℤ)) hq hnot
  convert h using 2
  push_cast; ring


/-- Toolkit: at most `A + 1` natural numbers are `≤ A` (for `A > -1`). -/
private lemma card_range_filter_le (q : ℕ) (A : ℝ) (hA : -1 ≤ A) :
    ((((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A)).card : ℝ)) ≤ A + 1 := by
  rcases lt_or_ge A 0 with hneg | hneg
  · have hempty : (Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n _ hn
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hsub : (Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A) ⊆ Finset.range (⌊A⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_range]
      have h1 : n ≤ ⌊A⌋₊ := Nat.le_floor hn.2
      omega
    have h3 : ((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A)).card ≤ ⌊A⌋₊ + 1 := by
      simpa using Finset.card_le_card hsub
    have h5 : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le hneg
    have h6 : ((((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A)).card : ℝ))
        ≤ (⌊A⌋₊ : ℝ) + 1 := by
      have h7 : (((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ A)).card : ℝ)
          ≤ (((⌊A⌋₊ + 1 : ℕ)) : ℝ) := by exact_mod_cast h3
      simpa using h7
    linarith

/-- Toolkit: at most `q - B` natural numbers below `q` are `≥ B`. -/
private lemma card_range_filter_ge (q : ℕ) (B : ℝ) (hB : B ≤ (q : ℝ)) :
    ((((Finset.range q).filter (fun n : ℕ => B ≤ (n : ℝ))).card : ℝ)) ≤ (q : ℝ) - B := by
  have hset : (Finset.range q).filter (fun n : ℕ => B ≤ (n : ℝ)) = Finset.Ico ⌈B⌉₊ q := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro h
      exact ⟨Nat.ceil_le.mpr h.2, h.1⟩
    · intro h
      have h1 : B ≤ ((⌈B⌉₊ : ℕ) : ℝ) := Nat.le_ceil B
      have h2 : ((⌈B⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1
      exact ⟨h.2, by linarith⟩
  rw [hset]
  by_cases hBq : ⌈B⌉₊ ≤ q
  · have hc : (Finset.Ico ⌈B⌉₊ q).card = q - ⌈B⌉₊ := Nat.card_Ico _ _
    have hcast : ((Finset.Ico ⌈B⌉₊ q).card : ℝ) = (q : ℝ) - ((⌈B⌉₊ : ℕ) : ℝ) := by
      rw [hc]
      push_cast [hBq]
      ring
    have h2 : ((⌈B⌉₊ : ℕ) : ℝ) ≥ B := Nat.le_ceil B
    linarith
  · have hempty : Finset.Ico ⌈B⌉₊ q = ∅ := by
      rw [Finset.Ico_eq_empty_iff]; omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-- Toolkit: count of `x ∈ [1,P]` (`P ≤ q`) with `nint (a x / q + β) ≤ s`. -/
private lemma card_nint_apart_le (a : ℤ) {q : ℕ} (hq : 2 ≤ q) (hgcd : Int.gcd a q = 1)
    (β : ℝ) {P : ℕ} (hP : P ≤ q) {s : ℝ} (hs : 0 ≤ s) :
    ((((Finset.Icc 1 P).filter
      (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s)).card : ℝ))
      ≤ 2 * s * (q : ℝ) + 1 := by
  rcases le_or_gt (1 / 2 : ℝ) s with hhalf | hhalf
  · have h0 : ((Finset.Icc 1 P).filter
        (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s)).card ≤ P := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Icc]; omega
    have h1 : (((Finset.Icc 1 P).filter
        (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s)).card : ℝ) ≤ (P : ℝ) := by
      exact_mod_cast h0
    have h2 : (P : ℝ) ≤ (q : ℝ) := by exact_mod_cast hP
    have h3 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  · have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
    have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (show 0 < q by omega)
    set K : ℤ := ⌊(q : ℝ) * β⌋ with hK
    set r : ℝ := Int.fract ((q : ℝ) * β) with hr
    have hr0 : 0 ≤ r := Int.fract_nonneg _
    have hr1 : r < 1 := Int.fract_lt_one _
    have hKr : (K : ℝ) + r = (q : ℝ) * β := Int.floor_add_fract _
    have key : ∀ x : ℕ, (a : ℝ) * (x : ℝ) / (q : ℝ) + β
        = (((((a * (x : ℤ) + K) % (q : ℤ) : ℤ)) : ℝ) + r) / (q : ℝ)
          + ((((a * (x : ℤ) + K) / (q : ℤ) : ℤ)) : ℝ) := by
      intro x
      have hm : ((a * (x : ℤ) + K : ℤ) : ℝ)
          = (((((a * (x : ℤ) + K) % (q : ℤ) : ℤ)) : ℝ))
            + (q : ℝ) * ((((a * (x : ℤ) + K) / (q : ℤ) : ℤ)) : ℝ) := by
        have h := Int.emod_add_mul_ediv (a * (x : ℤ) + K) (q : ℤ)
        have h' : ((a * (x : ℤ) + K : ℤ) : ℝ)
            = ((((a * (x : ℤ) + K) % (q : ℤ)
                + (q : ℤ) * ((a * (x : ℤ) + K) / (q : ℤ)) : ℤ)) : ℝ) := by rw [h]
        rw [h']; push_cast; ring
      have hnum : (a : ℝ) * (x : ℝ) + (q : ℝ) * β
          = (((((a * (x : ℤ) + K) % (q : ℤ) : ℤ)) : ℝ) + r
              + (q : ℝ) * ((((a * (x : ℤ) + K) / (q : ℤ) : ℤ)) : ℝ)) := by
        rw [← hKr]
        calc (a : ℝ) * (x : ℝ) + ((K : ℝ) + r)
            = ((a * (x : ℤ) + K : ℤ) : ℝ) + r := by push_cast; ring
          _ = _ := by rw [hm]; ring
      rw [show (a : ℝ) * (x : ℝ) / (q : ℝ) + β
            = ((a : ℝ) * (x : ℝ) + (q : ℝ) * β) / (q : ℝ) by field_simp]
      rw [hnum]
      field_simp
    have disj : ∀ x : ℕ, nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s →
        ((((a * (x : ℤ) + K) % (q : ℤ) : ℤ)) : ℝ) ≤ s * (q : ℝ) - r ∨
        (q : ℝ) - r - s * (q : ℝ) ≤ ((((a * (x : ℤ) + K) % (q : ℤ) : ℤ)) : ℝ) := by
      intro x hx
      set u : ℤ := (a * (x : ℤ) + K) % (q : ℤ) with hu
      have hu1 : u < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
      have hx' : nint (((u : ℝ) + r) / (q : ℝ)) ≤ s := by
        have h0 : ((a : ℝ) * (x : ℝ) / (q : ℝ) + β)
            = (((u : ℝ) + r) / (q : ℝ)) + ((((a * (x : ℤ) + K) / (q : ℤ) : ℤ)) : ℝ) := by
          have hk := key x
          rw [← hu] at hk
          exact hk
        rw [h0] at hx
        rwa [nint_add_intCast] at hx
      obtain ⟨j, hj⟩ := exists_int_eq_abs_nint (((u : ℝ) + r) / (q : ℝ))
      rw [hj] at hx'
      have hu0 : (0 : ℤ) ≤ u := Int.emod_nonneg _ hqZ.ne'
      have hu1'' : u ≤ (q : ℤ) - 1 := by omega
      have hu1' : (u : ℝ) ≤ (q : ℝ) - 1 := by
        have : ((u : ℤ) : ℝ) ≤ (((q : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hu1''
        push_cast at this; linarith
      have hz0 : (0 : ℝ) ≤ ((u : ℝ) + r) / (q : ℝ) := by positivity
      have hz1 : ((u : ℝ) + r) / (q : ℝ) < 1 := by
        rw [div_lt_iff₀ hq0]; linarith
      have hj0 : (0 : ℤ) ≤ j := by
        rcases lt_or_ge j 0 with h | h
        · exfalso
          have hj1 : (j : ℝ) ≤ -1 := by
            have hh : j ≤ -1 := by omega
            exact_mod_cast hh
          have hge : |((u : ℝ) + r) / (q : ℝ) - (j : ℝ)| ≥ 1 := by
            rw [abs_of_nonneg (by linarith)]
            linarith
          linarith
        · exact h
      have hj1 : j ≤ 1 := by
        rcases lt_or_ge 1 j with h | h
        · exfalso
          have h2 : (2 : ℝ) ≤ (j : ℝ) := by
            have hh : (2 : ℤ) ≤ j := by omega
            exact_mod_cast hh
          have hge : |((u : ℝ) + r) / (q : ℝ) - (j : ℝ)| ≥ 1 := by
            have hneg : ((u : ℝ) + r) / (q : ℝ) - (j : ℝ) < 0 := by linarith
            rw [abs_of_neg hneg]
            linarith
          linarith
        · exact h
      interval_cases j
      · left
        have h3 : ((u : ℝ) + r) / (q : ℝ) ≤ s := by
          simpa using (abs_le.mp hx').2
        have h4 : (u : ℝ) + r ≤ s * (q : ℝ) := (div_le_iff₀ hq0).mp h3
        linarith
      · right
        have h1 : 1 - ((u : ℝ) + r) / (q : ℝ) ≤ s := by
          have h2 := neg_abs_le (((u : ℝ) + r) / (q : ℝ) - ((1 : ℤ) : ℝ))
          push_cast at h2
          linarith
        have h2 : 1 - ((u : ℝ) + r) / (q : ℝ) = ((q : ℝ) - ((u : ℝ) + r)) / (q : ℝ) := by
          field_simp
        rw [h2] at h1
        have h4 : (q : ℝ) - ((u : ℝ) + r) ≤ s * (q : ℝ) := (div_le_iff₀ hq0).mp h1
        linarith
    set S : Finset ℕ :=
      (Finset.Icc 1 P).filter (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s) with hS
    have hSx : ∀ x ∈ S, 1 ≤ x ∧ x ≤ P := by
      intro x hx
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hx
      exact hx.1
    have hSn : ∀ x ∈ S, nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ s := by
      intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact hx.2
    have hinj : ∀ x ∈ S, ∀ y ∈ S,
        (a * (x : ℤ) + K) % (q : ℤ) = (a * (y : ℤ) + K) % (q : ℤ) → x = y := by
      intro x hx y hy hxy
      by_contra hne
      have hx1 := hSx x hx
      have hy1 := hSx y hy
      have hdvd : (q : ℤ) ∣ a * ((x : ℤ) - (y : ℤ)) := by
        have h1 := Int.emod_add_mul_ediv (a * (x : ℤ) + K) (q : ℤ)
        have h2 := Int.emod_add_mul_ediv (a * (y : ℤ) + K) (q : ℤ)
        have e1 : (q : ℤ) * ((a * (x : ℤ) + K) / (q : ℤ))
            = (a * (x : ℤ) + K) - ((a * (x : ℤ) + K) % (q : ℤ)) := by linarith
        have e2 : (q : ℤ) * ((a * (y : ℤ) + K) / (q : ℤ))
            = (a * (y : ℤ) + K) - ((a * (y : ℤ) + K) % (q : ℤ)) := by linarith
        refine ⟨((a * (x : ℤ) + K) / (q : ℤ)) - ((a * (y : ℤ) + K) / (q : ℤ)), ?_⟩
        have h5 : (q : ℤ) * (((a * (x : ℤ) + K) / (q : ℤ)) - ((a * (y : ℤ) + K) / (q : ℤ)))
            = (a * (x : ℤ) + K) - (a * (y : ℤ) + K)
              - (((a * (x : ℤ) + K) % (q : ℤ)) - ((a * (y : ℤ) + K) % (q : ℤ))) := by
          rw [mul_sub, e1, e2]; ring
        rw [h5, hxy]; ring
      have hlt : ∀ z : ℕ, 1 ≤ z → z < q → ¬ (q : ℤ) ∣ a * (z : ℤ) := by
        intro z hz0 hzq hdvd'
        have hgcd' : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact hgcd
        have hqdvd : (q : ℤ) ∣ (z : ℤ) := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd' hgcd'
        obtain ⟨c, hc⟩ := hqdvd
        have hz0' : (1 : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz0
        have hzq' : (z : ℤ) < (q : ℤ) := by exact_mod_cast hzq
        have hq1 : (1 : ℤ) ≤ (q : ℤ) := by omega
        rcases lt_or_gt_of_ne (show c ≠ 0 by intro h; rw [h, mul_zero] at hc; omega) with hc0 | hc0
        · nlinarith
        · nlinarith
      rcases lt_or_gt_of_ne hne with hlt' | hlt'
      · have hcon := hlt (y - x) (by omega) (by omega)
        refine hcon ?_
        have hcast : (((y - x : ℕ) : ℤ)) = ((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) := by
          push_cast [show x ≤ y by omega]; ring
        rw [hcast]
        have hneg : a * (((y : ℕ) : ℤ) - ((x : ℕ) : ℤ)) = -(a * ((x : ℤ) - (y : ℤ))) := by ring
        rw [hneg]
        exact hdvd.neg_right
      · have hcon := hlt (x - y) (by omega) (by omega)
        refine hcon ?_
        have hcast : (((x - y : ℕ) : ℤ)) = ((x : ℕ) : ℤ) - ((y : ℕ) : ℤ) := by
          push_cast [show y ≤ x by omega]; ring
        rw [hcast]
        exact hdvd
    set u : ℕ → ℕ := fun x => ((a * (x : ℤ) + K) % (q : ℤ)).toNat with hu'
    have hu_val : ∀ x : ℕ, (u x : ℝ) = (((((a * (x : ℤ) + K) % (q : ℤ)) : ℤ)) : ℝ) := by
      intro x
      have h1 : 0 ≤ (a * (x : ℤ) + K) % (q : ℤ) := Int.emod_nonneg _ hqZ.ne'
      have h2 : ((u x : ℕ) : ℤ) = (a * (x : ℤ) + K) % (q : ℤ) := by
        simp only [hu']; exact Int.toNat_of_nonneg h1
      have h3 : ((u x : ℕ) : ℝ) = ((((u x : ℕ)) : ℤ) : ℝ) := by push_cast; ring
      rw [h3, h2]
    have hu_lt : ∀ x : ℕ, u x < q := by
      intro x
      have h1 : (a * (x : ℤ) + K) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
      have h2 : (((u x : ℕ)) : ℤ) < (q : ℤ) := by
        rw [show (((u x : ℕ)) : ℤ) = (a * (x : ℤ) + K) % (q : ℤ) from by
          simp only [hu']; exact Int.toNat_of_nonneg (Int.emod_nonneg _ hqZ.ne')]
        exact h1
      exact_mod_cast h2
    have hinj2 : ∀ x ∈ S, ∀ y ∈ S, u x = u y → x = y := by
      intro x hx y hy hxy
      refine hinj x hx y hy ?_
      have h1 := hu_val x
      have h2 := hu_val y
      have h3 : (u x : ℝ) = (u y : ℝ) := by rw [hxy]
      have h4 : ((u x : ℝ)) = ((u y : ℝ)) := h3
      rw [h1, h2] at h4
      exact_mod_cast h4
    have hsub : S.image u ⊆ (Finset.range q).filter
        (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r ∨ (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ)) := by
      intro n hn
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hu_lt x), ?_⟩
      have hdisj := disj x (hSn x hxS)
      have hv := hu_val x
      rw [← hv] at hdisj
      exact hdisj
    have hcard : ((S.card : ℝ)) ≤
        ((((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r)).card : ℝ))
        + ((((Finset.range q).filter
            (fun n : ℕ => (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ))).card : ℝ)) := by
      have himg : (S.image u).card = S.card := Finset.card_image_of_injOn hinj2
      have h1 : ((S.image u).card : ℝ) ≤
          ((((Finset.range q).filter
            (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r
              ∨ (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ))).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((((Finset.range q).filter
            (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r
              ∨ (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ))).card : ℝ))
          ≤ ((((Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r)).card : ℝ))
            + ((((Finset.range q).filter
              (fun n : ℕ => (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ))).card : ℝ)) := by
        have hset : (Finset.range q).filter
            (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r
              ∨ (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ))
            = (Finset.range q).filter (fun n : ℕ => (n : ℝ) ≤ s * (q : ℝ) - r)
              ∪ (Finset.range q).filter
                (fun n : ℕ => (q : ℝ) - r - s * (q : ℝ) ≤ (n : ℝ)) := by
          rw [Finset.filter_or]
        rw [hset]
        exact_mod_cast Finset.card_union_le _ _
      rw [himg] at h1
      linarith
    have hb1 := card_range_filter_le q (s * (q : ℝ) - r) (by nlinarith [hs, hq0.le, hr1])
    have hb2 := card_range_filter_ge q ((q : ℝ) - r - s * (q : ℝ)) (by nlinarith)
    have : (S.card : ℝ) ≤ 2 * s * (q : ℝ) + 1 := by linarith
    simpa [hS] using this


/-- Toolkit: telescoping sum of consecutive differences over `Icc`. -/
private lemma sum_Icc_sub_telescope (f : ℕ → ℝ) {m q : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q + 1) :
    ∑ k ∈ Finset.Icc m q, (f (k-1) - f k) = f (m-1) - f q := by
  have h1 : Finset.Icc m q = Finset.Ico m (q+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 := Finset.sum_range_sub (fun i => f (m - 1 + i)) (q + 1 - m)
  have hconv : ∑ i ∈ Finset.range (q + 1 - m), (f (m + i - 1) - f (m + i))
      = - ∑ i ∈ Finset.range (q + 1 - m), (f (m - 1 + (i + 1)) - f (m - 1 + i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h3 : m - 1 + (i + 1) = m + i := by omega
    have h4 : m - 1 + i = m + i - 1 := by omega
    rw [h3, h4]; ring
  rw [hconv, h2]
  have h5 : m - 1 + (q + 1 - m) = q := by omega
  have h6 : m - 1 + 0 = m - 1 := by omega
  rw [h5, h6]
  ring

/-- Toolkit: `1/k ≤ log k - log (k-1)` for `k ≥ 2`. -/
private lemma one_div_le_log_ratio {k : ℕ} (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ≤ Real.log (k : ℝ) - Real.log (((k - 1 : ℕ)) : ℝ) := by
  have hcast : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    push_cast [show 1 ≤ k by omega]; ring
  have hk0 : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hpos : (0 : ℝ) < ((k : ℝ) - 1) / (k : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  have hlog : Real.log (((k : ℝ) - 1) / (k : ℝ))
      = Real.log ((k : ℝ) - 1) - Real.log (k : ℝ) :=
    Real.log_div (by linarith) (ne_of_gt hk0)
  rw [hlog] at h
  have h2 : ((k : ℝ) - 1) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
    field_simp; ring
  rw [h2] at h
  rw [hcast]
  linarith

/-- Toolkit: the harmonic sum up to `m` is at most `1 + log m`. -/
private lemma harmonic_le_log (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (m : ℝ) := by
  have hsplit : Finset.Icc 1 m = insert 1 (Finset.Icc 2 m) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 m := by simp
  rw [hsplit, Finset.sum_insert hnot]
  have htel : ∑ k ∈ Finset.Icc 2 m, (Real.log (k : ℝ) - Real.log (((k - 1 : ℕ)) : ℝ))
      = Real.log (m : ℝ) - Real.log 1 := by
    have htel' := sum_Icc_sub_telescope (fun k => Real.log (k : ℝ)) (m := 2) (q := m)
      (by omega) (by omega)
    have hneg : ∑ k ∈ Finset.Icc 2 m, (Real.log (k : ℝ) - Real.log (((k - 1 : ℕ)) : ℝ))
        = - ∑ k ∈ Finset.Icc 2 m, (Real.log (((k - 1 : ℕ)) : ℝ) - Real.log (k : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hneg, htel']
    have h2 : (((2 - 1 : ℕ)) : ℝ) = 1 := by norm_num
    rw [h2, Real.log_one]
    ring
  have hle : ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / (k : ℝ)
      ≤ ∑ k ∈ Finset.Icc 2 m, (Real.log (k : ℝ) - Real.log (((k - 1 : ℕ)) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact one_div_le_log_ratio (by omega)
  rw [htel] at hle
  simp only [Real.log_one, sub_zero] at hle
  linarith

set_option maxHeartbeats 1000000 in
/-- Toolkit: the Abel summation bound from the counting bound. -/
private lemma sum_min_le (S : Finset ℕ) (n : ℕ → ℝ) (U : ℝ) (hU0 : 0 < U) {q : ℕ} (hq : 2 ≤ q)
    (hn0 : ∀ x ∈ S, 0 ≤ n x) (hn1 : ∀ x ∈ S, n x ≤ 1 / 2)
    (hcount : ∀ t : ℝ, 0 ≤ t → ((S.filter (fun x => n x ≤ t)).card : ℝ) ≤ 2 * t * (q : ℝ) + 3)
    (g b : ℕ → ℝ) (hg0 : g 0 = U)
    (hgk : ∀ k : ℕ, 1 ≤ k → g k = min U ((2 * (q:ℝ)) / (k : ℝ)))
    (hbv : ∀ k : ℕ, b k = (k : ℝ) / (2 * (q : ℝ))) :
    ∑ x ∈ S, min U (1 / n x) ≤ 4 * U + 2 * (q : ℝ) * Real.log q + 2 * (S.card : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  have hbmono : ∀ k l : ℕ, k ≤ l → b k ≤ b l := by
    intro k l hkl
    rw [hbv, hbv]
    have h1 : ((k : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    exact (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * (q:ℝ))).mpr h1
  have hdiff_nonneg : ∀ k : ℕ, 1 ≤ k → 0 ≤ g (k-1) - g k := by
    intro k hk
    rcases eq_or_lt_of_le hk with h | h
    · subst h
      rw [hg0, hgk 1 le_rfl]
      simp
    · have hk1 : 1 ≤ k - 1 := by omega
      rw [hgk (k-1) hk1, hgk k hk]
      have h1 : ((2 * (q:ℝ)) / (k : ℝ)) ≤ ((2 * (q:ℝ)) / ((k-1 : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : ((k-1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          have h' : k - 1 ≤ k := by omega
          exact_mod_cast h'
        nlinarith
      exact sub_nonneg.mpr (min_le_min_left _ h1)
  have hdiff_le : ∀ k : ℕ, 2 ≤ k →
      g (k-1) - g k ≤ (2 * (q:ℝ)) / (((k-1 : ℕ) : ℝ) * (k : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k - 1 := by omega
    rw [hgk (k-1) hk1, hgk k (by omega)]
    have hx : ((2 * (q:ℝ)) / (k : ℝ)) ≤ ((2 * (q:ℝ)) / ((k-1 : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : ((k-1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        have h' : k - 1 ≤ k := by omega
        exact_mod_cast h'
      nlinarith
    have key : ∀ x y : ℝ, y ≤ x → min U x - min U y ≤ x - y := by
      intro x y hxy
      rcases le_total x U with hx | hx <;> rcases le_total y U with hy | hy
      · rw [min_eq_right hx, min_eq_right hy]; try linarith
      · rw [min_eq_right hx, min_eq_left hy]; try linarith
      · rw [min_eq_left hx, min_eq_right hy]; try linarith
      · rw [min_eq_left hx, min_eq_left hy]; try linarith
    have hlip := key _ _ hx
    have heq : ((2 * (q:ℝ)) / ((k-1 : ℕ) : ℝ)) - ((2 * (q:ℝ)) / (k : ℝ))
        = (2 * (q:ℝ)) / (((k-1 : ℕ) : ℝ) * (k : ℝ)) := by
      have hkc : ((k:ℝ) - ((k-1 : ℕ) : ℝ)) = 1 := by
        push_cast [show 1 ≤ k by omega]; ring
      field_simp
      linarith
    linarith
  have hpt : ∀ x ∈ S, min U (1 / n x) ≤
      (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * (if n x ≤ b k then (1:ℝ) else 0)) + g q := by
    intro x hxS
    have ht0 := hn0 x hxS
    have ht1 := hn1 x hxS
    have hPq : n x ≤ b q := by
      rw [hbv]
      rw [show ((q:ℝ) / (2 * (q:ℝ))) = 1/2 by field_simp]
      exact ht1
    have hne : ((Finset.Icc 1 q).filter (fun k => n x ≤ b k)).Nonempty :=
      ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_refl q⟩, hPq⟩⟩
    set k0 := ((Finset.Icc 1 q).filter (fun k => n x ≤ b k)).min' hne with hk0
    have hk0mem : k0 ∈ (Finset.Icc 1 q).filter (fun k => n x ≤ b k) := Finset.min'_mem _ _
    have hk0P : n x ≤ b k0 := (Finset.mem_filter.mp hk0mem).2
    have hk0Icc : 1 ≤ k0 ∧ k0 ≤ q := Finset.mem_Icc.mp (Finset.mem_filter.mp hk0mem).1
    have hk0min : ∀ k ∈ Finset.Icc 1 q, n x ≤ b k → k0 ≤ k := by
      intro k hk hPk
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hk, hPk⟩)
    have hK : (Finset.Icc 1 q).filter (fun k => n x ≤ b k) = Finset.Icc k0 q := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro h
        exact ⟨hk0min k (Finset.mem_Icc.mpr h.1) h.2, h.1.2⟩
      · intro h
        exact ⟨⟨by omega, h.2⟩, le_trans hk0P (hbmono k0 k h.1)⟩
    have hsum_eq : (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * (if n x ≤ b k then (1:ℝ) else 0))
        = g (k0-1) - g q := by
      have hstep : (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * (if n x ≤ b k then (1:ℝ) else 0))
          = ∑ k ∈ (Finset.Icc 1 q).filter (fun k => n x ≤ b k), (g (k-1) - g k) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hkb : n x ≤ b k <;> simp [hkb]
      rw [hstep, hK, sum_Icc_sub_telescope g hk0Icc.1 (by omega)]
    rw [hsum_eq]
    rcases eq_or_lt_of_le hk0Icc.1 with h1 | h1
    · rw [← h1, hg0]
      have hle : min U (1 / n x) ≤ U := min_le_left _ _
      linarith
    · have hk0ge : 2 ≤ k0 := by omega
      have hprev : ¬ (n x ≤ b (k0-1)) := by
        intro hcon
        have h2 := hk0min (k0-1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hcon
        omega
      rw [hbv] at hprev
      push_neg at hprev
      rw [hgk (k0-1) (by omega)]
      have h2 : 1 / n x ≤ (2 * (q:ℝ)) / ((k0-1 : ℕ) : ℝ) := by
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · rw [← h0]
          simp only [div_zero]
          positivity
        · have hk0pos : (0:ℝ) < ((k0-1 : ℕ) : ℝ) := by
            have : 0 < k0 - 1 := by omega
            exact_mod_cast this
          rw [div_le_div_iff₀ h0 hk0pos]
          have hb' : ((k0-1 : ℕ) : ℝ) / (2 * (q:ℝ)) < n x := hprev
          rw [div_lt_iff₀ (by positivity)] at hb'
          rw [one_mul]
          linarith
      have h2' : min U (1 / n x) ≤ min U ((2 * (q:ℝ)) / ((k0-1 : ℕ) : ℝ)) :=
        min_le_min_left U h2
      linarith
  have hstep1 : ∑ x ∈ S, min U (1 / n x)
      ≤ ∑ x ∈ S, ((∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * (if n x ≤ b k then (1:ℝ) else 0)) + g q) :=
    Finset.sum_le_sum hpt
  have hstep2 : ∑ x ∈ S, ((∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * (if n x ≤ b k then (1:ℝ) else 0)) + g q)
      = (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((S.filter (fun x => n x ≤ b k)).card : ℝ))
        + (S.card : ℝ) * g q := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_boole]
  have hD : ∀ k ∈ Finset.Icc 1 q, ((S.filter (fun x => n x ≤ b k)).card : ℝ) ≤ (k : ℝ) + 3 := by
    intro k hk
    have hb0 : 0 ≤ b k := by rw [hbv]; positivity
    have h1 := hcount (b k) hb0
    have hbk : 2 * b k * (q:ℝ) = (k:ℝ) := by
      rw [hbv]; field_simp
    linarith
  have hstep3 : (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((S.filter (fun x => n x ≤ b k)).card : ℝ))
      ≤ ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) + 3) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    exact mul_le_mul_of_nonneg_left (hD k hk) (hdiff_nonneg k (Finset.mem_Icc.mp hk).1)
  have hsplit : ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) + 3)
      = (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) - 1))
        + 4 * ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have htel : ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) = g 0 - g q :=
    sum_Icc_sub_telescope g (le_refl 1) (by omega)
  have hgq_le : g q ≤ 2 := by
    rw [hgk q (by omega)]
    have h1 : ((2 * (q:ℝ)) / (q:ℝ)) = 2 := by field_simp
    rw [h1]
    exact min_le_right _ _
  have hgq0 : 0 ≤ g q := by
    rw [hgk q (by omega)]
    exact le_min (le_of_lt hU0) (by positivity)
  have hpart1 : ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) - 1)
      ≤ 2 * (q:ℝ) * Real.log q := by
    have hsubset : Finset.Icc 1 q = insert 1 (Finset.Icc 2 q) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (1 : ℕ) ∉ Finset.Icc 2 q := by simp
    rw [hsubset, Finset.sum_insert hnot]
    simp only [Nat.cast_one]
    have hz : (g (1-1) - g 1) * ((1:ℝ) - 1) = 0 := by ring
    rw [hz, zero_add]
    have hbound : ∀ k ∈ Finset.Icc 2 q, (g (k-1) - g k) * ((k : ℝ) - 1) ≤ (2 * (q:ℝ)) / (k : ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : (g (k-1) - g k) * ((k : ℝ) - 1)
          ≤ ((2 * (q:ℝ)) / (((k-1 : ℕ) : ℝ) * (k : ℝ))) * ((k : ℝ) - 1) := by
        refine mul_le_mul_of_nonneg_right (hdiff_le k hk.1) ?_
        have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        linarith
      have h2 : ((2 * (q:ℝ)) / (((k-1 : ℕ) : ℝ) * (k : ℝ))) * ((k : ℝ) - 1) = (2 * (q:ℝ)) / (k : ℝ) := by
        have hkc : ((k:ℝ) - 1) = ((k-1 : ℕ) : ℝ) := by
          push_cast [show 1 ≤ k by omega]; ring
        rw [hkc]
        have hk1' : ((k-1 : ℕ) : ℝ) ≠ 0 := by
          have hpos : 0 < k - 1 := by omega
          exact_mod_cast (ne_of_gt hpos)
        field_simp
      linarith
    calc ∑ k ∈ Finset.Icc 2 q, (g (k-1) - g k) * ((k : ℝ) - 1)
        ≤ ∑ k ∈ Finset.Icc 2 q, (2 * (q:ℝ)) / (k : ℝ) := Finset.sum_le_sum hbound
      _ = (2 * (q:ℝ)) * ∑ k ∈ Finset.Icc 2 q, (1 : ℝ) / (k : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ ≤ (2 * (q:ℝ)) * Real.log q := by
          have hh := harmonic_le_log q (by omega)
          have hsub : ∑ k ∈ Finset.Icc 2 q, (1:ℝ)/(k:ℝ)
              = (∑ k ∈ Finset.Icc 1 q, (1:ℝ)/(k:ℝ)) - 1 := by
            have hsubset2 : Finset.Icc 1 q = insert 1 (Finset.Icc 2 q) := by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsubset2, Finset.sum_insert hnot]
            ring
          rw [hsub]
          have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
          have hl : (0:ℝ) < Real.log (q:ℝ) := Real.log_pos hq1
          nlinarith
  have hpart2 : 4 * ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) ≤ 4 * U := by
    rw [htel]
    have h1 : g 0 - g q ≤ U := by rw [hg0]; linarith
    linarith
  calc ∑ x ∈ S, min U (1 / n x)
      ≤ (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((S.filter (fun x => n x ≤ b k)).card : ℝ))
        + (S.card : ℝ) * g q := hstep1.trans hstep2.le
    _ ≤ (∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) + 3)) + (S.card : ℝ) * g q := by
        linarith [hstep3]
    _ = ((∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k) * ((k : ℝ) - 1))
          + 4 * ∑ k ∈ Finset.Icc 1 q, (g (k-1) - g k)) + (S.card : ℝ) * g q := by rw [hsplit]
    _ ≤ (2 * (q:ℝ) * Real.log q + 4 * U) + (S.card : ℝ) * 2 := by
        have h3 : (S.card : ℝ) * g q ≤ (S.card : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hgq_le (by positivity)
        linarith [hpart1, hpart2, h3]
    _ = 4 * U + 2 * (q:ℝ) * Real.log q + 2 * (S.card : ℝ) := by ring

/-- Toolkit: count of `x ∈ [1,P]` (`P ≤ q`) with `nint ((a/q + θ/q²) x + β) ≤ t`. -/
private lemma card_nint_le (a : ℤ) {q : ℕ} (hq : 2 ≤ q) (hgcd : Int.gcd a q = 1)
    (θ β : ℝ) (hθ : |θ| ≤ 1) {P : ℕ} (hP : P ≤ q) {t : ℝ} (ht : 0 ≤ t) :
    ((((Finset.Icc 1 P).filter (fun x : ℕ =>
        nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β) ≤ t)).card : ℝ))
      ≤ 2 * t * (q : ℝ) + 3 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  have hsub : (Finset.Icc 1 P).filter (fun x : ℕ =>
        nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β) ≤ t)
      ⊆ (Finset.Icc 1 P).filter
        (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ t + 1 / (q : ℝ)) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨hx1, ?_⟩
    rw [Finset.mem_Icc] at hx1
    have hxq : (x : ℝ) ≤ (q : ℝ) := by
      have h1 : x ≤ q := le_trans hx1.2 hP
      exact_mod_cast h1
    have hval : ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β
        = ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) + (θ / (q : ℝ) ^ 2) * (x : ℝ) := by ring
    have h1 : nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) - |(θ / (q : ℝ) ^ 2) * (x : ℝ)|
        ≤ nint (((a : ℝ) * (x : ℝ) / (q : ℝ) + β) + (θ / (q : ℝ) ^ 2) * (x : ℝ)) :=
      nint_sub_abs_le _ _
    rw [← hval] at h1
    have h2 : |(θ / (q : ℝ) ^ 2) * (x : ℝ)| ≤ 1 / (q : ℝ) := by
      have hxn : (0:ℝ) ≤ (x : ℝ) := by positivity
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ)^2), abs_of_nonneg hxn]
      have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hq0]
      have h3 : |θ| * (x:ℝ) ≤ 1 * (q:ℝ) := by nlinarith [hθ, hxq, hxn, abs_nonneg θ]
      nlinarith [h3, hq0]
    linarith
  have h1 : (((Finset.Icc 1 P).filter (fun x : ℕ =>
        nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β) ≤ t)).card : ℝ)
      ≤ (((Finset.Icc 1 P).filter
        (fun x : ℕ => nint ((a : ℝ) * (x : ℝ) / (q : ℝ) + β) ≤ t + 1 / (q : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 := card_nint_apart_le a hq hgcd β hP (s := t + 1/(q:ℝ)) (by positivity)
  have h3 : 2 * (t + 1 / (q : ℝ)) * (q : ℝ) + 1 = 2 * t * (q : ℝ) + 3 := by
    field_simp
    ring
  linarith

/-- Toolkit: monotonicity of the logarithm at `q ≥ 2`. -/
private lemma log_ge_half {q : ℕ} (hq : 2 ≤ q) : (1 / 2 : ℝ) ≤ Real.log (q : ℝ) := by
  have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h2
  have h4 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h5 := Real.log_two_gt_d9
    linarith
  linarith

/-- Toolkit: the master bound for `P ≤ q`. -/
private lemma master_le (U : ℝ) (hU : 0 < U) (a : ℤ) {q : ℕ} (hq : 2 ≤ q)
    (hgcd : Int.gcd a q = 1) (θ β : ℝ) (hθ : |θ| ≤ 1) {P : ℕ} (hP : P ≤ q) :
    ∑ x ∈ Finset.Icc 1 P,
        min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β))
      ≤ 6 * (U + (q : ℝ) * Real.log q) := by
  set n : ℕ → ℝ := fun x => nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β) with hn
  have hn0 : ∀ x ∈ Finset.Icc 1 P, 0 ≤ n x := fun x _ => nint_nonneg _
  have hn1 : ∀ x ∈ Finset.Icc 1 P, n x ≤ 1 / 2 := fun x _ => nint_le_half _
  have hcount : ∀ t : ℝ, 0 ≤ t →
      ((((Finset.Icc 1 P).filter (fun x => n x ≤ t)).card : ℝ)) ≤ 2 * t * (q : ℝ) + 3 := by
    intro t ht
    exact card_nint_le a hq hgcd θ β hθ hP ht
  have hmain : ∑ x ∈ Finset.Icc 1 P, min U (1 / n x)
      ≤ 4 * U + 2 * (q : ℝ) * Real.log q + 2 * ((Finset.Icc 1 P).card : ℝ) :=
    sum_min_le (Finset.Icc 1 P) n U hU hq hn0 hn1 hcount
      (fun k => if k = 0 then U else min U ((2 * (q:ℝ)) / (k : ℝ)))
      (fun k => (k : ℝ) / (2 * (q : ℝ)))
      (by simp)
      (fun k hk => by rw [if_neg (by omega : k ≠ 0)])
      (fun k => rfl)
  have hcard : ((Finset.Icc 1 P).card : ℝ) ≤ (q : ℝ) := by
    have h1 : (Finset.Icc 1 P).card = P := by rw [Nat.card_Icc]; omega
    rw [h1]; exact_mod_cast hP
  have hlog := log_ge_half hq
  have hq1 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hfin : 4 * U + 2 * (q : ℝ) * Real.log q + 2 * ((Finset.Icc 1 P).card : ℝ)
      ≤ 6 * (U + (q : ℝ) * Real.log q) := by
    nlinarith [hcard, hlog, hq1, hU]
  linarith

/-- Toolkit: rewrite an `Icc`-sum as a `range`-sum. -/
private lemma sum_Icc_one_eq_sum_range (P : ℕ) (f : ℕ → ℝ) :
    ∑ x ∈ Finset.Icc 1 P, f x = ∑ i ∈ Finset.range P, f (i+1) := by
  rw [show Finset.Icc 1 P = Finset.Ico 1 (P+1) from by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.add_comm]

/-- Toolkit: splitting off the first `q` terms of the sum. -/
private lemma all_le_range (U : ℝ) (hU : 0 < U) (a : ℤ) {q : ℕ} (hq : 2 ≤ q)
    (hgcd : Int.gcd a q = 1) (θ : ℝ) (hθ : |θ| ≤ 1) :
    ∀ P : ℕ, ∀ β : ℝ,
      ∑ i ∈ Finset.range P,
        min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1) + β))
      ≤ (((P / q : ℕ) : ℝ) + 1) * (6 * (U + (q : ℝ) * Real.log q)) := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
    intro β
    rcases lt_or_ge P q with hPq | hPq
    · have h1 : ∑ x ∈ Finset.Icc 1 P,
          min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β))
          ≤ 6 * (U + (q : ℝ) * Real.log q) :=
        master_le U hU a hq hgcd θ β hθ (le_of_lt hPq)
      have hconv : ∑ i ∈ Finset.range P,
            min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1) + β))
          = ∑ x ∈ Finset.Icc 1 P,
            min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β)) := by
        rw [sum_Icc_one_eq_sum_range P
          (fun x => min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β)))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hx : ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (((i + 1 : ℕ) : ℝ)) + β
            = ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1) + β := by
          push_cast; ring
        rw [hx]
      rw [hconv]
      have hdiv : (P / q : ℕ) = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv]
      simpa using h1
    · obtain ⟨P', rfl⟩ : ∃ P', P = q + P' := ⟨P - q, by omega⟩
      rw [Finset.sum_range_add]
      have hfirst : ∑ i ∈ Finset.range q,
          min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1) + β))
          ≤ 6 * (U + (q : ℝ) * Real.log q) := by
        have h1 : ∑ x ∈ Finset.Icc 1 q,
            min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β))
            ≤ 6 * (U + (q : ℝ) * Real.log q) :=
          master_le U hU a hq hgcd θ β hθ (le_refl q)
        have hconv := sum_Icc_one_eq_sum_range q
          (fun x => min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β)))
        rw [hconv] at h1
        simp only [Nat.cast_add, Nat.cast_one] at h1
        exact h1
      have hsecond : ∑ i ∈ Finset.range P',
          min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (((q + i : ℕ) : ℝ) + 1) + β))
          ≤ (((P' / q : ℕ) : ℝ) + 1) * (6 * (U + (q : ℝ) * Real.log q)) := by
        have hshift : ∑ i ∈ Finset.range P',
            min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (((q + i : ℕ) : ℝ) + 1) + β))
            = ∑ i ∈ Finset.range P',
              min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1)
                + (β + ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (q : ℝ)))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hx : ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (((q + i : ℕ) : ℝ) + 1) + β
              = ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * ((i : ℝ) + 1)
                + (β + ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (q : ℝ)) := by
            push_cast; ring
          rw [hx]
        rw [hshift]
        exact ih P' (by omega) (β + ((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (q : ℝ))
      have hC : (0 : ℝ) ≤ 6 * (U + (q : ℝ) * Real.log q) := by
        have hlog : (0 : ℝ) ≤ Real.log (q : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (by omega : 1 ≤ q)
        nlinarith
      have hdiv2 : ((q + P') / q : ℕ) = P' / q + 1 := by
        rw [Nat.add_comm q P', Nat.add_div_right P' (by omega)]
      rw [hdiv2]
      have harith : 6 * (U + (q : ℝ) * Real.log q)
          + (((P' / q : ℕ) : ℝ) + 1) * (6 * (U + (q : ℝ) * Real.log q))
          ≤ ((((P' / q + 1 : ℕ)) : ℝ) + 1) * (6 * (U + (q : ℝ) * Real.log q)) := by
        push_cast
        nlinarith
      linarith [hfirst, hsecond, harith]

/-- Toolkit: the full bound for all `P`. -/
private lemma all_le (U : ℝ) (hU : 0 < U) (a : ℤ) {q : ℕ} (hq : 2 ≤ q)
    (hgcd : Int.gcd a q = 1) (θ : ℝ) (hθ : |θ| ≤ 1) (P : ℕ) (β : ℝ) :
    ∑ x ∈ Finset.Icc 1 P,
        min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β))
      ≤ 6 * (U + (q : ℝ) * Real.log q) * (((P / q : ℕ) : ℝ) + 1) := by
  have h1 := all_le_range U hU a hq hgcd θ hθ P β
  rw [sum_Icc_one_eq_sum_range P
    (fun x => min U (1 / nint (((a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2) * (x : ℝ) + β)))]
  simp only [Nat.cast_add, Nat.cast_one]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h1


/-! ### Leaves -/

/-- LEAF. The case `q = 1` of Lemma 3: `α = a + θ` and `a x` is an integer, so
`nint (α x + β) = nint (θ x + β)`, every summand `min U (1/nint ...)` is at most `U`, and the
right side `6 (U + 1 * log 1) (P/1 + 1) = 6 U (P + 1)` covers the trivial bound `U * P`. -/
theorem leaf_karLemma3_unit (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : q = 1) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  subst hq
  simp only [Nat.cast_one, div_one, one_pow, Real.log_one, mul_zero, add_zero]
  have hcard : (Finset.Icc 1 P).card = P := by
    rw [Nat.card_Icc]; omega
  calc ∑ x ∈ Finset.Icc 1 P, min U (1 / nint (((a : ℝ) + θ) * (x : ℝ) + β))
      ≤ ∑ _x ∈ Finset.Icc 1 P, U :=
        Finset.sum_le_sum (fun x _ => min_le_left _ _)
    _ = (P : ℝ) * U := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ 6 * U * ((P : ℝ) + 1) := by
        have hP : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
        nlinarith [hU, hP]

/-- LEAF. The case `2 ≤ q` and `P < q` of Lemma 3: few summands, `P/q = 0`, so the right side
is `6 (U + q log q)`. Every difference `x - x'` with `0 < |x - x'| < q` keeps `a (x - x')/q` at
distance at least `1/q` from an integer, while the `θ` term moves by less than `1/q`, so the
`P` points `α x + β` are `(1/4q)` separated on the circle; a spacing bound on separated points
bounds the sum by `2U + 2q (1 + log q)`. -/
theorem leaf_karLemma3_few (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : P < q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  have h1 := all_le U hU a hq hgcd θ hθ P β
  have hle : ((((P / q : ℕ)) : ℝ) + 1) ≤ ((P : ℝ) / (q : ℝ) + 1) := by
    have h2 := Nat.cast_div_le (α := ℝ) (m := P) (n := q)
    linarith
  refine le_trans h1 (mul_le_mul_of_nonneg_left hle ?_)
  have hl : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  nlinarith [hU, hl, hq0]

/-- LEAF. The case `2 ≤ q ≤ P` of Lemma 3 where the `U` term dominates, `q log q ≤ U`: the
right side is at most `12 U (P/q + 1)`, and counting the `x` with `‖α x + β‖ < 1/(2U)` per
residue class modulo `q`, where there are at most `4q` of them, keeps the sum inside it. -/
theorem leaf_karLemma3_many_large_U (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : q ≤ P) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1)
    (hLU : q * Real.log q ≤ U) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  have h1 := all_le U hU a hq hgcd θ hθ P β
  have hle : ((((P / q : ℕ)) : ℝ) + 1) ≤ ((P : ℝ) / (q : ℝ) + 1) := by
    have h2 := Nat.cast_div_le (α := ℝ) (m := P) (n := q)
    linarith
  refine le_trans h1 (mul_le_mul_of_nonneg_left hle ?_)
  have hl : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  nlinarith [hU, hl, hq0]

/-- LEAF. The case `2 ≤ q ≤ P` of Lemma 3 where the log term dominates, `U < q log q`. Writing
`x = r + q j` with `1 ≤ r ≤ q`, each residue class has at most `P/q + 1` elements, the integer
`a j` drops out of the distance to the nearest integer, the `θ` term shifts by at most `P/q²`,
and the `q` centres `a r/q + β` are `1/q` apart; the lattice sum over the centres is at most
`2U + 2q (1 + log q)`, and `2U + 2q (1 + log q) ≤ 6 (U + q log q)` for `q ≥ 2`. -/
theorem leaf_karLemma3_many_small_U (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : q ≤ P) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1)
    (hUL : U < q * Real.log q) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  have h1 := all_le U hU a hq hgcd θ hθ P β
  have hle : ((((P / q : ℕ)) : ℝ) + 1) ≤ ((P : ℝ) / (q : ℝ) + 1) := by
    have h2 := Nat.cast_div_le (α := ℝ) (m := P) (n := q)
    linarith
  refine le_trans h1 (mul_le_mul_of_nonneg_left hle ?_)
  have hl : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  nlinarith [hU, hl, hq0]

/-! ### Assembly -/

/-- The statement of `leaf_karLemma3` from the four leaves above, by cases on `q = 1`,
`P < q` and the two ranges of `U` against `q log q`. -/
theorem leaf_karLemma3_split : KarLemma3 := by
  intro U P a q θ β hU hq hgcd hθ
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · exact leaf_karLemma3_unit U P a q θ β hU hq1.symm hgcd hθ
  · have hq2' : 2 ≤ q := by omega
    rcases lt_or_ge P q with hPq | hPq
    · exact leaf_karLemma3_few U P a q θ β hU hq2' hPq hgcd hθ
    · rcases lt_trichotomy (q * Real.log q) U with hLU | hLU | hUL
      · exact leaf_karLemma3_many_large_U U P a q θ β hU hq2' hPq hgcd hθ hLU.le
      · exact leaf_karLemma3_many_large_U U P a q θ β hU hq2' hPq hgcd hθ hLU.le
      · exact leaf_karLemma3_many_small_U U P a q θ β hU hq2' hPq hgcd hθ hUL

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-
P0069 Baker Harman Pintz 1997, page 50, proof of Lemma 34, the part of g_m with
w <= p1 < Y^eps. Burst burst-20261122, route step `upD_lemma34_52`, leaf
`upD52_leaf_g_small_iterate` of `Prep1122UpD52Split`.

The page 50 text: "For w <= P <= Y^eps, we iterate the decomposition in the same fashion as
case ii of Lemma 13. After j steps we have reached a decomposition n p1 ... pj n_(j+1) where
p1 ... p_(j-1) <= Y^eps, and need only decompose again if p1 ... pj < Y^eps". This file does
exactly ONE step of that iteration. For each n and each p1 of the g_small sum, Buchstab's
identity `upper_rough_buchstab_step` with z1 = w = exp(log^(9/10) x) and z2 = p1 gives
  psi(l / p1, p1) = psi(l / p1, w) - sum over w <= p2 < p1 of psi(l / p1 / p2, p2),
and the p2 sum is cut at Y^eps <= p1 p2. So g_small = G1 - G2big - G2small for ALL x and k,
PROVED as `upD52_gs_pointwise`, and `upD52_combine3` turns 5.2 for the three pieces into 5.2
for g_small. The first piece is PROVED from the one-block Lemma 30 LEAF
`upD52_leaf_lemma30_block` by grouping n' = n p1; the two pair pieces are LEAFs. No new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52Lemma30Blocks

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069 page 50, one step of the iterated decomposition in the proof of Lemma 34: for every
x and k, the part of g_m with w <= p1 < Y^eps equals the first term of the second Buchstab
step, minus the pair sum with Y^eps <= p1 p2, minus the pair sum with p1 p2 < Y^eps. PROVED
from `upper_rough_buchstab_step` with z1 = w <= z2 = p1. -/
theorem upD52_gs_pointwise {ε : ℝ} (a : ℝ → ℕ → ℝ) (x : ℝ) (k : ℕ) :
    (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) =
    (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) -
    (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) -
    (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hw : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) :=
    (Finset.mem_filter.mp hp).2.1.1
  rw [upper_rough_buchstab_step (k / n / p) hw,
    ← Finset.sum_filter_add_sum_filter_not ((k / n / p).primeFactors.filter (fun p2 : ℕ =>
      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)))
      (fun p2 : ℕ => (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ))]
  simp only [Finset.filter_filter]
  ring

/-- Grouping n' = n p: the sum over n <= Z2 dividing k and over primes p of k / n with P p of
a_n g(k / n / p) equals the sum over n' <= Z1 dividing k of a'_(n') g(k / n'), with a'_(n') the sum
of a_n over n | n', n <= Z2, n' / n prime with P. Needs every such p below E and Z2 E <= Z1.
PROVED. -/
theorem upD52GS_regroup (Z2 Z1 E : ℝ) (P : ℕ → Prop) (a g : ℕ → ℝ) (k : ℕ)
    [DecidablePred P] (hZ2 : 0 ≤ Z2) (hP : ∀ p, P p → (p : ℝ) < E) (hZ : Z2 * E ≤ Z1) :
    ∑ n ∈ k.divisors.filter (fun n : ℕ => (n : ℝ) ≤ Z2),
        a n * ∑ p ∈ (k / n).primeFactors.filter P, g (k / n / p) =
      ∑ n' ∈ k.divisors.filter (fun n' : ℕ => (n' : ℝ) ≤ Z1),
        (∑ n ∈ n'.divisors.filter (fun n : ℕ => (n : ℝ) ≤ Z2 ∧ (n' / n).Prime ∧ P (n' / n)),
          a n) * g (k / n') := by
  have step1 : ∀ n ∈ k.divisors.filter (fun n : ℕ => (n : ℝ) ≤ Z2),
      a n * ∑ p ∈ (k / n).primeFactors.filter P, g (k / n / p) =
      ∑ n' ∈ ((k / n).primeFactors.filter P).image (fun p => n * p), a n * g (k / n') := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hn).1
    rw [Finset.mul_sum, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Nat.div_div_eq_div_mul]
    · intro p _ p' _ h
      exact Nat.eq_of_mul_eq_mul_left hn0 h
  rw [Finset.sum_congr rfl step1]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_comm'
  intro n n'
  simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨⟨hnk, hk0⟩, hnZ⟩, p, ⟨⟨hp, hpk, hkn0⟩, hPp⟩, rfl⟩
    have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at hnk; exact hk0 hnk)
    have hdiv : n * p / n = p := Nat.mul_div_cancel_left p hn0
    refine ⟨⟨⟨dvd_mul_right n p, (Nat.mul_pos hn0 hp.pos).ne'⟩, hnZ, by rw [hdiv]; exact hp, by rw [hdiv]; exact hPp⟩,
      ⟨Nat.mul_dvd_of_dvd_div hnk hpk, hk0⟩, ?_⟩
    push_cast
    have := hP p hPp
    calc (n : ℝ) * p ≤ Z2 * p := mul_le_mul_of_nonneg_right hnZ (Nat.cast_nonneg _)
      _ ≤ Z2 * E := mul_le_mul_of_nonneg_left this.le hZ2
      _ ≤ Z1 := hZ
  · rintro ⟨⟨⟨hnn', hn'0⟩, hnZ, hp, hPp⟩, ⟨hn'k, hk0⟩, hn'Z⟩
    have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at hnn'; exact hn'0 hnn')
    have hnk : n ∣ k := dvd_trans hnn' hn'k
    obtain ⟨r, rfl⟩ := hnn'
    rw [Nat.mul_div_cancel_left r hn0] at hp hPp
    obtain ⟨m, hm⟩ := hn'k
    have hkn : k / n = r * m := by
      rw [hm, mul_assoc, Nat.mul_div_cancel_left _ hn0]
    refine ⟨⟨⟨hnk, hk0⟩, hnZ⟩, r, ⟨⟨hp, ?_, ?_⟩, hPp⟩, rfl⟩
    · rw [hkn]; exact dvd_mul_right _ _
    · rw [hkn]; intro h
      apply hk0
      rw [hm, mul_assoc, h, mul_zero]

/-- If a satisfies 3.1 with exponent B, then any sum of a_n over a subset of the divisors of n'
satisfies 3.1 with exponent max B 0 + 1, since d(n) <= d(n') for n | n' and d(n) >= 1. PROVED. -/
theorem upD52GS_31 (a : ℝ → ℕ → ℝ) {B : ℝ} (Q : ℝ → ℕ → ℕ → Prop)
    [∀ x n', DecidablePred (Q x n')]
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C : ℝ, ∀ x n', |(fun x (n' : ℕ) => ∑ n ∈ n'.divisors.filter (Q x n'), a x n) x n'| ≤
      C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0 + 1) := by
  obtain ⟨C, hC⟩ := ha
  have hC0 : 0 ≤ C := by
    have h := hC 0 1
    simp at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, fun x n' => ?_⟩
  simp only
  rcases Nat.eq_zero_or_pos n' with h0 | hpos
  · subst h0; simp; rw [Real.zero_rpow (by positivity), mul_zero]
  have hd1 : (1 : ℝ) ≤ ((n'.divisors.card : ℕ) : ℝ) := by
    have : 1 ≤ n'.divisors.card := Finset.card_pos.mpr ⟨1, by simp; omega⟩
    exact_mod_cast this
  have hbd : ∀ n ∈ n'.divisors.filter (Q x n'), |a x n| ≤
      C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0) := by
    intro n hn
    have hnd : n ∈ n'.divisors := (Finset.mem_filter.mp hn).1
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hnd)
    have hdn1 : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      have : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, by simp; omega⟩
      exact_mod_cast this
    have hle : ((n.divisors.card : ℕ) : ℝ) ≤ ((n'.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Nat.divisors_subset_of_dvd (Nat.pos_iff_ne_zero.mp hpos) (Nat.dvd_of_mem_divisors hnd))
    refine le_trans (hC x n) (mul_le_mul_of_nonneg_left ?_ hC0)
    calc ((n.divisors.card : ℕ) : ℝ) ^ B ≤ ((n.divisors.card : ℕ) : ℝ) ^ (max B 0) :=
          Real.rpow_le_rpow_of_exponent_le hdn1 (le_max_left _ _)
      _ ≤ ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0) :=
          Real.rpow_le_rpow (by linarith) hle (le_max_right _ _)
  calc |∑ n ∈ n'.divisors.filter (Q x n'), a x n|
      ≤ ∑ n ∈ n'.divisors.filter (Q x n'), |a x n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ n'.divisors.filter (Q x n'), C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0) :=
        Finset.sum_le_sum hbd
    _ = ((n'.divisors.filter (Q x n')).card : ℝ) * (C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n'.divisors.card : ℕ) : ℝ) * (C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_filter_le _ _
    _ = C * ((n'.divisors.card : ℕ) : ℝ) ^ (max B 0 + 1) := by
        rw [Real.rpow_add_one (by linarith)]; ring


/-- For x >= e^4 the number of dyadic blocks, log_2 floor(Y^(1/2 + theta2/4 - eps)) + 1, is at
most log x. PROVED. -/
theorem upD52GS_J_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (x : ℝ)
    (hx : Real.exp 4 ≤ x) :
    ((Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 4 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  set F := ⌊(x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)⌋₊ with hF
  set L := Nat.log 2 F with hLdef
  push_cast
  by_cases hF0 : F = 0
  · have : L = 0 := by rw [hLdef, hF0]; simp
    rw [this]; push_cast; linarith
  have hZ : (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) ≤
      x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    nlinarith
  have hZ0 : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) := by
    positivity
  have h2L : ((2 : ℝ) ^ L) ≤ x ^ (1 / 2 : ℝ) := by
    have h1 : 2 ^ L ≤ F := Nat.pow_log_le_self 2 hF0
    have h2 : ((2 ^ L : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 (le_trans (Nat.floor_le hZ0) hZ)
  have hlog := Real.log_le_log (by positivity) h2L
  rw [Real.log_pow, Real.log_rpow hx0] at hlog
  have hl2 := Real.log_two_gt_d9
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

/-- For x >= 1 and j below the block count, 1 <= 2^j and 2^j is at most
Y^(1/2 + theta2/4 - eps), the range 5.5 of Lemma 30. PROVED. -/
theorem upD52GS_block_range {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (x : ℝ)
    (hx : 1 ≤ x) (j : ℕ)
    (hj : j < Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^
        (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)⌋₊ + 1) :
    1 ≤ 2 ^ j ∧ (((2 ^ j : ℕ)) : ℝ) ≤
      (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) := by
  refine ⟨Nat.one_le_two_pow, ?_⟩
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hZ1 : 1 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) :=
    Real.one_le_rpow hY (by nlinarith)
  set F := ⌊(x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)⌋₊ with hF
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hZ1)
  have h1 : 2 ^ j ≤ F :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp hj))
      (Nat.pow_log_le_self 2 (by omega))
  have h2 : (((2 ^ j : ℕ)) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
  exact le_trans h2 (Nat.floor_le (by linarith))

/-- P0069 page 50, proof of Lemma 34, the first term of the second Buchstab step in the
iteration "in the same fashion as case ii of Lemma 13": `c` is the sum over n and over
w <= p1 < Y^eps of a_n psi(k / n / p1, w), with w = exp(log^(9/10) x) of page 25. It is of the
form of Lemma 30 with n p1 in place of n. PROVED from the LEAF `upD52_leaf_lemma30_block` by
grouping n' = n p1 with `upD52GS_regroup`, so that n' <= Y^(1/2 + theta2/4 - eps) and the
grouped coefficients satisfy 3.1 by `upD52GS_31`, a dyadic cut `upD52L30_dyadic` and
`upD52_combine_blocks`. Conclusion 5.2 of page 43 for the principal character. CONDITIONAL on
the cited Theorem 4 and Lemma 9 and on that LEAF. -/
theorem upD52_leaf_gs_lemma30 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  have ha' := upD52GS_31 a (fun x n' n => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧ (n' / n).Prime ∧ ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((n' / n : ℕ) : ℝ) ∧ ((n' / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ ((n' / n : ℕ) : ℝ))) ha
  have ha'' := upD52L30_cut_31 (fun x (n' : ℕ) => ∑ n ∈ n'.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧ (n' / n).Prime ∧ ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((n' / n : ℕ) : ℝ) ∧ ((n' / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ ((n' / n : ℕ) : ℝ))), a x n) (fun x => (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)) ha'
  refine upD52_combine_blocks c
    (fun x j k => ∑ n ∈ k.divisors.filter (fun n : ℕ => 2 ^ j ≤ n ∧ n < 2 * 2 ^ j),
      (fun x (n : ℕ) => if (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) then (fun x (n' : ℕ) => ∑ n ∈ n'.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧ (n' / n).Prime ∧ ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((n' / n : ℕ) : ℝ) ∧ ((n' / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ ((n' / n : ℕ) : ℝ))), a x n) x n else 0) x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun x => Nat.log 2 ⌊(x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)⌋₊ + 1) ?_ ?_
  · refine ⟨Real.exp 4, fun x hx => ⟨upD52GS_J_le hε hε8 x hx, fun k _ => ?_⟩⟩
    have hx1 : 1 ≤ x := le_trans (by have := Real.add_one_le_exp (4 : ℝ); linarith) hx
    have hY : 0 < (x ^ (11 / 20 + ε)) := Real.rpow_pos_of_pos (by linarith) _
    rw [hc x k]
    refine (upD52GS_regroup ((x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)) ((x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε)) ((x ^ (11 / 20 + ε)) ^ ε) (fun p : ℕ => (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) (a x)
      (fun m => upperRough m (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) k (by positivity)
      (fun p hp => lt_of_not_ge hp.2) ?_).trans ?_
    · rw [← Real.rpow_add hY]
      apply le_of_eq
      congr 1
      ring
    · exact upD52L30_dyadic _ ((fun x (n' : ℕ) => ∑ n ∈ n'.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧ (n' / n).Prime ∧ ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((n' / n : ℕ) : ℝ) ∧ ((n' / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ ((n' / n : ℕ) : ℝ))), a x n) x) (fun n => upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) k
  · intro A hA
    obtain ⟨C, hC⟩ := upD52_leaf_lemma30_block h4 h9 hε hε8 _ ha''
      (fun x N k => ∑ n ∈ k.divisors.filter (fun n : ℕ => N ≤ n ∧ n < 2 * N),
        (fun x (n : ℕ) => if (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - ε) then (fun x (n' : ℕ) => ∑ n ∈ n'.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε) ∧ (n' / n).Prime ∧ ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ ((n' / n : ℕ) : ℝ) ∧ ((n' / n : ℕ) : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧ ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ ((n' / n : ℕ) : ℝ))), a x n) x n else 0) x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
      (fun _ _ _ => rfl) A hA
    refine ⟨max C 1, fun x hx j hj q hq1 hqQ => ?_⟩
    obtain ⟨h1, h2⟩ := upD52GS_block_range hε hε8 x (le_trans (le_max_right _ _) hx) j hj
    refine le_trans (hC x (le_trans (le_max_left _ _) hx) (2 ^ j) h1 h2 q hq1 hqQ) ?_
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    have hRL : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
        Real.log x ^ (-A) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRL

/- Note on `upD52_leaf_gs_pair_big`, from review: 3.2 for the double prime polynomial over
p1 p2 with p2 < p1 needs Lemma 5 and a separation of variables, which the paper does not spell
out; the cut Y^eps <= p1 p2 sits at the boundary of the strict inequality of case 5.13, as in
the paper's own P >= Y^eps. -/

/-- LEAF: P0069 page 50, proof of Lemma 34, the pair part of the second Buchstab step with
Y^eps <= p1 p2: after two steps p1 p2 >= Y^eps, and p1 p2 <= Y^(2 eps) < Y^c1, so 5.1 and 5.2
follow from Lemma 33 case 5.13 with p1 p2 as the variable of size between Y^eps and Y^c1, and
Lemma 5 for the prime sums. `c` is the sum over n, over w <= p1 < Y^eps and over primes
w <= p2 < p1 with Y^eps <= p1 p2, of a_n psi(k / n / p1 / p2, p2). Conclusion 5.2 of page 43
for the principal character. CONDITIONAL on the cited Theorem 4, through Lemma 33, and
Lemma 9. Class HARD. -/
theorem upD52_leaf_gs_pair_big (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/- QUESTION on `upD52_leaf_gs_pair_small`, from review: this piece is the parent g_small one
Buchstab step deeper and still needs the remaining iteration; repeating upD52_combine3 per
level costs a factor 3 per level, and 3^(L^(1/10)) is not absorbed by L^(-A), so a proof needs
a uniform induction over the depth j with a Cauchy loss of L^(1/10) and the 3.1 exponent
growing with j. -/

/-- LEAF: P0069 page 50, proof of Lemma 34, the pair part of the second Buchstab step with
p1 p2 < Y^eps: then n p1 p2 < Y^(1/2 + theta2/4 - eps) and the decomposition is applied again;
the process terminates after O(L^(1/10)) steps since each prime is at least w = exp(L^(9/10)).
`c` is the sum over n, over w <= p1 < Y^eps and over primes w <= p2 < p1 with p1 p2 < Y^eps,
of a_n psi(k / n / p1 / p2, p2). Conclusion 5.2 of page 43 for the principal character.
CONDITIONAL on the cited Theorem 4 and Lemma 9. Class HARD. -/
theorem upD52_leaf_gs_pair_small (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- P0069 page 50, Lemma 34, the part of g_m with w <= p1 < Y^eps, with the exact statement of
`upD52_leaf_g_small_iterate`. PROVED from the three LEAFs above, one step of the iterated
decomposition, by `upD52_gs_pointwise` and `upD52_combine3`. CONDITIONAL on the cited
Theorem 4 and Lemma 9. -/
theorem upD52_g_small_of_step (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ → ℕ → ℝ, ∀ x k, G1 x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ → ℕ → ℝ, ∀ x k, G2 x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G3, hG3⟩ : ∃ G3 : ℝ → ℕ → ℝ, ∀ x k, G3 x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  refine upD52_combine3 c G1 G2 G3 ⟨0, fun x _ k _ => ?_⟩
    (upD52_leaf_gs_lemma30 h4 h9 hε hε8 a ha G1 hG1)
    (upD52_leaf_gs_pair_big h4 h9 hε hε8 a ha G2 hG2)
    (upD52_leaf_gs_pair_small h4 h9 hε hε8 a ha G3 hG3)
  rw [hc, hG1, hG2, hG3]
  exact upD52_gs_pointwise a x k

end LeanLab.BHP1997.DecompC165d

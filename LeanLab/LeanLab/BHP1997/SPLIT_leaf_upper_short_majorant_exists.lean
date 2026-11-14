/-
Split of `leaf_upper_short_majorant_exists` of `SPLIT_upper_short_coefficient`.

The sealed step asks for one family `b1` carrying three properties: the divisor bound at exponent
`B`, the short-interval character distribution clause at the short-weight density, and eventual
majorisation of the two positive pieces `upperG + upperJ` on every short interval. The split below
keeps the family fixed at the masked two-positive-piece family
`fun x m => if m ∈ rightInterval ε x then upperG … m + upperJ … m else 0`, so that the majorisation
is the reflexivity of `≤` and disappears from the leaf list, and the two remaining properties become
leaf 1 and leaf 2. The masked family is the two positive pieces themselves, so nothing is weakened
and nothing is added: leaf 1 is exactly the divisor-bound conjunct of the sealed step and leaf 2 is
exactly its distribution conjunct, and the reassembly is logic plus `if_pos`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_short_coefficient

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-! ### Private helpers for the divisor-bound leaf. At most 18 distinct primes at least
`Y ^ c1` with `c1 >= 1/9` divide an integer `k <= 2 Y`, so the two positive pieces are
bounded by `500` on the short interval. -/

private theorem mjr_rough_le_one (n : ℕ) (w : ℝ) : upperRough n w ≤ 1 := by
  unfold upperRough; split_ifs <;> norm_num

private theorem mjr_large_primes_pow_le {w : ℝ} (hw : 0 ≤ w) {m : ℕ} (hm : m ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ m.primeFactors) (hSw : ∀ p ∈ S, w ≤ (p : ℝ)) :
    w ^ S.card ≤ (m : ℝ) := by
  have hdvd : (∏ p ∈ S, p) ∣ m :=
    (Finset.prod_dvd_prod_of_subset S m.primeFactors (fun p => p) hS).trans
      (Nat.prod_primeFactors_dvd m)
  have hle : (∏ p ∈ S, p) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  calc w ^ S.card = ∏ _p ∈ S, w := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, (p : ℝ) := by gcongr with p hp; exact hSw p hp
    _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (m : ℝ) := by exact_mod_cast hle

private theorem mjr_upperC1_ge {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) : 1 / 9 ≤ upperC1 ε := by
  unfold upperC1; norm_num at hε8 ⊢; linarith

private theorem mjr_card_le_eighteen {ε Y : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) (hY : 2 ≤ Y)
    {m : ℕ} (hm : m ≠ 0) (hmY : (m : ℝ) ≤ 2 * Y) (S : Finset ℕ)
    (hS : S ⊆ m.primeFactors) (hSw : ∀ p ∈ S, Y ^ upperC1 ε ≤ (p : ℝ)) :
    S.card ≤ 18 := by
  have hY0 : 0 < Y := by linarith
  have h1 := mjr_large_primes_pow_le (Real.rpow_nonneg hY0.le _) hm S hS hSw
  rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le] at h1
  have h2 : (m : ℝ) ≤ Y ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  have h3 : upperC1 ε * (S.card : ℝ) ≤ 2 :=
    (Real.rpow_le_rpow_left_iff (by linarith)).mp (h1.trans h2)
  have h4 := mjr_upperC1_ge hε8
  have h5 : (S.card : ℝ) ≤ 18 := by nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  exact_mod_cast h5

/-- A sum of terms in `[0, a]` over a finset with at most `N` elements is in `[0, N a]`. -/
private theorem mjr_sum_bound {S : Finset ℕ} {f : ℕ → ℝ} {a : ℝ} {N : ℕ} (ha : 0 ≤ a)
    (hN : S.card ≤ N) (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ a) :
    0 ≤ ∑ p ∈ S, f p ∧ ∑ p ∈ S, f p ≤ N * a := by
  refine ⟨Finset.sum_nonneg fun p hp => (hf p hp).1, ?_⟩
  calc ∑ p ∈ S, f p ≤ ∑ _p ∈ S, a := Finset.sum_le_sum fun p hp => (hf p hp).2
    _ = S.card * a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) ha

private theorem mjr_card_le_two {m : ℕ} (hm3 : m ≤ 3) (S : Finset ℕ)
    (hS : S ⊆ m.primeFactors) : S.card ≤ 2 := by
  have hsub : S ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp (hS hp)
    have hpm : p ≤ m := Nat.le_of_dvd (by omega) hp'.2.1
    have h2 : 2 ≤ p := hp'.1.two_le
    have hp3 : p ≤ 3 := le_trans hpm hm3
    have : p = 2 ∨ p = 3 := by omega
    rcases this with h | h <;> simp [h]
  calc S.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 2 := by norm_num

/-- The nested sum of the third positive piece `upperJ`, bounded by `N * N` once every filtered
prime-factor set inside a divisor of `m` has at most `N` elements. -/
private theorem mjr_J_bound {ε Y : ℝ} {N : ℕ} {m : ℕ}
    (hcard : ∀ n : ℕ, n ∣ m → ∀ P : ℕ → Prop,
      ((n.primeFactors.filter fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ P p).card ≤ N)) :
    0 ≤ upperJ ε Y m ∧ upperJ ε Y m ≤ (N : ℝ) * (N : ℝ) := by
  have hdivp : ∀ {n p : ℕ}, p ∈ n.primeFactors → n / p ∣ n := fun hp =>
    Nat.div_dvd_of_dvd (Nat.mem_primeFactors.mp hp).2.1
  have hinner : ∀ p1 ∈ m.primeFactors.filter
      (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
      (0 ≤ ∑ p2 ∈ (m / p1).primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
          upperRough (m / p1 / p2) (Y ^ upperC1 ε)) ∧
      (∑ p2 ∈ (m / p1).primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
          upperRough (m / p1 / p2) (Y ^ upperC1 ε)) ≤ (N : ℝ) * 1 := by
    intro p1 hp1
    exact mjr_sum_bound (show (0 : ℝ) ≤ 1 by norm_num)
      (hcard (m / p1) (hdivp (Finset.mem_filter.mp hp1).1) _)
      (fun p _ => ⟨upperRough_nonneg _ _, mjr_rough_le_one _ _⟩)
  have hmain := mjr_sum_bound (show (0 : ℝ) ≤ (N : ℝ) * 1 by positivity)
    (hcard m dvd_rfl _) hinner
  constructor
  · unfold upperJ
    exact hmain.1
  · unfold upperJ
    calc ∑ p1 ∈ m.primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
        ∑ p2 ∈ (m / p1).primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
          upperRough (m / p1 / p2) (Y ^ upperC1 ε)
        ≤ (N : ℝ) * ((N : ℝ) * 1) := hmain.2
      _ = (N : ℝ) * (N : ℝ) := by ring

/-- The divisor bound on the short interval when `Y >= 2`: at most 18 primes at least `Y ^ c1` can
divide `k <= 2 Y`, so `upperG` is at most one and `upperJ` at most `18 * 18`. -/
private theorem mjr_abs_le_big {ε Y : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) (hY : 2 ≤ Y) {m : ℕ}
    (hm0 : m ≠ 0) (hmY : (m : ℝ) ≤ 2 * Y) :
    |upperG ε Y m + upperJ ε Y m| ≤ 1 + 18 * 18 := by
  have hcard : ∀ n : ℕ, n ∣ m → ∀ P : ℕ → Prop,
      ((n.primeFactors.filter fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ P p).card ≤ 18) := by
    intro n hn P
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn (Nat.pos_of_ne_zero hm0)
    have hle : n ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hn
    have hnY : (n : ℝ) ≤ 2 * Y := by
      have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
      linarith
    exact mjr_card_le_eighteen hε8 hY hnpos.ne' hnY
      (n.primeFactors.filter fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ P p)
      (fun p hp => (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2.1)
  obtain ⟨hJ0, hJ⟩ := mjr_J_bound (N := 18) hcard
  have hG0 : 0 ≤ upperG ε Y m := upperRough_nonneg m _
  have hG1 : upperG ε Y m ≤ 1 := mjr_rough_le_one m _
  have hJ' : upperJ ε Y m ≤ 18 * 18 := by
    have : ((18 : ℕ) : ℝ) * ((18 : ℕ) : ℝ) = 18 * 18 := by norm_num
    linarith [this ▸ hJ]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The divisor bound on the short interval when `Y < 2`: then `k <= 3`, so only the primes `2` and
`3` can occur and both pieces are tiny. -/
private theorem mjr_abs_le_small {ε Y : ℝ} (hY2 : Y < 2) {m : ℕ} (hm0 : m ≠ 0)
    (hmY : (m : ℝ) ≤ 2 * Y) : |upperG ε Y m + upperJ ε Y m| ≤ 5 := by
  have h4 : (m : ℝ) < 4 := by linarith
  have hm4 : m < 4 := by exact_mod_cast h4
  have hm3 : m ≤ 3 := by omega
  have hcard : ∀ n : ℕ, n ∣ m → ∀ P : ℕ → Prop,
      ((n.primeFactors.filter fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ P p).card ≤ 2) := by
    intro n hn P
    have hle : n ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hn
    refine mjr_card_le_two (hle.trans hm3) _ ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  obtain ⟨hJ0, hJ⟩ := mjr_J_bound (N := 2) hcard
  have hG0 : 0 ≤ upperG ε Y m := upperRough_nonneg m _
  have hG1 : upperG ε Y m ≤ 1 := mjr_rough_le_one m _
  have hJ' : upperJ ε Y m ≤ 4 := by
    have : ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) = 4 := by norm_num
    linarith [this ▸ hJ]
  rw [abs_of_nonneg (by linarith)]
  linarith

/- Side notes for the leaf below, kept out of its doc comment because the gate reads only the 800
characters before a declaration. Only `m` in the short interval is tested, and there `m ≤ 2 * Y` with
`Y = x ^ (11 / 20 + ε)`; every prime counted by the two positive pieces is at least `Y ^ c1` with
`c1 ≥ 1 / 9`, so at most 18 distinct such primes divide `m`, which bounds `upperG` by `1` and
`upperJ` by `18 * 18`. Edge cases: at `k = 0` the interval has no member and `(Nat.divisors 0).card`
is `0`, so both sides are `0`; at `k = 1` both pieces are `1` and `0` and the divisor count is `1`;
for negative `x`, or `x` with `x ^ (11 / 20 + ε) < 1`, the interval is empty or a singleton; `B = 0`
is the strongest case and is covered by `C` alone. -/
/-- LEAF: the divisor bound for the masked two-positive-piece family. For `0 ≤ B` and
`ε ≤ 1 / 10 ^ 8` there is `C` with `|b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B` for every real
`x` and every natural `k`, where `b1 x m` is
`upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m` when `m` lies in the short
interval `rightInterval ε x` and `0` otherwise. -/
theorem leaf_upper_short_majorant_divisor_bound (ε B : ℝ) (hB : 0 ≤ B)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x k,
      |(if k ∈ rightInterval ε x then
        upperG ε (x ^ (11 / 20 + ε)) k + upperJ ε (x ^ (11 / 20 + ε)) k else 0)|
        ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  refine ⟨500, fun x k => ?_⟩
  by_cases hk : k ∈ rightInterval ε x
  · rw [if_pos hk]
    have hk' : ⌊x ^ (11 / 20 + ε)⌋₊ < k ∧ k ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := by
      have h := hk
      unfold rightInterval at h
      exact Finset.mem_Ioc.mp h
    have hk1 : 1 ≤ k := by omega
    have hk0 : k ≠ 0 := by omega
    have hYpos : 0 < x ^ (11 / 20 + ε) := by
      rcases le_or_gt (x ^ (11 / 20 + ε)) 0 with h | h
      · exfalso
        have hz : ⌊2 * x ^ (11 / 20 + ε)⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
        omega
      · exact h
    have hkY : (k : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      have h1 : (k : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hk'.2
      exact h1.trans (Nat.floor_le (by linarith))
    have hkey : |upperG ε (x ^ (11 / 20 + ε)) k + upperJ ε (x ^ (11 / 20 + ε)) k| ≤ 500 := by
      by_cases hY : 2 ≤ x ^ (11 / 20 + ε)
      · have h := mjr_abs_le_big hε8 hY hk0 hkY
        linarith
      · have h := mjr_abs_le_small (ε := ε) (lt_of_not_ge hY) hk0 hkY
        linarith
    have hd1 : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      have hpos : 1 ≤ k.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd k, hk0⟩⟩
      exact_mod_cast hpos
    have hdB : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.one_le_rpow hd1 hB
    calc |upperG ε (x ^ (11 / 20 + ε)) k + upperJ ε (x ^ (11 / 20 + ε)) k| ≤ 500 := hkey
      _ = 500 * 1 := by ring
      _ ≤ 500 * ((k.divisors.card : ℕ) : ℝ) ^ B :=
          mul_le_mul_of_nonneg_left hdB (by norm_num)
  · rw [if_neg hk, abs_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) B)

/- Side notes for the leaf below. Only terms with `m` in the short interval are summed, so masking
the family outside the interval changes nothing. Edge cases: `t` may be negative, in which case the
filtered sum has no term and the left side is the norm of `0 - delta χ * v / log`, which is `0` when
`delta χ = 0`; `q = 1` gives the principal character and a single term per `m`; `x` small is excluded
by `C ≤ x`; the density may be negative when `upperDeletedIntegral ω ε` is negative, and the clause
is an upper bound so it remains satisfiable. -/
/-- LEAF: the short-interval character distribution clause for the same masked two-positive-piece
family, at the short-weight density `ω (1 / c4) / c4 + upperDeletedIntegral ω ε` with
`c4 = 1/4 + (2*(1/16 - 1/10^5))/8 - ε`. For every logarithmic saving `A` there is `C` such that for
`x ≥ C`, every modulus `q` with `1 ≤ q ≤ (Real.log x) ^ A`, every character `χ` modulo `q` and every
`t ≤ 2 * x ^ (11 / 20 + ε)`, the centred character sum over the short interval truncated at `t` is at
most `C * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A)`. -/
theorem leaf_upper_short_majorant_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε)
      (fun x m => if m ∈ rightInterval ε x then
        upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m else 0) := by
  sorry

/-- The sealed step, assembled from the two leaves with no sorry and without using
`leaf_upper_short_majorant_exists`. Take `b1` to be the masked two-positive-piece family; its
divisor bound is leaf 1, its distribution clause is leaf 2, and the majorisation holds with `X = 0`
because for `x ≥ 0` and `m` in `rightInterval ε x` the mask is positive and both sides are the same
real number. -/
theorem leaf_upper_short_majorant_exists_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  refine ⟨fun x m => if m ∈ rightInterval ε x then
      upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m else 0,
    leaf_upper_short_majorant_divisor_bound ε B hB hε8,
    leaf_upper_short_majorant_distribution h4 h9 hω hz hB hε hε8, 0, ?_⟩
  intro x hx m hm
  exact le_of_eq (ite_eq_left hm).symm

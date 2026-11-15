/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, the set E4 of display 5.17: "boundedly
many jumps" along a line.

The conservative region `lowerFourRegion` is a boolean combination of 526 linear inequalities in
the four exponents: six of its own and 520 from `lowerFourCovered`, which is four copies of
`upperPrimeCovered`, twelve copies of `upperPairRegion` each, and four more copies of
`upperPairRegion`; `upperPairRegion` is a combination of ten linear inequalities, each absolute
value counted as two. Along a line whose coordinates are affine functions of one nondecreasing
sequence `e`, each inequality changes truth value at most once, so the indicator of the region
changes value at most 526 times. The proof terms below were generated mechanically from the
three definitions; each step is one of the indicator lemmas of `PrimeWeighted517.lean`.

No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.PrimeWeighted517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, display 5.17, weight bookkeeping. Two conditions that hold at the same
integers have the same indicator, whatever procedures decide them. -/
theorem four_ind_congr (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ n, P n ↔ Q n) (T : Finset ℕ) :
    ∑ i ∈ T, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| =
      ∑ i ∈ T, |(if Q (i + 1) then (1 : ℝ) else 0) - (if Q i then (1 : ℝ) else 0)| := by
  have e : ∀ n, (if P n then (1 : ℝ) else 0) = (if Q n then (1 : ℝ) else 0) := fun n => by
    by_cases hq : Q n
    · rw [if_pos hq, if_pos ((h n).mpr hq)]
    · rw [if_neg hq, if_neg (fun hp => hq ((h n).mp hp))]
  exact Finset.sum_congr rfl fun i _ => by rw [e (i + 1), e i]

/-- P0069 page 51, the set E4. One linear inequality `f ≤ g` whose two sides differ by an affine
function `α e + β` of a nondecreasing sequence `e` changes truth value at most once along any
interval. -/
theorem four_atom_jump {e : ℕ → ℝ} (he : Monotone e) (f g : ℕ → ℝ) (α β : ℝ)
    (h : ∀ n, g n - f n = α * e n + β) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if f (i + 1) ≤ g (i + 1) then (1 : ℝ) else 0) - (if f i ≤ g i then (1 : ℝ) else 0)| ≤
      1 := by
  rcases le_or_gt 0 α with hα | hα
  · refine indicator_variation_mono_le_one (fun n => f n ≤ g n) (fun i hi => ?_) a b
    have hi' : f i ≤ g i := hi
    show f (i + 1) ≤ g (i + 1)
    have h1 := h i
    have h2 := h (i + 1)
    have h3 := mul_le_mul_of_nonneg_left (he (Nat.le_add_right i 1)) hα
    linarith
  · refine indicator_variation_anti_le_one (fun n => f n ≤ g n) (fun i hi => ?_) a b
    have hi' : f (i + 1) ≤ g (i + 1) := hi
    show f i ≤ g i
    have h1 := h i
    have h2 := h (i + 1)
    have h3 := mul_le_mul_of_nonpos_left (he (Nat.le_add_right i 1)) hα.le
    linarith

/-- P0069 page 51, the set E4. The indicator of `upperPairRegion`, ten linear inequalities, changes
value at most 10 times along a line with affine coordinates in a nondecreasing sequence. -/
theorem four_pair_jumps (ε : ℝ) {e : ℕ → ℝ} (he : Monotone e) (Fm Fn : ℕ → ℝ) (cm tm cn tn : ℝ)
    (hm : ∀ n, Fm n = cm + tm * e n) (hn : ∀ n, Fn n = cn + tn * e n) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if upperPairRegion ε (Fm (i + 1)) (Fn (i + 1)) then (1 : ℝ) else 0) -
        (if upperPairRegion ε (Fm i) (Fn i) then (1 : ℝ) else 0)| ≤ 10 := by
  have hiff : ∀ n : ℕ, upperPairRegion ε (Fm n) (Fn n) ↔
      ((Fn n ≤ Fm n) ∧ ((Fm n ≤ 1/2) ∧ (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fn n) ∧ ((Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∧ (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε)))))))) := fun n => by
    unfold upperPairRegion
    rw [abs_le, abs_le]
  refine le_of_eq_of_le (four_ind_congr (fun n : ℕ => upperPairRegion ε (Fm n) (Fn n))
    (fun n : ℕ => ((Fn n ≤ Fm n) ∧ ((Fm n ≤ 1/2) ∧ (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fn n) ∧ ((Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∧ (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε))))))))) hiff _) ?_
  have x1 := four_atom_jump he (fun n : ℕ => Fn n) (fun n : ℕ => Fm n)
    ((tm) - (tn) - ((0) - (0)))
    ((cm) - (cn))
    (fun n => by simp only [hm, hn]; ring) a b
  have x2 := four_atom_jump he (fun n : ℕ => Fm n) (fun n : ℕ => 1/2)
    ((1/2) - (tm) - ((1/2) - (0)))
    ((1/2) - (cm))
    (fun n => by simp only [hm]; ring) a b
  have x3 := four_atom_jump he (fun n : ℕ => (1+7*(2*(1/16-1/10^5)))/15-ε) (fun n : ℕ => Fn n)
    ((tn) - ((1+7*(2*(1/16-1/10^5)))/15-ε) - ((0) - ((1+7*(2*(1/16-1/10^5)))/15-ε)))
    ((cn) - ((1+7*(2*(1/16-1/10^5)))/15-ε))
    (fun n => by simp only [hn]; ring) a b
  have x4 := four_atom_jump he (fun n : ℕ => Fn n) (fun n : ℕ => (36*(2*(1/16-1/10^5))-2)/11-ε)
    (((36*(2*(1/16-1/10^5))-2)/11-ε) - (tn) - (((36*(2*(1/16-1/10^5))-2)/11-ε) - (0)))
    (((36*(2*(1/16-1/10^5))-2)/11-ε) - (cn))
    (fun n => by simp only [hn]; ring) a b
  have x5 := four_atom_jump he (fun n : ℕ => 2*Fn n-(2*(1/16-1/10^5))+ε) (fun n : ℕ => Fm n)
    ((tm) - (2*tn-(2*(1/16-1/10^5))+ε) - ((0) - (2*0-(2*(1/16-1/10^5))+ε)))
    ((cm) - (2*cn-(2*(1/16-1/10^5))+ε))
    (fun n => by simp only [hm, hn]; ring) a b
  have x6 := four_atom_jump he (fun n : ℕ => Fm n) (fun n : ℕ => (36*(2*(1/16-1/10^5))-2)/11-ε)
    (((36*(2*(1/16-1/10^5))-2)/11-ε) - (tm) - (((36*(2*(1/16-1/10^5))-2)/11-ε) - (0)))
    (((36*(2*(1/16-1/10^5))-2)/11-ε) - (cm))
    (fun n => by simp only [hm]; ring) a b
  have x7 := (indicator_variation_and_le (fun n : ℕ => (2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n))
    (fun n : ℕ => (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) (Finset.Ico a b)).trans (add_le_add x5 x6)
  have x8 := four_atom_jump he (fun n : ℕ => -(2*(1/16-1/10^5)-ε)) (fun n : ℕ => 4*Fm n+3*Fn n-2)
    ((4*tm+3*tn-2) - (-(2*(1/16-1/10^5)-ε)) - ((4*0+3*0-2) - (-(2*(1/16-1/10^5)-ε))))
    ((4*cm+3*cn-2) - (-(2*(1/16-1/10^5)-ε)))
    (fun n => by simp only [hm, hn]; ring) a b
  have x9 := four_atom_jump he (fun n : ℕ => 4*Fm n+3*Fn n-2) (fun n : ℕ => 2*(1/16-1/10^5)-ε)
    ((2*(1/16-1/10^5)-ε) - (4*tm+3*tn-2) - ((2*(1/16-1/10^5)-ε) - (4*0+3*0-2)))
    ((2*(1/16-1/10^5)-ε) - (4*cm+3*cn-2))
    (fun n => by simp only [hm, hn]; ring) a b
  have x10 := (indicator_variation_and_le (fun n : ℕ => (-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2))
    (fun n : ℕ => (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) (Finset.Ico a b)).trans (add_le_add x8 x9)
  have x11 := four_atom_jump he (fun n : ℕ => -(2*(1/16-1/10^5)-ε)) (fun n : ℕ => 4*Fm n+Fn n-2)
    ((4*tm+tn-2) - (-(2*(1/16-1/10^5)-ε)) - ((4*0+0-2) - (-(2*(1/16-1/10^5)-ε))))
    ((4*cm+cn-2) - (-(2*(1/16-1/10^5)-ε)))
    (fun n => by simp only [hm, hn]; ring) a b
  have x12 := four_atom_jump he (fun n : ℕ => 4*Fm n+Fn n-2) (fun n : ℕ => 2*(1/16-1/10^5)-ε)
    ((2*(1/16-1/10^5)-ε) - (4*tm+tn-2) - ((2*(1/16-1/10^5)-ε) - (4*0+0-2)))
    ((2*(1/16-1/10^5)-ε) - (4*cm+cn-2))
    (fun n => by simp only [hm, hn]; ring) a b
  have x13 := (indicator_variation_and_le (fun n : ℕ => (-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2))
    (fun n : ℕ => (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) (Finset.Ico a b)).trans (add_le_add x11 x12)
  have x14 := (indicator_variation_or_le (fun n : ℕ => ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)))
    (fun n : ℕ => ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε))) (Finset.Ico a b)).trans (add_le_add x10 x13)
  have x15 := (indicator_variation_or_le (fun n : ℕ => ((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)))
    (fun n : ℕ => (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε)))) (Finset.Ico a b)).trans (add_le_add x7 x14)
  have x16 := (indicator_variation_and_le (fun n : ℕ => (Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε))
    (fun n : ℕ => (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε))))) (Finset.Ico a b)).trans (add_le_add x4 x15)
  have x17 := (indicator_variation_and_le (fun n : ℕ => ((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fn n))
    (fun n : ℕ => ((Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∧ (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε)))))) (Finset.Ico a b)).trans (add_le_add x3 x16)
  have x18 := (indicator_variation_and_le (fun n : ℕ => (Fm n ≤ 1/2))
    (fun n : ℕ => (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fn n) ∧ ((Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∧ (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε))))))) (Finset.Ico a b)).trans (add_le_add x2 x17)
  have x19 := (indicator_variation_and_le (fun n : ℕ => (Fn n ≤ Fm n))
    (fun n : ℕ => ((Fm n ≤ 1/2) ∧ (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fn n) ∧ ((Fn n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∧ (((2*Fn n-(2*(1/16-1/10^5))+ε ≤ Fm n) ∧ (Fm n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)) ∨ (((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+3*Fn n-2) ∧ (4*Fm n+3*Fn n-2 ≤ 2*(1/16-1/10^5)-ε)) ∨ ((-(2*(1/16-1/10^5)-ε) ≤ 4*Fm n+Fn n-2) ∧ (4*Fm n+Fn n-2 ≤ 2*(1/16-1/10^5)-ε)))))))) (Finset.Ico a b)).trans (add_le_add x1 x18)
  exact x19.trans (by norm_num)

/-- P0069 page 51, the set E4. The indicator of `upperPrimeCovered`, twelve copies of
`upperPairRegion`, changes value at most 120 times along a line with affine coordinates. -/
theorem four_prime_jumps (ε : ℝ) {e : ℕ → ℝ} (he : Monotone e) (Fa Fb Fc : ℕ → ℝ) (ca ta cb tb cc tc : ℝ)
    (ha : ∀ n, Fa n = ca + ta * e n) (hb : ∀ n, Fb n = cb + tb * e n) (hc : ∀ n, Fc n = cc + tc * e n) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if upperPrimeCovered ε (Fa (i + 1)) (Fb (i + 1)) (Fc (i + 1)) then (1 : ℝ) else 0) -
        (if upperPrimeCovered ε (Fa i) (Fb i) (Fc i) then (1 : ℝ) else 0)| ≤ 120 := by
  have hiff : ∀ n : ℕ, upperPrimeCovered ε (Fa n) (Fb n) (Fc n) ↔
      ((upperPairRegion ε (Fa n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n)) ∨ ((upperPairRegion ε (Fa n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n)) ∨ ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))))))))))) := fun n => by
    exact Iff.rfl
  refine le_of_eq_of_le (four_ind_congr (fun n : ℕ => upperPrimeCovered ε (Fa n) (Fb n) (Fc n))
    (fun n : ℕ => ((upperPairRegion ε (Fa n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n)) ∨ ((upperPairRegion ε (Fa n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n)) ∨ ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))))))))))))) hiff _) ?_
  have x1 := four_pair_jumps ε he Fa Fb ca ta cb tb
    ha hb a b
  have x2 := four_pair_jumps ε he Fb Fa cb tb ca ta
    hb ha a b
  have x3 := four_pair_jumps ε he Fa Fc ca ta cc tc
    ha hc a b
  have x4 := four_pair_jumps ε he Fc Fa cc tc ca ta
    hc ha a b
  have x5 := four_pair_jumps ε he Fb Fc cb tb cc tc
    hb hc a b
  have x6 := four_pair_jumps ε he Fc Fb cc tc cb tb
    hc hb a b
  have x7 := four_pair_jumps ε he (fun n : ℕ => Fa n + Fb n) Fc (ca + cb) (ta + tb) cc tc
    (fun n => by simp only [ha, hb]; ring) hc a b
  have x8 := four_pair_jumps ε he Fc (fun n : ℕ => Fa n + Fb n) cc tc (ca + cb) (ta + tb)
    hc (fun n => by simp only [ha, hb]; ring) a b
  have x9 := four_pair_jumps ε he (fun n : ℕ => Fa n + Fc n) Fb (ca + cc) (ta + tc) cb tb
    (fun n => by simp only [ha, hc]; ring) hb a b
  have x10 := four_pair_jumps ε he Fb (fun n : ℕ => Fa n + Fc n) cb tb (ca + cc) (ta + tc)
    hb (fun n => by simp only [ha, hc]; ring) a b
  have x11 := four_pair_jumps ε he (fun n : ℕ => Fb n + Fc n) Fa (cb + cc) (tb + tc) ca ta
    (fun n => by simp only [hb, hc]; ring) ha a b
  have x12 := four_pair_jumps ε he Fa (fun n : ℕ => Fb n + Fc n) ca ta (cb + cc) (tb + tc)
    ha (fun n => by simp only [hb, hc]; ring) a b
  have x13 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fb n + Fc n) (Fa n)))
    (fun n : ℕ => (upperPairRegion ε (Fa n) (Fb n + Fc n))) (Finset.Ico a b)).trans (add_le_add x11 x12)
  have x14 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fb n) (Fa n + Fc n)))
    (fun n : ℕ => ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))) (Finset.Ico a b)).trans (add_le_add x10 x13)
  have x15 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n + Fc n) (Fb n)))
    (fun n : ℕ => ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))) (Finset.Ico a b)).trans (add_le_add x9 x14)
  have x16 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fc n) (Fa n + Fb n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))))) (Finset.Ico a b)).trans (add_le_add x8 x15)
  have x17 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n + Fb n) (Fc n)))
    (fun n : ℕ => ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))))) (Finset.Ico a b)).trans (add_le_add x7 x16)
  have x18 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fc n) (Fb n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))))))) (Finset.Ico a b)).trans (add_le_add x6 x17)
  have x19 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fb n) (Fc n)))
    (fun n : ℕ => ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))))))) (Finset.Ico a b)).trans (add_le_add x5 x18)
  have x20 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fc n) (Fa n)))
    (fun n : ℕ => ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))))))))) (Finset.Ico a b)).trans (add_le_add x4 x19)
  have x21 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n) (Fc n)))
    (fun n : ℕ => ((upperPairRegion ε (Fc n) (Fa n)) ∨ ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))))))))) (Finset.Ico a b)).trans (add_le_add x3 x20)
  have x22 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fb n) (Fa n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n)) ∨ ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n)))))))))))) (Finset.Ico a b)).trans (add_le_add x2 x21)
  have x23 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n) (Fb n)))
    (fun n : ℕ => ((upperPairRegion ε (Fb n) (Fa n)) ∨ ((upperPairRegion ε (Fa n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n)) ∨ ((upperPairRegion ε (Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fa n + Fb n) (Fc n)) ∨ ((upperPairRegion ε (Fc n) (Fa n + Fb n)) ∨ ((upperPairRegion ε (Fa n + Fc n) (Fb n)) ∨ ((upperPairRegion ε (Fb n) (Fa n + Fc n)) ∨ ((upperPairRegion ε (Fb n + Fc n) (Fa n)) ∨ (upperPairRegion ε (Fa n) (Fb n + Fc n))))))))))))) (Finset.Ico a b)).trans (add_le_add x1 x22)
  exact x23.trans (by norm_num)

/-- P0069 page 51, the set E4. The indicator of `lowerFourCovered`, four copies of
`upperPrimeCovered` and four of `upperPairRegion`, changes value at most 520 times along a line
with affine coordinates. -/
theorem four_covered_jumps (ε : ℝ) {e : ℕ → ℝ} (he : Monotone e) (Fa Fb Fc Fd : ℕ → ℝ) (ca ta cb tb cc tc cd td : ℝ)
    (ha : ∀ n, Fa n = ca + ta * e n) (hb : ∀ n, Fb n = cb + tb * e n) (hc : ∀ n, Fc n = cc + tc * e n) (hd : ∀ n, Fd n = cd + td * e n) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if lowerFourCovered ε (Fa (i + 1)) (Fb (i + 1)) (Fc (i + 1)) (Fd (i + 1)) then (1 : ℝ) else 0) -
        (if lowerFourCovered ε (Fa i) (Fb i) (Fc i) (Fd i) then (1 : ℝ) else 0)| ≤ 520 := by
  have hiff : ∀ n : ℕ, lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n) ↔
      ((upperPrimeCovered ε (Fa n) (Fb n) (Fc n)) ∨ ((upperPrimeCovered ε (Fa n) (Fb n) (Fd n)) ∨ ((upperPrimeCovered ε (Fa n) (Fc n) (Fd n)) ∨ ((upperPrimeCovered ε (Fb n) (Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n))))))))) := fun n => by
    exact Iff.rfl
  refine le_of_eq_of_le (four_ind_congr (fun n : ℕ => lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))
    (fun n : ℕ => ((upperPrimeCovered ε (Fa n) (Fb n) (Fc n)) ∨ ((upperPrimeCovered ε (Fa n) (Fb n) (Fd n)) ∨ ((upperPrimeCovered ε (Fa n) (Fc n) (Fd n)) ∨ ((upperPrimeCovered ε (Fb n) (Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n)))))))))) hiff _) ?_
  have x1 := four_prime_jumps ε he Fa Fb Fc ca ta cb tb cc tc
    ha hb hc a b
  have x2 := four_prime_jumps ε he Fa Fb Fd ca ta cb tb cd td
    ha hb hd a b
  have x3 := four_prime_jumps ε he Fa Fc Fd ca ta cc tc cd td
    ha hc hd a b
  have x4 := four_prime_jumps ε he Fb Fc Fd cb tb cc tc cd td
    hb hc hd a b
  have x5 := four_pair_jumps ε he (fun n : ℕ => Fa n + Fb n + Fc n) Fd (ca + cb + cc) (ta + tb + tc) cd td
    (fun n => by simp only [ha, hb, hc]; ring) hd a b
  have x6 := four_pair_jumps ε he (fun n : ℕ => Fa n + Fb n + Fd n) Fc (ca + cb + cd) (ta + tb + td) cc tc
    (fun n => by simp only [ha, hb, hd]; ring) hc a b
  have x7 := four_pair_jumps ε he (fun n : ℕ => Fa n + Fc n + Fd n) Fb (ca + cc + cd) (ta + tc + td) cb tb
    (fun n => by simp only [ha, hc, hd]; ring) hb a b
  have x8 := four_pair_jumps ε he (fun n : ℕ => Fb n + Fc n + Fd n) Fa (cb + cc + cd) (tb + tc + td) ca ta
    (fun n => by simp only [hb, hc, hd]; ring) ha a b
  have x9 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)))
    (fun n : ℕ => (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n))) (Finset.Ico a b)).trans (add_le_add x7 x8)
  have x10 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n)))) (Finset.Ico a b)).trans (add_le_add x6 x9)
  have x11 := (indicator_variation_or_le (fun n : ℕ => (upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n))))) (Finset.Ico a b)).trans (add_le_add x5 x10)
  have x12 := (indicator_variation_or_le (fun n : ℕ => (upperPrimeCovered ε (Fb n) (Fc n) (Fd n)))
    (fun n : ℕ => ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n)))))) (Finset.Ico a b)).trans (add_le_add x4 x11)
  have x13 := (indicator_variation_or_le (fun n : ℕ => (upperPrimeCovered ε (Fa n) (Fc n) (Fd n)))
    (fun n : ℕ => ((upperPrimeCovered ε (Fb n) (Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n))))))) (Finset.Ico a b)).trans (add_le_add x3 x12)
  have x14 := (indicator_variation_or_le (fun n : ℕ => (upperPrimeCovered ε (Fa n) (Fb n) (Fd n)))
    (fun n : ℕ => ((upperPrimeCovered ε (Fa n) (Fc n) (Fd n)) ∨ ((upperPrimeCovered ε (Fb n) (Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n)))))))) (Finset.Ico a b)).trans (add_le_add x2 x13)
  have x15 := (indicator_variation_or_le (fun n : ℕ => (upperPrimeCovered ε (Fa n) (Fb n) (Fc n)))
    (fun n : ℕ => ((upperPrimeCovered ε (Fa n) (Fb n) (Fd n)) ∨ ((upperPrimeCovered ε (Fa n) (Fc n) (Fd n)) ∨ ((upperPrimeCovered ε (Fb n) (Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fc n) (Fd n)) ∨ ((upperPairRegion ε (Fa n + Fb n + Fd n) (Fc n)) ∨ ((upperPairRegion ε (Fa n + Fc n + Fd n) (Fb n)) ∨ (upperPairRegion ε (Fb n + Fc n + Fd n) (Fa n))))))))) (Finset.Ico a b)).trans (add_le_add x1 x14)
  exact x15.trans (by norm_num)

/-- P0069 page 51, the set E4. The indicator of the conservative region `lowerFourRegion`, six
linear inequalities and the complement of `lowerFourCovered`, changes value at most 526 times
along a line with affine coordinates in a nondecreasing sequence. -/
theorem four_region_jumps_affine (ε : ℝ) {e : ℕ → ℝ} (he : Monotone e) (Fa Fb Fc Fd : ℕ → ℝ) (ca ta cb tb cc tc cd td : ℝ)
    (ha : ∀ n, Fa n = ca + ta * e n) (hb : ∀ n, Fb n = cb + tb * e n) (hc : ∀ n, Fc n = cc + tc * e n) (hd : ∀ n, Fd n = cd + td * e n) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if lowerFourRegion ε (Fa (i + 1)) (Fb (i + 1)) (Fc (i + 1)) (Fd (i + 1)) then (1 : ℝ) else 0) -
        (if lowerFourRegion ε (Fa i) (Fb i) (Fc i) (Fd i) then (1 : ℝ) else 0)| ≤ 526 := by
  have hiff : ∀ n : ℕ, lowerFourRegion ε (Fa n) (Fb n) (Fc n) (Fd n) ↔
      (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fd n) ∧ ((Fd n ≤ Fc n) ∧ ((Fc n ≤ Fb n) ∧ ((Fb n ≤ Fa n) ∧ ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))))))))) := fun n => by
    exact Iff.rfl
  refine le_of_eq_of_le (four_ind_congr (fun n : ℕ => lowerFourRegion ε (Fa n) (Fb n) (Fc n) (Fd n))
    (fun n : ℕ => (((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fd n) ∧ ((Fd n ≤ Fc n) ∧ ((Fc n ≤ Fb n) ∧ ((Fb n ≤ Fa n) ∧ ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n)))))))))) hiff _) ?_
  have x1 := four_atom_jump he (fun n : ℕ => (1+7*(2*(1/16-1/10^5)))/15-ε) (fun n : ℕ => Fd n)
    ((td) - ((1+7*(2*(1/16-1/10^5)))/15-ε) - ((0) - ((1+7*(2*(1/16-1/10^5)))/15-ε)))
    ((cd) - ((1+7*(2*(1/16-1/10^5)))/15-ε))
    (fun n => by simp only [hd]; ring) a b
  have x2 := four_atom_jump he (fun n : ℕ => Fd n) (fun n : ℕ => Fc n)
    ((tc) - (td) - ((0) - (0)))
    ((cc) - (cd))
    (fun n => by simp only [hc, hd]; ring) a b
  have x3 := four_atom_jump he (fun n : ℕ => Fc n) (fun n : ℕ => Fb n)
    ((tb) - (tc) - ((0) - (0)))
    ((cb) - (cc))
    (fun n => by simp only [hb, hc]; ring) a b
  have x4 := four_atom_jump he (fun n : ℕ => Fb n) (fun n : ℕ => Fa n)
    ((ta) - (tb) - ((0) - (0)))
    ((ca) - (cb))
    (fun n => by simp only [ha, hb]; ring) a b
  have x5 := four_atom_jump he (fun n : ℕ => Fa n+2*Fb n) (fun n : ℕ => 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε)
    ((1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) - (ta+2*tb) - ((1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) - (0+2*0)))
    ((1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) - (ca+2*cb))
    (fun n => by simp only [ha, hb]; ring) a b
  have x6 := four_atom_jump he (fun n : ℕ => Fa n+Fb n+Fc n) (fun n : ℕ => 1/2+(2*(1/16-1/10^5))/4-2*ε)
    ((1/2+(2*(1/16-1/10^5))/4-2*ε) - (ta+tb+tc) - ((1/2+(2*(1/16-1/10^5))/4-2*ε) - (0+0+0)))
    ((1/2+(2*(1/16-1/10^5))/4-2*ε) - (ca+cb+cc))
    (fun n => by simp only [ha, hb, hc]; ring) a b
  have x7 := four_covered_jumps ε he Fa Fb Fc Fd ca ta cb tb cc tc cd td
    ha hb hc hd a b
  have x8 := (indicator_variation_not_eq (fun n : ℕ => (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))) (Finset.Ico a b)).le.trans x7
  have x9 := (indicator_variation_and_le (fun n : ℕ => (Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε))
    (fun n : ℕ => (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n)))) (Finset.Ico a b)).trans (add_le_add x6 x8)
  have x10 := (indicator_variation_and_le (fun n : ℕ => (Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε))
    (fun n : ℕ => ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))))) (Finset.Ico a b)).trans (add_le_add x5 x9)
  have x11 := (indicator_variation_and_le (fun n : ℕ => (Fb n ≤ Fa n))
    (fun n : ℕ => ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n)))))) (Finset.Ico a b)).trans (add_le_add x4 x10)
  have x12 := (indicator_variation_and_le (fun n : ℕ => (Fc n ≤ Fb n))
    (fun n : ℕ => ((Fb n ≤ Fa n) ∧ ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))))))) (Finset.Ico a b)).trans (add_le_add x3 x11)
  have x13 := (indicator_variation_and_le (fun n : ℕ => (Fd n ≤ Fc n))
    (fun n : ℕ => ((Fc n ≤ Fb n) ∧ ((Fb n ≤ Fa n) ∧ ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n)))))))) (Finset.Ico a b)).trans (add_le_add x2 x12)
  have x14 := (indicator_variation_and_le (fun n : ℕ => ((1+7*(2*(1/16-1/10^5)))/15-ε ≤ Fd n))
    (fun n : ℕ => ((Fd n ≤ Fc n) ∧ ((Fc n ≤ Fb n) ∧ ((Fb n ≤ Fa n) ∧ ((Fa n+2*Fb n ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε) ∧ ((Fa n+Fb n+Fc n ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε) ∧ (¬ (lowerFourCovered ε (Fa n) (Fb n) (Fc n) (Fd n))))))))) (Finset.Ico a b)).trans (add_le_add x1 x13)
  exact x14.trans (by norm_num)

/-- P0069 page 51, the set E4, "boundedly many jumps" along a line: the statement of
`leaf_four_region_jumps`. Along any line whose four coordinates are affine functions of one
nondecreasing sequence `e`, the indicator of the region changes value at most 600 times. -/
theorem four_region_jumps (ε : ℝ) (e : ℕ → ℝ) (he : Monotone e)
    (c1 t1 c2 t2 c3 t3 c4 t4 : ℝ) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b,
      |(if lowerFourRegion ε (c1 + t1 * e (i + 1)) (c2 + t2 * e (i + 1)) (c3 + t3 * e (i + 1))
            (c4 + t4 * e (i + 1)) then (1 : ℝ) else 0) -
        (if lowerFourRegion ε (c1 + t1 * e i) (c2 + t2 * e i) (c3 + t3 * e i)
            (c4 + t4 * e i) then (1 : ℝ) else 0)| ≤ 600 :=
  (four_region_jumps_affine ε he (fun n => c1 + t1 * e n) (fun n => c2 + t2 * e n)
    (fun n => c3 + t3 * e n) (fun n => c4 + t4 * e n) c1 t1 c2 t2 c3 t3 c4 t4
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) a b).trans (by norm_num)

#print axioms four_region_jumps

end LeanLab.BHP1997.LowerShortC165

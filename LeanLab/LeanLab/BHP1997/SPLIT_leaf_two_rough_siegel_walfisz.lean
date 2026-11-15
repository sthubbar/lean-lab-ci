/-
Split of the two-prime rough input `leaf_two_rough_siegel_walfisz` of `Decomp514a`
into three leaves, with the sealed statement left unchanged and the target neither
imported nor used.

Where the cut is made. The coefficient `lowerTwoTerms` is a finite sum over the ordered
prime pairs `p2 < p1` with `p1 * p2 ∣ m` whose exponent pair lies in the discarded region.
Write `n = m / (p1 * p2)` for the rough cofactor. The ordered two-prime expansion is cut
at `n = p2`: a pair is long when `p2 ≤ n` and short otherwise, which is the cut the argument
itself makes, since a long cofactor is the case where the rough variable is long enough to
carry the character saving, and a short one forces `n < p2 < p1` and hence `n ^ 3 < m`, a
short rough variable. The recorded obstruction for this input names exactly two missing
pieces, the ordered prime factor reindexing and the character cancellation after summing the
outer exponent pairs; the first leaf is the reindexing bookkeeping and is proved here, the
other two leaves are the cancellation on the two ranges. Each sub-sum is strictly smaller
than the whole family: it drops the other range of pairs, keeps the same quantifier block
and the same modulus range, and adds no hypothesis that the family does not already satisfy.
The extension at the end is the triangle inequality together with the two constants; it has
no unproved step.

Degenerate readings checked before keeping the leaves. At `m = 0` the divisor set is empty
(`Nat.divisors 0 = ∅`) and all three sums are zero, so the identity holds there too. At
`m = 1`, and at every `m` with no admissible ordered pair, both sides are zero as well. The
split condition `p2 ≤ m / (p1 * p2)` is the truncated natural division, which is harmless
here because the guard `p1 * p2 ∣ m` makes the quotient exact on every term that survives
it; when the guard fails the term is zero on both sides. At `ε > 0` the exponent
`11 / 20 + ε` stays in `(11 / 20, 11 / 20 + 1/10^8]`, so no negative power of `x` appears.
In the extension the constant is `max (2 * max C1 C2) 1`, which is at least one, so `x ≥ 1`,
hence `Real.log x ≥ 0` and the factor `Real.log x ^ (-A)` is nonnegative; that also excludes
`x = 0`. A negative leaf constant is allowed and does not break the extension: the two leaf
bounds are added and compared with `max (2 * max C1 C2) 1`, which dominates `C1 + C2` in both
sign regimes.

The two analytic leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-- LEAF 1 of 3. Step: the pointwise bookkeeping identity. The coefficient of `m` in the
ordered two-prime expansion equals its long-cofactor piece, where the rough cofactor `n`
satisfies `p2 ≤ n`, plus its short-cofactor piece, where `n < p2`. Both pieces keep the same
guards: both primes, `p2 < p1`, `p1 * p2 ∣ m`, and the discarded exponent region. Proved
here, so this leaf is closed. -/
theorem leaf_two_terms_pair_split (ε x : ℝ) (m : ℕ) :
    lowerTwoTerms ε x m = (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) + (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) := by
  have hp : ∀ p1 p2 : ℕ,
      (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) then rough (m / (p1 * p2)) p2 else (0 : ℝ)) =
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2) then rough (m / (p1 * p2)) p2 else 0) +
          (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2)) then rough (m / (p1 * p2)) p2 else 0) := by
    intro p1 p2
    by_cases hb : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
    · by_cases he : p2 ≤ m / (p1 * p2)
      · rw [ite_eq_left hb, ite_eq_left ⟨hb, he⟩, ite_eq_right (by simp [he]), add_zero]
      · rw [ite_eq_left hb, ite_eq_right (by simp [he]), ite_eq_left ⟨hb, he⟩, zero_add]
    · rw [ite_eq_right hb, ite_eq_right (fun h : (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧ p2 ≤ m / (p1 * p2) => hb h.1),
        ite_eq_right (fun h : (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧ ¬ (p2 ≤ m / (p1 * p2)) => hb h.1), add_zero]
  unfold lowerTwoTerms
  calc (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
        (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) then rough (m / (p1 * p2)) p2 else (0 : ℝ)))
      = ∑ p1 ∈ m.divisors,
          ((∑ p2 ∈ m.divisors,
              (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
                  ∧ p2 ≤ m / (p1 * p2) then rough (m / (p1 * p2)) p2 else 0)) +
            (∑ p2 ∈ m.divisors,
              (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
                  ∧ ¬ (p2 ≤ m / (p1 * p2)) then rough (m / (p1 * p2)) p2 else 0))) := by
        refine Finset.sum_congr rfl (fun p1 _ => ?_)
        exact (Finset.sum_congr rfl (fun p2 _ => hp p1 p2)).trans Finset.sum_add_distrib
    _ = (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) + (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) := Finset.sum_add_distrib

/-- A divisor sum of `m` is a sum over a box, with the divisibility indicator. -/
private theorem sum_divisors_eq_sum_Icc {α : Type*} [AddCommMonoid α] {m N : ℕ}
    (hmN : m ≤ N) (hm0 : m ≠ 0) (f : ℕ → α) :
    ∑ p ∈ m.divisors, f p = ∑ p ∈ Finset.Icc 1 N, if p ∣ m then f p else 0 := by
  have hsub : m.divisors ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpd, _⟩ := Nat.mem_divisors.mp hp
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hpd hmpos,
      (Nat.le_of_dvd hmpos hpd).trans hmN⟩
  have key := Finset.sum_subset hsub (f := fun p => if p ∣ m then f p else 0)
    (fun p _ hpn => by
      rw [if_neg]
      intro hpd
      exact hpn (Nat.mem_divisors.mpr ⟨hpd, hm0⟩))
  rw [show (∑ p ∈ m.divisors, f p) = ∑ p ∈ m.divisors, (if p ∣ m then f p else 0) from
    Finset.sum_congr rfl (fun p hp => by rw [if_pos (Nat.mem_divisors.mp hp).1])]
  exact key

/-- Summing over the multiples of `P` in `S` is summing over the quotients `n` with `P * n ∈ S`. -/
private theorem sum_filter_dvd_eq {α : Type*} [AddCommMonoid α] {P N : ℕ} (hP : 0 < P)
    {S : Finset ℕ} (hSpos : ∀ m ∈ S, 0 < m) (hSN : ∀ m ∈ S, m ≤ N) (f : ℕ → α) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => P * n ∈ S), f (P * n)
      = ∑ m ∈ S.filter (fun m => P ∣ m), f m := by
  set T : Finset ℕ := (Finset.Icc 1 N).filter (fun n => P * n ∈ S) with hT
  have himg : T.image (fun n => P * n) = S.filter (fun m => P ∣ m) := by
    ext m
    constructor
    · intro hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨-, hnS⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnS, ⟨n, rfl⟩⟩
    · intro hm
      obtain ⟨hmS, n, rfl⟩ := Finset.mem_filter.mp hm
      have hm0 : 0 < P * n := hSpos _ hmS
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · rw [h, mul_zero] at hm0
          exact absurd hm0 (lt_irrefl 0)
        · exact h
      have hnN : n ≤ N := (Nat.le_mul_of_pos_left n hP).trans (hSN _ hmS)
      exact Finset.mem_image.mpr
        ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hmS⟩, rfl⟩
  have hsum : ∑ m ∈ T.image (fun n => P * n), f m = ∑ n ∈ T, f (P * n) :=
    Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel hP hab)
  rw [← himg, ← hsum]

/-- The ordered prime expansion of the rough variable: a triple sum over `(p1, p2, n)` with
`m = p1 * p2 * n`, for a coefficient that vanishes when `p1 * p2 ∤ m`. -/
private theorem sum_divisors_reindex {α : Type*} [AddCommMonoid α] {S : Finset ℕ} {N : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m) (hSN : ∀ m ∈ S, m ≤ N)
    (F : ℕ → ℕ → ℕ → α) (hF : ∀ m p1 p2, ¬ (p1 * p2 ∣ m) → F m p1 p2 = 0) :
    ∑ m ∈ S, ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, F m p1 p2
      = ∑ p1 ∈ Finset.Icc 1 N, ∑ p2 ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if p1 * p2 * n ∈ S then F (p1 * p2 * n) p1 p2 else 0 := by
  have hbox : ∑ m ∈ S, ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, F m p1 p2
      = ∑ m ∈ S, ∑ p1 ∈ Finset.Icc 1 N, ∑ p2 ∈ Finset.Icc 1 N,
          if p1 * p2 ∣ m then F m p1 p2 else 0 := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [sum_divisors_eq_sum_Icc (hSN m hm) (ne_of_gt (hSpos m hm))]
    refine Finset.sum_congr rfl (fun p1 _ => ?_)
    by_cases hpm : p1 ∣ m
    · rw [if_pos hpm, sum_divisors_eq_sum_Icc (hSN m hm) (ne_of_gt (hSpos m hm))]
      refine Finset.sum_congr rfl (fun p2 _ => ?_)
      by_cases h2 : p2 ∣ m
      · rw [if_pos h2]
        by_cases hp : p1 * p2 ∣ m
        · rw [if_pos hp]
        · rw [if_neg hp, hF m p1 p2 hp]
      · rw [if_neg h2]
        by_cases hp : p1 * p2 ∣ m
        · rw [if_pos hp]
          exact absurd (dvd_trans (show p2 ∣ p1 * p2 from ⟨p1, mul_comm p1 p2⟩) hp) h2
        · rw [if_neg hp]
    · rw [if_neg hpm]
      refine (Finset.sum_eq_zero (fun p2 _ => ?_)).symm
      by_cases hp : p1 * p2 ∣ m
      · rw [if_pos hp]
        exact absurd (dvd_trans (show p1 ∣ p1 * p2 from ⟨p2, rfl⟩) hp) hpm
      · rw [if_neg hp]
  refine hbox.trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p1 hp1 => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p2 hp2 => ?_)
  have hP : 0 < p1 * p2 :=
    Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp1).1)
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp2).1)
  rw [← Finset.sum_filter, ← sum_filter_dvd_eq (P := p1 * p2) hP hSpos hSN (fun m => F m p1 p2),
    Finset.sum_filter]

/-- The long-cofactor summand reindexed onto the triple `(p1, p2, n)`, `m = p1 * p2 * n`:
the ordered prime expansion of the rough variable that `Decomp514a` names as its missing step. -/
private theorem long_reindex_triple {ε x : ℝ} (t : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
              ∧ p2 ≤ m / (p1 * p2)
              then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)
      = ∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
          if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
              lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
              p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
            then (rough n p2 : ℂ) * χ ((p1 * p2 * n : ℕ) : ZMod q) else 0 := by
  have hSpos : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t), 0 < m := by
    intro m hm
    have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    omega
  have hSN : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t), m ≤ ⌊t⌋₊ := by
    intro m hm
    exact Nat.le_floor (Finset.mem_filter.mp hm).2
  have hcast : ∀ m : ℕ,
      (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
              ∧ p2 ≤ m / (p1 * p2)
              then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)
        = ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            (((if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
              ∧ p2 ≤ m / (p1 * p2)
              then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) := by
    intro m
    have h1 : (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
          if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
              lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ)
        = ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            (((if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
              ∧ p2 ≤ m / (p1 * p2)
              then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p1 _ => ?_)
      rw [Complex.ofReal_sum]
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p1 _ => ?_)
    rw [Finset.sum_mul]
  simp_rw [hcast]
  rw [sum_divisors_reindex hSpos hSN
    (fun m p1 p2 => (((if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
      ∧ p2 ≤ m / (p1 * p2)
      then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) ?_]
  · refine Finset.sum_congr rfl (fun p1 hp1 => Finset.sum_congr rfl (fun p2 hp2 =>
      Finset.sum_congr rfl (fun n _ => ?_)))
    have hP : 0 < p1 * p2 :=
      Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp1).1)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp2).1)
    have hdiv : (p1 * p2 * n) / (p1 * p2) = n := Nat.mul_div_right n hP
    have hdvd : p1 * p2 ∣ p1 * p2 * n := ⟨n, rfl⟩
    by_cases hq : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n
    · by_cases hPS : p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)
      · have hR : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) := by
          tauto
        have hF : ((p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ p1 * p2 * n ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧
            p2 ≤ (p1 * p2 * n) / (p1 * p2)) := by
          rw [hdiv]
          tauto
        rw [if_pos hPS, if_pos hR, if_pos hF, hdiv]
        try rfl
      · have hconjR : ¬ (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) := by
          tauto
        rw [if_neg hPS, if_neg hconjR]
    · have hconjR : ¬ (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
          lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
          p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) := by
        tauto
      by_cases hPS : p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)
      · have hcF : ¬ ((p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ p1 * p2 * n ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧
            p2 ≤ (p1 * p2 * n) / (p1 * p2)) := by
          rw [hdiv]
          tauto
        rw [if_pos hPS, if_neg hcF, if_neg hconjR]
        simp
      · rw [if_neg hPS, if_neg hconjR]
  · intro m p1 p2 h
    have hc : ¬ ((p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧ p2 ≤ m / (p1 * p2)) := by
      intro hcc
      exact h hcc.1.2.2.2.1
    rw [if_neg hc]
    simp

/-! ### Two bricks towards leaf 2

The long-cofactor sum is a triple sum over `(p1, p2, n)` with `m = p1 * p2 * n`
(`long_reindex_triple`). Two steps of the argument do not depend on the arithmetic of the
exponent region, and are proved here:

* `prime_char_interval_bound`: the prime-character prefix bound of `Prime514` on an arbitrary
  integer interval, by subtracting the two prefix errors.
* `long_le_prime_chi_window`: for fixed `(p2, n)` the factor `ψ(n, p2) χ p2 χ n` pulls out of
  the `p1` sum and has norm at most `ψ(n, p2) ≤ 1`, so the long sum is dominated by a sum of
  `p1`-window character sums.

What is still missing for leaf 2 is the arithmetic of the region: `lowerTwoDiscarded` has to
be disintegrated in `expo p1` into finitely many intervals (for fixed `expo p2` it is the
interval `[b, min (1/2) (1 - 2b)]` minus the finitely many covered intervals `X`, `Y`, `Z`,
`W`), so that `prime_char_interval_bound` can be applied to each piece at ambient scale
`2 * Y / (p2 * n)`, and the resulting `∑ 1 / (p2 * n)` has to be bounded by a polylogarithm.
-/

/-- The prime-character prefix bound of `Prime514.character_prime_prefix_bound` on an
arbitrary integer interval `(⌊u⌋, ⌊v⌋]`, by subtracting the two prefix errors. -/
private theorem prime_char_interval_bound (D : ℝ) (hD : 0 < D) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ Real.sqrt X / Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ X →
        ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)‖ ≤
          2 * ((q : ℝ) * (K * X / Real.log X ^ D)) := by
  obtain ⟨B, hB, K, hK, hb⟩ := LeanLab.BHP1997.Prime514.character_prime_prefix_bound D hD
  refine ⟨B, hB, K, hK, fun X hX q _ hq hqX χ hχ u v hu huv hv => ?_⟩
  have hsplit : (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q))
      = (∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q))
        - (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)) := by
    have hc := Finset.sum_Ioc_consecutive
      (fun n : ℕ => (primeWeight n : ℂ) * χ (n : ZMod q)) (Nat.zero_le ⌊u⌋₊)
      (Nat.floor_le_floor huv)
    have h0 : ∀ N : ℕ, (∑ n ∈ Finset.Ioc 0 N, (primeWeight n : ℂ) * χ (n : ZMod q))
        = ∑ n ∈ Finset.Icc 1 N, (primeWeight n : ℂ) * χ (n : ZMod q) := by
      intro N
      have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hset]
    rw [h0, h0] at hc
    rw [eq_sub_iff_add_eq, add_comm]
    exact hc
  rw [hsplit]
  have h1 := hb X hX q hq hqX χ hχ v (hu.trans huv) hv
  have h2 := hb X hX q hq hqX χ hχ u hu (huv.trans hv)
  calc ‖(∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q))
        - (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q))‖
      ≤ ‖∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)‖
        + ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)‖ := norm_sub_le _ _
    _ ≤ (q : ℝ) * (K * X / Real.log X ^ D) + (q : ℝ) * (K * X / Real.log X ^ D) :=
        add_le_add h1 h2
    _ = 2 * ((q : ℝ) * (K * X / Real.log X ^ D)) := by ring

/-- `χ` of a product of three natural numbers is the product of the three values. -/
private theorem chi_three {q : ℕ} (χ : DirichletCharacter ℂ q) (p1 p2 n : ℕ) :
    χ ((p1 * p2 * n : ℕ) : ZMod q) =
      χ (p1 : ZMod q) * χ (p2 : ZMod q) * χ (n : ZMod q) := by
  rw [Nat.cast_mul, Nat.cast_mul, map_mul, map_mul]

/-- Swap the order of a triple finite sum: `sum_{p1} sum_{p2} sum_n = sum_{p2} sum_n sum_{p1}`. -/
private theorem sum_swap_three {ι : Type*} [DecidableEq ι] (s t u : Finset ι)
    (F : ι → ι → ι → ℂ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, F a b c) = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, F a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]

/-- The long-cofactor triple sum is dominated by the `p1`-window character sums: for fixed
`(p2, n)` the factor `ψ(n, p2) χ p2 χ n` pulls out of the `p1` sum and has norm at most
`ψ(n, p2) ≤ 1`. -/
private theorem long_le_prime_chi_window {ε x : ℝ} (t : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖
      ≤ ∑ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
          rough n p2 * ‖∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
                p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
              then χ (p1 : ZMod q) else 0‖ := by
  rw [long_reindex_triple t χ, sum_swap_three]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p2 _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  have hfac : (∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
        if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then (rough n p2 : ℂ) * χ ((p1 * p2 * n : ℕ) : ZMod q) else 0)
      = ((rough n p2 : ℂ) * (χ (p2 : ZMod q) * χ (n : ZMod q))) *
        (∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
          if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
              lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
              p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p1 _ => ?_)
    by_cases hC : (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
        p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
    · rw [if_pos hC, if_pos hC, chi_three]
      ring
    · rw [if_neg hC, if_neg hC, mul_zero]
  rw [hfac, norm_mul]
  have hr : (0 : ℝ) ≤ rough n p2 := rough_nonneg n p2
  have hnorm : ‖((rough n p2 : ℝ) : ℂ) * (χ (p2 : ZMod q) * χ (n : ZMod q))‖ ≤ rough n p2 := by
    have h1 := χ.norm_le_one (p2 : ZMod q)
    have h2 := χ.norm_le_one (n : ZMod q)
    have h3 : (0 : ℝ) ≤ ‖χ (p2 : ZMod q)‖ := norm_nonneg _
    have h4 : (0 : ℝ) ≤ ‖χ (n : ZMod q)‖ := norm_nonneg _
    have h5 : ‖χ (p2 : ZMod q)‖ * ‖χ (n : ZMod q)‖ ≤ 1 := by
      nlinarith [mul_le_mul h1 h2 h4 zero_le_one]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    nlinarith [h5, hr]
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- `expo` is `log p / log Z`, so for `Z > 1` and `p ≥ 1` the condition `expo p ≤ u` is the
interval condition `p ≤ Z ^ u`. This is the translation that turns the exponent region
`lowerTwoDiscarded` into intervals in the prime `p1`. -/
private theorem expo_le_iff {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p) {u : ℝ} :
    expo ε x p ≤ u ↔ (p : ℝ) ≤ scaleZ ε x ^ u := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold expo
  rw [div_le_iff₀ hLZ, ← Real.log_rpow hZ0 u,
    Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hZ0 u)]

/-- Strict form of `expo_le_iff`. -/
private theorem expo_lt_iff {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p) {u : ℝ} :
    expo ε x p < u ↔ (p : ℝ) < scaleZ ε x ^ u := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ
  unfold expo
  rw [div_lt_iff₀ hLZ, ← Real.log_rpow hZ0 u,
    Real.log_lt_log_iff (by exact_mod_cast hp) (Real.rpow_pos_of_pos hZ0 u)]

/-- `expo`, strict lower form: `l < expo p` is the interval condition `Z ^ l < p`. -/
private theorem lt_expo_iff {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p) {l : ℝ} :
    l < expo ε x p ↔ scaleZ ε x ^ l < (p : ℝ) := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold expo
  rw [lt_div_iff₀ hLZ, ← Real.log_rpow hZ0 l,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hZ0 l) hp0]

/-- `expo p` lies in `(l, u]` exactly when `p` lies in `(Z ^ l, Z ^ u]`, for `Z > 1` and
`p ≥ 1`. -/
private theorem expo_mem_Ioc_iff {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p)
    {l u : ℝ} :
    expo ε x p ∈ Set.Ioc l u ↔ (p : ℝ) ∈ Set.Ioc (scaleZ ε x ^ l) (scaleZ ε x ^ u) := by
  rw [Set.mem_Ioc, Set.mem_Ioc, lt_expo_iff hZ hp, expo_le_iff hZ hp]

/-- The exponent of a prime in the discarded region: `E2` keeps `expo p1 ≤ 1 / 2` and
`expo p2 ≤ expo p1`. Hence every ordered pair of the long-cofactor piece has
`p1 ≤ Z ^ (1 / 2)` and `p2 ≤ p1`. -/
private theorem discarded_expo_bounds {ε : ℝ} {a b : ℝ} (h : lowerTwoDiscarded ε a b) :
    b ≤ a ∧ a ≤ 1 / 2 := ⟨h.2.1, h.2.2.1⟩

/-- `expo` dominates a constant exactly when the prime dominates `Z ^ l`. -/
private theorem le_expo_iff {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p) {l : ℝ} :
    l ≤ expo ε x p ↔ scaleZ ε x ^ l ≤ (p : ℝ) := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ
  unfold expo
  rw [le_div_iff₀ hLZ, ← Real.log_rpow hZ0 l,
    Real.log_le_log_iff (Real.rpow_pos_of_pos hZ0 l) (by exact_mod_cast hp)]

/-- `expo p ≤ u` as an integer interval condition on `p`. -/
private theorem expo_le_iff_floor {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p)
    {u : ℝ} : expo ε x p ≤ u ↔ p ≤ ⌊scaleZ ε x ^ u⌋₊ := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  rw [expo_le_iff hZ hp]
  constructor
  · exact Nat.le_floor
  · intro h
    exact le_trans (by exact_mod_cast h) (Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hZ0 u)))

/-- `l ≤ expo p` as an integer interval condition on `p`. -/
private theorem le_expo_iff_ceil {ε x : ℝ} (hZ : 1 < scaleZ ε x) {p : ℕ} (hp : 1 ≤ p)
    {l : ℝ} : l ≤ expo ε x p ↔ ⌈scaleZ ε x ^ l⌉₊ ≤ p :=
  (le_expo_iff hZ hp).trans Nat.ceil_le.symm

/-- The discarded region as a product of five step functions in `a`, one per clause of `E2`:
the base interval `[b, min (1/2) (1 - 2b)]` times the four complements of the covered sets
`X`, `Y`, `Z` and `upperPairRegion`. Because a product of step functions has variation at
most the sum of their variations, this replaces "decompose the region into intervals" by
"bound the character sum against a step function", and no ordering of the covered intervals is
needed. -/
private theorem ite_five_prod (P Q1 Q2 Q3 Q4 : Prop) [Decidable P] [Decidable Q1] [Decidable Q2]
    [Decidable Q3] [Decidable Q4] :
    (if (P ∧ ¬ Q1 ∧ ¬ Q2 ∧ ¬ Q3 ∧ ¬ Q4) then (1 : ℝ) else 0) =
      (if P then (1 : ℝ) else 0) * (if Q1 then (0 : ℝ) else 1) * (if Q2 then (0 : ℝ) else 1)
        * (if Q3 then (0 : ℝ) else 1) * (if Q4 then (0 : ℝ) else 1) := by
  by_cases hP : P <;> by_cases h1 : Q1 <;> by_cases h2 : Q2 <;> by_cases h3 : Q3 <;>
    by_cases h4 : Q4 <;> simp [hP, h1, h2, h3, h4]

private theorem region_factorization {ε a b : ℝ} :
    (if lowerTwoDiscarded ε a b then (1 : ℝ) else 0) =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ b ≤ a ∧ a ≤ 1 / 2 ∧
            a + 2 * b ≤ 1) then 1 else 0)
      * (if a + 2 * b ≤ 1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε
          then (0 : ℝ) else 1)
      * (if (4 * a + 7 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
            1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b)
          then (0 : ℝ) else 1)
      * (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            4 * a + 5 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
            1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b)
          then (0 : ℝ) else 1)
      * (if upperPairRegion ε a b then (0 : ℝ) else 1) := by
  have hprod := ite_five_prod
    ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ b ≤ a ∧ a ≤ 1 / 2 ∧
      a + 2 * b ≤ 1)
    (a + 2 * b ≤ 1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε)
    (4 * a + 7 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
      1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b)
    (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
      4 * a + 5 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
      1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b)
    (upperPairRegion ε a b)
  have hiff : (((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ b ≤ a ∧ a ≤ 1 / 2 ∧
        a + 2 * b ≤ 1) ∧
        ¬ (a + 2 * b ≤ 1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε) ∧
        ¬ (4 * a + 7 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
            1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b) ∧
        ¬ (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            4 * a + 5 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
            1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ a + b) ∧
        ¬ upperPairRegion ε a b) ↔ lowerTwoDiscarded ε a b := by
    unfold lowerTwoDiscarded
    tauto
  rw [← hprod]
  by_cases hd : lowerTwoDiscarded ε a b
  · rw [if_pos hd, if_pos (hiff.mpr hd)]
  · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]

/-! ### The region in the prime variable

`region_factorization` is pointwise in `a = expo p1`. The five factors are turned into
indicators of integer intervals in `p1` by the `expo` equivalence (`expo_le_iff`,
`le_expo_iff`, `Nat.ceil_le`, `Nat.le_floor`), except the `upperPairRegion` factor, which is
kept in the exponent variable and handled by its own product structure. -/

/-- The `A ≤ n ≤ B` form of an interval indicator: its consecutive differences are supported on
`{A, B + 1}`. -/
private theorem abs_sub_indicator_le_le (A B : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |(if A ≤ n ∧ n ≤ B then (1 : ℝ) else 0)
      - (if A ≤ n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0)|
    ≤ (if n = A ∨ n = B + 1 then (1 : ℝ) else 0) := by
  by_cases hAB : n = A ∨ n = B + 1
  · rw [if_pos hAB]
    have hx : (if A ≤ n ∧ n ≤ B then (1 : ℝ) else 0) = 0 ∨
        (if A ≤ n ∧ n ≤ B then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    have hy : (if A ≤ n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) = 0 ∨
        (if A ≤ n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    rcases hx with h | h <;> rcases hy with k | k <;> rw [h, k] <;> norm_num
  · rw [if_neg hAB]
    have hiff : (A ≤ n ∧ n ≤ B) ↔ (A ≤ n - 1 ∧ n - 1 ≤ B) := by omega
    have hEq : (if A ≤ n ∧ n ≤ B then (1 : ℝ) else 0)
        = (if A ≤ n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) := by
      by_cases hp : (A ≤ n ∧ n ≤ B)
      · rw [if_pos hp, if_pos (hiff.mp hp)]
      · rw [if_neg hp, if_neg (fun h => hp (hiff.mpr h))]
    rw [hEq, sub_self, abs_zero]

/-- The total variation of an `A ≤ n ≤ B` indicator is at most two. -/
private theorem sum_abs_sub_indicator_le_le (A B N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |(if A ≤ n ∧ n ≤ B then (1 : ℝ) else 0)
      - (if A ≤ n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0)| ≤ 2 := by
  refine (Finset.sum_le_sum
    (fun n hn => abs_sub_indicator_le_le A B (Finset.mem_Icc.mp hn).1)).trans ?_
  have hcard : (∑ n ∈ Finset.Icc 1 N, (if n = A ∨ n = B + 1 then (1 : ℝ) else 0))
      = (((Finset.Icc 1 N).filter (fun n => n = A ∨ n = B + 1)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hcard]
  have hsub : (Finset.Icc 1 N).filter (fun n => n = A ∨ n = B + 1)
      ⊆ ({A, B + 1} : Finset ℕ) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    tauto
  have hc : ((Finset.Icc 1 N).filter (fun n => n = A ∨ n = B + 1)).card ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    have h2 := Finset.card_insert_le A ({B + 1} : Finset ℕ)
    simpa using h2
  exact_mod_cast hc

set_option maxHeartbeats 2000000 in
/-- The discarded region at `a = expo p`, as a product of indicators of integer intervals in
`p`. Four factors are intervals (or complements of intervals) with endpoints
`ceil (Z ^ l)` and `floor (Z ^ u)`; the `upperPairRegion` factor is kept in the exponent
variable. -/
private theorem region_p_factorization {ε x : ℝ} (hZ : 1 < scaleZ ε x) {b : ℝ}
    {p : ℕ} (hp : 1 ≤ p) :
    (if lowerTwoDiscarded ε (expo ε x p) b then (1 : ℝ) else 0) =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ p ∧
            p ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊)
          then (1 : ℝ) else 0)
      * (if p ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * b)⌋₊
          then (0 : ℝ) else 1)
      * (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p ∧
            p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p ∧
            p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if upperPairRegion ε (expo ε x p) b then (0 : ℝ) else 1) := by
  have hF1 : ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ b ≤ expo ε x p ∧
      expo ε x p ≤ 1 / 2 ∧ expo ε x p + 2 * b ≤ 1) ↔
      (((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ p ∧
        p ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊)) := by
    have e1 : b ≤ expo ε x p ↔ ⌈scaleZ ε x ^ b⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e2 : expo ε x p ≤ 1 / 2 ↔ p ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ :=
      expo_le_iff_floor (u := 1 / 2) hZ hp
    have e4 : expo ε x p ≤ 1 - 2 * b ↔ p ≤ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊ :=
      expo_le_iff_floor hZ hp
    have e3 : expo ε x p + 2 * b ≤ 1 ↔ expo ε x p ≤ 1 - 2 * b := by
      constructor <;> intro h <;> linarith
    constructor
    · intro h
      obtain ⟨hA, hB, hC, hD⟩ := h
      exact ⟨hA, e1.1 hB, le_min_iff.2 ⟨e2.1 hC, e4.1 (e3.1 hD)⟩⟩
    · intro h
      obtain ⟨hA, hB, hC⟩ := h
      obtain ⟨hC1, hC2⟩ := le_min_iff.1 hC
      exact ⟨hA, e1.2 hB, e2.2 hC1, e3.2 (e4.2 hC2)⟩
  have hF2 : (expo ε x p + 2 * b ≤
        1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε) ↔
      p ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * b)⌋₊ := by
    have e : expo ε x p + 2 * b ≤
        1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε ↔
        expo ε x p ≤
          1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * b := by
      constructor <;> intro h <;> linarith
    exact e.trans (expo_le_iff_floor hZ hp)
  have hF3 : (4 * expo ε x p + 7 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
      1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ expo ε x p + b) ↔
      (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p ∧
        p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4)⌋₊) := by
    have e1 : 1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ expo ε x p + b ↔
        1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b ≤ expo ε x p := by
      constructor <;> intro h <;> linarith
    have e2 : 1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b ≤ expo ε x p ↔
        ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e3 : 4 * expo ε x p + 7 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ↔
        expo ε x p ≤ (2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4 := by
      constructor <;> intro h <;> linarith
    have e4 : expo ε x p ≤ (2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4 ↔
        p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4)⌋₊ :=
      expo_le_iff_floor hZ hp
    rw [e3, e4, e1, e2]
    tauto
  have hF4 : (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
      4 * expo ε x p + 5 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∧
      1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ expo ε x p + b) ↔
      (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
        ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p ∧
        p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4)⌋₊) := by
    have e1 : 1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε ≤ expo ε x p + b ↔
        1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b ≤ expo ε x p := by
      constructor <;> intro h <;> linarith
    have e2 : 1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
        ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b ≤ expo ε x p ↔
        ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
          ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e3 : 4 * expo ε x p + 5 * b ≤ 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ↔
        expo ε x p ≤ (2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4 := by
      constructor <;> intro h <;> linarith
    have e4 : expo ε x p ≤ (2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4 ↔
        p ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4)⌋₊ :=
      expo_le_iff_floor hZ hp
    rw [e3, e4, e1, e2]
    tauto
  rw [region_factorization]
  simp only [hF1, hF2, hF3, hF4]


/-! ### The `upperPairRegion` factor

`upperPairRegion` is a union of three intervals, so it is not an interval indicator. Written as
`(b-only) * 1{b ≤ a} * 1{a ≤ 1/2} * (1 - (1 - P1) (1 - P2) (1 - P3))` it is a product of
`0`-`1`-valued factors, all of them indicators of integer intervals in `p` once `a = expo p`.
The variation of a product is at most the sum of the variations of its factors, so the union
costs a constant, not an ordering argument. -/

/-- A union of three pieces as a product of complements. -/
private theorem ite_or_three_prod (A B C P1 P2 P3 : Prop) [Decidable A] [Decidable B]
    [Decidable C] [Decidable P1] [Decidable P2] [Decidable P3] :
    (if (A ∧ B ∧ C ∧ (P1 ∨ P2 ∨ P3)) then (1 : ℝ) else 0) =
      (if A then (1 : ℝ) else 0) * (if B then (1 : ℝ) else 0) * (if C then (1 : ℝ) else 0)
        * (1 - (1 - (if P1 then (1 : ℝ) else 0)) * (1 - (if P2 then (1 : ℝ) else 0))
              * (1 - (if P3 then (1 : ℝ) else 0))) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases h1 : P1 <;>
    by_cases h2 : P2 <;> by_cases h3 : P3 <;> simp [hA, hB, hC, h1, h2, h3]

set_option maxHeartbeats 2000000 in
/-- `upperPairRegion` at `a = expo p`, as a product of indicators of integer intervals in `p`
(the three `b`-only conditions of the region are constant in `p`). -/
private theorem upr_factorization {ε x : ℝ} (hZ : 1 < scaleZ ε x) {b : ℝ} {p : ℕ}
    (hp : 1 ≤ p) :
    (if upperPairRegion ε (expo ε x p) b then (1 : ℝ) else 0) =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
            b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) then (1 : ℝ) else 0)
      * (if ⌈scaleZ ε x ^ b⌉₊ ≤ p then (1 : ℝ) else 0)
      * (if p ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)
      * (1 - (1 - (if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ p ∧
                p ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
              then (1 : ℝ) else 0))
          * (1 - (if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p ∧
                p ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
              then (1 : ℝ) else 0))
          * (1 - (if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p ∧
                p ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
              then (1 : ℝ) else 0))) := by
  have hP1 : (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ expo ε x p ∧
        expo ε x p ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ↔
      (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ p ∧
        p ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊) := by
    have e1 : 2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ expo ε x p ↔
        ⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e2 : expo ε x p ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ↔
        p ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊ :=
      expo_le_iff_floor hZ hp
    rw [e1, e2]
  have hP2 : (|4 * expo ε x p + 3 * b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε) ↔
      (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p ∧
        p ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊) := by
    have e0 : |4 * expo ε x p + 3 * b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ↔
        (2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ≤ expo ε x p ∧
          expo ε x p ≤ (2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 := by
      rw [abs_le]
      constructor
      · intro h
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · intro h
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have e1 : (2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ≤ expo ε x p ↔
        ⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e2 : expo ε x p ≤ (2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ↔
        p ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊ :=
      expo_le_iff_floor hZ hp
    rw [e0, e1, e2]
  have hP3 : (|4 * expo ε x p + b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε) ↔
      (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p ∧
        p ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊) := by
    have e0 : |4 * expo ε x p + b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ↔
        (2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ≤ expo ε x p ∧
          expo ε x p ≤ (2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 := by
      rw [abs_le]
      constructor
      · intro h
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · intro h
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have e1 : (2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ≤ expo ε x p ↔
        ⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ p :=
      le_expo_iff_ceil hZ hp
    have e2 : expo ε x p ≤ (2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4 ↔
        p ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊ :=
      expo_le_iff_floor hZ hp
    rw [e0, e1, e2]
  have hbd : ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
      b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ↔
      ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
        b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) := Iff.rfl
  have hle : b ≤ expo ε x p ↔ ⌈scaleZ ε x ^ b⌉₊ ≤ p :=
    le_expo_iff_ceil hZ hp
  have hhalf : expo ε x p ≤ 1 / 2 ↔ p ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ :=
    expo_le_iff_floor (u := 1 / 2) hZ hp
  have hU : upperPairRegion ε (expo ε x p) b ↔
      (((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
          b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ∧
        b ≤ expo ε x p ∧ expo ε x p ≤ 1 / 2 ∧
        ((2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ expo ε x p ∧
            expo ε x p ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ∨
          |4 * expo ε x p + 3 * b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∨
          |4 * expo ε x p + b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) := by
    unfold upperPairRegion
    tauto
  rw [show (if upperPairRegion ε (expo ε x p) b then (1 : ℝ) else 0) =
      (if (((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
            b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ∧
          b ≤ expo ε x p ∧ expo ε x p ≤ 1 / 2 ∧
          ((2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ expo ε x p ∧
              expo ε x p ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) ∨
            |4 * expo ε x p + 3 * b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε ∨
            |4 * expo ε x p + b - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) then
        (1 : ℝ) else 0) from by simp only [hU]]
  rw [ite_or_three_prod]
  simp only [hbd, hle, hhalf, hP1, hP2, hP3]


/-- A lower half-line indicator of `ℕ` changes only at its endpoint. -/
private theorem abs_sub_half_le (A : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |(if A ≤ n then (1 : ℝ) else 0) - (if A ≤ n - 1 then (1 : ℝ) else 0)|
    ≤ (if n = A then (1 : ℝ) else 0) := by
  by_cases h : n = A
  · rw [if_pos h]
    have hx : (if A ≤ n then (1 : ℝ) else 0) = 0 ∨ (if A ≤ n then (1 : ℝ) else 0) = 1 := by
      split_ifs <;> simp
    have hy : (if A ≤ n - 1 then (1 : ℝ) else 0) = 0 ∨
        (if A ≤ n - 1 then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    rcases hx with a | a <;> rcases hy with b | b <;> rw [a, b] <;> norm_num
  · rw [if_neg h]
    have hiff : (A ≤ n) ↔ (A ≤ n - 1) := by omega
    have hEq : (if A ≤ n then (1 : ℝ) else 0) = (if A ≤ n - 1 then (1 : ℝ) else 0) := by
      by_cases hp : A ≤ n
      · rw [if_pos hp, if_pos (hiff.mp hp)]
      · rw [if_neg hp, if_neg (fun hh => hp (hiff.mpr hh))]
    rw [hEq, sub_self, abs_zero]

/-- The total variation of a lower half-line indicator is at most one. -/
private theorem sum_abs_sub_half_le (A N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |(if A ≤ n then (1 : ℝ) else 0)
      - (if A ≤ n - 1 then (1 : ℝ) else 0)| ≤ 1 := by
  refine (Finset.sum_le_sum
    (fun n hn => abs_sub_half_le A (Finset.mem_Icc.mp hn).1)).trans ?_
  have hcard : (∑ n ∈ Finset.Icc 1 N, (if n = A then (1 : ℝ) else 0))
      = (((Finset.Icc 1 N).filter (fun n => n = A)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hcard]
  have hc : ((Finset.Icc 1 N).filter (fun n => n = A)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_singleton] at ha hb
    rw [ha.2, hb.2]
  exact_mod_cast hc

/-- An upper half-line indicator of `ℕ` changes only at its endpoint. -/
private theorem abs_sub_half_upper_le (B : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |(if n ≤ B then (1 : ℝ) else 0) - (if n - 1 ≤ B then (1 : ℝ) else 0)|
    ≤ (if n = B + 1 then (1 : ℝ) else 0) := by
  by_cases h : n = B + 1
  · rw [if_pos h]
    have hx : (if n ≤ B then (1 : ℝ) else 0) = 0 ∨ (if n ≤ B then (1 : ℝ) else 0) = 1 := by
      split_ifs <;> simp
    have hy : (if n - 1 ≤ B then (1 : ℝ) else 0) = 0 ∨
        (if n - 1 ≤ B then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    rcases hx with a | a <;> rcases hy with b | b <;> rw [a, b] <;> norm_num
  · rw [if_neg h]
    have hiff : (n ≤ B) ↔ (n - 1 ≤ B) := by omega
    have hEq : (if n ≤ B then (1 : ℝ) else 0) = (if n - 1 ≤ B then (1 : ℝ) else 0) := by
      by_cases hp : n ≤ B
      · rw [if_pos hp, if_pos (hiff.mp hp)]
      · rw [if_neg hp, if_neg (fun hh => hp (hiff.mpr hh))]
    rw [hEq, sub_self, abs_zero]

/-- The total variation of an upper half-line indicator is at most one. -/
private theorem sum_abs_sub_half_upper_le (B N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |(if n ≤ B then (1 : ℝ) else 0)
      - (if n - 1 ≤ B then (1 : ℝ) else 0)| ≤ 1 := by
  refine (Finset.sum_le_sum
    (fun n hn => abs_sub_half_upper_le B (Finset.mem_Icc.mp hn).1)).trans ?_
  have hcard : (∑ n ∈ Finset.Icc 1 N, (if n = B + 1 then (1 : ℝ) else 0))
      = (((Finset.Icc 1 N).filter (fun n => n = B + 1)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hcard]
  have hc : ((Finset.Icc 1 N).filter (fun n => n = B + 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_singleton] at ha hb
    rw [ha.2, hb.2]
  exact_mod_cast hc

/-! ### Summation by parts

The character saving has to be extracted from a sum whose weight is *not* an interval indicator
but a step function: the region, written as a product of five step functions in `expo p1`
(`region_factorization`). The three lemmas below say that a product of `0`-`1`-valued interval
indicators has variation at most twice the number of factors, and that Abel summation converts
variation `V` plus `‖χ‖`-bounded prefix sums `B` into the bound `(V + 1) * B`. No ordering of
the covered intervals of `E2` is needed anywhere. -/

/-- An interval indicator of `ℕ` changes only at the two endpoints, so its consecutive
differences are supported on `{A + 1, B + 1}`. -/
private theorem abs_sub_indicator_le (A B : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |(if A < n ∧ n ≤ B then (1 : ℝ) else 0)
      - (if A < n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0)|
    ≤ (if n = A + 1 ∨ n = B + 1 then (1 : ℝ) else 0) := by
  by_cases hAB : n = A + 1 ∨ n = B + 1
  · rw [if_pos hAB]
    have hx : (if A < n ∧ n ≤ B then (1 : ℝ) else 0) = 0 ∨
        (if A < n ∧ n ≤ B then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    have hy : (if A < n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) = 0 ∨
        (if A < n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) = 1 := by split_ifs <;> simp
    rcases hx with h | h <;> rcases hy with k | k <;> rw [h, k] <;> norm_num
  · rw [if_neg hAB]
    have hiff : (A < n ∧ n ≤ B) ↔ (A < n - 1 ∧ n - 1 ≤ B) := by omega
    have hEq : (if A < n ∧ n ≤ B then (1 : ℝ) else 0)
        = (if A < n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0) := by
      by_cases hp : (A < n ∧ n ≤ B)
      · rw [if_pos hp, if_pos (hiff.mp hp)]
      · rw [if_neg hp, if_neg (fun h => hp (hiff.mpr h))]
    rw [hEq, sub_self, abs_zero]

/-- The total variation of an interval indicator is at most two. -/
private theorem sum_abs_sub_indicator_le (A B N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |(if A < n ∧ n ≤ B then (1 : ℝ) else 0)
      - (if A < n - 1 ∧ n - 1 ≤ B then (1 : ℝ) else 0)| ≤ 2 := by
  refine (Finset.sum_le_sum
    (fun n hn => abs_sub_indicator_le A B (Finset.mem_Icc.mp hn).1)).trans ?_
  have hcard : (∑ n ∈ Finset.Icc 1 N, (if n = A + 1 ∨ n = B + 1 then (1 : ℝ) else 0))
      = (((Finset.Icc 1 N).filter (fun n => n = A + 1 ∨ n = B + 1)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hcard]
  have hsub : (Finset.Icc 1 N).filter (fun n => n = A + 1 ∨ n = B + 1)
      ⊆ ({A + 1, B + 1} : Finset ℕ) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    tauto
  have hc : ((Finset.Icc 1 N).filter (fun n => n = A + 1 ∨ n = B + 1)).card ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    have h2 := Finset.card_insert_le (A + 1) ({B + 1} : Finset ℕ)
    simpa using h2
  exact_mod_cast hc

/-- The variation of a product of two `0`-`1`-valued weights is at most the sum of their
variations. -/
private theorem abs_prod_sub_prod_le {f g : ℕ → ℝ} (hf : ∀ n, f n = 0 ∨ f n = 1)
    (hg : ∀ n, g n = 0 ∨ g n = 1) (n : ℕ) :
    |f n * g n - f (n - 1) * g (n - 1)|
      ≤ |f n - f (n - 1)| + |g n - g (n - 1)| := by
  rcases hf n with a | a <;> rcases hf (n - 1) with b | b <;>
    rcases hg n with c | c <;> rcases hg (n - 1) with d | d <;>
    rw [a, b, c, d] <;> norm_num


/-- Two `0`-`1`-valued reals: the product difference is at most the sum of the differences. -/
private theorem abs_mul_sub_mul_le {a b c d : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  rcases ha with h | h <;> rcases hb with k | k <;> rcases hc with m | m <;>
    rcases hd with n | n <;> rw [h, k, m, n] <;> norm_num

/-- A product of two `0`-`1`-valued reals is `0` or `1`. -/
private theorem zero_or_one_mul {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = 0 ∨ a * b = 1 := by
  rcases ha with h | h <;> rcases hb with k | k <;> rw [h, k] <;> norm_num

/-- Five `0`-`1`-valued reals: the product difference is at most the sum of the five
differences. -/
private theorem abs_prod_five_sub_le {a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : ℝ}
    (h1a : a1 = 0 ∨ a1 = 1) (h1b : b1 = 0 ∨ b1 = 1)
    (h2a : a2 = 0 ∨ a2 = 1) (h2b : b2 = 0 ∨ b2 = 1)
    (h3a : a3 = 0 ∨ a3 = 1) (h3b : b3 = 0 ∨ b3 = 1)
    (h4a : a4 = 0 ∨ a4 = 1) (h4b : b4 = 0 ∨ b4 = 1)
    (h5a : a5 = 0 ∨ a5 = 1) (h5b : b5 = 0 ∨ b5 = 1) :
    |a1 * a2 * a3 * a4 * a5 - b1 * b2 * b3 * b4 * b5|
      ≤ |a1 - b1| + |a2 - b2| + |a3 - b3| + |a4 - b4| + |a5 - b5| := by
  have h12a : a1 * a2 = 0 ∨ a1 * a2 = 1 := zero_or_one_mul h1a h2a
  have h12b : b1 * b2 = 0 ∨ b1 * b2 = 1 := zero_or_one_mul h1b h2b
  have h34a : a3 * a4 = 0 ∨ a3 * a4 = 1 := zero_or_one_mul h3a h4a
  have h34b : b3 * b4 = 0 ∨ b3 * b4 = 1 := zero_or_one_mul h3b h4b
  have h345a : a3 * a4 * a5 = 0 ∨ a3 * a4 * a5 = 1 := zero_or_one_mul h34a h5a
  have h345b : b3 * b4 * b5 = 0 ∨ b3 * b4 * b5 = 1 := zero_or_one_mul h34b h5b
  have hA : a1 * a2 * a3 * a4 * a5 = (a1 * a2) * (a3 * a4 * a5) := by ring
  have hB : b1 * b2 * b3 * b4 * b5 = (b1 * b2) * (b3 * b4 * b5) := by ring
  rw [hA, hB]
  refine (abs_mul_sub_mul_le h12a h345a h12b h345b).trans ?_
  have step2 : |a3 * a4 * a5 - b3 * b4 * b5| ≤ |a3 - b3| + |a4 - b4| + |a5 - b5| := by
    have hA' : a3 * a4 * a5 = (a3 * a4) * a5 := by ring
    have hB' : b3 * b4 * b5 = (b3 * b4) * b5 := by ring
    rw [hA', hB']
    refine (abs_mul_sub_mul_le h34a h5a h34b h5b).trans ?_
    have := abs_mul_sub_mul_le h3a h4a h3b h4b
    linarith [abs_nonneg (a3 - b3), abs_nonneg (a4 - b4), abs_nonneg (a5 - b5)]
  have := abs_mul_sub_mul_le h1a h2a h1b h2b
  linarith [abs_nonneg (a1 - b1), abs_nonneg (a2 - b2), abs_nonneg (a3 - b3),
    abs_nonneg (a4 - b4), abs_nonneg (a5 - b5)]

/-- Summation by parts: a `0`-`1`-valued weight whose variation is at most `V`, paired with a
sequence whose partial sums up to `N` are bounded by `B`, has sum at most `(V + 1) * B`. -/
private theorem norm_sum_mul_le {N : ℕ} (f : ℕ → ℝ) (g : ℕ → ℂ) (V B : ℝ)
    (hf : ∀ n, f n = 0 ∨ f n = 1)
    (hV : ∑ i ∈ Finset.range (N - 1), |f (i + 1) - f i| ≤ V)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤ (V + 1) * B := by
  rw [Finset.sum_range_by_parts (f := f) (g := fun i => g i)]
  have hfin : ∀ n : ℕ, ‖f n‖ ≤ 1 := by
    intro n
    rcases hf n with h | h <;> rw [h] <;> norm_num
  have hBN : 0 ≤ B := le_trans (norm_nonneg _) (hB N le_rfl)
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖f (N - 1) • (∑ i ∈ Finset.range N, g i)‖ ≤ B := by
    rw [norm_smul]
    calc ‖f (N - 1)‖ * ‖∑ i ∈ Finset.range N, g i‖ ≤ 1 * B :=
          mul_le_mul (hfin _) (hB N le_rfl) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have h2 : ‖∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) • (∑ j ∈ Finset.range (i + 1), g j)‖
      ≤ V * B := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (N - 1),
        ‖(f (i + 1) - f i) • (∑ j ∈ Finset.range (i + 1), g j)‖ ≤ |f (i + 1) - f i| * B := by
      intro i hi
      have hi' : i + 1 ≤ N := by
        have := Finset.mem_range.mp hi
        omega
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB (i + 1) hi') (abs_nonneg _)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hV hBN
  linarith [h1, h2, hBN]

/-! ### Transport of the Abel bound to an integer interval

`norm_sum_mul_le` sums over `range N`. The window bound below sums over `Ioc A B`: the character
saving has to be applied at the ambient scale of the window (bounded below by `Z ^ (1/8)`), not at
the scale of the whole range, so the partial sums run from `A` upwards and the ambient is the top
of the window. These three lemmas move the Abel bound to that shape. -/

/-- Reindexing `Ioc a b` as `range (b - a)`. -/
private theorem sum_Ioc_eq_sum_range' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.Ioc a b, f i = ∑ i ∈ Finset.range (b - a), f (a + 1 + i) := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : a ≤ b
    · rw [Finset.sum_Ioc_succ_top hab, ih, Nat.succ_sub hab, Finset.sum_range_succ,
        show a + 1 + (b - a) = b + 1 by omega]
    · have h1 : Finset.Ioc a (b + 1) = ∅ := by
        rw [Finset.Ioc_eq_empty]
        omega
      have h2 : b + 1 - a = 0 := by omega
      rw [h1, h2]
      simp

/-- Reindexing `Icc 1 N` as `range N`. -/
private theorem sum_Icc_eq_sum_range' {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 N, f i = ∑ i ∈ Finset.range N, f (i + 1) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset, sum_Ioc_eq_sum_range']
  exact Finset.sum_congr rfl (fun i _ => by congr 1; omega)

/-- Summation by parts on an integer interval: a `0`-`1`-valued weight whose total variation
over `Ioc A B` is at most `V`, paired with a sequence whose partial sums over `Ioc A k`,
`A ≤ k ≤ B`, are bounded by `Bnd`, has sum at most `(V + 1) * Bnd`. -/
private theorem norm_sum_mul_Ioc_le {A B : ℕ} (f : ℕ → ℝ) (g : ℕ → ℂ) (V Bnd : ℝ)
    (hf : ∀ n, f n = 0 ∨ f n = 1) (hBnd : 0 ≤ Bnd)
    (hV : ∑ n ∈ Finset.Ioc A B, |f n - f (n - 1)| ≤ V)
    (hB : ∀ k, A ≤ k → k ≤ B → ‖∑ n ∈ Finset.Ioc A k, g n‖ ≤ Bnd) :
    ‖∑ n ∈ Finset.Ioc A B, f n • g n‖ ≤ (V + 1) * Bnd := by
  by_cases hAB : A ≤ B
  · have hV0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc A B, |f n - f (n - 1)| :=
      Finset.sum_nonneg (fun n _ => abs_nonneg _)
    have hVnn : (0 : ℝ) ≤ V := le_trans hV0 hV
    set m := B - A with hm
    rw [sum_Ioc_eq_sum_range' A B (fun n => f n • g n)]
    refine norm_sum_mul_le (fun i => f (A + 1 + i)) (fun i => g (A + 1 + i)) V Bnd
      (fun i => hf _) ?_ ?_
    · -- the variation, as a sub-sum of the variation over `Ioc A B`
      have hstep : ∑ i ∈ Finset.range (m - 1),
          |f (A + 1 + (i + 1)) - f (A + 1 + i)|
          = ∑ n ∈ Finset.Ioc (A + 1) B, |f n - f (n - 1)| := by
        rw [sum_Ioc_eq_sum_range' (A + 1) B (fun n => |f n - f (n - 1)|),
          show m - 1 = B - (A + 1) by omega]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [show A + 2 + i - 1 = A + 1 + i by omega,
            show A + 1 + (i + 1) = A + 2 + i by omega])
      rw [hstep]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hV
      · intro n hn
        simp only [Finset.mem_Ioc] at hn ⊢
        omega
      · intro n _ _
        exact abs_nonneg _
    · intro k hk
      have hsum : ∑ i ∈ Finset.range k, g (A + 1 + i) = ∑ n ∈ Finset.Ioc A (A + k), g n := by
        rw [sum_Ioc_eq_sum_range' A (A + k) g,
          show A + k - A = k by omega]
      rw [hsum]
      exact hB (A + k) (by omega) (by omega)
  · have hempty : Finset.Ioc A B = ∅ := by
      rw [Finset.Ioc_eq_empty]
      omega
    rw [hempty] at hV
    have hVnn : (0 : ℝ) ≤ V := by simpa using hV
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    have : (0 : ℝ) ≤ (V + 1) * Bnd := by
      have : (0 : ℝ) ≤ V + 1 := by linarith
      exact mul_nonneg this hBnd
    exact this

/-- `|(1 - a) - (1 - b)| = |a - b|`, the bridge from a complement of an indicator to the
indicator itself. -/
private theorem abs_one_sub_sub_one_sub {a b : ℝ} : |(1 - a) - (1 - b)| = |a - b| := by
  rw [show (1 - a) - (1 - b) = b - a by ring, abs_sub_comm]

/-- The variation of a product of five `0`-`1`-valued weights is at most the sum of the five
variations. Combined with the per-factor bounds this bounds the variation of the region weight,
which is what Abel summation needs. -/
private theorem sum_variation_five {F f1 f2 f3 f4 f5 : ℕ → ℝ}
    (hF : ∀ n, F n = f1 n * f2 n * f3 n * f4 n * f5 n)
    (h1 : ∀ n, f1 n = 0 ∨ f1 n = 1) (h2 : ∀ n, f2 n = 0 ∨ f2 n = 1)
    (h3 : ∀ n, f3 n = 0 ∨ f3 n = 1) (h4 : ∀ n, f4 n = 0 ∨ f4 n = 1)
    (h5 : ∀ n, f5 n = 0 ∨ f5 n = 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |F n - F (n - 1)| ≤
      ∑ n ∈ Finset.Icc 1 N, (|f1 n - f1 (n - 1)| + |f2 n - f2 (n - 1)|
        + |f3 n - f3 (n - 1)| + |f4 n - f4 (n - 1)| + |f5 n - f5 (n - 1)|) := by
  refine Finset.sum_le_sum (fun n _ => ?_)
  simp only [hF]
  exact abs_prod_five_sub_le (h1 n) (h1 (n - 1)) (h2 n) (h2 (n - 1)) (h3 n) (h3 (n - 1))
    (h4 n) (h4 (n - 1)) (h5 n) (h5 (n - 1))

/-- The base factor of the region weight: an interval indicator, gated by the `b`-condition
`L - eps <= b`, which is constant in the prime. -/
private theorem var_f_base {ε x : ℝ} (b : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
      |(if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ n ∧
            n ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊)
          then (1 : ℝ) else 0)
        - (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ n - 1 ∧
            n - 1 ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊)
          then (1 : ℝ) else 0)| ≤ 2 := by
  by_cases hb : ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b)
  · simp only [hb, true_and]
    exact sum_abs_sub_indicator_le_le _ _ N
  · have hzero : ∀ n : ℕ,
        (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ n ∧
            n ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊)
          then (1 : ℝ) else 0) = 0 := by
      intro n
      rw [if_neg]
      intro h
      exact hb h.1
    simp only [hzero]
    simp

/-- The `X` factor of the region weight: the complement of an upper half-line. -/
private theorem var_f_upper {ε x : ℝ} (B : ℕ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
      |(if n ≤ B then (0 : ℝ) else 1) - (if n - 1 ≤ B then (0 : ℝ) else 1)| ≤ 1 := by
  have hEq : ∀ n : ℕ, (if n ≤ B then (0 : ℝ) else 1) = 1 - (if n ≤ B then (1 : ℝ) else 0) := by
    intro n
    by_cases h : n ≤ B <;> simp [h]
  simp only [hEq, abs_one_sub_sub_one_sub]
  exact sum_abs_sub_half_upper_le B N

/-- The `Y` factor of the region weight: the complement of an interval. -/
private theorem var_f_compl {ε x : ℝ} (A B : ℕ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
      |(if (A ≤ n ∧ n ≤ B) then (0 : ℝ) else 1)
        - (if (A ≤ n - 1 ∧ n - 1 ≤ B) then (0 : ℝ) else 1)| ≤ 2 := by
  have hEq : ∀ n : ℕ,
      (if (A ≤ n ∧ n ≤ B) then (0 : ℝ) else 1) = 1 - (if (A ≤ n ∧ n ≤ B) then (1 : ℝ) else 0) := by
    intro n
    by_cases h : (A ≤ n ∧ n ≤ B) <;> simp [h]
  simp only [hEq, abs_one_sub_sub_one_sub]
  exact sum_abs_sub_indicator_le_le A B N

/-- The `Z` factor of the region weight: the complement of an interval, gated by the constant
`b`-condition `b <= B3 - eps`; the gate is either true (an interval) or false (identically one). -/
private theorem var_f_gated {ε x : ℝ} (b : ℝ) (A B : ℕ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
      |(if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧ A ≤ n ∧ n ≤ B)
          then (0 : ℝ) else 1)
        - (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧ A ≤ n - 1 ∧ n - 1 ≤ B)
          then (0 : ℝ) else 1)| ≤ 2 := by
  by_cases hb : b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε
  · have hiff : ∀ n : ℕ,
        ((b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧ A ≤ n ∧ n ≤ B)
          ↔ (A ≤ n ∧ n ≤ B)) := by
      intro n
      constructor
      · intro h
        exact ⟨h.2.1, h.2.2⟩
      · intro h
        exact ⟨hb, h.1, h.2⟩
    simp only [hiff]
    exact var_f_compl (ε := ε) (x := x) A B N
  · have hone : ∀ n : ℕ,
        (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧ A ≤ n ∧ n ≤ B)
          then (0 : ℝ) else 1) = 1 := by
      intro n
      rw [if_neg]
      intro h
      exact hb h.1
    simp only [hone]
    simp

/-! ### The window as an integer interval in `p1`

The character saving is applied to `p1` in the window cut out by `p1 * p2 * n ∈ J`, `p1 * p2 * n ≤ t`
and the exponent region. The first two are an interval in `p1` with integer endpoints; this section
records that, and the variation bounds that the Abel step consumes. -/

/-- The window condition on `p1` as an integer interval. -/
private theorem window_interval_iff {ε x : ℝ} (t : ℝ) {p2 n p : ℕ} (hP : 0 < p2 * n)
    (hp : 1 ≤ p) :
    (p * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) ↔
      (⌊x ^ (11 / 20 + ε)⌋₊ / (p2 * n) < p ∧
        p ≤ min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n))) := by
  rw [Finset.mem_filter, rightInterval, Finset.mem_Ioc, Nat.mul_assoc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hm1 : p * (p2 * n) ≤ ⌊t⌋₊ := Nat.le_floor h3
    exact ⟨(Nat.div_lt_iff_lt_mul hP).mpr h1, le_min
      ((Nat.le_div_iff_mul_le hP).mpr h2) ((Nat.le_div_iff_mul_le hP).mpr hm1)⟩
  · rintro ⟨h1, h2⟩
    have h2' := le_min_iff.mp h2
    have h1' := (Nat.div_lt_iff_lt_mul hP).mp h1
    have h2'' := (Nat.le_div_iff_mul_le hP).mp h2'.1
    have h3' := (Nat.le_div_iff_mul_le hP).mp h2'.2
    have ht1 : (1 : ℕ) ≤ ⌊t⌋₊ := by
      have hpm : 1 ≤ p * (p2 * n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have ht0 : (0 : ℝ) < t := Nat.pos_of_floor_pos (by omega : 0 < ⌊t⌋₊)
    exact ⟨⟨h1', h2''⟩, by
      have hc : ((p * (p2 * n) : ℕ) : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3'
      have ht2 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
      linarith⟩

/-- A conjunction of three indicator propositions is a product of three indicators. -/
private theorem ite_three_prod (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    (if (P ∧ Q ∧ R) then (1 : ℝ) else 0) =
      (if P then (1 : ℝ) else 0) * (if Q then (1 : ℝ) else 0) * (if R then (1 : ℝ) else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

/-- The complement of a `0`-`1`-valued real is `0` or `1`. -/
private theorem one_sub_zero_or_one {a : ℝ} (h : a = 0 ∨ a = 1) :
    (1 - a = 0 ∨ 1 - a = 1) := by
  rcases h with h | h <;> rw [h] <;> norm_num

/-- A `1`/`0` indicator is `0` or `1`. -/
private theorem ite_one_zero_zero_or_one (P : Prop) [Decidable P] :
    ((if P then (1 : ℝ) else 0) = 0 ∨ (if P then (1 : ℝ) else 0) = 1) := by
  split_ifs <;> simp

/-- Seven `0`-`1`-valued reals: the product difference is at most the sum of the seven
differences. -/
private theorem abs_prod_seven_sub_le {f1 f2 f3 f4 f5 f6 f7 : ℕ → ℝ}
    (h1 : ∀ n, f1 n = 0 ∨ f1 n = 1) (h2 : ∀ n, f2 n = 0 ∨ f2 n = 1)
    (h3 : ∀ n, f3 n = 0 ∨ f3 n = 1) (h4 : ∀ n, f4 n = 0 ∨ f4 n = 1)
    (h5 : ∀ n, f5 n = 0 ∨ f5 n = 1) (h6 : ∀ n, f6 n = 0 ∨ f6 n = 1)
    (h7 : ∀ n, f7 n = 0 ∨ f7 n = 1) (n : ℕ) :
    |(f1 n * f2 n * f3 n * f4 n * f5 n * f6 n * f7 n)
        - (f1 (n - 1) * f2 (n - 1) * f3 (n - 1) * f4 (n - 1) * f5 (n - 1) * f6 (n - 1)
            * f7 (n - 1))|
      ≤ |f1 n - f1 (n - 1)| + |f2 n - f2 (n - 1)| + |f3 n - f3 (n - 1)| + |f4 n - f4 (n - 1)|
        + |f5 n - f5 (n - 1)| + |f6 n - f6 (n - 1)| + |f7 n - f7 (n - 1)| := by
  have hA : f1 n * f2 n * f3 n * f4 n * f5 n * f6 n * f7 n
      = (f1 n * f2 n * f3 n * f4 n * f5 n) * (f6 n * f7 n) := by ring
  have hB : f1 (n - 1) * f2 (n - 1) * f3 (n - 1) * f4 (n - 1) * f5 (n - 1) * f6 (n - 1)
      * f7 (n - 1) = (f1 (n - 1) * f2 (n - 1) * f3 (n - 1) * f4 (n - 1) * f5 (n - 1))
        * (f6 (n - 1) * f7 (n - 1)) := by ring
  rw [hA, hB]
  have h123n : f1 n * f2 n * f3 n = 0 ∨ f1 n * f2 n * f3 n = 1 :=
    zero_or_one_mul (zero_or_one_mul (h1 n) (h2 n)) (h3 n)
  have h123m : f1 (n - 1) * f2 (n - 1) * f3 (n - 1) = 0 ∨
      f1 (n - 1) * f2 (n - 1) * f3 (n - 1) = 1 :=
    zero_or_one_mul (zero_or_one_mul (h1 (n - 1)) (h2 (n - 1))) (h3 (n - 1))
  have h5n : f1 n * f2 n * f3 n * f4 n * f5 n = 0 ∨ f1 n * f2 n * f3 n * f4 n * f5 n = 1 :=
    zero_or_one_mul (zero_or_one_mul h123n (h4 n)) (h5 n)
  have h5m : f1 (n - 1) * f2 (n - 1) * f3 (n - 1) * f4 (n - 1) * f5 (n - 1) = 0 ∨
      f1 (n - 1) * f2 (n - 1) * f3 (n - 1) * f4 (n - 1) * f5 (n - 1) = 1 :=
    zero_or_one_mul (zero_or_one_mul h123m (h4 (n - 1))) (h5 (n - 1))
  have h67n : f6 n * f7 n = 0 ∨ f6 n * f7 n = 1 := zero_or_one_mul (h6 n) (h7 n)
  have h67m : f6 (n - 1) * f7 (n - 1) = 0 ∨ f6 (n - 1) * f7 (n - 1) = 1 :=
    zero_or_one_mul (h6 (n - 1)) (h7 (n - 1))
  have hstep1 := abs_mul_sub_mul_le h5n h67n h5m h67m
  have hstep2 := abs_prod_five_sub_le (h1 n) (h1 (n - 1)) (h2 n) (h2 (n - 1)) (h3 n) (h3 (n - 1))
    (h4 n) (h4 (n - 1)) (h5 n) (h5 (n - 1))
  have hstep3 := abs_mul_sub_mul_le (h6 n) (h7 n) (h6 (n - 1)) (h7 (n - 1))
  linarith [abs_nonneg (f6 n - f6 (n - 1)), abs_nonneg (f7 n - f7 (n - 1))]

/-- A nonnegative sum over `Ioc A B` is at most the sum over `Icc 1 N` when `B ≤ N`. -/
private theorem sum_Ioc_le_sum_Icc {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {A B N : ℕ} (hB : B ≤ N) :
    ∑ n ∈ Finset.Ioc A B, g n ≤ ∑ n ∈ Finset.Icc 1 N, g n := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA
    have hset : Finset.Ioc 0 B = Finset.Icc 1 B := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hB)
      (fun x _ _ => hg x)
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hg x)
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_Icc]
    omega

/-! ### The variation weight of the long-cofactor window

The weight is the product of the five region factors of `region_p_factorization`, the window
interval in `p1` (`window_interval_iff`), and the half-line `p2 < p1`. The `upperPairRegion`
factor is expanded by `upr_factorization` into six `0`-`1` factors. Every factor is an interval
indicator or a half-line indicator, so the total variation is at most `4 * 2 + 8 + 2 + 1 = 19`;
with the `k = 1` term (`W 0` is a junk value) the bound `24` is safe. -/

/-- The union `1 - (1 - g3) (1 - g4) (1 - g5)` of three `0`-`1` indicators varies by at most the
sum of their variations. -/
private theorem abs_three_union_sub_le {g3 g4 g5 : ℕ → ℝ}
    (h3 : ∀ n, g3 n = 0 ∨ g3 n = 1) (h4 : ∀ n, g4 n = 0 ∨ g4 n = 1)
    (h5 : ∀ n, g5 n = 0 ∨ g5 n = 1) (n : ℕ) :
    |(1 - (1 - g3 n) * (1 - g4 n) * (1 - g5 n))
        - (1 - (1 - g3 (n - 1)) * (1 - g4 (n - 1)) * (1 - g5 (n - 1)))|
      ≤ |g3 n - g3 (n - 1)| + |g4 n - g4 (n - 1)| + |g5 n - g5 (n - 1)| := by
  rw [abs_one_sub_sub_one_sub]
  have h := abs_prod_seven_sub_le (f1 := fun m => 1 - g3 m) (f2 := fun m => 1 - g4 m)
    (f3 := fun m => 1 - g5 m) (f4 := fun _ => (1 : ℝ)) (f5 := fun _ => (1 : ℝ))
    (f6 := fun _ => (1 : ℝ)) (f7 := fun _ => (1 : ℝ))
    (fun m => one_sub_zero_or_one (h3 m)) (fun m => one_sub_zero_or_one (h4 m))
    (fun m => one_sub_zero_or_one (h5 m)) (fun _ => Or.inr rfl) (fun _ => Or.inr rfl)
    (fun _ => Or.inr rfl) (fun _ => Or.inr rfl) n
  simp only [mul_one] at h
  rw [abs_one_sub_sub_one_sub (a := g3 n) (b := g3 (n - 1)),
    abs_one_sub_sub_one_sub (a := g4 n) (b := g4 (n - 1)),
    abs_one_sub_sub_one_sub (a := g5 n) (b := g5 (n - 1))] at h
  simp only [sub_self, abs_zero, add_zero] at h
  linarith [h]

/-- The complement of the `upperPairRegion` factor, as a product of the gate, two half-lines and
the three-piece union. Its variation is at most the sum of theirs. -/
private theorem abs_upr_compl_sub_le (gate : ℝ) (hgate : gate = 0 ∨ gate = 1)
    {g1 g2 g3 g4 g5 : ℕ → ℝ}
    (h1 : ∀ n, g1 n = 0 ∨ g1 n = 1) (h2 : ∀ n, g2 n = 0 ∨ g2 n = 1)
    (h3 : ∀ n, g3 n = 0 ∨ g3 n = 1) (h4 : ∀ n, g4 n = 0 ∨ g4 n = 1)
    (h5 : ∀ n, g5 n = 0 ∨ g5 n = 1) (n : ℕ) :
    |(1 - gate * g1 n * g2 n * (1 - (1 - g3 n) * (1 - g4 n) * (1 - g5 n)))
        - (1 - gate * g1 (n - 1) * g2 (n - 1)
            * (1 - (1 - g3 (n - 1)) * (1 - g4 (n - 1)) * (1 - g5 (n - 1))))|
      ≤ |g1 n - g1 (n - 1)| + |g2 n - g2 (n - 1)| + |g3 n - g3 (n - 1)|
        + |g4 n - g4 (n - 1)| + |g5 n - g5 (n - 1)| := by
  rw [abs_one_sub_sub_one_sub]
  have o4 : ∀ m, (1 - (1 - g3 m) * (1 - g4 m) * (1 - g5 m)) = 0 ∨
      (1 - (1 - g3 m) * (1 - g4 m) * (1 - g5 m)) = 1 := by
    intro m
    rcases h3 m with a | a <;> rcases h4 m with b | b <;> rcases h5 m with c | c <;>
      rw [a, b, c] <;> norm_num
  have h := abs_prod_seven_sub_le (f1 := fun _ => gate) (f2 := g1) (f3 := g2)
    (f4 := fun m => 1 - (1 - g3 m) * (1 - g4 m) * (1 - g5 m))
    (f5 := fun _ => (1 : ℝ)) (f6 := fun _ => (1 : ℝ)) (f7 := fun _ => (1 : ℝ))
    (fun _ => hgate) h1 h2 o4 (fun _ => Or.inr rfl) (fun _ => Or.inr rfl)
    (fun _ => Or.inr rfl) n
  simp only [mul_one] at h
  have hu := abs_three_union_sub_le h3 h4 h5 n
  simp only [sub_self, abs_zero, add_zero] at h
  linarith [h, hu, abs_nonneg (g3 n - g3 (n - 1)), abs_nonneg (g4 n - g4 (n - 1)),
    abs_nonneg (g5 n - g5 (n - 1))]

/-- The sum over `Icc 2 N` is at most the sum over `Icc 1 N` of a nonnegative summand. -/
private theorem sum_Icc_two_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, g k ≤ ∑ k ∈ Finset.Icc 1 N, g k := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hg x)
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  omega

/-- Peeling the `k = 1` term off the variation sum. -/
private theorem sum_Icc_one_le_one_add {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k ≤ g 1 + ∑ k ∈ Finset.Icc 2 N, g k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : (0 : ℝ) ≤ g 1 := hg 1
    have h2 : ∑ k ∈ Finset.Icc 2 0, g k = 0 := by simp
    simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty, h2]
    linarith [h1]
  · have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

/-- A `0`-`1`-valued real differs from another by at most one. -/
private theorem abs_sub_le_one {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    |a - b| ≤ 1 := by
  rcases ha with h | h <;> rcases hb with k | k <;> rw [h, k] <;> norm_num

/-- The total variation of the long-cofactor window weight over `Icc 1 N`. -/
private theorem var_weight {ε x : ℝ} (hZ : 1 < scaleZ ε x) (t b : ℝ) (p2 A0 B0 : ℕ)
    (W : ℕ → ℝ)
    (hW : ∀ m, W m =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ m ∧
            m ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊) then (1 : ℝ) else 0)
      * (if m ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * b)⌋₊ then (0 : ℝ) else 1)
      * (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if upperPairRegion ε (expo ε x m) b then (0 : ℝ) else 1)
      * (if (A0 + 1 ≤ m ∧ m ≤ B0) then (1 : ℝ) else 0)
      * (if p2 + 1 ≤ m then (1 : ℝ) else 0)) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, |W k - W (k - 1)| ≤ 24) ∧ (∀ m, W m = 0 ∨ W m = 1) := by
  set f1 : ℕ → ℝ := fun m =>
    (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧ ⌈scaleZ ε x ^ b⌉₊ ≤ m ∧
          m ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * b)⌋₊) then (1 : ℝ) else 0)
    with hf1
  set f2 : ℕ → ℝ := fun m =>
    (if m ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * b)⌋₊ then (0 : ℝ) else 1)
    with hf2
  set f3 : ℕ → ℝ := fun m =>
    (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
            3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ m ∧
          m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * b) / 4)⌋₊)
        then (0 : ℝ) else 1)
    with hf3
  set f4 : ℕ → ℝ := fun m =>
    (if (b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
          ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
            ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - b)⌉₊ ≤ m ∧
          m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * b) / 4)⌋₊)
        then (0 : ℝ) else 1)
    with hf4
  set f5 : ℕ → ℝ := fun m => (if upperPairRegion ε (expo ε x m) b then (0 : ℝ) else 1) with hf5
  set f6 : ℕ → ℝ := fun m => (if (A0 + 1 ≤ m ∧ m ≤ B0) then (1 : ℝ) else 0) with hf6
  set f7 : ℕ → ℝ := fun m => (if p2 + 1 ≤ m then (1 : ℝ) else 0) with hf7
  have hW' : ∀ m, W m = f1 m * f2 m * f3 m * f4 m * f5 m * f6 m * f7 m := by
    intro m
    rw [hW m, hf1, hf2, hf3, hf4, hf5, hf6, hf7]
  have o1 : ∀ m, f1 m = 0 ∨ f1 m = 1 := by
    intro m; simp only [hf1]; split_ifs <;> simp
  have o2 : ∀ m, f2 m = 0 ∨ f2 m = 1 := by
    intro m; simp only [hf2]; split_ifs <;> simp
  have o3 : ∀ m, f3 m = 0 ∨ f3 m = 1 := by
    intro m; simp only [hf3]; split_ifs <;> simp
  have o4 : ∀ m, f4 m = 0 ∨ f4 m = 1 := by
    intro m; simp only [hf4]; split_ifs <;> simp
  have o5 : ∀ m, f5 m = 0 ∨ f5 m = 1 := by
    intro m; simp only [hf5]; split_ifs <;> simp
  have o6 : ∀ m, f6 m = 0 ∨ f6 m = 1 := by
    intro m; simp only [hf6]; split_ifs <;> simp
  have o7 : ∀ m, f7 m = 0 ∨ f7 m = 1 := by
    intro m; simp only [hf7]; split_ifs <;> simp
  have oW : ∀ m, W m = 0 ∨ W m = 1 := by
    intro m
    rw [hW' m]
    exact zero_or_one_mul (zero_or_one_mul (zero_or_one_mul (zero_or_one_mul
      (zero_or_one_mul (zero_or_one_mul (o1 m) (o2 m)) (o3 m)) (o4 m)) (o5 m)) (o6 m)) (o7 m)
  refine ⟨?_, oW⟩
  refine (sum_Icc_one_le_one_add (fun k => abs_nonneg _) N).trans ?_
  have hhead : |W 1 - W 0| ≤ 1 := abs_sub_le_one (oW 1) (oW 0)
  have htail : ∑ k ∈ Finset.Icc 2 N, |W k - W (k - 1)| ≤ 22 := by
    have hstep : ∑ k ∈ Finset.Icc 2 N, |W k - W (k - 1)|
        ≤ ∑ k ∈ Finset.Icc 2 N, (|f1 k - f1 (k - 1)| + |f2 k - f2 (k - 1)|
            + |f3 k - f3 (k - 1)| + |f4 k - f4 (k - 1)| + |f5 k - f5 (k - 1)|
            + |f6 k - f6 (k - 1)| + |f7 k - f7 (k - 1)|) :=
      Finset.sum_le_sum (fun k hk => by
        rw [hW' k, hW' (k - 1)]
        exact abs_prod_seven_sub_le o1 o2 o3 o4 o5 o6 o7 k)
    refine hstep.trans ?_
    · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have v1 : ∑ k ∈ Finset.Icc 2 N, |f1 k - f1 (k - 1)| ≤ 2 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf1]
        exact var_f_base b N
      have v2 : ∑ k ∈ Finset.Icc 2 N, |f2 k - f2 (k - 1)| ≤ 1 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf2]
        exact var_f_upper (ε := ε) (x := x) _ N
      have v3 : ∑ k ∈ Finset.Icc 2 N, |f3 k - f3 (k - 1)| ≤ 2 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf3]
        exact var_f_compl (ε := ε) (x := x) _ _ N
      have v4 : ∑ k ∈ Finset.Icc 2 N, |f4 k - f4 (k - 1)| ≤ 2 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf4]
        exact var_f_gated (ε := ε) (x := x) b _ _ N
      have v6 : ∑ k ∈ Finset.Icc 2 N, |f6 k - f6 (k - 1)| ≤ 2 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf6]
        exact sum_abs_sub_indicator_le_le (A0 + 1) B0 N
      have v7 : ∑ k ∈ Finset.Icc 2 N, |f7 k - f7 (k - 1)| ≤ 1 := by
        refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
        rw [hf7]
        exact sum_abs_sub_half_le _ N
      have v5 : ∑ k ∈ Finset.Icc 2 N, |f5 k - f5 (k - 1)| ≤ 8 := by
        have hterm : ∀ k ∈ Finset.Icc 2 N, |f5 k - f5 (k - 1)|
            ≤ |(if ⌈scaleZ ε x ^ b⌉₊ ≤ k then (1 : ℝ) else 0)
                - (if ⌈scaleZ ε x ^ b⌉₊ ≤ k - 1 then (1 : ℝ) else 0)|
              + |(if k ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)
                - (if k - 1 ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)|
              + |(if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ k ∧
                    k ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
                  then (1 : ℝ) else 0)
                - (if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ k - 1 ∧
                    k - 1 ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
                  then (1 : ℝ) else 0)|
              + |(if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k ∧
                    k ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                  then (1 : ℝ) else 0)
                - (if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k - 1 ∧
                    k - 1 ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                  then (1 : ℝ) else 0)|
              + |(if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k ∧
                    k ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                  then (1 : ℝ) else 0)
                - (if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k - 1 ∧
                    k - 1 ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                  then (1 : ℝ) else 0)| := by
          intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have hk1 : 1 ≤ k := by omega
          have hkm : 1 ≤ k - 1 := by omega
          rw [hf5]
          simp only []
          rw [show (if upperPairRegion ε (expo ε x k) b then (0 : ℝ) else 1)
              = 1 - (if upperPairRegion ε (expo ε x k) b then (1 : ℝ) else 0) from by
                by_cases h : upperPairRegion ε (expo ε x k) b <;> simp [h],
            show (if upperPairRegion ε (expo ε x (k - 1)) b then (0 : ℝ) else 1)
              = 1 - (if upperPairRegion ε (expo ε x (k - 1)) b then (1 : ℝ) else 0) from by
                by_cases h : upperPairRegion ε (expo ε x (k - 1)) b <;> simp [h],
            upr_factorization (ε := ε) (x := x) (b := b) (p := k) hZ hk1,
            upr_factorization (ε := ε) (x := x) (b := b) (p := k - 1) hZ hkm]
          set GT : ℝ := (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b ∧
              b ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) then (1 : ℝ) else 0) with hGT
          set G1 : ℕ → ℝ := fun m => (if ⌈scaleZ ε x ^ b⌉₊ ≤ m then (1 : ℝ) else 0) with hG1
          set G2 : ℕ → ℝ := fun m => (if m ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)
            with hG2
          set G3 : ℕ → ℝ := fun m =>
            (if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ m ∧
                m ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
              then (1 : ℝ) else 0) with hG3
          set G4 : ℕ → ℝ := fun m =>
            (if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ m ∧
                m ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
              then (1 : ℝ) else 0) with hG4
          set G5 : ℕ → ℝ := fun m =>
            (if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ m ∧
                m ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
              then (1 : ℝ) else 0) with hG5
          have oGT : GT = 0 ∨ GT = 1 := by rw [hGT]; split_ifs <;> simp
          have oG1 : ∀ m, G1 m = 0 ∨ G1 m = 1 := by
            intro m; simp only [hG1]; split_ifs <;> simp
          have oG2 : ∀ m, G2 m = 0 ∨ G2 m = 1 := by
            intro m; simp only [hG2]; split_ifs <;> simp
          have oG3 : ∀ m, G3 m = 0 ∨ G3 m = 1 := by
            intro m; simp only [hG3]; split_ifs <;> simp
          have oG4 : ∀ m, G4 m = 0 ∨ G4 m = 1 := by
            intro m; simp only [hG4]; split_ifs <;> simp
          have oG5 : ∀ m, G5 m = 0 ∨ G5 m = 1 := by
            intro m; simp only [hG5]; split_ifs <;> simp
          exact abs_upr_compl_sub_le GT oGT oG1 oG2 oG3 oG4 oG5 k
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
        have u1 : ∑ k ∈ Finset.Icc 2 N,
            |(if ⌈scaleZ ε x ^ b⌉₊ ≤ k then (1 : ℝ) else 0)
              - (if ⌈scaleZ ε x ^ b⌉₊ ≤ k - 1 then (1 : ℝ) else 0)| ≤ 1 := by
          refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
          exact sum_abs_sub_half_le _ N
        have u2 : ∑ k ∈ Finset.Icc 2 N,
            |(if k ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)
              - (if k - 1 ≤ ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ then (1 : ℝ) else 0)| ≤ 1 := by
          refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
          exact sum_abs_sub_half_upper_le _ N
        have u3 : ∑ k ∈ Finset.Icc 2 N,
            |(if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ k ∧
                  k ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
                then (1 : ℝ) else 0)
              - (if (⌈scaleZ ε x ^ (2 * b - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε)⌉₊ ≤ k - 1 ∧
                  k - 1 ≤ ⌊scaleZ ε x ^ ((36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε)⌋₊)
                then (1 : ℝ) else 0)| ≤ 2 := by
          refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
          exact sum_abs_sub_indicator_le_le _ _ N
        have u4 : ∑ k ∈ Finset.Icc 2 N,
            |(if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k ∧
                  k ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                then (1 : ℝ) else 0)
              - (if (⌈scaleZ ε x ^ ((2 - 3 * b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k - 1 ∧
                  k - 1 ≤ ⌊scaleZ ε x ^ ((2 - 3 * b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                then (1 : ℝ) else 0)| ≤ 2 := by
          refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
          exact sum_abs_sub_indicator_le_le _ _ N
        have u5 : ∑ k ∈ Finset.Icc 2 N,
            |(if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k ∧
                  k ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                then (1 : ℝ) else 0)
              - (if (⌈scaleZ ε x ^ ((2 - b - ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌉₊ ≤ k - 1 ∧
                  k - 1 ≤ ⌊scaleZ ε x ^ ((2 - b + ((2 * (1 / 16 - 1 / 10 ^ 5)) - ε)) / 4)⌋₊)
                then (1 : ℝ) else 0)| ≤ 2 := by
          refine (sum_Icc_two_le (fun k => abs_nonneg _) N).trans ?_
          exact sum_abs_sub_indicator_le_le _ _ N
        linarith
      linarith
  linarith

/-! ### The pointwise reduction and the one-window character bound

For a fixed pair `(p2, n)` the `p1` summand is the `0`-`1` window weight `W` against
`primeWeight p1 * χ p1` (`window_summand_factor`), and the Abel step of `norm_sum_mul_Ioc_le`
with the prime-character interval bound at ambient scale `X` bounds the window sum
(`window_abel`). -/

/-- The `p1` summand over a fixed pair `(p2, n)` is the window weight against
`primeWeight p1 * χ p1`: the five region factors, the window interval and the half-line
`p2 < p1` are exactly the conditions, and `p1.Prime` is carried by `primeWeight`. -/
private theorem window_summand_factor {ε x t : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p2 n : ℕ} (hp2 : p2.Prime) (hn : p2 ≤ n) (hZ : 1 < scaleZ ε x) (hP : 0 < p2 * n)
    {A0 B0 : ℕ}
    (hivl : ∀ p : ℕ, (p * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
      ↔ (A0 + 1 ≤ p ∧ p ≤ B0))
    (W : ℕ → ℝ)
    (hW : ∀ m, W m =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ expo ε x p2 ∧ ⌈scaleZ ε x ^ (expo ε x p2)⌉₊ ≤ m ∧
            m ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * expo ε x p2)⌋₊) then (1 : ℝ) else 0)
      * (if m ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * expo ε x p2)⌋₊ then (0 : ℝ) else 1)
      * (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - expo ε x p2)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * expo ε x p2) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if (expo ε x p2 ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - expo ε x p2)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * expo ε x p2) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if upperPairRegion ε (expo ε x m) (expo ε x p2) then (0 : ℝ) else 1)
      * (if (A0 + 1 ≤ m ∧ m ≤ B0) then (1 : ℝ) else 0)
      * (if p2 + 1 ≤ m then (1 : ℝ) else 0)) :
    ∀ p1 : ℕ, 1 ≤ p1 →
      (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
          lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
          p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
        then χ (p1 : ZMod q) else 0)
      = W p1 • ((primeWeight p1 : ℂ) * χ (p1 : ZMod q)) := by
  intro p1 hp1
  have hreg := region_p_factorization (ε := ε) (x := x) (b := expo ε x p2) hZ hp1
  have hWv : W p1 = (if lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) then (1 : ℝ) else 0)
      * (if (A0 + 1 ≤ p1 ∧ p1 ≤ B0) then (1 : ℝ) else 0)
      * (if p2 + 1 ≤ p1 then (1 : ℝ) else 0) := by
    rw [hW p1, ← hreg]
  by_cases hprime : p1.Prime
  · by_cases hrest : (p2 < p1 ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧
        p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
    · have hW1 : W p1 = 1 := by
        rw [hWv, if_pos hrest.2.1, if_pos ((hivl p1).mp hrest.2.2), if_pos (by omega)]
        norm_num
      rw [if_pos ⟨hprime, hp2, hrest.1, hrest.2.1, hn, hrest.2.2⟩, hW1]
      simp [primeWeight, hprime]
    · have hW0 : W p1 = 0 := by
        rw [hWv]
        have hconj : ¬(lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧
            (A0 + 1 ≤ p1 ∧ p1 ≤ B0) ∧ p2 + 1 ≤ p1) := by
          intro h
          exact hrest ⟨by omega, h.1, (hivl p1).mpr h.2.1⟩
        rcases not_and_or.mp hconj with h1 | h1
        · rw [if_neg h1]; ring
        · rcases not_and_or.mp h1 with h2 | h2
          · rw [if_neg h2]; ring
          · rw [if_neg h2]; ring
      rw [if_neg (by tauto), hW0]
      simp
  · rw [if_neg (by tauto)]
    simp [primeWeight, hprime]

/-- The one-window character bound: the window weight has variation at most `24`
(`var_weight`) and the prime-character prefix sums over intervals are bounded at ambient scale
`X` (`prime_char_interval_bound`), so the window sum is at most `25 * 2 * q * K * X / log ^ D X`.
-/
private theorem window_abel {ε x t : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {p2 n : ℕ} (hp2 : p2.Prime) (hn : p2 ≤ n) (hZ : 1 < scaleZ ε x) (hP : 0 < p2 * n)
    {D B K X : ℝ} (hK : 0 < K) (hq : 1 ≤ q) (hχ : χ ≠ 1)
    (hKb : ∀ Y : ℝ, 2 ≤ Y → ∀ (r : ℕ) [NeZero r], 1 ≤ r →
      (r : ℝ) ≤ Real.sqrt Y / Real.log Y ^ B →
      ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Y →
        ‖∑ m ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, (primeWeight m : ℂ) * ψ (m : ZMod r)‖ ≤
          2 * ((r : ℝ) * (K * Y / Real.log Y ^ D)))
    (hX2 : 2 ≤ X) (hqX : (q : ℝ) ≤ Real.sqrt X / Real.log X ^ B)
    (hXup : ((min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n)) : ℕ) : ℝ) ≤ X)
    (W : ℕ → ℝ)
    (hW : ∀ m, W m =
      (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ expo ε x p2 ∧ ⌈scaleZ ε x ^ (expo ε x p2)⌉₊ ≤ m ∧
            m ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * expo ε x p2)⌋₊) then (1 : ℝ) else 0)
      * (if m ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε - 2 * expo ε x p2)⌋₊ then (0 : ℝ) else 1)
      * (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - expo ε x p2)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 7 * expo ε x p2) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if (expo ε x p2 ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
            ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
              ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε - expo ε x p2)⌉₊ ≤ m ∧
            m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε - 5 * expo ε x p2) / 4)⌋₊)
          then (0 : ℝ) else 1)
      * (if upperPairRegion ε (expo ε x m) (expo ε x p2) then (0 : ℝ) else 1)
      * (if (⌊x ^ (11 / 20 + ε)⌋₊ / (p2 * n) + 1 ≤ m ∧
            m ≤ min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n))) then (1 : ℝ) else 0)
      * (if p2 + 1 ≤ m then (1 : ℝ) else 0))
    (h01 : ∀ m, W m = 0 ∨ W m = 1)
    (hivl : ∀ p : ℕ, (p * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
      ↔ (⌊x ^ (11 / 20 + ε)⌋₊ / (p2 * n) + 1 ≤ p ∧
          p ≤ min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n)))) :
    ‖∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0)‖
      ≤ 25 * (2 * ((q : ℝ) * (K * X / Real.log X ^ D))) := by
  set A0 : ℕ := ⌊x ^ (11 / 20 + ε)⌋₊ / (p2 * n) with hA0
  set B0 : ℕ := min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n)) with hB0
  have hivl' : ∀ p : ℕ, (p * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
      ↔ (A0 + 1 ≤ p ∧ p ≤ B0) := by
    intro p
    rw [hivl p, hA0, hB0]
  have hB0t : B0 ≤ ⌊t⌋₊ := by
    rw [hB0]
    exact le_trans (min_le_right _ _) (Nat.div_le_self _ _)
  have hvan : ∑ p1 ∈ Finset.Ioc A0 B0,
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0)
      = ∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0) := by
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
      exact ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le A0) hp.1),
        le_trans hp.2 hB0t⟩
    · intro p _ hpout
      rw [if_neg]
      intro hC
      obtain ⟨h1, h2⟩ := (hivl' p).mp hC.2.2.2.2.2
      simp only [Finset.mem_Ioc] at hpout
      exact hpout ⟨Nat.lt_of_succ_le h1, h2⟩
  rw [← hvan]
  have hpt : ∀ p1 ∈ Finset.Ioc A0 B0,
      (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
          lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
          p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
        then χ (p1 : ZMod q) else 0)
      = W p1 • ((primeWeight p1 : ℂ) * χ (p1 : ZMod q)) := by
    intro p1 hp1
    have hp1' : 1 ≤ p1 := by
      have h := (Finset.mem_Ioc.mp hp1).1
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le A0) h)
    exact window_summand_factor χ hp2 hn hZ hP hivl' W hW p1 hp1'
  rw [Finset.sum_congr rfl hpt]
  have hvar : ∑ p ∈ Finset.Ioc A0 B0, |W p - W (p - 1)| ≤ 24 := by
    refine le_trans (sum_Ioc_le_sum_Icc (fun p => abs_nonneg _) hB0t) ?_
    exact (var_weight hZ t (expo ε x p2) p2 A0 B0 W hW ⌊t⌋₊).1
  have hB : ∀ k, A0 ≤ k → k ≤ B0 →
      ‖∑ p ∈ Finset.Ioc A0 k, (primeWeight p : ℂ) * χ (p : ZMod q)‖ ≤
        2 * ((q : ℝ) * (K * X / Real.log X ^ D)) := by
    intro k hk1 hk2
    have hkv : (k : ℝ) ≤ X := by
      have h1 : (k : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast le_trans hk2 le_rfl
      have h2 : (B0 : ℝ) ≤ X := by
        rw [hB0]
        exact hXup
      linarith
    have hk1' : (0 : ℝ) ≤ (A0 : ℝ) := by positivity
    have hk2' : (A0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have := hKb X hX2 q hq hqX χ hχ (A0 : ℝ) (k : ℝ) hk1' hk2' hkv
    simpa using this
  have hBndnn : (0 : ℝ) ≤ 2 * ((q : ℝ) * (K * X / Real.log X ^ D)) := by
    have hLX : 0 < Real.log X := Real.log_pos (by linarith)
    have hXD : 0 < Real.log X ^ D := Real.rpow_pos_of_pos hLX D
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have h1 : 0 < K * X / Real.log X ^ D := div_pos (by positivity) hXD
    have h2 : 0 ≤ (q : ℝ) * (K * X / Real.log X ^ D) := mul_nonneg hq0 h1.le
    linarith
  have hAbel := norm_sum_mul_Ioc_le W (fun p => (primeWeight p : ℂ) * χ (p : ZMod q)) 24
    (2 * ((q : ℝ) * (K * X / Real.log X ^ D))) h01 hBndnn hvar hB
  rw [show (24 + 1 : ℝ) = 25 by norm_num] at hAbel
  exact hAbel
/-! ### From the region to the ambient scale of the window

`E2` gives `β₁ ≥ β₂ ≥ 0.1249`, hence `p₁ ≥ Z^0.1249`, and the window gives `p₁ ≤ X = 2Y/(p₂n)`.
So the ambient scale of every nonempty window is at least `x^0.0686`, which is what the
modulus condition `q ≤ √X / log^B X` and the error term `log^{-D} X` need. -/

/-- `E2` forces the larger prime exponent to be at least `0.1249`. -/
private theorem expo_ge_1249 {ε a b : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8)
    (h : lowerTwoDiscarded ε a b) : (0.1249 : ℝ) ≤ a := by
  have h1 : (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ b := h.1
  have h2 : b ≤ a := h.2.1
  have h3 : (0.1249 : ℝ) ≤
      (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - (1 / 10 ^ 8 : ℝ) := by norm_num
  linarith

/-- `Z ^ c ≤ p` for every `c ≤ expo p`. -/
private theorem ge_scaleZ_rpow_expo {ε x : ℝ} (hx0 : 0 < x) (hZ : 1 < scaleZ ε x)
    {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : c ≤ expo ε x p) :
    scaleZ ε x ^ c ≤ (p : ℝ) := by
  have hZ0 : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : (0 : ℝ) < Real.log (scaleZ ε x) := Real.log_pos hZ
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : Real.log (p : ℝ) = expo ε x p * Real.log (scaleZ ε x) := by
    unfold expo
    field_simp
  have h1 : c * Real.log (scaleZ ε x) ≤ Real.log (p : ℝ) := by
    rw [hlog]
    nlinarith [hLZ, hc]
  calc scaleZ ε x ^ c = Real.exp (Real.log (scaleZ ε x) * c) := Real.rpow_def_of_pos hZ0 c
    _ = Real.exp (c * Real.log (scaleZ ε x)) := by rw [mul_comm]
    _ ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.mpr h1
    _ = (p : ℝ) := Real.exp_log hp0

/-- `x^0.0686 ≤ Z^0.1249`. -/
private theorem x_rpow_le_scaleZ_rpow {ε x : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε) :
    x ^ (0.0686 : ℝ) ≤ scaleZ ε x ^ (0.1249 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hYpos : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hZpos : (0 : ℝ) < scaleZ ε x := by unfold scaleZ; linarith
  have h1 : shortY ε x ^ (0.1249 : ℝ) ≤ scaleZ ε x ^ (0.1249 : ℝ) :=
    Real.rpow_le_rpow hYpos.le (by unfold scaleZ; linarith) (by norm_num)
  have h2 : x ^ ((11 / 20 + ε) * 0.1249) = shortY ε x ^ (0.1249 : ℝ) := by
    unfold shortY
    rw [Real.rpow_mul hx0.le]
  have h3 : (0.0686 : ℝ) ≤ (11 / 20 + ε) * 0.1249 := by nlinarith
  calc x ^ (0.0686 : ℝ) ≤ x ^ ((11 / 20 + ε) * 0.1249) :=
        Real.rpow_le_rpow_of_exponent_le hx1 h3
    _ = shortY ε x ^ (0.1249 : ℝ) := h2
    _ ≤ scaleZ ε x ^ (0.1249 : ℝ) := h1

/-- A point of the window gives `Z ^ 0.1249 ≤ 2Y/(p₂ n)`. -/
private theorem window_scale_lower {ε x t : ℝ} (hx1 : 1 ≤ x)
    {p1 p2 n : ℕ} (hp1 : 1 ≤ p1) (hP : 0 < p2 * n) (hZ : 1 < scaleZ ε x)
    (hε8 : ε ≤ 1 / 10 ^ 8)
    (hdisc : lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
    (hin : p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) :
    scaleZ ε x ^ (0.1249 : ℝ) ≤ 2 * shortY ε x / ((p2 * n : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hYpos : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hP0 : (0 : ℝ) < ((p2 * n : ℕ) : ℝ) := by exact_mod_cast hP
  have hstep1 : scaleZ ε x ^ (0.1249 : ℝ) ≤ (p1 : ℝ) :=
    ge_scaleZ_rpow_expo hx0 hZ hp1 (expo_ge_1249 hε8 hdisc)
  have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hin).1
  have h2Y : ((p1 * p2 * n : ℕ) : ℝ) ≤ 2 * shortY ε x := by
    have h := hIoc.2
    have h1 : ((p1 * p2 * n : ℕ) : ℝ) ≤ ((⌊2 * shortY ε x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h
    have h2 : ((⌊2 * shortY ε x⌋₊ : ℕ) : ℝ) ≤ 2 * shortY ε x :=
      Nat.floor_le (by linarith)
    linarith
  have hmul : (p1 : ℝ) * ((p2 * n : ℕ) : ℝ) ≤ 2 * shortY ε x := by
    have hc : ((p1 * p2 * n : ℕ) : ℝ) = (p1 : ℝ) * ((p2 * n : ℕ) : ℝ) := by
      push_cast
      ring
    linarith [hc ▸ h2Y]
  rw [le_div_iff₀ hP0]
  nlinarith [hstep1, hmul, hP0]

/-- The per-pair reduction: for a fixed pair `(p₂, n)` the window sum obeys the character saving
at the pair's own ambient scale. The empty window contributes nothing. -/
private theorem window_pair {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    {A B D K : ℝ} (hB : 0 < B) (hK : 0 < K) (hD : 0 < D)
    (hKb : ∀ Y : ℝ, 2 ≤ Y → ∀ (r : ℕ) [NeZero r], 1 ≤ r →
      (r : ℝ) ≤ Real.sqrt Y / Real.log Y ^ B →
      ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Y →
        ‖∑ m ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, (primeWeight m : ℂ) * ψ (m : ZMod r)‖ ≤
          2 * ((r : ℝ) * (K * Y / Real.log Y ^ D)))
    {x t : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hq : 1 ≤ q) (hqA : (q : ℝ) ≤ Real.log x ^ A)
    (hx1 : 1 ≤ x) (hthr : (2 : ℝ) ^ ((1 : ℝ) / 0.0686) ≤ x) (hxle : 2 * shortY ε x ≤ x)
    (hlogone : 1 ≤ Real.log x)
    (hlogbig : Real.log x ^ (A + B + 1) ≤ x ^ (0.03 : ℝ))
    {p2 n : ℕ} (hp2 : p2.Prime) (hn : p2 ≤ n) (hP : 0 < p2 * n) :
    ‖∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0)‖
      ≤ 50 * (q : ℝ) * K * (2 * shortY ε x / ((p2 * n : ℕ) : ℝ))
          / (0.1249 * Real.log (scaleZ ε x)) ^ D := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hYpos : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hZpos : (0 : ℝ) < scaleZ ε x := by unfold scaleZ; linarith
  have hZ : 1 < scaleZ ε x := by
    unfold scaleZ shortY
    have h1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
    linarith
  have hLZ : (0 : ℝ) < Real.log (scaleZ ε x) := Real.log_pos hZ
  have hP0 : (0 : ℝ) < ((p2 * n : ℕ) : ℝ) := by exact_mod_cast hP
  set X : ℝ := 2 * shortY ε x / ((p2 * n : ℕ) : ℝ) with hXdef
  have hXpos : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hXle : X ≤ x := by
    rw [hXdef]
    have h1 : 2 * shortY ε x / ((p2 * n : ℕ) : ℝ) ≤ 2 * shortY ε x := by
      rw [div_le_iff₀ hP0]
      have h2 : (1 : ℝ) ≤ ((p2 * n : ℕ) : ℝ) := by exact_mod_cast hP
      nlinarith [hYpos]
    linarith
  set A0 : ℕ := ⌊x ^ (11 / 20 + ε)⌋₊ / (p2 * n) with hA0
  set B0 : ℕ := min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n)) with hB0
  set W : ℕ → ℝ := fun m =>
    (if ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ expo ε x p2 ∧
          ⌈scaleZ ε x ^ (expo ε x p2)⌉₊ ≤ m ∧
          m ≤ min ⌊scaleZ ε x ^ (1 / 2 : ℝ)⌋₊ ⌊scaleZ ε x ^ (1 - 2 * expo ε x p2)⌋₊)
        then (1 : ℝ) else 0)
    * (if m ≤ ⌊scaleZ ε x ^ (1 / 2 + (1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε
          - 2 * expo ε x p2)⌋₊ then (0 : ℝ) else 1)
    * (if (⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
            3 * ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε
            - expo ε x p2)⌉₊ ≤ m ∧
          m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε
            - 7 * expo ε x p2) / 4)⌋₊) then (0 : ℝ) else 1)
    * (if (expo ε x p2 ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε ∧
          ⌈scaleZ ε x ^ (1 / 2 - ((2 * (1 / 16 - 1 / 10 ^ 5)) +
            ((1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε)) / 4 + ε
            - expo ε x p2)⌉₊ ≤ m ∧
          m ≤ ⌊scaleZ ε x ^ ((2 + (2 * (1 / 16 - 1 / 10 ^ 5)) - ε
            - 5 * expo ε x p2) / 4)⌋₊) then (0 : ℝ) else 1)
    * (if upperPairRegion ε (expo ε x m) (expo ε x p2) then (0 : ℝ) else 1)
    * (if (A0 + 1 ≤ m ∧ m ≤ B0) then (1 : ℝ) else 0)
    * (if p2 + 1 ≤ m then (1 : ℝ) else 0) with hWdef
  have h01 : ∀ m, W m = 0 ∨ W m = 1 :=
    (var_weight hZ t (expo ε x p2) p2 A0 B0 W (fun m => rfl) ⌊t⌋₊).2
  have hivl : ∀ p : ℕ, (p * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
      ↔ (A0 + 1 ≤ p ∧ p ≤ B0) := by
    intro p
    rcases Nat.eq_zero_or_pos p with h0 | hpos
    · subst h0
      have h1 : ¬ (0 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)) := by
        simp only [Finset.mem_filter, Finset.mem_Ioc, rightInterval, Nat.zero_mul]
        intro h
        exact Nat.not_lt_zero _ h.1.1
      exact ⟨fun h => absurd h h1, fun h => absurd h.1 (Nat.not_succ_le_zero A0)⟩
    · rw [window_interval_iff t hP hpos, hA0, hB0]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.succ_le_of_lt h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.lt_of_succ_le h1, h2⟩
  by_cases hne : ∃ p1 : ℕ, p1 ∈ Finset.Icc 1 ⌊t⌋₊ ∧
      (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧
        p2 ≤ n ∧ p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
  · obtain ⟨p1, hp1mem, hprime, -, -, hdisc, -, hwin⟩ := hne
    have hp1 : 1 ≤ p1 := (Finset.mem_Icc.mp hp1mem).1
    have hXlow : scaleZ ε x ^ (0.1249 : ℝ) ≤ X := by
      rw [hXdef]
      exact window_scale_lower hx1 hp1 hP hZ hε8 hdisc hwin
    have hXbig : x ^ (0.0686 : ℝ) ≤ X :=
      le_trans (x_rpow_le_scaleZ_rpow hx1 hε.le) hXlow
    have hX2 : 2 ≤ X := by
      have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 0.0686)) ^ (0.0686 : ℝ) ≤ x ^ (0.0686 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hthr (by norm_num)
      have h5 : ((2 : ℝ) ^ ((1 : ℝ) / 0.0686)) ^ (0.0686 : ℝ) = 2 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have h4 : (2 : ℝ) ≤ x ^ (0.0686 : ℝ) := by rw [← h5]; exact h3
      linarith
    have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
    have hqX : (q : ℝ) ≤ Real.sqrt X / Real.log X ^ B := by
      have hlx : (0 : ℝ) < Real.log x := by linarith
      have hlogXle : Real.log X ≤ Real.log x := Real.log_le_log hXpos hXle
      have hlogB : Real.log X ^ B ≤ Real.log x ^ B :=
        Real.rpow_le_rpow (le_of_lt hlogX) hlogXle hB.le
      have hsqrt : x ^ (0.0343 : ℝ) ≤ Real.sqrt X := by
        rw [Real.sqrt_eq_rpow]
        have h1 : x ^ (0.0343 : ℝ) = (x ^ (0.0686 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hx0.le]
          norm_num
        rw [h1]
        exact Real.rpow_le_rpow (by positivity) hXbig (by norm_num)
      have hAB : Real.log x ^ A * Real.log x ^ B = Real.log x ^ (A + B) := by
        rw [← Real.rpow_add hlx]
      have hle1 : Real.log x ^ (A + B) ≤ Real.log x ^ (A + B + 1) :=
        Real.rpow_le_rpow_of_exponent_le hlogone (by linarith)
      have hx0343 : x ^ (0.03 : ℝ) ≤ x ^ (0.0343 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have hmul : (q : ℝ) * Real.log x ^ B ≤ x ^ (0.0343 : ℝ) := by
        have hqB : (q : ℝ) * Real.log x ^ B ≤ Real.log x ^ A * Real.log x ^ B :=
          mul_le_mul_of_nonneg_right hqA (Real.rpow_pos_of_pos hlx B).le
        rw [hAB] at hqB
        linarith [hqB, hle1, hlogbig, hx0343]
      have hstep1 : (q : ℝ) ≤ x ^ (0.0343 : ℝ) / Real.log x ^ B := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hlx B)]
        linarith [hmul]
      refine le_trans hstep1 ?_
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlx B) (Real.rpow_pos_of_pos hlogX B)]
      exact mul_le_mul hsqrt hlogB (Real.rpow_pos_of_pos hlogX B).le (Real.sqrt_nonneg X)
    have hXup : ((B0 : ℕ) : ℝ) ≤ X := by
      rw [hB0, hXdef]
      have h1 : ((min (⌊2 * x ^ (11 / 20 + ε)⌋₊ / (p2 * n)) (⌊t⌋₊ / (p2 * n)) : ℕ) : ℝ)
          ≤ ((⌊2 * shortY ε x⌋₊ / (p2 * n) : ℕ) : ℝ) := by
        exact_mod_cast min_le_left _ _
      have h2 : ((⌊2 * shortY ε x⌋₊ / (p2 * n) : ℕ) : ℝ)
          ≤ 2 * shortY ε x / ((p2 * n : ℕ) : ℝ) := by
        rw [le_div_iff₀ hP0]
        have h3 : ((⌊2 * shortY ε x⌋₊ / (p2 * n) : ℕ) : ℝ) * ((p2 * n : ℕ) : ℝ)
            = (((⌊2 * shortY ε x⌋₊ / (p2 * n)) * (p2 * n) : ℕ) : ℝ) := by
          push_cast
          ring
        rw [h3]
        have h4 : (⌊2 * shortY ε x⌋₊ / (p2 * n)) * (p2 * n) ≤ ⌊2 * shortY ε x⌋₊ :=
          Nat.div_mul_le_self _ _
        have h5 : ((⌊2 * shortY ε x⌋₊ : ℕ) : ℝ) ≤ 2 * shortY ε x :=
          Nat.floor_le (by linarith)
        exact le_trans (by exact_mod_cast h4) h5
      linarith
    have hlt : (0.1249 : ℝ) * Real.log (scaleZ ε x) ≤ Real.log X := by
      have h1 : Real.log (scaleZ ε x ^ (0.1249 : ℝ)) ≤ Real.log X :=
        Real.log_le_log (Real.rpow_pos_of_pos hZpos _) hXlow
      rwa [Real.log_rpow hZpos] at h1
    have hAb := window_abel χ hp2 hn hZ hP hK hq hχ hKb hX2 hqX hXup W (fun m => rfl) h01 hivl
    refine hAb.trans ?_
    have hYpos2 : (0 : ℝ) < (0.1249 * Real.log (scaleZ ε x)) ^ D :=
      Real.rpow_pos_of_pos (by linarith) D
    have hlogD : (0.1249 * Real.log (scaleZ ε x)) ^ D ≤ Real.log X ^ D :=
      Real.rpow_le_rpow (by linarith) hlt hD.le
    have hinv : (Real.log X ^ D)⁻¹ ≤ ((0.1249 * Real.log (scaleZ ε x)) ^ D)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hYpos2 hlogD
    have hdiv : X / Real.log X ^ D ≤ X / (0.1249 * Real.log (scaleZ ε x)) ^ D := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hXpos.le
    have h1 : 25 * (2 * ((q : ℝ) * (K * X / Real.log X ^ D)))
        = 50 * (q : ℝ) * K * (X / Real.log X ^ D) := by ring
    rw [h1]
    have h3 : 50 * (q : ℝ) * K * (X / Real.log X ^ D)
        ≤ 50 * (q : ℝ) * K * (X / (0.1249 * Real.log (scaleZ ε x)) ^ D) := by
      refine mul_le_mul_of_nonneg_left hdiv ?_
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
      positivity
    refine le_trans h3 (le_of_eq ?_)
    ring
  · have hzero : (∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
            p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
          then χ (p1 : ZMod q) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun p1 hp1 => ?_)
      rw [if_neg]
      intro h
      exact hne ⟨p1, hp1, h⟩
    rw [hzero, norm_zero]
    have hpos : (0 : ℝ) < (0.1249 * Real.log (scaleZ ε x)) ^ D :=
      Real.rpow_pos_of_pos (by linarith) D
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hX0 : (0 : ℝ) ≤ X := hXpos.le
    have : (0 : ℝ) ≤ 50 * (q : ℝ) * K * X / (0.1249 * Real.log (scaleZ ε x)) ^ D := by
      have h1 : (0 : ℝ) ≤ 50 * (q : ℝ) * K * X := by positivity
      exact div_nonneg h1 hpos.le
    linarith [this]


/-! ### The two elementary inputs of the pair sum

`sum_pair_inv_le` is the harmonic bound `∑∑ 1/(p₂ n) ≤ (1 + log N)²`; `log_pow_le_rpow_small`
is the threshold behind the modulus condition `q ≤ √X / log^B X`, which needs
`log^(A+B) x ≤ x^0.03` for `x` beyond an explicit constant. -/

/-- `∑_{p₂, n ≤ N} 1/(p₂ n) ≤ (1 + log N)^2`. -/
private theorem sum_pair_inv_le (N : ℕ) :
    ∑ p2 ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (((p2 * n : ℕ)) : ℝ)⁻¹
      ≤ (1 + Real.log N) ^ 2 := by
  have hfac : ∑ p2 ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (((p2 * n : ℕ)) : ℝ)⁻¹
      = (∑ p2 ∈ Finset.Icc 1 N, ((p2 : ℕ) : ℝ)⁻¹)
        * (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ)⁻¹) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p2 _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [Nat.cast_mul, mul_inv]
  have hh : ∀ M : ℕ, (∑ n ∈ Finset.Icc 1 M, ((n : ℕ) : ℝ)⁻¹) = (harmonic M : ℝ) := by
    intro M
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp only [hfac, hh]
  have hb : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have h0 : (0 : ℝ) ≤ (harmonic N : ℝ) := by
    rw [← hh]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have h1L : (0 : ℝ) ≤ 1 + Real.log N := by
    have hL : (0 : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    linarith
  nlinarith [mul_le_mul hb hb h0 h1L]

/-- `log^M x ≤ x^0.03` beyond the explicit threshold `(M / 0.015)^(M / 0.015)`. -/
private theorem log_pow_le_rpow_small {M : ℝ} (hM : 1 ≤ M) :
    ∀ x : ℝ, (M / 0.015) ^ (M / 0.015) ≤ x → Real.log x ^ M ≤ x ^ (0.03 : ℝ) := by
  intro x hx
  have hM0 : 0 < M := by linarith
  set r : ℝ := 0.015 / M with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hMne : (0 : ℝ) < M / 0.015 := by positivity
  have hbase1 : (1 : ℝ) ≤ M / 0.015 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hx1 : (1 : ℝ) ≤ x := by
    have h3 : (1 : ℝ) ≤ (M / 0.015) ^ (M / 0.015) :=
      Real.one_le_rpow hbase1 (by linarith)
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x ^ r / r := Real.log_le_rpow_div hx0.le hr0
  have hrm : r * M = 0.015 := by rw [hr]; field_simp
  have hstep : Real.log x ^ M ≤ (x ^ r / r) ^ M :=
    Real.rpow_le_rpow hlx0 hlog (by linarith)
  have hxr : (0 : ℝ) ≤ x ^ r := (Real.rpow_pos_of_pos hx0 _).le
  have hsplit : (x ^ r / r) ^ M = x ^ (0.015 : ℝ) / r ^ M := by
    rw [Real.div_rpow hxr hr0.le, ← Real.rpow_mul hx0.le, hrm]
  have hreq : r = (M / 0.015)⁻¹ := by rw [hr]; field_simp
  have haM : (M / 0.015) ^ M ≤ x ^ (0.015 : ℝ) := by
    have h1 : ((M / 0.015) ^ (M / 0.015)) ^ (0.015 : ℝ) ≤ x ^ (0.015 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_pos_of_pos hMne _).le hx (by norm_num)
    have h2 : ((M / 0.015) ^ (M / 0.015)) ^ (0.015 : ℝ) = (M / 0.015) ^ M := by
      rw [← Real.rpow_mul hMne.le]
      congr 1
      field_simp
    rwa [h2] at h1
  have hrM : (0 : ℝ) < r ^ M := Real.rpow_pos_of_pos hr0 M
  have hone : (1 : ℝ) ≤ x ^ (0.015 : ℝ) * r ^ M := by
    have h3 : (r ^ M)⁻¹ = (M / 0.015) ^ M := by
      rw [hreq, Real.inv_rpow hMne.le, inv_inv]
    have h4 : (r ^ M)⁻¹ ≤ x ^ (0.015 : ℝ) := by rw [h3]; exact haM
    have h5 := mul_le_mul_of_nonneg_right h4 hrM.le
    rwa [inv_mul_cancel₀ hrM.ne'] at h5
  have hfin : x ^ (0.015 : ℝ) / r ^ M ≤ x ^ (0.03 : ℝ) := by
    rw [div_le_iff₀ hrM]
    have hxadd : x ^ (0.03 : ℝ) = x ^ (0.015 : ℝ) * x ^ (0.015 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [hxadd]
    have h0 : (0 : ℝ) ≤ x ^ (0.015 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
    nlinarith [hone, h0, hrM]
  calc Real.log x ^ M ≤ (x ^ r / r) ^ M := hstep
    _ = x ^ (0.015 : ℝ) / r ^ M := hsplit
    _ ≤ x ^ (0.03 : ℝ) := hfin



/-- The pair sum: after `window_pair` the remaining double sum is `∑ ψ(n,p₂)/(p₂n)`, which is at
most `(1 + log ⌊t⌋)^2`. -/
private theorem window_pair_sum {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    {A B D K : ℝ} (hB : 0 < B) (hK : 0 < K) (hD : 0 < D)
    (hKb : ∀ Y : ℝ, 2 ≤ Y → ∀ (r : ℕ) [NeZero r], 1 ≤ r →
      (r : ℝ) ≤ Real.sqrt Y / Real.log Y ^ B →
      ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Y →
        ‖∑ m ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, (primeWeight m : ℂ) * ψ (m : ZMod r)‖ ≤
          2 * ((r : ℝ) * (K * Y / Real.log Y ^ D)))
    {x t : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hq : 1 ≤ q) (hqA : (q : ℝ) ≤ Real.log x ^ A)
    (hx1 : 1 ≤ x) (hthr : (2 : ℝ) ^ ((1 : ℝ) / 0.0686) ≤ x) (hxle : 2 * shortY ε x ≤ x)
    (hlogone : 1 ≤ Real.log x)
    (hlogbig : Real.log x ^ (A + B + 1) ≤ x ^ (0.03 : ℝ)) :
    ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
                lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
              ∧ p2 ≤ m / (p1 * p2)
              then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖
      ≤ 50 * (q : ℝ) * K * (2 * shortY ε x) / (0.1249 * Real.log (scaleZ ε x)) ^ D
          * (1 + Real.log ⌊t⌋₊) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hYpos : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hZpos : (0 : ℝ) < scaleZ ε x := by unfold scaleZ; linarith
  have hLZ : (0 : ℝ) < Real.log (scaleZ ε x) := by
    apply Real.log_pos
    unfold scaleZ shortY
    have h1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
    linarith
  have hcpos : (0 : ℝ) < (0.1249 * Real.log (scaleZ ε x)) ^ D :=
    Real.rpow_pos_of_pos (by linarith) D
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  refine le_trans (long_le_prime_chi_window t χ) ?_
  have hpair : ∀ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∀ n ∈ Finset.Icc 1 ⌊t⌋₊,
      ‖∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
          (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
              lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
              p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
            then χ (p1 : ZMod q) else 0)‖
        ≤ 50 * (q : ℝ) * K * (2 * shortY ε x / ((p2 * n : ℕ) : ℝ))
            / (0.1249 * Real.log (scaleZ ε x)) ^ D := by
    intro p2 hp2mem n hnm
    by_cases hp : p2.Prime ∧ p2 ≤ n
    · have hP : 0 < p2 * n := by
        have h1 : 1 ≤ p2 := (Finset.mem_Icc.mp hp2mem).1
        have h2 : 1 ≤ n := (Finset.mem_Icc.mp hnm).1
        positivity
      exact window_pair hε hε8 hB hK hD hKb χ hχ hq hqA hx1 hthr hxle hlogone hlogbig
        hp.1 hp.2 hP
    · have hzero : (∑ p1 ∈ Finset.Icc 1 ⌊t⌋₊,
          (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
              lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) ∧ p2 ≤ n ∧
              p1 * p2 * n ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
            then χ (p1 : ZMod q) else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun p1 _ => ?_)
        rw [if_neg]
        intro h
        exact hp ⟨h.2.1, h.2.2.2.2.1⟩
      rw [hzero, norm_zero]
      have h1 : (0 : ℝ) ≤ 50 * (q : ℝ) * K * (2 * shortY ε x / ((p2 * n : ℕ) : ℝ)) := by
        have hP : (0 : ℝ) < ((p2 * n : ℕ) : ℝ) := by
          have h1 : 1 ≤ p2 := (Finset.mem_Icc.mp hp2mem).1
          have h2 : 1 ≤ n := (Finset.mem_Icc.mp hnm).1
          have h3 : 0 < p2 * n := by positivity
          exact_mod_cast h3
        positivity
      exact div_nonneg h1 hcpos.le
  refine le_trans (Finset.sum_le_sum (fun p2 hp2 => Finset.sum_le_sum (fun n hn =>
    mul_le_mul_of_nonneg_left (hpair p2 hp2 n hn) (rough_nonneg n p2)))) ?_
  have hfac : ∀ p2 n : ℕ,
      50 * (q : ℝ) * K * (2 * shortY ε x / ((p2 * n : ℕ) : ℝ))
          / (0.1249 * Real.log (scaleZ ε x)) ^ D
        = (50 * (q : ℝ) * K * (2 * shortY ε x)) / (0.1249 * Real.log (scaleZ ε x)) ^ D
            * (((p2 * n : ℕ) : ℝ))⁻¹ := by
    intro p2 n
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hsum2 : ∑ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
      rough n p2 * (((p2 * n : ℕ) : ℝ))⁻¹ ≤ (1 + Real.log ⌊t⌋₊) ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun p2 _ => Finset.sum_le_sum (fun n _ => ?_)))
      (sum_pair_inv_le ⌊t⌋₊)
    · have h1 : rough n p2 ≤ 1 := rough_le_one n p2
      have h2 : (0 : ℝ) ≤ (((p2 * n : ℕ) : ℝ))⁻¹ := by positivity
      simpa using mul_le_mul_of_nonneg_right h1 h2
  calc ∑ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
        rough n p2 * (50 * (q : ℝ) * K * (2 * shortY ε x / ((p2 * n : ℕ) : ℝ))
          / (0.1249 * Real.log (scaleZ ε x)) ^ D)
      = (50 * (q : ℝ) * K * (2 * shortY ε x)) / (0.1249 * Real.log (scaleZ ε x)) ^ D
          * ∑ p2 ∈ Finset.Icc 1 ⌊t⌋₊, ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
              rough n p2 * (((p2 * n : ℕ) : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p2 _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hfac p2 n]
        ring
    _ ≤ (50 * (q : ℝ) * K * (2 * shortY ε x)) / (0.1249 * Real.log (scaleZ ε x)) ^ D
          * (1 + Real.log ⌊t⌋₊) ^ 2 := by
        refine mul_le_mul_of_nonneg_left hsum2 ?_
        have h1 : (0 : ℝ) ≤ 50 * (q : ℝ) * K * (2 * shortY ε x) := by positivity
        exact div_nonneg h1 hcpos.le


/-- The final numeric comparison: at `D = 2A+6` the pair-sum bound is at most
`900 K (0.1249·11/20)^{-D}` times `Y log^{-A} x`. -/
private theorem final_estimate {ε K A : ℝ} (hε : 0 ≤ ε) (hA : 0 < A) (hK : 0 < K)
    {x t : ℝ} {q : ℕ} (hx1 : 1 ≤ x) (hlogone : 1 ≤ Real.log x)
    (hxle : 2 * shortY ε x ≤ x) (ht : t ≤ 2 * shortY ε x)
    (hqA : (q : ℝ) ≤ Real.log x ^ A) :
    50 * (q : ℝ) * K * (2 * shortY ε x) / (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6)
        * (1 + Real.log ⌊t⌋₊) ^ 2
      ≤ 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * x ^ (11 / 20 + ε)
          * Real.log x ^ (-A) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hYpos : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
  have hZpos : (0 : ℝ) < scaleZ ε x := by unfold scaleZ; linarith
  have hlx : (0 : ℝ) < Real.log x := by linarith
  have hLZ : (0 : ℝ) < Real.log (scaleZ ε x) := by
    apply Real.log_pos
    unfold scaleZ shortY
    have h1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
    linarith
  have hDpos : (0 : ℝ) < 2 * A + 6 := by linarith
  have hapos : (0 : ℝ) < 0.1249 * (11 / 20 : ℝ) := by norm_num
  have hcDpos : (0 : ℝ) < (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlogt0 : (0 : ℝ) ≤ Real.log ⌊t⌋₊ := by
    rcases Nat.eq_zero_or_pos ⌊t⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogt1 : Real.log ⌊t⌋₊ ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos ⌊t⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · have ht1 : (1 : ℝ) ≤ t := (Nat.floor_pos).mp hpos
      refine Real.log_le_log (by exact_mod_cast hpos) ?_
      calc ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
        _ ≤ 2 * shortY ε x := ht
        _ ≤ x := hxle
  have hnum : (1 + Real.log ⌊t⌋₊) ^ 2 ≤ 4 * Real.log x ^ 2 := by
    have h2 : (0 : ℝ) ≤ 1 + Real.log ⌊t⌋₊ := by linarith
    have h4 : (1 + Real.log ⌊t⌋₊) ^ 2 ≤ (1 + Real.log x) ^ 2 := by
      have hh := mul_self_le_mul_self h2 (by linarith : 1 + Real.log ⌊t⌋₊ ≤ 1 + Real.log x)
      simpa [pow_two] using hh
    have h5 : (1 + Real.log x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith [hlogone, hlx]
    linarith
  have hLZge : (11 / 20 : ℝ) * Real.log x ≤ Real.log (scaleZ ε x) := by
    have h1 : Real.log (shortY ε x) ≤ Real.log (scaleZ ε x) := by
      refine Real.log_le_log hYpos ?_
      unfold scaleZ
      linarith
    have h2 : Real.log (shortY ε x) = (11 / 20 + ε) * Real.log x := by
      unfold shortY
      rw [Real.log_rpow hx0]
    rw [h2] at h1
    nlinarith [h1, hlx]
  have hden : (0.1249 * ((11 / 20 : ℝ) * Real.log x)) ^ (2 * A + 6)
      ≤ (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) := by
    refine Real.rpow_le_rpow (by positivity) ?_ hDpos.le
    nlinarith [hLZge]
  have hsplit : (0.1249 * ((11 / 20 : ℝ) * Real.log x)) ^ (2 * A + 6)
      = (0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by norm_num) hlx.le, ← mul_assoc,
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 0.1249)
        (by norm_num : (0 : ℝ) ≤ (11 / 20 : ℝ))]
  have hcd : (0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6)
      ≤ (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) := hsplit ▸ hden
  have hcancel : (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * Real.log x ^ (-A)
      * ((0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6))
      = Real.log x ^ (2 * A + 6 - A) := by
    have h1 : (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * (0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6)
        = 1 := by
      rw [← Real.rpow_add hapos]
      norm_num
    have h2 : Real.log x ^ (-A) * Real.log x ^ (2 * A + 6) = Real.log x ^ (2 * A + 6 - A) := by
      rw [← Real.rpow_add hlx]
      congr 1
      ring
    calc (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * Real.log x ^ (-A)
          * ((0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6))
        = ((0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * (0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6))
            * (Real.log x ^ (-A) * Real.log x ^ (2 * A + 6)) := by ring
      _ = Real.log x ^ (2 * A + 6 - A) := by rw [h1, h2, one_mul]
  have hnum2 : 50 * (q : ℝ) * K * (2 * shortY ε x) * (1 + Real.log ⌊t⌋₊) ^ 2
      ≤ 900 * K * (shortY ε x) * Real.log x ^ (2 * A + 6 - A) := by
    have hq1 : (q : ℝ) * (1 + Real.log ⌊t⌋₊) ^ 2 ≤ Real.log x ^ A * (4 * Real.log x ^ 2) :=
      mul_le_mul hqA hnum (by positivity) (Real.rpow_pos_of_pos hlx A).le
    have hq2 : Real.log x ^ A * (4 * Real.log x ^ 2) ≤ 4 * Real.log x ^ (2 * A + 6 - A) := by
      have h3 : Real.log x ^ A * (Real.log x) ^ 2 = Real.log x ^ (A + 2) := by
        have e : (Real.log x) ^ 2 = Real.log x ^ (2 : ℝ) :=
          (Real.rpow_natCast (Real.log x) 2).symm
        rw [e, ← Real.rpow_add hlx]
      have h4 : Real.log x ^ (A + 2) ≤ Real.log x ^ (2 * A + 6 - A) :=
        Real.rpow_le_rpow_of_exponent_le hlogone (by linarith)
      calc Real.log x ^ A * (4 * Real.log x ^ 2) = 4 * (Real.log x ^ A * Real.log x ^ 2) := by ring
        _ = 4 * Real.log x ^ (A + 2) := by rw [h3]
        _ ≤ 4 * Real.log x ^ (2 * A + 6 - A) := by linarith
    have h5 : (q : ℝ) * (1 + Real.log ⌊t⌋₊) ^ 2 ≤ 4 * Real.log x ^ (2 * A + 6 - A) :=
      le_trans hq1 hq2
    have h6 : (0 : ℝ) ≤ Real.log x ^ (2 * A + 6 - A) := (Real.rpow_pos_of_pos hlx _).le
    calc 50 * (q : ℝ) * K * (2 * shortY ε x) * (1 + Real.log ⌊t⌋₊) ^ 2
        = 100 * K * (shortY ε x) * ((q : ℝ) * (1 + Real.log ⌊t⌋₊) ^ 2) := by ring
      _ ≤ 100 * K * (shortY ε x) * (4 * Real.log x ^ (2 * A + 6 - A)) := by
          refine mul_le_mul_of_nonneg_left h5 ?_
          positivity
      _ = 400 * K * (shortY ε x) * Real.log x ^ (2 * A + 6 - A) := by ring
      _ ≤ 900 * K * (shortY ε x) * Real.log x ^ (2 * A + 6 - A) := by
          have h7 : (0 : ℝ) ≤ (shortY ε x) * Real.log x ^ (2 * A + 6 - A) := by positivity
          nlinarith [h7, hK.le]
  have hRHS : 900 * K * (shortY ε x) * Real.log x ^ (2 * A + 6 - A)
      ≤ 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * x ^ (11 / 20 + ε)
          * Real.log x ^ (-A) * (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) := by
    have hxeq : x ^ (11 / 20 + ε) = shortY ε x := rfl
    rw [hxeq]
    have hstep : 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * (shortY ε x)
        * Real.log x ^ (-A)
        * ((0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6))
        = 900 * K * (shortY ε x) * Real.log x ^ (2 * A + 6 - A) := by
      rw [show 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * (shortY ε x)
          * Real.log x ^ (-A)
          * ((0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6))
          = 900 * K * (shortY ε x)
            * ((0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * Real.log x ^ (-A)
              * ((0.1249 * (11 / 20 : ℝ)) ^ (2 * A + 6) * Real.log x ^ (2 * A + 6))) by ring,
        hcancel]
    refine le_trans (le_of_eq hstep.symm) ?_
    refine mul_le_mul_of_nonneg_left hcd ?_
    positivity
  have hLHS : 50 * (q : ℝ) * K * (2 * shortY ε x)
        / (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) * (1 + Real.log ⌊t⌋₊) ^ 2
      = 50 * (q : ℝ) * K * (2 * shortY ε x) * (1 + Real.log ⌊t⌋₊) ^ 2
          / (0.1249 * Real.log (scaleZ ε x)) ^ (2 * A + 6) := by ring
  rw [hLHS, div_le_iff₀ hcDpos]
  exact le_trans hnum2 hRHS

/-- LEAF 2 of 3. Step: the long-cofactor sub-sum. The ordered pairs whose coarse factor
`p1 * p2` leaves a rough cofactor of at least `p2` obey the logarithmic saving with a
polylogarithmic modulus. Strictly easier than the whole family: it keeps only the pairs with
`p2 ≤ m / (p1 * p2)`. Open. -/
theorem leaf_two_rough_long_cofactor {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨B, hBpos, K, hKpos, hKb⟩ := prime_char_interval_bound (2 * A + 6) (by linarith)
  have hD : (0 : ℝ) < 2 * A + 6 := by linarith
  set T1 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 0.0686) with hT1
  set T2 : ℝ := ((A + B + 1) / 0.015) ^ ((A + B + 1) / 0.015) with hT2
  set T3 : ℝ := Real.exp (Real.exp 1) with hT3
  set T4 : ℝ := 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) with hT4
  set T5 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (9 / 20 - ε)) with hT5
  have hT1nn : (0 : ℝ) < T1 := by rw [hT1]; positivity
  have hT2nn : (0 : ℝ) < T2 := by rw [hT2]; positivity
  have hT3nn : (0 : ℝ) < T3 := by rw [hT3]; positivity
  have hT4nn : (0 : ℝ) < T4 := by rw [hT4]; positivity
  have hT5nn : (0 : ℝ) < T5 := by rw [hT5]; positivity
  refine ⟨T1 + T2 + T3 + T4 + T5 + 1, ?_⟩
  intro x hx q hq hqA χ hχ t ht
  haveI : NeZero q := ⟨by omega⟩
  have hT1x : T1 ≤ x := by linarith
  have hT2x : T2 ≤ x := by linarith
  have hT3x : T3 ≤ x := by linarith
  have hT4x : T4 ≤ x := by linarith
  have hT5x : T5 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hthr : (2 : ℝ) ^ ((1 : ℝ) / 0.0686) ≤ x := hT1x
  have hthrm : ((A + B + 1) / 0.015) ^ ((A + B + 1) / 0.015) ≤ x := hT2x
  have hM1 : (1 : ℝ) ≤ A + B + 1 := by linarith
  have hlogbig : Real.log x ^ (A + B + 1) ≤ x ^ (0.03 : ℝ) :=
    log_pow_le_rpow_small hM1 x hthrm
  have hlogone : 1 ≤ Real.log x := by
    have h1 : Real.log (Real.exp (Real.exp 1)) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hT3x
    rw [Real.log_exp] at h1
    have h2 : (1 : ℝ) ≤ Real.exp 1 := by
      have h3 : Real.exp 0 ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      simpa using h3
    linarith
  have hxle : 2 * shortY ε x ≤ x := by
    have hd : (0 : ℝ) < 9 / 20 - ε := by linarith
    have h1 : (2 : ℝ) ≤ x ^ (9 / 20 - ε) := by
      have h2 : ((2 : ℝ) ^ ((1 : ℝ) / (9 / 20 - ε))) ^ (9 / 20 - ε) ≤ x ^ (9 / 20 - ε) :=
        Real.rpow_le_rpow (by positivity) hT5x hd.le
      have h3 : ((2 : ℝ) ^ ((1 : ℝ) / (9 / 20 - ε))) ^ (9 / 20 - ε) = 2 := by
        have hs : (9 / 20 - ε) ≠ 0 := ne_of_gt hd
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          show (1 : ℝ) / (9 / 20 - ε) * (9 / 20 - ε) = 1 by
            rw [one_div]
            exact inv_mul_cancel₀ hs,
          Real.rpow_one]
      linarith [h3 ▸ h2]
    have h4 : x ^ (9 / 20 - ε) * x ^ (11 / 20 + ε) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h5 : (0 : ℝ) < shortY ε x := Real.rpow_pos_of_pos hx0 _
    have h6 : 2 * shortY ε x ≤ x ^ (9 / 20 - ε) * shortY ε x := by
      have h7 := mul_le_mul_of_nonneg_right h1 h5.le
      linarith
    have h8 : x ^ (9 / 20 - ε) * shortY ε x = x := by
      rw [show shortY ε x = x ^ (11 / 20 + ε) from rfl]
      exact h4
    linarith [h6, h8 ▸ h6]
  refine le_trans (window_pair_sum hε hε8 hBpos hKpos hD hKb χ hχ hq hqA hx1 hthr hxle
    hlogone hlogbig) ?_
  refine le_trans (final_estimate hε.le hA hKpos hx1 hlogone hxle ht hqA) ?_
  have hC : 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6))
      ≤ T1 + T2 + T3 + T4 + T5 + 1 := by
    rw [← hT4]
    linarith
  have hpos : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have h1 : (0 : ℝ) < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
    have h2 : (0 : ℝ) ≤ Real.log x ^ (-A) := (Real.rpow_pos_of_pos (by linarith) _).le
    positivity
  have hshape : 900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)) * x ^ (11 / 20 + ε)
        * Real.log x ^ (-A)
      = (900 * K * (0.1249 * (11 / 20 : ℝ)) ^ (-(2 * A + 6)))
          * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
  have hgoal : (T1 + T2 + T3 + T4 + T5 + 1) * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
      = (T1 + T2 + T3 + T4 + T5 + 1)
          * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
  rw [hshape, hgoal]
  exact mul_le_mul_of_nonneg_right hC hpos


/-! ### The short-cofactor piece

The cut `n < p2` with `ψ(n, p2) = 1` forces the rough cofactor `n = m / (p1 * p2)` to be one:
any `n ≥ 2` has a prime divisor at most `n`. So the short piece is supported on `m = p1 * p2`,
and there `expo p1 + expo p2 = log m / log Z ≥ 1 - log 4 / log Z`, while `E2` forces
`expo p2 ≥ 0.1249` and `expo p1 + 2 * expo p2 ≤ 1`. Once `Z ≥ 4 ^ 10` the two are
incompatible, so the whole piece vanishes and the leaf is bounded by the empty sum. -/

/-- A positive rough cofactor strictly below `p2` is one. -/
private theorem rough_eq_one_of_lt {n p : ℕ} (hn : 1 ≤ n) (h : rough n p = 1)
    (hlt : n < p) : n = 1 := by
  by_contra hne
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hc : ∀ r : ℕ, r.Prime → r ∣ n → p ≤ r := by
    unfold rough at h
    split_ifs at h with hh
    · exact hh
    · exact absurd h (by norm_num)
  have h1 : p ≤ r := hc r hrp hrd
  have h2 : r ≤ n := Nat.le_of_dvd (by omega) hrd
  omega

/-- `rough` takes only the values zero and one. -/
private theorem rough_eq_zero_or_one (n p : ℕ) : rough n p = 0 ∨ rough n p = 1 := by
  unfold rough
  split_ifs <;> simp

/-- At scale `x ≥ 10 ^ 12` the short-cofactor conditions are contradictory. -/
private theorem short_pair_vanishes {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    {x : ℝ} (hx : (10 ^ 12 : ℝ) ≤ x) {m p1 p2 : ℕ}
    (hmJ : m ∈ rightInterval ε x) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hdvd : p1 * p2 ∣ m)
    (hdisc : lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
    (hshort : ¬ (p2 ≤ m / (p1 * p2))) :
    rough (m / (p1 * p2)) p2 = 0 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hθ : (1 / 2 : ℝ) ≤ 11 / 20 + ε := by linarith
  have hZge : (4 ^ 10 : ℝ) ≤ scaleZ ε x := by
    have hsqrt : (10 ^ 6 : ℝ) ≤ Real.sqrt x := by
      have h := Real.sqrt_le_sqrt (show ((10 ^ 6 : ℝ) ^ 2) ≤ x by norm_num; linarith)
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hxq : Real.sqrt x ≤ x ^ (11 / 20 + ε) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 hθ
    unfold scaleZ shortY
    nlinarith
  have hZpos : (0 : ℝ) < scaleZ ε x := by linarith
  have hLZ : (0 : ℝ) < Real.log (scaleZ ε x) := Real.log_pos (by linarith)
  have hLZ10 : 10 * Real.log 4 ≤ Real.log (scaleZ ε x) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4 ^ 10) hZge
    rwa [Real.log_pow] at h
  have hmpos : 0 < m := by
    have h := (Finset.mem_Ioc.mp hmJ).1
    omega
  have hmY : x ^ (11 / 20 + ε) ≤ (m : ℝ) := by
    have h1 : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hmJ).1
    have h2 : (x ^ (11 / 20 + ε)) < ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    linarith
  have hm_eq : m = (m / (p1 * p2)) * (p1 * p2) := (Nat.div_mul_cancel hdvd).symm
  have hn1 : 1 ≤ m / (p1 * p2) := by
    rcases Nat.eq_zero_or_pos (m / (p1 * p2)) with h | h
    · rw [h] at hm_eq
      simp at hm_eq
      omega
    · exact h
  rcases rough_eq_zero_or_one (m / (p1 * p2)) p2 with h0 | h1
  · exact h0
  exfalso
  have hn_eq : m / (p1 * p2) = 1 := rough_eq_one_of_lt hn1 h1 (by omega)
  have hm_prod : m = p1 * p2 := by
    rw [hn_eq] at hm_eq
    simpa using hm_eq
  have hb_low : (0.1249 : ℝ) ≤ expo ε x p2 := by
    have h1 : (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε ≤ expo ε x p2 := hdisc.1
    have h2 : (0.1249 : ℝ) ≤
        (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - (1 / 10 ^ 8 : ℝ) := by norm_num
    linarith [hε8]
  have hab : expo ε x p1 + expo ε x p2 = Real.log (m : ℝ) / Real.log (scaleZ ε x) := by
    have h1 : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1.pos
    have h2 : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2.pos
    unfold expo
    rw [hm_prod, Nat.cast_mul, Real.log_mul h1.ne' h2.ne', add_div]
  have hlogm : Real.log (scaleZ ε x) - Real.log 4 ≤ Real.log (m : ℝ) := by
    have hYpos : (0 : ℝ) < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
    have hlog := Real.log_le_log hYpos hmY
    have hZY : scaleZ ε x / 4 = x ^ (11 / 20 + ε) := by
      unfold scaleZ shortY
      ring
    have hsp : Real.log (x ^ (11 / 20 + ε)) = Real.log (scaleZ ε x) - Real.log 4 := by
      rw [← hZY, Real.log_div hZpos.ne' (by norm_num)]
    linarith
  have hratio : Real.log 4 / Real.log (scaleZ ε x) ≤ 1 / 10 := by
    rw [div_le_iff₀ hLZ]
    linarith
  have hsum : 1 - 1 / 10 ≤ expo ε x p1 + expo ε x p2 := by
    have hsplit : (Real.log (scaleZ ε x) - Real.log 4) / Real.log (scaleZ ε x) =
        1 - Real.log 4 / Real.log (scaleZ ε x) := by
      field_simp
    have hmono := div_le_div_of_nonneg_right hlogm hLZ.le
    rw [hab]
    linarith
  have hupper : expo ε x p1 + 2 * expo ε x p2 ≤ 1 := hdisc.2.2.2.1
  linarith

/-- LEAF 3 of 3. Step: the short-cofactor sub-sum. The ordered pairs whose rough cofactor is
smaller than `p2` obey the same logarithmic saving; there `n < p2 < p1`, so `n ^ 3 < m` and
the rough variable is short. Strictly easier than the whole family: it keeps only the pairs
with `¬ (p2 ≤ m / (p1 * p2))`. Open. -/
theorem leaf_two_rough_short_cofactor {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  refine ⟨10 ^ 12, ?_⟩
  intro x hx q hq hqA χ hχ t ht
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hzero : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) = 0 := by
    intro m hm
    have hmJ := (Finset.mem_filter.mp hm).1
    have hcoef : (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p1 _ => Finset.sum_eq_zero (fun p2 _ => ?_))
      split_ifs with h
      · exact short_pair_vanishes hε hε8 hx hmJ h.1.1 h.1.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2
      · rfl
    rw [hcoef]
    simp
  rw [Finset.sum_eq_zero hzero, norm_zero]
  have hY0 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
  have hL0 : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have : (0 : ℝ) ≤ (10 ^ 12 : ℝ) := by norm_num
  nlinarith [hY0, hL0, this]

/-- The sealed statement, proved from the three leaves: split the coefficient pointwise,
distribute the finite sum, apply the triangle inequality, and compare the two leaf constants
with `max (2 * max C1 C2) 1`, which is at least one so that `x ≥ 1` and the logarithmic
factor is nonnegative. -/
theorem leaf_two_rough_siegel_walfisz_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := leaf_two_rough_long_cofactor hε hε8 A hA
  obtain ⟨C2, h2⟩ := leaf_two_rough_short_cofactor hε hε8 A hA
  refine ⟨max (2 * max C1 C2) 1, ?_⟩
  intro x hx q hq hqA χ hχ t ht
  have hx1 : 1 ≤ x := le_trans (le_max_right (2 * max C1 C2) (1 : ℝ)) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hC1 : C1 ≤ max (2 * max C1 C2) 1 := by
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
      have h2' : max C1 C2 ≤ 2 * max C1 C2 := by linarith
      have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
      have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  have hC2 : C2 ≤ max (2 * max C1 C2) 1 := by
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h1' : C2 ≤ max C1 C2 := le_max_right C1 C2
      have h2' : max C1 C2 ≤ 2 * max C1 C2 := by linarith
      have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h1' : C2 ≤ max C1 C2 := le_max_right C1 C2
      have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  have hCs : C1 + C2 ≤ max (2 * max C1 C2) 1 := by
    have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
    have h2' : C2 ≤ max C1 C2 := le_max_right C1 C2
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  set Y := x ^ (11 / 20 + ε) with hYs
  set L := Real.log x ^ (-A) with hLs
  have hY0 : 0 ≤ Y := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg hx1) _
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) with hSs
  have hpt : ∀ m : ℕ, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
      (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) + (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) := by
    intro m
    rw [leaf_two_terms_pair_split ε x m, ofReal_add]
    ring
  have hsplit : (∑ m ∈ S, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)) =
      (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
        (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) := by
    calc (∑ m ∈ S, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q))
        = ∑ m ∈ S, ((((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) + (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) :=
          Finset.sum_congr rfl (fun m _ => hpt m)
      _ = (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
            (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) := Finset.sum_add_distrib
  rw [hsplit]
  have hb1 := h1 x (le_trans hC1 hx) q hq hqA χ hχ t ht
  have hb2 := h2 x (le_trans hC2 hx) q hq hqA χ hχ t ht
  have htri : ‖(∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
      (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q))‖ ≤
      ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ +
        ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ := norm_add_le _ _
  have hsum : ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ +
      ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤ C1 * Y * L + C2 * Y * L :=
    add_le_add hb1 hb2
  have hcancel : C1 * Y * L + C2 * Y * L = ((C1 + C2) * Y) * L := by ring
  have hstep : ((C1 + C2) * Y) * L ≤ ((max (2 * max C1 C2) 1) * Y) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hY0) hL0
  linarith

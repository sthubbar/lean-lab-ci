/-
Brun's pure sieve for the indexed Goldbach polynomial m * (n - m).
Source: Brun 1919, page 103, displays 5 and 6.
This is a lab derivation with the local density adapted at primes dividing n.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.S1.Remainder
import LeanLab.PNTSieve.BrunPure

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach.PureSieve

open LeanLab.SchnirelmannGoldbach.S1

/-- The indexed survivor count retains both ordered Goldbach representations. -/
def survivors (n : ℕ) (P : Finset ℕ) : ℕ :=
  #{m ∈ range n | ∀ p ∈ P, ¬ p ∣ m * (n - m)}

/-- The number of indices at which d divides the Goldbach polynomial. -/
def multiples (n d : ℕ) : ℕ := #{m ∈ range n | d ∣ m * (n - m)}

/-- CRT gives the exact product of local densities, with bounded endpoint error. -/
theorem multiples_error (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    |(multiples n (∏ p ∈ P, p) : ℝ) -
      n * ∏ p ∈ P, (wt n p / p)| ≤ ∏ p ∈ P, wt n p := by
  let d := ∏ p ∈ P, p
  have hd : 0 < d := Finset.prod_pos fun p hp => (hP p hp).pos
  have hc := count_periodic_approx (rootPred n d) hd (rootPred_periodic n d) n
  have heq : multiples n d = #{m ∈ range n | rootPred n d m} := by
    unfold multiples
    congr 1
    apply filter_congr
    intro m hm
    exact dvd_iff_rootPred (by have := mem_range.mp hm; omega)
  rw [← heq, show (#{m ∈ range d | rootPred n d m} : ℝ) = ∏ p ∈ P, wt n p from
    cnt_prod_primes n P hP] at hc
  have hmain : (n : ℝ) * ∏ p ∈ P, (wt n p / p) =
      (∏ p ∈ P, wt n p) * n / d := by
    rw [prod_div_distrib, show (d : ℝ) = ∏ p ∈ P, (p : ℝ) by simp [d]]
    ring
  rw [hmain]
  exact hc

/-- A Goldbach pair outside the sifting primes survives the polynomial sieve. -/
theorem r_le_survivors_add (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    r n ≤ survivors n P + 2 * P.card := by
  have hsub : {m ∈ range n | m.Prime ∧ (n - m).Prime} ⊆
      {m ∈ range n | ∀ p ∈ P, ¬ p ∣ m * (n - m)} ∪
        (P ∪ P.image (fun p => n - p)) := by
    intro m hm
    obtain ⟨hmn, hm, hq⟩ := mem_filter.mp hm
    by_cases hmP : m ∈ P
    · exact mem_union_right _ (mem_union_left _ hmP)
    by_cases hqP : n - m ∈ P
    · exact mem_union_right _ (mem_union_right _ (mem_image.mpr
        ⟨n - m, hqP, by have := mem_range.mp hmn; omega⟩))
    apply mem_union_left
    refine mem_filter.mpr ⟨hmn, ?_⟩
    intro p hp hd
    rcases (hP p hp).dvd_mul.mp hd with hd | hd
    · have he := (Nat.dvd_prime_two_le hm (hP p hp).two_le).mp hd
      exact hmP (he ▸ hp)
    · have he := (Nat.dvd_prime_two_le hq (hP p hp).two_le).mp hd
      exact hqP (he ▸ hp)
  have h1 := card_le_card hsub
  have h2 := card_union_le {m ∈ range n | ∀ p ∈ P, ¬ p ∣ m * (n - m)}
    (P ∪ P.image (fun p => n - p))
  have h3 := card_union_le P (P.image (fun p => n - p))
  have h4 := card_image_le (s := P) (f := fun p => n - p)
  unfold r survivors
  omega

example : survivors 10 {2, 3} = 1 := by decide
example : multiples 10 3 = 7 := by decide
example : r 10 = 3 := by decide

/-- The finite Brun sum counts indices, not distinct polynomial values. -/
def brunCount (n : ℕ) (P : Finset ℕ) (k : ℕ) : ℤ :=
  ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
    (-1 : ℤ) ^ T.card * multiples n (∏ p ∈ T, p)

/-- Exchanging the finite sums gives the pointwise Bonferroni truncation. -/
theorem brunCount_eq (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    brunCount n P k = ∑ m ∈ range n,
      LeanLab.PNTSieve.Bonferroni.trunc (P.filter (fun p => p ∣ m * (n - m))) k := by
  unfold brunCount multiples
  have hterm : ∀ T ∈ P.powerset.filter (fun T => T.card ≤ k),
      (-1 : ℤ) ^ T.card * (#{m ∈ range n | (∏ p ∈ T, p) ∣ m * (n - m)} : ℤ) =
        ∑ m ∈ range n, if (∏ p ∈ T, p) ∣ m * (n - m) then (-1 : ℤ) ^ T.card else 0 := by
    intro T _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_congr rfl hterm, sum_comm]
  exact sum_congr rfl (fun m _ => LeanLab.PNTSieve.Bonferroni.pointwise P hP k _)

/-- Even truncations are upper bounds and odd truncations are lower bounds. -/
theorem brun_bounds (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (Even k → (survivors n P : ℤ) ≤ brunCount n P k) ∧
    (Odd k → brunCount n P k ≤ (survivors n P : ℤ)) := by
  have hs : (survivors n P : ℤ) = ∑ m ∈ range n,
      if P.filter (fun p => p ∣ m * (n - m)) = ∅ then (1 : ℤ) else 0 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    unfold survivors
    congr 2
    apply filter_congr
    intro m _
    rw [filter_eq_empty_iff]
  rw [hs, brunCount_eq n P hP k]
  constructor
  · intro hk
    exact sum_le_sum fun m _ => LeanLab.PNTSieve.Bonferroni.bonferroni_even _ hk
  · intro hk
    exact sum_le_sum fun m _ => LeanLab.PNTSieve.Bonferroni.bonferroni_odd _ hk

example : brunCount 10 {2, 3} 0 = 10 := by decide
example : brunCount 10 {2, 3} 1 = -2 := by decide
example : brunCount 10 {2, 3} 2 = 1 := by decide

/-- The complete truncation remainder has the explicit Brun weight 2 to the subset size. -/
theorem brunCount_error (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    |(brunCount n P k : ℝ) - n *
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, (wt n p / p)| ≤
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k), (2 : ℝ) ^ T.card := by
  have heq : (brunCount n P k : ℝ) - n *
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, (wt n p / p) =
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ((multiples n (∏ p ∈ T, p) : ℝ) -
          n * ∏ p ∈ T, (wt n p / p)) := by
    unfold brunCount
    push_cast
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro T _
    ring
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro T hT
  have hTP : T ⊆ P := (mem_powerset.mp (mem_filter.mp hT).1)
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc |(multiples n (∏ p ∈ T, p) : ℝ) - n * ∏ p ∈ T, (wt n p / p)|
      ≤ ∏ p ∈ T, wt n p := multiples_error n T (fun p hp => hP p (hTP hp))
    _ ≤ ∏ p ∈ T, (2 : ℝ) :=
      prod_le_prod₀ (fun p _ => (wt_pos n p).le) (fun p _ => wt_le_two n p)
    _ = (2 : ℝ) ^ T.card := by simp

/-- Brun's explicit remainder is the truncated binomial expansion of 3 to the prime count. -/
theorem remainder_eq_binomial (P : Finset ℕ) (k : ℕ) :
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k), (2 : ℝ) ^ T.card =
      ∑ j ∈ range (k + 1), (P.card.choose j : ℝ) * 2 ^ j := by
  rw [sum_filter, sum_powerset_apply_card (fun j => if j ≤ k then (2 : ℝ) ^ j else 0)]
  simp only [nsmul_eq_mul]
  rcases le_total k P.card with hk | hk
  · rw [← sum_subset (range_subset_range.mpr (Nat.succ_le_succ hk))]
    · apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega)]
    · intro j _ hj
      rw [if_neg (by have := mem_range.not.mp hj; omega), mul_zero]
  · symm
    rw [← sum_subset (range_subset_range.mpr (Nat.succ_le_succ hk))]
    · apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega)]
    · intro j _ hj
      rw [Nat.choose_eq_zero_of_lt (by have := mem_range.not.mp hj; omega)]
      simp

/-- Brun display 5 for ordered Goldbach representations, including all endpoint pairs. -/
theorem r_le_brun_main (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : Even k) :
    (r n : ℝ) ≤ n *
      ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, (wt n p / p) +
      ∑ j ∈ range (k + 1), (P.card.choose j : ℝ) * 2 ^ j + 2 * P.card := by
  have hb : (survivors n P : ℝ) ≤ (brunCount n P k : ℝ) := by
    exact_mod_cast (brun_bounds n P hP k).1 hk
  have he := (abs_le.mp (brunCount_error n P hP k)).2
  rw [remainder_eq_binomial] at he
  have hr : (r n : ℝ) ≤ (survivors n P : ℝ) + 2 * P.card := by
    exact_mod_cast r_le_survivors_add n P hP
  linarith

end LeanLab.SchnirelmannGoldbach.PureSieve

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.multiples_error

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.r_le_survivors_add

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.brunCount_eq

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.brun_bounds

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.brunCount_error

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.remainder_eq_binomial

#print axioms LeanLab.SchnirelmannGoldbach.PureSieve.r_le_brun_main

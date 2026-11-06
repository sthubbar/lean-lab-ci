import LeanLab.AlmostPrimes.Decomp416a

/-!
AI wrote the Lean code. Goldbach is open.
Campbell 2026 v1, https://arxiv.org/abs/2608.09488v1,
printed page 10, Lemma 4.3, equation 4.4.
The finite divisor sums are represented by subsets of the sifting primes.
The Rankin argument also appears in the existing DDLemma23Full.rankin_sum_lt
and CampbellLemma43.rankin14 proofs. This file keeps its parameters free.
-/

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp416b
open CampbellCase2 CampbellLemma43 Decomp416a

/-- LEAF. Campbell page 10, equation 4.4, its first inequality.
The remainder sum is bounded by nineteen sixths times the divisor sum with weight eight. -/
theorem R4A_le_divisor_sum (N : ℕ) (hN : 2 ≤ N) (z D : ℝ) :
    R4A N z D ≤ (19 / 6 : ℝ) *
      ∑ s ∈ (primesBelow z).powerset.filter
        (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), (8 : ℝ) ^ s.card := by
  unfold R4A
  rw [mul_sum]
  apply sum_le_sum
  intro s hs
  have hsub : s ⊆ primesBelow z := mem_powerset.mp (mem_filter.mp hs).1
  have hp : ∀ p ∈ s, p.Prime := fun p hp => (mem_primesBelow.mp (hsub hp)).1
  have h3 : 3 ∉ s := by
    intro h
    exact (mem_primesBelow.mp (hsub h)).2.1 rfl
  have hb := mul_le_mul_of_nonneg_left (rA_bound_sharp N hN hp h3)
    (by positivity : (0 : ℝ) ≤ 4 ^ s.card)
  calc (4 : ℝ) ^ s.card * |rA N s| ≤ 4 ^ s.card * ((19 / 6 : ℝ) * 2 ^ s.card) := hb
    _ = (19 / 6 : ℝ) * 8 ^ s.card := by rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]; ring

/-- LEAF. Campbell page 10, equation 4.4, Rankin's trick and the finite Euler product.
The exponent may be any nonnegative real number. -/
theorem rankin_divisor_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D δ : ℝ) (hD : 0 < D) (hδ : 0 ≤ δ) :
    ∑ s ∈ P.powerset.filter
        (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), (8 : ℝ) ^ s.card ≤
      D ^ δ * ∏ p ∈ P, (1 + 8 / (p : ℝ) ^ δ) := by
  let w : ℕ → ℝ := fun p => 8 * (p : ℝ) ^ (-δ)
  have hp0 : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).pos
  have ht (s : Finset ℕ) (hs : s ⊆ P) (hd : (∏ p ∈ s, (p : ℝ)) < D) :
      (8 : ℝ) ^ s.card ≤ D ^ δ * ∏ p ∈ s, w p := by
    have hpos : 0 < ∏ p ∈ s, (p : ℝ) := prod_pos fun p hp => hp0 p (hs hp)
    have he : D ^ δ * ∏ p ∈ s, w p =
        (8 : ℝ) ^ s.card * (D / ∏ p ∈ s, (p : ℝ)) ^ δ := by
      dsimp only [w]
      rw [prod_mul_distrib, prod_const, Real.div_rpow hD.le hpos.le,
        Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs hp)).le)]
      rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity),
        ← Real.finsetProd_rpow s _ (fun p hp => (hp0 p (hs hp)).le)]
      ring
    rw [he]
    have ho : 1 ≤ (D / ∏ p ∈ s, (p : ℝ)) ^ δ :=
      Real.one_le_rpow ((le_div_iff₀ hpos).mpr (by simpa using hd.le)) hδ
    simpa using mul_le_mul_of_nonneg_left ho (by positivity : (0 : ℝ) ≤ 8 ^ s.card)
  calc _ ≤ ∑ s ∈ P.powerset.filter
          (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), D ^ δ * ∏ p ∈ s, w p := by
        apply sum_le_sum
        intro s hs
        exact ht s (mem_powerset.mp (mem_filter.mp hs).1) (mem_filter.mp hs).2
    _ ≤ ∑ s ∈ P.powerset, D ^ δ * ∏ p ∈ s, w p := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro s hs _
        have hsub := mem_powerset.mp hs
        apply mul_nonneg (by positivity)
        exact prod_nonneg fun p hp => by dsimp [w]; positivity
    _ = D ^ δ * ∏ p ∈ P, (1 + 8 / (p : ℝ) ^ δ) := by
        rw [← mul_sum, ← prod_one_add]
        congr 1
        apply prod_congr rfl
        intro p hp
        dsimp [w]
        rw [Real.rpow_neg (hp0 p hp).le, div_eq_mul_inv]

/-- Campbell page 10, equation 4.4, for the concrete pre-sieved sequence.
No cited sieve theorem or explicit prime estimate is an input. -/
theorem R4A_rankin (N : ℕ) (hN : 2 ≤ N) (z D δ : ℝ)
    (hD : 0 < D) (hδ : 0 ≤ δ) :
    R4A N z D ≤ (19 / 6 : ℝ) * D ^ δ *
      ∏ p ∈ primesBelow z, (1 + 8 / (p : ℝ) ^ δ) := by
  have hP : ∀ p ∈ primesBelow z, p.Prime := fun p hp => (mem_primesBelow.mp hp).1
  calc R4A N z D ≤ (19 / 6 : ℝ) *
      ∑ s ∈ (primesBelow z).powerset.filter
        (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D), (8 : ℝ) ^ s.card :=
      R4A_le_divisor_sum N hN z D
    _ ≤ (19 / 6 : ℝ) * (D ^ δ * ∏ p ∈ primesBelow z, (1 + 8 / (p : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left (rankin_divisor_sum _ hP D δ hD hδ) (by norm_num)
    _ = _ := by ring

example : R4A 3 5 2 ≤ (19 / 6 : ℝ) * 2 ^ (1 / 2 : ℝ) *
    ∏ p ∈ primesBelow 5, (1 + 8 / (p : ℝ) ^ (1 / 2 : ℝ)) :=
  R4A_rankin 3 (by decide) 5 2 (1 / 2) (by norm_num) (by norm_num)

end LeanLab.AlmostPrimes.Decomp416b

#print axioms LeanLab.AlmostPrimes.Decomp416b.R4A_le_divisor_sum
#print axioms LeanLab.AlmostPrimes.Decomp416b.rankin_divisor_sum
#print axioms LeanLab.AlmostPrimes.Decomp416b.R4A_rankin

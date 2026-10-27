import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, page 83: elementary bounds on the factors of a sieve survivor.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

noncomputable section

/-- The product of the prime factors is at least the threshold to their total count. -/
lemma rough_pow_length_le {x : ℕ} (hx : 1 ≤ x) {R : ℝ} (hR : 0 ≤ R)
    (hrough : ∀ p ∈ x.primeFactorsList, R ≤ (p : ℝ)) :
    R ^ x.primeFactorsList.length ≤ (x : ℝ) := by
  have hlist : ∀ l : List ℕ, (∀ p ∈ l, R ≤ (p : ℝ)) →
      R ^ l.length ≤ (l.prod : ℝ) := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro h
      simp only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ']
      exact mul_le_mul (h p (by simp))
        (ih (fun q hq => h q (by simp [hq]))) (pow_nonneg hR _) (Nat.cast_nonneg _)
  simpa only [Nat.prod_primeFactorsList (by omega : x ≠ 0)] using
    hlist x.primeFactorsList hrough

/-- A size bound below the next threshold power forces the desired factor count. -/
lemma almostGT_of_pow_bound {x k : ℕ} (hx : 1 ≤ x) {R : ℝ} (hR : 1 ≤ R)
    (hrough : ∀ p ∈ x.primeFactorsList, R < (p : ℝ))
    (hsize : (x : ℝ) < R ^ (k + 1)) : AlmostGT k R x := by
  refine ⟨hx, ?_, hrough⟩
  by_contra hcount
  have hk : k + 1 ≤ x.primeFactorsList.length := by omega
  have hpow := pow_le_pow_right₀ hR hk
  have hprod := rough_pow_length_le hx (by linarith : 0 ≤ R)
    (fun p hp => (hrough p hp).le)
  linarith

/-- Page 83: square roughness and a size bound force every multiplicity below s. -/
lemma factorization_lt_of_square_rough {x s : ℕ} (hx : 1 ≤ x) (hs : 2 ≤ s)
    {R : ℝ} (hR : 0 ≤ R)
    (hsquare : ∀ p : ℕ, p.Prime → p ^ 2 ∣ x → R < (p : ℝ))
    (hsize : (x : ℝ) ≤ R ^ s) :
    ∀ p ∈ x.primeFactors, x.factorization p < s := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_contra hmult
  have hsp : s ≤ x.factorization p := by omega
  have hpow : p ^ s ∣ x :=
    hprime.pow_dvd_iff_le_factorization (by omega : x ≠ 0) |>.mpr hsp
  have hsquarep : p ^ 2 ∣ x :=
    hprime.pow_dvd_iff_le_factorization (by omega : x ≠ 0) |>.mpr (hs.trans hsp)
  have hRp := hsquare p hprime hsquarep
  have hlt : R ^ s < (p : ℝ) ^ s := pow_lt_pow_left₀ hRp hR (by omega : s ≠ 0)
  have hle : (p : ℝ) ^ s ≤ (x : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < x) hpow
  linarith

/-- Both elementary conclusions needed for the part 2 survivor inclusion. -/
theorem c2_survivor_of_bounds {x k s : ℕ} (hx : 1 ≤ x) (hs : 2 ≤ s)
    {R T : ℝ} (hR : 1 ≤ R) (hT : 0 ≤ T)
    (hrough : ∀ p ∈ x.primeFactorsList, R < (p : ℝ))
    (hsquare : ∀ p : ℕ, p.Prime → p ^ 2 ∣ x → T < (p : ℝ))
    (hsizeR : (x : ℝ) < R ^ (k + 1)) (hsizeT : (x : ℝ) ≤ T ^ s) :
    AlmostGT k R x ∧ ∀ p ∈ x.primeFactors, x.factorization p < s :=
  ⟨almostGT_of_pow_bound hx hR hrough hsizeR,
    factorization_lt_of_square_rough hx hs hT hsquare hsizeT⟩

example : AlmostGT 2 (5 / 2) 15 := by
  apply almostGT_of_pow_bound (by norm_num) (by norm_num : (1 : ℝ) ≤ 5 / 2)
  · intro p hp
    norm_num [show Nat.primeFactorsList 15 = [3, 5] by norm_num] at hp
    rcases hp with rfl | rfl <;> norm_num
  · norm_num

example : AlmostGT 2 (5 / 2) 9 ∧
    ∀ p ∈ (9 : ℕ).primeFactors, (9 : ℕ).factorization p < 3 := by
  apply c2_survivor_of_bounds (by norm_num) (by norm_num)
    (by norm_num : (1 : ℝ) ≤ 5 / 2) (by norm_num : (0 : ℝ) ≤ 5 / 2)
  · intro p hp
    norm_num [show Nat.primeFactorsList 9 = [3, 3] by norm_num] at hp
    subst p
    norm_num
  · intro p hp hsq
    have hle := Nat.le_of_dvd (by norm_num : 0 < 9) hsq
    have hp2 := hp.two_le
    have hp3 : p ≤ 3 := by nlinarith
    interval_cases p <;> norm_num at *
  · norm_num
  · norm_num

end
end LeanLab.Ricci1937

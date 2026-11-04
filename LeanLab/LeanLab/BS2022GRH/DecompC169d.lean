/- AI wrote this Lean code for CODEX task169.
Theorem 4 and Table 1, journal pp. 1218 and 1219. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148f
import LeanLab.AlmostPrimeSums.Decomp1527b

namespace LeanLab.BS2022GRH.DecompC169d
open Real Finset Classical ChenThresholdGRH Decomp148f
noncomputable section

/-- Prime subsets with product below QD, p. 1219 remainder domain. -/
def subsets (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ) : Finset (Finset ℕ) :=
  (siftingPrimes P z).powerset.filter
    (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D)

/-- A finite sieve weight evaluated on the divisors of m, Theorem 4 proof input. -/
def weightValue (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (w : Finset ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ T ∈ subsets P Q z D, if (∏ p ∈ T, p : ℕ) ∣ m then w T else 0

/-- The actual weighted divisor sum before replacing counts by their model, p. 1219. -/
def weightedActual (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (z D : ℝ) (w : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ subsets P Q z D, w T * ∑ m ∈ supp.filter (fun m => (∏ p ∈ T, p : ℕ) ∣ m), a m

/-- The same weighted sum with the multiplicative model, p. 1219 definition of r. -/
def weightedModel (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ) (w : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ subsets P Q z D, w T *
    ∑ m ∈ supp, a m * ∏ p ∈ (∏ q ∈ T, q : ℕ).primeFactors, g m p

/-- Interchange the two finite sums defining the actual weighted count. -/
theorem weighted_actual_eq (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) :
    weightedActual supp a P Q z D w =
      ∑ m ∈ supp, a m * weightValue P Q z D w m := by
  unfold weightedActual weightValue
  simp_rw [sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro T hT
  split_ifs <;> ring

/-- Weights of absolute value at most one cost at most the stated remainder R. -/
theorem weighted_error_le (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ) (w : Finset ℕ → ℝ)
    (hw : ∀ T ∈ subsets P Q z D, |w T| ≤ 1) :
    |weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w| ≤
      errorSum supp a P Q g z D := by
  unfold weightedActual weightedModel
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  change |∑ T ∈ subsets P Q z D, w T * divisorError supp a g (∏ p ∈ T, p)| ≤ _
  calc
    _ ≤ ∑ T ∈ subsets P Q z D, |w T * divisorError supp a g (∏ p ∈ T, p)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ errorSum supp a P Q g z D := by
      unfold errorSum
      change (∑ T ∈ subsets P Q z D, _) ≤ ∑ T ∈ subsets P Q z D, _
      apply sum_le_sum
      intro T hT
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw T hT) (abs_nonneg _)).trans_eq (one_mul _)

/-- A pointwise majorant gives an upper bound for the sifted sum. -/
theorem upper_of_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hw : ∀ m ∈ supp,
      (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ≤
        weightValue P Q z D w m) :
    sifted supp a P z ≤ weightedActual supp a P Q z D w := by
  rw [weighted_actual_eq]
  unfold sifted
  rw [sum_filter]
  apply sum_le_sum
  intro m hm
  have h := mul_le_mul_of_nonneg_left (hw m hm) (ha m)
  split_ifs at h ⊢ <;> simpa using h

/-- A pointwise minorant gives a lower bound for the sifted sum. -/
theorem lower_of_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hw : ∀ m ∈ supp, weightValue P Q z D w m ≤
      (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0)) :
    weightedActual supp a P Q z D w ≤ sifted supp a P z := by
  rw [weighted_actual_eq]
  unfold sifted
  rw [sum_filter]
  apply sum_le_sum
  intro m hm
  have h := mul_le_mul_of_nonneg_left (hw m hm) (ha m)
  split_ifs at h ⊢ <;> simpa using h

/-! The finite Rosser construction. The primes in Q are sieved exactly.
The cube cutoff is the stopping condition of BJS Section 2.4 equation 28.
The numerical Rosser pairing is reused from AlmostPrimeSums.Decomp1527b. -/

/-- Rosser support with exact exceptional primes, BJS Section 2.4 p. 10. -/
def rosserSupport (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ) (upper : Bool) :
    Finset (Finset ℕ) :=
  (siftingPrimes P z).powerset.filter (fun T =>
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D upper (∏ p ∈ T \ Q, p) ≠ 0)

/-- Signed Rosser weight on prime subsets, BJS Section 2.4 p. 10. -/
def rosserSubsetWeight (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (upper : Bool) (T : Finset ℕ) : ℝ :=
  if T ∈ rosserSupport P Q z D upper then (-1 : ℝ) ^ T.card else 0

/-- Every Rosser subset weight has absolute value at most one, p. 10. -/
theorem abs_rosserSubsetWeight (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (upper : Bool) (T : Finset ℕ) : |rosserSubsetWeight P Q z D upper T| ≤ 1 := by
  unfold rosserSubsetWeight
  split_ifs <;> simp [abs_pow]

/-- A product of distinct primes is squarefree. Auxiliary finite fact for p. 10. -/
theorem prime_subset_squarefree (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hT p hp) (hT q hq)).mpr hpq
  · exact fun p hp => (hT p hp).squarefree

/-- The Mobius coefficient on distinct primes is minus one to the cardinality.
Auxiliary finite sign identity for BJS Section 2.4 p. 10. -/
theorem moebius_prime_subset (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℝ) = (-1 : ℝ) ^ T.card := by
  have hs := prime_subset_squarefree T hT
  have hc := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hs.ne_zero).mpr hs
  have hcard : ArithmeticFunction.cardFactors (∏ p ∈ T, p) = T.card := by
    rw [← hc]
    simp only [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors, Nat.primeFactors_prod hT]
  rw [ArithmeticFunction.moebius_apply_of_squarefree hs]
  push_cast
  rw [hcard]

/-- The Rosser support is exactly the decreasing prime prefix cube family.
Indices start at zero. Upper tests even indices and lower tests odd indices.
This is the stopping condition of BJS Section 2.4 p. 10 equation 28. -/
theorem mem_rosserSupport_iff (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (b : Bool) (T : Finset ℕ) :
    T ∈ rosserSupport P Q z D b ↔
      T ⊆ siftingPrimes P z ∧ ∀ k < (T \ Q).card, (b = true ↔ k % 2 = 0) →
        ((((T \ Q).sort (· ≥ ·)).take k).prod : ℝ) *
          (((T \ Q).sort (· ≥ ·)).getD k 0 : ℝ) ^ 3 < D := by
  have heq (hT : T ⊆ siftingPrimes P z) :
      (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) ≠ 0) ↔
      ∀ k < (T \ Q).card, (b = true ↔ k % 2 = 0) →
        ((((T \ Q).sort (· ≥ ·)).take k).prod : ℝ) *
          (((T \ Q).sort (· ≥ ·)).getD k 0 : ℝ) ^ 3 < D := by
    have hp : ∀ p ∈ T \ Q, p.Prime :=
      fun p hp => hP p (mem_filter.mp (hT (mem_sdiff.mp hp).1)).2.1
    have hs := prime_subset_squarefree (T \ Q) hp
    have hm0 : (ArithmeticFunction.moebius (∏ p ∈ T \ Q, p) : ℝ) ≠ 0 := by
      rw [moebius_prime_subset _ hp]
      exact pow_ne_zero _ (by norm_num)
    unfold LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight
    simp only [hs, true_and, LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes,
      Nat.primeFactors_prod hp, length_sort]
    split_ifs <;> simp_all
  simp only [rosserSupport, mem_filter, mem_powerset]
  constructor
  · rintro ⟨hT, hw⟩
    exact ⟨hT, (heq hT).mp hw⟩
  · rintro ⟨hT, hc⟩
    exact ⟨hT, (heq hT).mpr hc⟩

/-- The subset formula equals the numerical Rosser coefficient times the
exact exceptional prime sign. BJS Section 2.4 p. 10. -/
theorem rosserSubsetWeight_eq (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (upper : Bool) (T : Finset ℕ) (hT : T ⊆ siftingPrimes P z)
    (hP : ∀ p ∈ P, p.Prime) :
    rosserSubsetWeight P Q z D upper T = (-1 : ℝ) ^ (T ∩ Q).card *
      LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D upper (∏ p ∈ T \ Q, p) := by
  have hp : ∀ p ∈ T \ Q, p.Prime := by
    intro p hp
    exact hP p (mem_filter.mp (hT (mem_sdiff.mp hp).1)).2.1
  have hc : (T \ Q).card + (T ∩ Q).card = T.card := card_sdiff_add_card_inter T Q
  unfold rosserSubsetWeight rosserSupport
  simp only [mem_filter, mem_powerset, hT, true_and]
  have hm := moebius_prime_subset (T \ Q) hp
  have hm0 : (ArithmeticFunction.moebius (∏ p ∈ T \ Q, p) : ℝ) ≠ 0 := by
    rw [hm]
    exact pow_ne_zero _ (by norm_num)
  unfold LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight
  split_ifs <;> simp_all [hm, ← pow_add, Nat.add_comm, hc]

/-- Rosser support is contained in the permitted remainder domain.
BJS Section 2.4 p. 10 and journal p. 1219. -/
theorem rosserSupport_subset (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P) (hz : 2 ≤ z) (hzD : z ≤ D)
    (upper : Bool) : rosserSupport P Q z D upper ⊆ subsets P Q z D := by
  intro T hT
  obtain ⟨hTP, hw⟩ := mem_filter.mp hT
  have hsub := mem_powerset.mp hTP
  have hp : ∀ p ∈ T \ Q, p.Prime := by
    intro p hp
    exact hP p (mem_filter.mp (hsub (mem_sdiff.mp hp).1)).2.1
  have hout : ((∏ p ∈ T \ Q, p : ℕ) : ℝ) < D := by
    rcases LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight_support D
      (by linarith) upper _ hw with h | h
    · exact h
    · have hm : (∏ p ∈ T \ Q, p : ℕ) ∈ T \ Q := by
        have hm := Nat.mem_primeFactors.mpr ⟨h, dvd_rfl, h.ne_zero⟩
        rwa [Nat.primeFactors_prod hp] at hm
      exact ((mem_filter.mp (hsub (mem_sdiff.mp hm).1)).2.2).trans_le hzD
  have hQpos : 0 < (∏ p ∈ Q, (p : ℝ)) := by
    apply prod_pos
    intro p hp
    exact_mod_cast (hP p (hQ hp)).pos
  have hinter : (∏ p ∈ T ∩ Q, (p : ℝ)) ≤ ∏ p ∈ Q, (p : ℝ) := by
    apply prod_le_prod_of_subset_of_one_le₀ inter_subset_right
    · exact fun p _ => Nat.cast_nonneg p
    · intro p hp _
      exact_mod_cast (hP p (hQ hp)).one_lt.le
  apply mem_filter.mpr
  refine ⟨hTP, ?_⟩
  have hprod : (∏ p ∈ T, (p : ℝ)) =
      (∏ p ∈ T ∩ Q, (p : ℝ)) * ∏ p ∈ T \ Q, (p : ℝ) := by
    exact (prod_inter_mul_prod_sdiff T Q (fun p : ℕ => (p : ℝ))).symm
  push_cast at hout ⊢
  rw [hprod]
  calc
    _ ≤ (∏ p ∈ Q, (p : ℝ)) * ∏ p ∈ T \ Q, (p : ℝ) :=
      mul_le_mul_of_nonneg_right hinter (prod_nonneg (fun p _ => Nat.cast_nonneg p))
    _ < _ := mul_lt_mul_of_pos_left hout hQpos

/-- The finite divisor sum can be extended to every prime subset since
all omitted Rosser weights vanish. Journal p. 1219. -/
theorem rosser_weightValue_powerset (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P) (hz : 2 ≤ z) (hzD : z ≤ D)
    (upper : Bool) (m : ℕ) :
    weightValue P Q z D (rosserSubsetWeight P Q z D upper) m =
      ∑ T ∈ (siftingPrimes P z).powerset,
        if (∏ p ∈ T, p : ℕ) ∣ m then rosserSubsetWeight P Q z D upper T else 0 := by
  unfold weightValue
  apply sum_subset (filter_subset _ _)
  intro T hT hnot
  have hs : T ∉ rosserSupport P Q z D upper :=
    fun h => hnot (rosserSupport_subset P Q z D hP hQ hz hzD upper h)
  simp [rosserSubsetWeight, hs]

/-- Least prime toggling gives the two Rosser signs. This is the finite
pairing of Ricci1937.decompJ365_brun_toggle_lower for BJS p. 10. -/
theorem rosser_powerset_bounds (γ Q : Finset ℕ) (D : ℝ)
    (hγ : ∀ p ∈ γ, p.Prime) :
    (∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
      LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T \ Q, p)) ≤
      (if γ = ∅ then 1 else 0) ∧
    (if γ = ∅ then (1 : ℝ) else 0) ≤
      ∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
        LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T \ Q, p) := by
  by_cases he : γ = ∅
  · subst γ
    simp [LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight,
      LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes]
  rw [if_neg he]
  have hne := nonempty_iff_ne_empty.mpr he
  by_cases hQ : (γ ∩ Q).Nonempty
  · obtain ⟨ν, hν⟩ := hQ
    obtain ⟨hνγ, hνQ⟩ := mem_inter.mp hν
    have heq (b : Bool) :
        (∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
          LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p)) = 0 := by
      rw [← insert_erase hνγ, sum_powerset_insert (notMem_erase ν γ), ← sum_add_distrib]
      apply sum_eq_zero
      intro T hT
      have hn : ν ∉ T := notMem_of_mem_powerset_of_notMem hT (notMem_erase ν γ)
      have hi : insert ν T ∩ Q = insert ν (T ∩ Q) := by
        ext p
        by_cases heq : p = ν <;> simp_all
      have hd : insert ν T \ Q = T \ Q := insert_sdiff_of_mem T hνQ
      rw [hi, hd, card_insert_of_notMem (fun h => hn (mem_inter.mp h).1), pow_succ]
      ring
    rw [heq false, heq true]
    exact ⟨le_rfl, le_rfl⟩
  · have hdis : Disjoint γ Q := disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp hQ)
    let ν := γ.min' hne
    have hν : ν ∈ γ := min'_mem γ hne
    have hpair (T : Finset ℕ) (hT : T ∈ (γ.erase ν).powerset) :
        0 ≤ LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T, p) +
          LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ insert ν T, p) ∧
        LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T, p) +
          LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ insert ν T, p) ≤ 0 := by
      have ht := mem_powerset.mp hT
      have hp : ∀ p ∈ T, p.Prime := fun p hp => hγ p (mem_erase.mp (ht hp)).2
      have hn : ν ∉ T := notMem_of_mem_powerset_of_notMem hT (notMem_erase ν γ)
      rw [prod_insert hn, mul_comm ν]
      apply LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight_smallest_pair_sign D (hγ ν hν)
      intro p hp'
      rw [Nat.primeFactors_prod hp] at hp'
      have hpγ := (mem_erase.mp (ht hp')).2
      exact lt_of_le_of_ne (min'_le γ p hpγ) (Ne.symm (mem_erase.mp (ht hp')).1)
    have hsum (b : Bool) :
        (∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
          LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p)) =
        ∑ T ∈ (γ.erase ν).powerset,
          (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T, p) +
           LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ insert ν T, p)) := by
      have hreduce : ∀ T ∈ γ.powerset, Disjoint T Q :=
        fun T hT => hdis.mono_left (mem_powerset.mp hT)
      have hr : (∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
          LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p)) =
          ∑ T ∈ γ.powerset, LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T, p) := by
        apply sum_congr rfl
        intro T hT
        simp [disjoint_iff_inter_eq_empty.mp (hreduce T hT), sdiff_eq_left.mpr (hreduce T hT)]
      rw [hr]
      conv_lhs => rw [← insert_erase hν, sum_powerset_insert (notMem_erase ν γ), ← sum_add_distrib]
    rw [hsum false, hsum true]
    exact ⟨sum_nonpos (fun T hT => (hpair T hT).2),
      sum_nonneg (fun T hT => (hpair T hT).1)⟩

/-- The Rosser subset sum is a minorant and a majorant of the sifting
indicator. BJS Section 2.4 p. 10 and journal pp. 1218 and 1219. -/
theorem rosser_pointwise (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P) (hz : 2 ≤ z) (hzD : z ≤ D) (m : ℕ) :
    weightValue P Q z D (rosserSubsetWeight P Q z D false) m ≤
      (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ∧
    (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ≤
      weightValue P Q z D (rosserSubsetWeight P Q z D true) m := by
  let γ := (siftingPrimes P z).filter (· ∣ m)
  have hp : ∀ p ∈ siftingPrimes P z, p.Prime :=
    fun p hp => hP p (mem_filter.mp hp).2.1
  have heq (b : Bool) :
      weightValue P Q z D (rosserSubsetWeight P Q z D b) m =
      ∑ T ∈ γ.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
        LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) := by
    rw [rosser_weightValue_powerset P Q z D hP hQ hz hzD, ← sum_filter]
    have hf : (siftingPrimes P z).powerset.filter (fun T => (∏ p ∈ T, p : ℕ) ∣ m) =
        γ.powerset := by
      ext T
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨hT, hd⟩
        exact (LeanLab.PNTSieve.Bonferroni.dvd_iff_subset _ hp hT m).mp hd
      · intro hT
        have hs := hT.trans (filter_subset _ _)
        exact ⟨hs, (LeanLab.PNTSieve.Bonferroni.dvd_iff_subset _ hp hs m).mpr hT⟩
    rw [hf]
    apply sum_congr rfl
    intro T hT
    exact rosserSubsetWeight_eq P Q z D b T
      ((mem_powerset.mp hT).trans (filter_subset _ _)) hP
  have hind : (∀ p ∈ siftingPrimes P z, ¬ p ∣ m) ↔ γ = ∅ := by
    simp [γ, filter_eq_empty_iff]
  rw [heq false, heq true]
  simp only [hind]
  exact rosser_powerset_bounds γ Q D (fun p hp' => hp p (mem_filter.mp hp').1)

/-- The prime polynomial for the finite Rosser model, BJS Section 2.4 p. 10.
Exceptional primes carry exact inclusion exclusion coefficients. -/
def rosserPrimeModel (S Q : Finset ℕ) (D : ℝ) (b : Bool) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (T ∩ Q).card *
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) * ∏ p ∈ T, g p

/-- Split each prime subset into its exceptional and ordinary parts.
Finite indexing identity for the BJS model, Section 2.4 p. 10. -/
theorem sum_powerset_split234 (S Q : Finset ℕ) (f : Finset ℕ → Finset ℕ → ℝ) :
    (∑ T ∈ S.powerset, f (T ∩ Q) (T \ Q)) =
      ∑ U ∈ (S ∩ Q).powerset, ∑ V ∈ (S \ Q).powerset, f U V := by
  rw [← sum_product' (S ∩ Q).powerset (S \ Q).powerset f]
  apply sum_bij (fun T _ => (T ∩ Q, T \ Q))
  · intro T hT
    have ht := mem_powerset.mp hT
    apply mem_product.mpr
    constructor
    · apply mem_powerset.mpr
      intro p hp
      exact mem_inter.mpr ⟨ht (mem_inter.mp hp).1, (mem_inter.mp hp).2⟩
    · apply mem_powerset.mpr
      intro p hp
      exact mem_sdiff.mpr ⟨ht (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
  · intro T hT R hR heq
    have hi := congrArg Prod.fst heq
    have hd := congrArg Prod.snd heq
    change T ∩ Q = R ∩ Q at hi
    change T \ Q = R \ Q at hd
    rw [← sdiff_union_inter T Q, hd, hi, sdiff_union_inter]
  · rintro ⟨U, V⟩ hUV
    obtain ⟨hU, hV⟩ := mem_product.mp hUV
    have hu := mem_powerset.mp hU
    have hv := mem_powerset.mp hV
    refine ⟨U ∪ V, mem_powerset.mpr (union_subset
      (hu.trans inter_subset_left) (hv.trans sdiff_subset)), ?_⟩
    apply Prod.ext <;> ext p <;> simp only [mem_inter, mem_sdiff, mem_union]
    · have h1 : p ∈ U → p ∈ Q := fun h => (mem_inter.mp (hu h)).2
      have h2 : p ∈ V → p ∉ Q := fun h => (mem_sdiff.mp (hv h)).2
      tauto
    · have h1 : p ∈ U → p ∈ Q := fun h => (mem_inter.mp (hu h)).2
      have h2 : p ∈ V → p ∉ Q := fun h => (mem_sdiff.mp (hv h)).2
      tauto
  · intro T hT
    rfl

/-- Exact exceptional primes factor out of the Rosser prime model as their
Euler factors. No density condition is needed. BJS Theorem 6 and Section 2.4 p. 10. -/
theorem rosserPrimeModel_factor (S Q : Finset ℕ) (D : ℝ) (b : Bool) (g : ℕ → ℝ) :
    rosserPrimeModel S Q D b g =
      (∏ p ∈ S ∩ Q, (1 - g p)) * rosserPrimeModel (S \ Q) ∅ D b g := by
  have hterm (T : Finset ℕ) :
      (-1 : ℝ) ^ (T ∩ Q).card *
        LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) *
          (∏ p ∈ T, g p) =
      ((-1 : ℝ) ^ (T ∩ Q).card * ∏ p ∈ T ∩ Q, g p) *
        (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) *
          ∏ p ∈ T \ Q, g p) := by
    rw [← prod_inter_mul_prod_sdiff T Q g]
    ring
  unfold rosserPrimeModel
  simp_rw [hterm]
  rw [sum_powerset_split234 S Q (fun U V =>
    ((-1 : ℝ) ^ U.card * ∏ p ∈ U, g p) *
      (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ V, p) * ∏ p ∈ V, g p))]
  have hfactor : (∑ U ∈ (S ∩ Q).powerset, (-1 : ℝ) ^ U.card * ∏ p ∈ U, g p) =
      ∏ p ∈ S ∩ Q, (1 - g p) := by
    rw [show (∏ p ∈ S ∩ Q, (1 - g p)) = ∏ p ∈ S ∩ Q, (1 + -g p) by rfl,
      prod_one_add]
    apply sum_congr rfl
    intro U hU
    rw [prod_neg]
  simp only [inter_empty, card_empty, pow_zero, sdiff_empty, one_mul]
  rw [← hfactor]
  simp_rw [← mul_sum]
  rw [sum_mul]

/-- The aggregate Rosser model is the sum of the individual prime models.
All prime factor indexing and finite sum interchange is explicit. Journal p. 1219. -/
theorem weightedModel_eq_rosserPrimeModel (supp : Finset ℕ) (a : ℕ → ℝ)
    (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P) (hz : 2 ≤ z) (hzD : z ≤ D) (b : Bool) :
    weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D b) =
      ∑ m ∈ supp, a m * rosserPrimeModel (siftingPrimes P z) Q D b (g m) := by
  have hp : ∀ T ∈ (siftingPrimes P z).powerset, ∀ p ∈ T, p.Prime := by
    intro T hT p hp
    exact hP p (mem_filter.mp ((mem_powerset.mp hT) hp)).2.1
  have hext : weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D b) =
      ∑ T ∈ (siftingPrimes P z).powerset,
        rosserSubsetWeight P Q z D b T * ∑ m ∈ supp, a m * ∏ p ∈ T, g m p := by
    unfold weightedModel
    calc
      _ = ∑ T ∈ subsets P Q z D,
          rosserSubsetWeight P Q z D b T * ∑ m ∈ supp, a m * ∏ p ∈ T, g m p := by
        apply sum_congr rfl
        intro T hT
        rw [Nat.primeFactors_prod (hp T (mem_filter.mp hT).1)]
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro T hT hn
        have hs : T ∉ rosserSupport P Q z D b :=
          fun h => hn (rosserSupport_subset P Q z D hP hQ hz hzD b h)
        simp [rosserSubsetWeight, hs]
  rw [hext]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  unfold rosserPrimeModel
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [rosserSubsetWeight_eq P Q z D b T (mem_powerset.mp hT) hP]
  ring

/-- A pointwise prime model upper bound suffices for the aggregate upper
model estimate. Journal p. 1219 definition of the main mass. -/
theorem rosser_model_upper_of_prime (supp : Finset ℕ) (a : ℕ → ℝ)
    (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hz : 2 ≤ z) (hzD : z ≤ D)
    (h : ∀ n ∈ supp, rosserPrimeModel (siftingPrimes P z) Q D true (g n) ≤
      C * ∏ p ∈ siftingPrimes P z, (1 - g n p)) :
    weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D true) ≤
      C * mainMass supp a P g z := by
  rw [weightedModel_eq_rosserPrimeModel supp a P Q g z D hP hQ hz hzD]
  unfold mainMass
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  exact (mul_le_mul_of_nonneg_left (h n hn) (ha n)).trans_eq (by ring)

/-- A pointwise prime model lower bound suffices for the aggregate lower
model estimate. Journal p. 1219 definition of the main mass. -/
theorem rosser_model_lower_of_prime (supp : Finset ℕ) (a : ℕ → ℝ)
    (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hz : 2 ≤ z) (hzD : z ≤ D)
    (h : ∀ n ∈ supp, C * ∏ p ∈ siftingPrimes P z, (1 - g n p) ≤
      rosserPrimeModel (siftingPrimes P z) Q D false (g n)) :
    C * mainMass supp a P g z ≤
      weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D false) := by
  rw [weightedModel_eq_rosserPrimeModel supp a P Q g z D hP hQ hz hzD]
  unfold mainMass
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hh := mul_le_mul_of_nonneg_left (h n hn) (ha n)
  convert hh using 1 <;> ring

/-- Below the finite cutoff no Rosser coefficient is removed. The individual
prime model is then the full Euler product. BJS Section 2.4 p. 10. -/
theorem rosserPrimeModel_exact_of_small (S Q : Finset ℕ) (D z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p ∈ S, p.Prime) (hSz : ∀ p ∈ S, (p : ℝ) ≤ z)
    (hsmall : ((∏ p ∈ S \ Q, p : ℕ) : ℝ) * z ^ 2 < D) (b : Bool) (g : ℕ → ℝ) :
    rosserPrimeModel S Q D b g = ∏ p ∈ S, (1 - g p) := by
  have hc (T : Finset ℕ) (hT : T ⊆ S) :
      (-1 : ℝ) ^ (T ∩ Q).card *
        LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T \ Q, p) =
          (-1 : ℝ) ^ T.card := by
    have hp : ∀ p ∈ T \ Q, p.Prime :=
      fun p hp => hP p (hT (mem_sdiff.mp hp).1)
    have hle : ((∏ p ∈ T \ Q, p : ℕ) : ℝ) ≤ (∏ p ∈ S \ Q, p : ℕ) := by
      exact_mod_cast prod_le_prod_of_subset_of_one_le (by
          intro p hp
          exact mem_sdiff.mpr ⟨hT (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩)
        (fun p hp _ => (hP p (mem_sdiff.mp hp).1).one_lt.le)
    have hs : ((∏ p ∈ T \ Q, p : ℕ) : ℝ) * z ^ 2 < D :=
      (mul_le_mul_of_nonneg_right hle (sq_nonneg z)).trans_lt hsmall
    rw [LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight_eq_moebius_of_small D z hz b
      (fun p hp' => by
        rw [Nat.primeFactors_prod hp] at hp'
        exact hSz p (hT (mem_sdiff.mp hp').1)) hs,
      moebius_prime_subset _ hp, ← pow_add, Nat.add_comm, card_sdiff_add_card_inter]
  unfold rosserPrimeModel
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * ∏ p ∈ T, g p := by
      apply sum_congr rfl
      intro T hT
      rw [hc T (mem_powerset.mp hT)]
    _ = _ := by
      rw [show (∏ p ∈ S, (1 - g p)) = ∏ p ∈ S, (1 + -g p) by rfl, prod_one_add]
      apply sum_congr rfl
      intro T hT
      rw [prod_neg]

/-- In the finite exact regime the aggregate model is exactly mainMass.
This is an unconditional restricted regime, not the uniform Table 1 estimate.
Journal p. 1219 and BJS Section 2.4 p. 10. -/
theorem weightedModel_exact_of_small (supp : Finset ℕ) (a : ℕ → ℝ)
    (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P) (hz : 2 ≤ z) (hzD : z ≤ D)
    (hsmall : ((∏ p ∈ siftingPrimes P z \ Q, p : ℕ) : ℝ) * z ^ 2 < D) (b : Bool) :
    weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D b) =
      mainMass supp a P g z := by
  rw [weightedModel_eq_rosserPrimeModel supp a P Q g z D hP hQ hz hzD]
  unfold mainMass
  apply sum_congr rfl
  intro n hn
  rw [rosserPrimeModel_exact_of_small _ Q D z (by linarith)
    (fun p hp => hP p (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2.le) hsmall]

/-- Both selected Table 1 model bounds hold in the nonempty finite exact
regime. No density premise or cited model input is used. Journal pp. 1218 and 1219. -/
theorem rosser_selected_models_of_small234 (supp : Finset ℕ) (a : ℕ → ℝ)
    (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z) (hzD : z ≤ D)
    (hsmall : ((∏ p ∈ siftingPrimes P z \ Q, p : ℕ) : ℝ) * z ^ 2 < D) :
    (log D / log z ≤ 3 →
      weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D true) ≤
        (2 * exp eulerMascheroniConstant / (log D / log z) +
          (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z) ∧
    (z ^ 2 ≤ D → log D / log z ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z ≤
          weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D false)) := by
  let s := log D / log z
  have hlz : 0 < log z := log_pos (by linarith)
  have hld : 0 < log D := log_pos (by linarith)
  have hs0 : 0 < s := div_pos hld hlz
  have hh : 0 ≤ hS s := by
    unfold hS
    split_ifs <;> positivity
  have hmass : 0 ≤ mainMass supp a P g z := by
    apply sum_nonneg
    intro n hn
    apply mul_nonneg (ha n)
    apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hg n p (mem_filter.mp hp).2.1).2.le
  constructor
  · intro hs
    rw [weightedModel_exact_of_small supp a P Q g z D hP hQ hz hzD hsmall true]
    have hF := LeanLab.AlmostPrimeSums.Decomp1527a.one_lt_Fsieve s hs0 (by dsimp [s]; linarith)
    have hF' : 1 ≤ 2 * exp eulerMascheroniConstant / s := by
      simpa only [LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve, show s ≤ 3 from hs,
        ↓reduceIte] using hF.le
    have herr : 0 ≤ (1 / 8349 : ℝ) * 112 * exp 2 * hS s := by positivity
    have hc : 1 ≤ 2 * exp eulerMascheroniConstant / s +
        (1 / 8349 : ℝ) * 112 * exp 2 * hS s := by linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hmass
  · intro hD hs
    rw [weightedModel_exact_of_small supp a P Q g z D hP hQ hz hzD hsmall false]
    have hs2 : 2 ≤ s := by
      have hl := log_le_log (pow_pos (by linarith : 0 < z) 2) hD
      rw [log_pow] at hl
      exact (le_div_iff₀ hlz).mpr (by norm_num at hl; linarith)
    have hf := LeanLab.AlmostPrimeSums.Decomp1527a.fsieve_lt_one s hs0 hs
    have hf' : 2 * exp eulerMascheroniConstant * log (s - 1) / s ≤ 1 := by
      by_cases h2 : s ≤ 2
      · have he : s = 2 := le_antisymm h2 hs2
        rw [he]
        norm_num
      · simpa only [LeanLab.AlmostPrimeSums.Decomp1527a.fsieve, h2, ↓reduceIte] using hf.le
    have herr : 0 ≤ (1 / 8349 : ℝ) * 114 * exp 2 * hS s := by positivity
    have hc : 2 * exp eulerMascheroniConstant * log (s - 1) / s -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS s ≤ 1 := by linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hmass

/-- LEAF. Upper Rosser model estimate. BJS Theorem 6 and Section 2.4,
pp. 4 to 5 and 10 to 17. Journal pp. 1218 and 1219, Table 1 row 6100.
The fixed level hypothesis retains the U-1611 source concern.
No finite weight sign or support obligation is included in this input. -/
theorem rosser_upper_model (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D true) ≤
        (2 * exp eulerMascheroniConstant / (log D / log z) +
          (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z  := by
  sorry

/-- LEAF. Upper sieve weights and their model estimate, Theorem 4 p. 1218 and Table 1.
Construct the explicit Rosser weights from the cited Theorem 6 of arXiv 2207.09452.
The row 6100 supplies C1 equal to 112 at epsilon equal to 1/8349. -/
theorem upper_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    ∃ w : Finset ℕ → ℝ,
      (∀ T ∈ subsets P Q z D, |w T| ≤ 1) ∧
      (∀ m ∈ supp, (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ≤
        weightValue P Q z D w m) ∧
      weightedModel supp a P Q g z D w ≤
        (2 * exp eulerMascheroniConstant / (log D / log z) +
          (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z := by
  refine ⟨rosserSubsetWeight P Q z D true, ?_, ?_, ?_⟩
  · exact fun T _ => abs_rosserSubsetWeight P Q z D true T
  · intro m _
    exact (rosser_pointwise P Q z D hP hQ hz hzD m).2
  · exact rosser_upper_model supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs

/-- LEAF. Lower Rosser model estimate. BJS Theorem 6 and Section 2.4,
pp. 4 to 5 and 10 to 17. Journal pp. 1218 and 1219, Table 1 row 6100.
The fixed level hypothesis retains the U-1611 source concern.
No finite weight sign or support obligation is included in this input. -/
theorem rosser_lower_model (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z ≤
        weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D false)  := by
  sorry

/-- LEAF. Lower sieve weights and their model estimate, Theorem 4 p. 1218 and Table 1.
The row 6100 supplies C2 equal to 114 at epsilon equal to 1/8349.
The signed minorant and absolute weight bound remain explicit obligations. -/
theorem lower_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    ∃ w : Finset ℕ → ℝ,
      (∀ T ∈ subsets P Q z D, |w T| ≤ 1) ∧
      (∀ m ∈ supp, weightValue P Q z D w m ≤
        (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0)) ∧
      (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z ≤
        weightedModel supp a P Q g z D w := by
  refine ⟨rosserSubsetWeight P Q z D false, ?_, ?_, ?_⟩
  · exact fun T _ => abs_rosserSubsetWeight P Q z D false T
  · intro m _
    exact (rosser_pointwise P Q z D hP hQ hz (le_trans (by nlinarith : z ≤ z ^ 2) hzD) m).1
  · exact rosser_lower_model supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs

/-- Exact selected LinearSieveT4 from the two weight certificates.
All remainder bookkeeping is proved. The weight construction remains OPEN. -/
theorem linearSieveT4_8349 : LinearSieveT4 (1 / 8349) 112 114 := by
  intro supp a P Q g z D ha hsupp hP hQ hg _he0 _he1 hz hprod
  constructor
  · intro hzD hs
    obtain ⟨w, hw, hup, hmodel⟩ := upper_weights supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs
    have herr := weighted_error_le supp a P Q g z D w hw
    have hactual := upper_of_weights supp a P Q z D w ha hup
    have := le_abs_self (weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w)
    change sifted supp a P z ≤ _
    change _ ≤ (2 * exp eulerMascheroniConstant / (log D / log z) +
      (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z +
      errorSum supp a P Q g z D
    linarith
  · intro hzD hs
    obtain ⟨w, hw, hlo, hmodel⟩ := lower_weights supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs
    have herr := weighted_error_le supp a P Q g z D w hw
    have hactual := lower_of_weights supp a P Q z D w ha hlo
    have := neg_abs_le (weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w)
    change _ ≤ sifted supp a P z
    change _ * mainMass supp a P g z - errorSum supp a P Q g z D ≤ _
    linarith

/-- A nonzero two prime support instance with a nonempty exceptional set.
Theorem 4 finite Rosser construction, journal pp. 1218 and 1219. -/
theorem rosser_nontrivial_instance234 (b : Bool) :
    rosserSubsetWeight ({2, 3} : Set ℕ) {2} 4 64 b {2, 3} = 1 := by
  have hp : ∀ p ∈ ({2, 3} : Set ℕ), p.Prime := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> norm_num
  have ht : ({2, 3} : Finset ℕ) ⊆ siftingPrimes ({2, 3} : Set ℕ) 4 := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num [siftingPrimes]
  rw [rosserSubsetWeight_eq _ _ _ _ _ _ ht hp]
  rw [show ({2, 3} : Finset ℕ) ∩ {2} = {2} by decide,
    show ({2, 3} : Finset ℕ) \ {2} = {3} by decide]
  cases b <;> norm_num [LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight,
    LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes, Nat.prime_three.primeFactors,
    Nat.prime_three.squarefree, ArithmeticFunction.moebius_apply_prime Nat.prime_three]

/-- Both pointwise signs hold on a nonempty two prime system for every m.
Theorem 4 finite Rosser construction, journal pp. 1218 and 1219. -/
theorem rosser_pointwise_instance234 (m : ℕ) :
    weightValue ({2, 3} : Set ℕ) {2} 4 64
      (rosserSubsetWeight ({2, 3} : Set ℕ) {2} 4 64 false) m ≤
      (if ∀ p ∈ siftingPrimes ({2, 3} : Set ℕ) 4, ¬ p ∣ m then (1 : ℝ) else 0) ∧
    (if ∀ p ∈ siftingPrimes ({2, 3} : Set ℕ) 4, ¬ p ∣ m then (1 : ℝ) else 0) ≤
      weightValue ({2, 3} : Set ℕ) {2} 4 64
        (rosserSubsetWeight ({2, 3} : Set ℕ) {2} 4 64 true) m := by
  have hp : ∀ p ∈ ({2, 3} : Set ℕ), p.Prime := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hq : ↑({2} : Finset ℕ) ⊆ ({2, 3} : Set ℕ) := by
    intro p hp
    simp only [mem_coe, mem_singleton] at hp
    subst p
    simp
  have hh := rosser_pointwise ({2, 3} : Set ℕ) {2} 4 64 hp hq
    (by norm_num) (by norm_num) m
  split_ifs at hh ⊢ <;> simp_all

/-! Reused delay functions for the remaining analytic model step.
Ported from subfish-zhou/goldbach-lean by CODEX task234.
Source commit 9d4c3a4010d42aedd9e7231bf94386019cfffccc.
File MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965ChenDelayFunctions.lean.
Copyright 2026 UyNewNas. Licensed under the Apache License, Version 2.0.
License text: LICENSE-Apache-2.0-task234.txt in this folder.
Port changes: imports and namespace only.
The source constructs the delay pair by finite steps with no cited axiom.
No Table 1 constant or sieve model estimate follows from this construction alone.
AI wrote the port. Goldbach is open. -/
namespace RosserDelay234
open Set Filter MeasureTheory
open scoped Topology

/-- `false` selects the upper function; `true` selects the lower function. -/
def delayInitial (A : ℝ) (b : Bool) : ℝ := if b then 0 else A

/-- Finite method of steps for the weighted pair. The denominator is truncated
only outside the domain of integration, where its value is immaterial. -/
def delayStep (A : ℝ) : ℕ → Bool → ℝ → ℝ
  | 0, b, _ => delayInitial A b
  | n + 1, b, u => delayInitial A b +
      ∫ t in (2 : ℝ)..max 2 u, delayStep A n (!b) (t - 1) / max 1 (t - 1)

theorem delayStep_initial (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayStep A n b u = delayInitial A b := by
  cases n <;> simp [delayStep, max_eq_left hu]

theorem continuous_delayStep (A : ℝ) (n : ℕ) (b : Bool) :
    Continuous (delayStep A n b) := by
  induction n generalizing b with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun t : ℝ =>
        delayStep A n (!b) (t - 1) / max 1 (t - 1)) :=
      ((ih (!b)).comp (continuous_id.sub continuous_const)).div
        (continuous_const.max (continuous_id.sub continuous_const))
        (fun t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    exact continuous_const.add
      ((intervalIntegral.continuous_primitive (fun a c => hc.intervalIntegrable a c) 2).comp
        (continuous_const.max continuous_id))

/-- One more step does not change the solution on the already constructed range. -/
theorem delayStep_succ_eq (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 2) :
    delayStep A (n + 1) b u = delayStep A n b u := by
  induction n generalizing b u with
  | zero =>
    rw [delayStep_initial A 1 b (by simpa using hu), delayStep_initial A 0 b (by simpa using hu)]
  | succ n ih =>
    simp only [delayStep]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ max 2 u := (uIcc_of_le (le_max_left 2 u) ▸ ht).2
    have hb : t - 1 ≤ (n : ℝ) + 2 := by
      have : max 2 u ≤ (n : ℝ) + 3 := max_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by
        push_cast at hu
        linarith)
      linarith
    change delayStep A (n + 1) (!b) (t - 1) / max 1 (t - 1) =
      delayStep A n (!b) (t - 1) / max 1 (t - 1)
    rw [ih (!b) hb]

theorem delayStep_eq_of_le (A : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (b : Bool) {u : ℝ} (hu : u ≤ (n : ℝ) + 2) :
    delayStep A m b u = delayStep A n b u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [delayStep_succ_eq A m b (le_trans hu (by exact_mod_cast Nat.add_le_add_right hnm 2))]
    exact ih

/-- A globally defined weighted function, requiring only finitely many integrals
at any argument. The ceiling is only a choice of a sufficiently large step. -/
def delayWeight (A : ℝ) (b : Bool) (u : ℝ) : ℝ :=
  delayStep A ⌈u⌉₊ b u

/-- Any sufficiently advanced finite step computes the global function exactly. -/
theorem delayWeight_eq_step (A : ℝ) (n : ℕ) (b : Bool) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 2) :
    delayWeight A b u = delayStep A n b u := by
  unfold delayWeight
  rcases le_total n ⌈u⌉₊ with h | h
  · exact delayStep_eq_of_le A h b hu
  · exact (delayStep_eq_of_le A h b (by linarith [Nat.le_ceil u])).symm

theorem delayWeight_initial (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayWeight A b u = delayInitial A b := by
  rw [delayWeight_eq_step A 0 b (by simpa using hu)]
  rfl

theorem continuous_delayWeight (A : ℝ) (b : Bool) :
    Continuous (delayWeight A b) := by
  rw [continuous_iff_continuousAt]
  intro u
  apply (continuous_delayStep A ⌈u⌉₊ b).continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (by linarith [Nat.le_ceil u] :
    u < (⌈u⌉₊ : ℝ) + 2)] with v hv
  exact delayWeight_eq_step A ⌈u⌉₊ b hv.le

/-- The globally continuous delayed integrand, including an irrelevant extension
to the left of the initial endpoint. -/
def delayIntegrand (A : ℝ) (b : Bool) (t : ℝ) : ℝ :=
  delayWeight A (!b) (t - 1) / max 1 (t - 1)

theorem continuous_delayIntegrand (A : ℝ) (b : Bool) :
    Continuous (delayIntegrand A b) :=
  ((continuous_delayWeight A (!b)).comp (continuous_id.sub continuous_const)).div
    (continuous_const.max (continuous_id.sub continuous_const))
    (fun _t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

/-- The global integral equation, proved by stabilization, not assumed. -/
theorem delayWeight_integral (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 ≤ u) :
    delayWeight A b u = delayInitial A b + ∫ t in (2 : ℝ)..u, delayIntegrand A b t := by
  rw [delayWeight_eq_step A (⌈u⌉₊ + 1) b (by
    have := Nat.le_ceil u
    push_cast
    linarith), delayStep, max_eq_right hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ≤ u := (uIcc_of_le hu ▸ ht).2
  unfold delayIntegrand
  rw [delayWeight_eq_step A ⌈u⌉₊ (!b) (by linarith [Nat.le_ceil u])]

/-- The unweighted delay pair with arbitrary initial upper constant. -/
def delayFunction (A : ℝ) (b : Bool) (u : ℝ) : ℝ := delayWeight A b u / u

theorem mul_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≠ 0) :
    u * delayFunction A b u = delayWeight A b u := by
  unfold delayFunction
  field_simp

theorem delayFunction_initial (A : ℝ) (b : Bool) {u : ℝ} (hu : u ≤ 2) :
    delayFunction A b u = delayInitial A b / u := by
  rw [delayFunction, delayWeight_initial A b hu]

theorem continuousOn_delayFunction (A : ℝ) (b : Bool) :
    ContinuousOn (delayFunction A b) (Ioi 0) :=
  (continuous_delayWeight A b).continuousOn.div continuousOn_id
    (fun _ hu => ne_of_gt hu)

theorem delayIntegrand_eq (A : ℝ) (b : Bool) {t : ℝ} (ht : 2 ≤ t) :
    delayIntegrand A b t = delayFunction A (!b) (t - 1) := by
  simp only [delayIntegrand, delayFunction, max_eq_right (by linarith : 1 ≤ t - 1)]

/-- Formula (5.7), for the explicitly constructed pair. -/
theorem delayFunction_integral_recurrence (A : ℝ) (b : Bool) {v u : ℝ}
    (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * delayFunction A b u =
      v * delayFunction A b v + ∫ t in v..u, delayFunction A (!b) (t - 1) := by
  have hu : 2 ≤ u := hv.trans hvu
  rw [mul_delayFunction A b (by linarith), mul_delayFunction A b (by linarith),
    delayWeight_integral A b hu, delayWeight_integral A b hv]
  have hc := continuous_delayIntegrand A b
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 2 v) (hc.intervalIntegrable v u)
  have heq : (∫ t in v..u, delayIntegrand A b t) =
      ∫ t in v..u, delayFunction A (!b) (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact delayIntegrand_eq A b (hv.trans (uIcc_of_le hvu ▸ ht).1)
  rw [heq] at hadd
  linarith

theorem hasDerivAt_delayWeight (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayWeight A b) (delayFunction A (!b) (u - 1)) u := by
  have hd := ((continuous_delayIntegrand A b).integral_hasStrictDerivAt 2 u).hasDerivAt
  rw [delayIntegrand_eq A b hu.le] at hd
  apply (hd.const_add (delayInitial A b)).congr_of_eventuallyEq
  filter_upwards [eventually_ge_nhds hu] with v hv
  exact delayWeight_integral A b hv


/-- The literal weighted differential equation (5.6) away from the endpoint. -/
theorem hasDerivAt_mul_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * delayFunction A b x)
      (delayFunction A (!b) (u - 1)) u := by
  apply (hasDerivAt_delayWeight A b hu).congr_of_eventuallyEq
  filter_upwards [eventually_ge_nhds hu] with v hv
  exact mul_delayFunction A b (by linarith)


theorem delayStep_nonneg {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (b : Bool) (u : ℝ) :
    0 ≤ delayStep A n b u := by
  have hi : ∀ b, 0 ≤ delayInitial A b := by
    intro b
    cases b
    · exact hA
    · exact le_rfl
  induction n generalizing b u with
  | zero => exact hi b
  | succ n ih =>
    apply add_nonneg (hi b)
    apply intervalIntegral.integral_nonneg (le_max_left 2 u)
    intro t _
    exact div_nonneg (ih (!b) (t - 1)) (le_trans zero_le_one (le_max_left _ _))

theorem delayInitial_le_delayWeight {A : ℝ} (hA : 0 ≤ A) (b : Bool) (u : ℝ) :
    delayInitial A b ≤ delayWeight A b u := by
  rw [delayWeight_eq_step A (⌈u⌉₊ + 1) b (by
    push_cast
    linarith [Nat.le_ceil u])]
  change delayInitial A b ≤ delayInitial A b + _
  apply le_add_of_nonneg_right
  apply intervalIntegral.integral_nonneg (le_max_left 2 u)
  intro t _
  exact div_nonneg (delayStep_nonneg hA _ (!b) (t - 1))
    (le_trans zero_le_one (le_max_left _ _))

/-- The normalization constant from Jurkat--Richert (5.5). -/
def jr1965DelayConstant : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

/-- The actual global upper delay function, constructed by finite method of steps.
This is not the legacy placeholder `sieveFunctionF`. -/
def jr1965F : ℝ → ℝ := delayFunction jr1965DelayConstant false

/-- The actual global lower delay function, constructed by finite method of steps.
This is not the legacy placeholder `sieveFunctionf`. -/
def jr1965f : ℝ → ℝ := delayFunction jr1965DelayConstant true

theorem jr1965F_initial {u : ℝ} (hu : u ≤ 2) :
    jr1965F u = 2 * Real.exp Real.eulerMascheroniConstant / u := by
  simpa [jr1965F, jr1965DelayConstant, delayInitial] using
    delayFunction_initial jr1965DelayConstant false hu

theorem jr1965f_initial {u : ℝ} (hu : u ≤ 2) : jr1965f u = 0 := by
  simpa [jr1965f, delayInitial] using delayFunction_initial jr1965DelayConstant true hu

theorem continuousOn_jr1965F : ContinuousOn jr1965F (Ioi 0) :=
  continuousOn_delayFunction jr1965DelayConstant false

theorem continuousOn_jr1965f : ContinuousOn jr1965f (Ioi 0) :=
  continuousOn_delayFunction jr1965DelayConstant true

theorem jr1965F_integral_recurrence {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * jr1965F u = v * jr1965F v + ∫ t in v..u, jr1965f (t - 1) :=
  delayFunction_integral_recurrence jr1965DelayConstant false hv hvu

theorem jr1965f_integral_recurrence {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u * jr1965f u = v * jr1965f v + ∫ t in v..u, jr1965F (t - 1) :=
  delayFunction_integral_recurrence jr1965DelayConstant true hv hvu

theorem hasDerivAt_mul_jr1965F {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * jr1965F x) (jr1965f (u - 1)) u :=
  hasDerivAt_mul_delayFunction jr1965DelayConstant false hu

theorem hasDerivAt_mul_jr1965f {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun x => x * jr1965f x) (jr1965F (u - 1)) u :=
  hasDerivAt_mul_delayFunction jr1965DelayConstant true hu


theorem jr1965F_pos {u : ℝ} (hu : 0 < u) : 0 < jr1965F u := by
  have hA : 0 < jr1965DelayConstant := by
    unfold jr1965DelayConstant
    positivity
  exact div_pos (lt_of_lt_of_le hA (delayInitial_le_delayWeight hA.le false u)) hu

theorem jr1965f_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ jr1965f u :=
  div_nonneg (delayStep_nonneg (by unfold jr1965DelayConstant; positivity) _ true u) hu.le

/-- The first extended upper formula, Jurkat--Richert (5.8). -/
theorem jr1965F_eq_of_le_three {u : ℝ} (hu : u ≤ 3) :
    jr1965F u = 2 * Real.exp Real.eulerMascheroniConstant / u := by
  by_cases hsmall : u ≤ 2
  · exact jr1965F_initial hsmall
  have hlarge : 2 ≤ u := le_of_lt (lt_of_not_ge hsmall)
  have h := jr1965F_integral_recurrence le_rfl hlarge
  have hz : (∫ t in (2 : ℝ)..u, jr1965f (t - 1)) = 0 := by
    calc
      _ = ∫ _t in (2 : ℝ)..u, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact jr1965f_initial (by have := (uIcc_of_le hlarge ▸ ht).2; linarith)
      _ = 0 := by simp
  rw [hz, jr1965F_initial le_rfl] at h
  apply (eq_div_iff (by linarith : u ≠ 0)).2
  nlinarith



/-- The constructed lower delay function agrees with the explicit formula
used in the sealed lower weight leaf on the full interval from 2 to 4.
Journal p. 1219 and Nathanson equations 9.27 and 9.28 cited there. -/
theorem jr1965f_eq_on_two_four {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    jr1965f u = 2 * exp eulerMascheroniConstant * log (u - 1) / u := by
  have hr := jr1965f_integral_recurrence le_rfl hu
  have hi : (∫ t in (2 : ℝ)..u, jr1965F (t - 1)) =
      2 * exp eulerMascheroniConstant * log (u - 1) := by
    calc
      _ = ∫ t in (2 : ℝ)..u, 2 * exp eulerMascheroniConstant * (1 / (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [jr1965F_eq_of_le_three (by
          have := (uIcc_of_le hu ▸ ht).2
          linarith)]
        ring
      _ = 2 * exp eulerMascheroniConstant * ∫ t in (2 : ℝ)..u, 1 / (t - 1) :=
        intervalIntegral.integral_const_mul _ _
      _ = 2 * exp eulerMascheroniConstant * log (u - 1) := by
        rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1 / t) 1]
        norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
        rw [integral_one_div_of_pos (by norm_num) (by linarith), div_one]
  rw [jr1965f_initial le_rfl, mul_zero, zero_add, hi] at hr
  exact (eq_div_iff (by linarith : u ≠ 0)).mpr (by simpa only [mul_comm] using hr)


/-! Additional narrow port from JurkatRichert1965ChenDelayMonotonicity.lean.
Same source commit, copyright and Apache 2.0 attribution as the construction above.
The common limit is not identified with one here. Table 1 stays OPEN. -/
def delayDifference (A : ℝ) (u : ℝ) : ℝ :=
  delayWeight A false u - delayWeight A true u

theorem continuous_delayDifference (A : ℝ) : Continuous (delayDifference A) :=
  (continuous_delayWeight A false).sub (continuous_delayWeight A true)

theorem delayDifference_initial (A : ℝ) {u : ℝ} (hu : u ≤ 2) :
    delayDifference A u = A := by
  simp [delayDifference, delayWeight_initial A _ hu, delayInitial]

theorem hasDerivAt_delayDifference (A : ℝ) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayDifference A) (-delayDifference A (u - 1) / (u - 1)) u := by
  apply ((hasDerivAt_delayWeight A false hu).sub
    (hasDerivAt_delayWeight A true hu)).congr_deriv
  simp only [Bool.not_false, Bool.not_true, delayFunction, delayDifference]
  ring

/-- The renewal identity, including its initial endpoint. -/
theorem delayDifference_renewal (A : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    (u - 1) * delayDifference A u = ∫ t in (u - 1)..u, delayDifference A t := by
  let P : ℝ → ℝ := fun x => ∫ t in (1 : ℝ)..x, delayDifference A t
  let R : ℝ → ℝ := fun x => (x - 1) * delayDifference A x - (P x - P (x - 1))
  have hc := continuous_delayDifference A
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (fun a b => hc.intervalIntegrable a b) 1
  have hR : Continuous R := ((continuous_id.sub continuous_const).mul hc).sub
    (hP.sub (hP.comp (continuous_id.sub continuous_const)))
  have hd (x : ℝ) (hx : x ∈ interior (Set.Icc 2 u)) : HasDerivAt R 0 x := by
    rw [interior_Icc] at hx
    have hdx := hasDerivAt_delayDifference A hx.1
    have hp := (hc.integral_hasStrictDerivAt 1 x).hasDerivAt
    have hq := ((hc.integral_hasStrictDerivAt 1 (x - 1)).hasDerivAt).comp x
      ((hasDerivAt_id x).sub_const 1)
    apply ((((hasDerivAt_id x).sub_const 1).mul hdx).sub (hp.sub hq)).congr_deriv
    dsimp
    field_simp [ne_of_gt (show 0 < x - 1 by linarith [hx.1])]
    ring
  have hanti : AntitoneOn R (Set.Icc 2 u) := antitoneOn_of_deriv_nonpos (convex_Icc ..)
    hR.continuousOn (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv.le)
  have hmono : MonotoneOn R (Set.Icc 2 u) := monotoneOn_of_deriv_nonneg (convex_Icc ..)
    hR.continuousOn (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv.ge)
  have heq : R u = R 2 := le_antisymm
    (hanti ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu)
    (hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu)
  have hi : P 2 = A := by
    change (∫ t in (1 : ℝ)..2, delayDifference A t) = A
    calc
      _ = ∫ _t in (1 : ℝ)..2, A := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact delayDifference_initial A (by
          have := (uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2) ▸ ht).2
          exact this)
      _ = A := by norm_num
  have hbase : R 2 = 0 := by
    dsimp [R]
    rw [delayDifference_initial A le_rfl, hi]
    norm_num [P]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 1 (u - 1)) (hc.intervalIntegrable (u - 1) u)
  rw [hbase] at heq
  dsimp [R, P] at heq
  linarith

private theorem exists_first_zero_on {H : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Set.Icc a b)) (ha : 0 < H a) (hb : H b ≤ 0) :
    ∃ c ∈ Set.Ioc a b, H c = 0 ∧ ∀ x ∈ Set.Ico a c, 0 < H x := by
  have hex : ∃ x ∈ Set.Icc a b, H x = 0 :=
    intermediate_value_Icc' hab hc ⟨hb, ha.le⟩
  let S := Set.Icc a b ∩ H ⁻¹' ({0} : Set ℝ)
  have hclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  have hne : S.Nonempty := by
    rcases hex with ⟨x, hx, hz⟩
    exact ⟨x, hx, hz⟩
  obtain ⟨c, hcS, hmin⟩ := hcompact.exists_isMinOn hne continuous_id.continuousOn
  have hcz : H c = 0 := hcS.2
  have hac : a < c := lt_of_le_of_ne hcS.1.1 (by
    intro h
    rw [← h] at hcz
    linarith)
  refine ⟨c, ⟨hac, hcS.1.2⟩, hcz, ?_⟩
  intro x hx
  by_contra hpos
  have hxnonpos : H x ≤ 0 := le_of_not_gt hpos
  obtain ⟨y, hy, hyz⟩ := intermediate_value_Icc' hx.1
    (hc.mono (Icc_subset_Icc le_rfl (hx.2.le.trans hcS.1.2))) ⟨hxnonpos, ha.le⟩
  have hcy : c ≤ y := hmin ⟨⟨hy.1, hy.2.trans (hx.2.le.trans hcS.1.2)⟩, hyz⟩
  linarith [hy.2, hx.2]

/-- Strict positivity of the weighted difference, by its renewal identity. -/
theorem delayDifference_pos {A : ℝ} (hA : 0 < A) (u : ℝ) :
    0 < delayDifference A u := by
  by_cases hu : u ≤ 2
  · simpa [delayDifference_initial A hu] using hA
  by_contra hpos
  have hu' : 2 ≤ u := (lt_of_not_ge hu).le
  obtain ⟨c, hc, hzero, hbefore⟩ := exists_first_zero_on hu'
    (continuous_delayDifference A).continuousOn
    (by simpa [delayDifference_initial A le_rfl] using hA) (le_of_not_gt hpos)
  have hposbefore (t : ℝ) (ht : t < c) : 0 < delayDifference A t := by
    by_cases ht2 : t ≤ 2
    · simpa [delayDifference_initial A ht2] using hA
    · exact hbefore t ⟨(lt_of_not_ge ht2).le, ht⟩
  have hint : 0 < ∫ t in (c - 1)..c, delayDifference A t := by
    apply intervalIntegral.integral_pos (by linarith) (continuous_delayDifference A).continuousOn
    · intro t ht
      rcases ht.2.eq_or_lt with h | h
      · rw [h, hzero]
      · exact (hposbefore t h).le
    · exact ⟨c - 1, ⟨le_rfl, by linarith⟩, hposbefore _ (by linarith)⟩
  have hrenew := delayDifference_renewal A hc.1.le
  rw [hzero, mul_zero] at hrenew
  linarith

/-- The strict gap (5.11), for the constructed pair and positive normalization. -/
theorem delayFunction_lower_lt_upper {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    delayFunction A true u < delayFunction A false u := by
  have h := delayDifference_pos hA u
  exact (div_lt_div_iff_of_pos_right hu).2 (sub_pos.mp h)

theorem jr1965f_lt_jr1965F {u : ℝ} (hu : 0 < u) : jr1965f u < jr1965F u :=
  delayFunction_lower_lt_upper (by unfold jr1965DelayConstant; positivity) hu

/-- The unweighted differential equation on the open delay range. -/
theorem hasDerivAt_delayFunction (A : ℝ) (b : Bool) {u : ℝ} (hu : 2 < u) :
    HasDerivAt (delayFunction A b)
      ((delayFunction A (!b) (u - 1) - delayFunction A b u) / u) u := by
  apply ((hasDerivAt_delayWeight A b hu).div (hasDerivAt_id u)
    (ne_of_gt (show 0 < u by linarith))).congr_deriv
  dsimp [delayFunction]
  field_simp

theorem hasDerivAt_jr1965F {u : ℝ} (hu : 2 < u) :
    HasDerivAt jr1965F ((jr1965f (u - 1) - jr1965F u) / u) u :=
  hasDerivAt_delayFunction jr1965DelayConstant false hu

theorem hasDerivAt_jr1965f {u : ℝ} (hu : 2 < u) :
    HasDerivAt jr1965f ((jr1965F (u - 1) - jr1965f u) / u) u :=
  hasDerivAt_delayFunction jr1965DelayConstant true hu

private theorem hasDerivAt_jr1965F_initial {u : ℝ} (hu : 0 < u) (hu3 : u < 3) :
    HasDerivAt jr1965F (-jr1965DelayConstant / u ^ 2) u := by
  have hd := (hasDerivAt_const u jr1965DelayConstant).div
    (hasDerivAt_id u) (ne_of_gt hu)
  have hd' : HasDerivAt (fun x : ℝ => jr1965DelayConstant / x)
      (-jr1965DelayConstant / u ^ 2) u := hd.congr_deriv (by simp)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hu3] with x hx
  exact jr1965F_eq_of_le_three hx.le

private theorem jr1965F_antitoneOn_before {c : ℝ}
    (hbefore : ∀ x ∈ Set.Ico 3 c, jr1965f (x - 1) < jr1965F x) :
    AntitoneOn jr1965F (Set.Ioc 0 c) := by
  have hd (x : ℝ) (hx : x ∈ interior (Set.Ioc 0 c)) :
      DifferentiableAt ℝ jr1965F x ∧ deriv jr1965F x ≤ 0 := by
    rw [interior_Ioc] at hx
    by_cases hx2 : x ≤ 2
    · have h := hasDerivAt_jr1965F_initial hx.1 (by linarith)
      refine ⟨h.differentiableAt, ?_⟩
      rw [h.deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by
        unfold jr1965DelayConstant; positivity))
        (sq_nonneg x)
    · have hx2' : 2 < x := lt_of_not_ge hx2
      have h := hasDerivAt_jr1965F hx2'
      refine ⟨h.differentiableAt, ?_⟩
      rw [h.deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ hx.1.le
      apply sub_nonpos.mpr
      by_cases hx3 : x ≤ 3
      · rw [jr1965f_initial (by linarith)]
        exact (jr1965F_pos hx.1).le
      · exact (hbefore x ⟨(lt_of_not_ge hx3).le, hx.2⟩).le
  exact antitoneOn_of_deriv_nonpos (convex_Ioc ..)
    (continuousOn_jr1965F.mono (fun _ hx => hx.1))
    (fun x hx => (hd x hx).1.differentiableWithinAt) (fun x hx => (hd x hx).2)

private theorem jr1965f_monotoneOn_of_upper_antitone {c : ℝ}
    (hF : AntitoneOn jr1965F (Set.Ioc 0 c)) : MonotoneOn jr1965f (Set.Icc 2 c) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc ..)
    (continuousOn_jr1965f.mono (fun _ hx => lt_of_lt_of_le (by norm_num) hx.1))
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_jr1965f hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_jr1965f hx.1).deriv]
    apply div_nonneg _ (by linarith [hx.1])
    apply sub_nonneg.mpr
    exact (jr1965f_lt_jr1965F (by linarith [hx.1])).le.trans
      (hF ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hx.1], hx.2.le⟩ (by linarith))

/-- The delayed lower function stays strictly below the current upper function.
At a first failure, the upper function is decreasing up to that point, hence the
lower one is increasing, contradicting the strict upper/lower gap. -/
theorem jr1965f_sub_one_lt_jr1965F {u : ℝ} (hu : 2 ≤ u) :
    jr1965f (u - 1) < jr1965F u := by
  by_cases hu3 : u ≤ 3
  · rw [jr1965f_initial (by linarith)]
    exact jr1965F_pos (by linarith)
  let H : ℝ → ℝ := fun x => jr1965F x - jr1965f (x - 1)
  have hcont : ContinuousOn H (Set.Icc 3 u) := by
    apply (continuousOn_jr1965F.mono (fun _ hx =>
      lt_of_lt_of_le (by norm_num) hx.1)).sub
    exact continuousOn_jr1965f.comp (continuousOn_id.sub continuousOn_const)
      (fun x hx => by change 0 < x - 1; linarith [hx.1])
  have h3 : 0 < H 3 := by
    dsimp [H]
    rw [jr1965f_initial (by norm_num), sub_zero]
    exact jr1965F_pos (by norm_num)
  by_contra h
  have huH : H u ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
  obtain ⟨c, hc, hzero, hbefore⟩ :=
    exists_first_zero_on (lt_of_not_ge hu3).le hcont h3 huH
  have hF := jr1965F_antitoneOn_before
    (fun x hx => sub_pos.mp (hbefore x hx))
  have hf := jr1965f_monotoneOn_of_upper_antitone hF
  have hf' : jr1965f (c - 1) ≤ jr1965f c :=
    hf ⟨by linarith [hc.1], by linarith⟩
      ⟨by linarith [hc.1], le_rfl⟩ (by linarith)
  have hgap := jr1965f_lt_jr1965F (show 0 < c by linarith [hc.1])
  dsimp [H] at hzero
  linarith

/-- The upper function is decreasing on the entire positive half-line. -/
theorem antitoneOn_jr1965F : AntitoneOn jr1965F (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact jr1965F_antitoneOn_before
    (fun z hz => jr1965f_sub_one_lt_jr1965F (by linarith [hz.1]))
    ⟨hx, hxy⟩ ⟨hy, le_rfl⟩ hxy

/-- The lower function is increasing on the entire positive half-line. -/
theorem monotoneOn_jr1965f : MonotoneOn jr1965f (Set.Ioi 0) := by
  intro x hx y hy hxy
  by_cases hx2 : x ≤ 2
  · rw [jr1965f_initial hx2]
    exact jr1965f_nonneg hy
  · exact jr1965f_monotoneOn_of_upper_antitone
      (antitoneOn_jr1965F.mono (fun _ hz => hz.1))
      ⟨(lt_of_not_ge hx2).le, hxy⟩ ⟨by linarith, le_rfl⟩ hxy


theorem jr1965F_le_delayConstant {u : ℝ} (hu : 1 ≤ u) :
    jr1965F u ≤ jr1965DelayConstant := by
  have h := antitoneOn_jr1965F (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show u ∈ Set.Ioi 0 from lt_of_lt_of_le zero_lt_one hu) hu
  simpa [jr1965F_initial (by norm_num : (1 : ℝ) ≤ 2), jr1965DelayConstant] using h

theorem jr1965f_le_delayConstant {u : ℝ} (hu : 1 ≤ u) :
    jr1965f u ≤ jr1965DelayConstant :=
  (jr1965f_lt_jr1965F (lt_of_lt_of_le zero_lt_one hu)).le.trans
    (jr1965F_le_delayConstant hu)



#print axioms continuous_delayDifference
#print axioms delayDifference_initial
#print axioms hasDerivAt_delayDifference
#print axioms delayDifference_renewal
#print axioms exists_first_zero_on
#print axioms delayDifference_pos
#print axioms delayFunction_lower_lt_upper
#print axioms jr1965f_lt_jr1965F
#print axioms hasDerivAt_delayFunction
#print axioms hasDerivAt_jr1965F
#print axioms hasDerivAt_jr1965f
#print axioms hasDerivAt_jr1965F_initial
#print axioms jr1965F_antitoneOn_before
#print axioms jr1965f_monotoneOn_of_upper_antitone
#print axioms jr1965f_sub_one_lt_jr1965F
#print axioms antitoneOn_jr1965F
#print axioms monotoneOn_jr1965f
#print axioms jr1965F_le_delayConstant
#print axioms jr1965f_le_delayConstant

/-! Additional narrow port from JurkatRichert1965ChenDelayDecay.lean.
Same source commit, copyright and Apache 2.0 attribution as the construction above.
The common limit is not identified with one here. Table 1 stays OPEN. -/
theorem antitone_delayDifference {A : ℝ} (hA : 0 < A) :
    Antitone (delayDifference A) := by
  have hanti : AntitoneOn (delayDifference A) (Set.Ici 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
      (continuous_delayDifference A).continuousOn
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      exact (hasDerivAt_delayDifference A hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      rw [(hasDerivAt_delayDifference A hu).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (delayDifference_pos hA _).le) (by linarith)
  intro u v huv
  by_cases hu : 2 ≤ u
  · exact hanti hu (hu.trans huv) huv
  · by_cases hv : v ≤ 2
    · rw [delayDifference_initial A hv, delayDifference_initial A (lt_of_not_ge hu).le]
    · have h := hanti (show (2 : ℝ) ∈ Set.Ici 2 by norm_num)
        (show v ∈ Set.Ici 2 from (lt_of_not_ge hv).le) (lt_of_not_ge hv).le
      rw [delayDifference_initial A (lt_of_not_ge hu).le]
      simpa only [delayDifference_initial A le_rfl] using h

/-- The renewal average is bounded by its left endpoint. -/
theorem mul_delayDifference_le_previous {A u : ℝ} (hA : 0 < A) (hu : 2 ≤ u) :
    (u - 1) * delayDifference A u ≤ delayDifference A (u - 1) := by
  rw [delayDifference_renewal A hu]
  calc
    _ ≤ ∫ _t in (u - 1)..u, delayDifference A (u - 1) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_delayDifference A).intervalIntegrable _ _)
        (intervalIntegrable_const)
      intro t ht
      exact antitone_delayDifference hA ht.1
    _ = delayDifference A (u - 1) := by simp

theorem antitoneOn_exp_mul_delayDifference {A : ℝ} (hA : 0 < A) :
    AntitoneOn (fun u => Real.exp u * delayDifference A u) (Set.Ici 2) := by
  have hd (u : ℝ) (hu : 2 < u) :
      HasDerivAt (fun u => Real.exp u * delayDifference A u)
        (Real.exp u * delayDifference A u +
          Real.exp u * (-delayDifference A (u - 1) / (u - 1))) u :=
    (Real.hasDerivAt_exp u).mul (hasDerivAt_delayDifference A hu)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
    (Real.continuous_exp.mul (continuous_delayDifference A)).continuousOn
  · intro u hu
    rw [interior_Ici, Set.mem_Ioi] at hu
    exact (hd u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici, Set.mem_Ioi] at hu
    change deriv (fun u => Real.exp u * delayDifference A u) u ≤ 0
    rw [(hd u hu).deriv]
    have h : delayDifference A u ≤ delayDifference A (u - 1) / (u - 1) :=
      (le_div_iff₀ (show 0 < u - 1 by linarith)).2
      (by simpa [mul_comm] using mul_delayDifference_le_previous hA hu.le)
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos u).le
    rw [neg_div]
    nlinarith

theorem delayDifference_le_exp {A u : ℝ} (hA : 0 < A) :
    delayDifference A u ≤ A * Real.exp 2 * Real.exp (-u) := by
  by_cases hu2 : 2 ≤ u
  · have h := antitoneOn_exp_mul_delayDifference hA
      (show (2 : ℝ) ∈ Set.Ici 2 by norm_num) hu2 hu2
    dsimp only at h
    rw [delayDifference_initial A le_rfl] at h
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-u)).le
    have heq : Real.exp u * delayDifference A u * Real.exp (-u) =
        delayDifference A u := by
      rw [mul_right_comm, ← Real.exp_add]
      simp
    rw [heq] at h'
    simpa only [mul_comm (Real.exp 2) A] using h'
  · rw [delayDifference_initial A (lt_of_not_ge hu2).le, mul_assoc, ← Real.exp_add]
    exact le_mul_of_one_le_right hA.le
      (Real.one_le_exp_iff.mpr (by linarith))

/-- One constant controls the upper/lower gap on the entire source range. -/
theorem jr1965F_sub_jr1965f_le_exp {u : ℝ} (hu : 1 ≤ u) :
    jr1965F u - jr1965f u ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  have hA : 0 < jr1965DelayConstant := by unfold jr1965DelayConstant; positivity
  have hgap : jr1965F u - jr1965f u = delayDifference jr1965DelayConstant u / u := by
    simp [jr1965F, jr1965f, delayFunction, delayDifference, sub_div]
  rw [hgap]
  exact (div_le_self (delayDifference_pos hA u).le hu).trans
    (delayDifference_le_exp hA)

/-- The common limit is constructed from the lower function, not postulated. -/
def jr1965CommonLimit : ℝ := sSup (jr1965f '' Set.Ici 1)

private theorem bddAbove_jr1965f_image : BddAbove (jr1965f '' Set.Ici 1) :=
  ⟨jr1965DelayConstant, by
    rintro _ ⟨u, hu, rfl⟩
    exact jr1965f_le_delayConstant hu⟩

theorem jr1965f_le_commonLimit {u : ℝ} (hu : 1 ≤ u) :
    jr1965f u ≤ jr1965CommonLimit :=
  le_csSup bddAbove_jr1965f_image ⟨u, hu, rfl⟩

theorem commonLimit_le_jr1965F {u : ℝ} (hu : 1 ≤ u) :
    jr1965CommonLimit ≤ jr1965F u := by
  unfold jr1965CommonLimit
  apply csSup_le (s := jr1965f '' Set.Ici 1) ⟨jr1965f 1, 1, by norm_num, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  change 1 ≤ t at ht
  rcases le_total t u with h | h
  · exact (monotoneOn_jr1965f (by change 0 < t; linarith)
      (by change 0 < u; linarith) h).trans
      (jr1965f_lt_jr1965F (by linarith)).le
  · exact (jr1965f_lt_jr1965F (by linarith : 0 < t)).le.trans
      (antitoneOn_jr1965F (by change 0 < u; linarith)
        (by change 0 < t; linarith) h)

theorem abs_jr1965F_sub_commonLimit_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965F u - jr1965CommonLimit| ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (commonLimit_le_jr1965F hu))]
  exact (sub_le_sub_left (jr1965f_le_commonLimit hu) _).trans
    (jr1965F_sub_jr1965f_le_exp hu)

theorem abs_jr1965f_sub_commonLimit_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965f u - jr1965CommonLimit| ≤
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (jr1965f_le_commonLimit hu)), neg_sub]
  exact (sub_le_sub_right (commonLimit_le_jr1965F hu) _).trans
    (jr1965F_sub_jr1965f_le_exp hu)

theorem tendsto_jr1965F_commonLimit :
    Tendsto jr1965F atTop (𝓝 jr1965CommonLimit) := by
  have hbound : Tendsto (fun u : ℝ =>
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (jr1965DelayConstant * Real.exp 2)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  simpa [Real.dist_eq] using abs_jr1965F_sub_commonLimit_le_exp hu

theorem tendsto_jr1965f_commonLimit :
    Tendsto jr1965f atTop (𝓝 jr1965CommonLimit) := by
  have hbound : Tendsto (fun u : ℝ =>
      jr1965DelayConstant * Real.exp 2 * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (jr1965DelayConstant * Real.exp 2)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  simpa [Real.dist_eq] using abs_jr1965f_sub_commonLimit_le_exp hu


#print axioms antitone_delayDifference
#print axioms mul_delayDifference_le_previous
#print axioms antitoneOn_exp_mul_delayDifference
#print axioms delayDifference_le_exp
#print axioms jr1965F_sub_jr1965f_le_exp
#print axioms bddAbove_jr1965f_image
#print axioms jr1965f_le_commonLimit
#print axioms commonLimit_le_jr1965F
#print axioms abs_jr1965F_sub_commonLimit_le_exp
#print axioms abs_jr1965f_sub_commonLimit_le_exp
#print axioms tendsto_jr1965F_commonLimit
#print axioms tendsto_jr1965f_commonLimit

end RosserDelay234


end
end LeanLab.BS2022GRH.DecompC169d

#print axioms LeanLab.BS2022GRH.DecompC169d.weighted_actual_eq
#print axioms LeanLab.BS2022GRH.DecompC169d.weighted_error_le
#print axioms LeanLab.BS2022GRH.DecompC169d.upper_of_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.lower_of_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.upper_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.lower_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.linearSieveT4_8349

#print axioms LeanLab.BS2022GRH.DecompC169d.abs_rosserSubsetWeight

#print axioms LeanLab.BS2022GRH.DecompC169d.prime_subset_squarefree

#print axioms LeanLab.BS2022GRH.DecompC169d.moebius_prime_subset

#print axioms LeanLab.BS2022GRH.DecompC169d.rosserSubsetWeight_eq

#print axioms LeanLab.BS2022GRH.DecompC169d.rosserSupport_subset

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_weightValue_powerset

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_powerset_bounds

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_pointwise

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_upper_model

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_lower_model

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayStep_initial

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuous_delayStep

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayStep_succ_eq

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayStep_eq_of_le

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayWeight_eq_step

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayWeight_initial

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuous_delayWeight

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuous_delayIntegrand

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayWeight_integral

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.mul_delayFunction

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayFunction_initial

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuousOn_delayFunction

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayIntegrand_eq

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayFunction_integral_recurrence

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.hasDerivAt_delayWeight

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.hasDerivAt_mul_delayFunction

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayStep_nonneg

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.delayInitial_le_delayWeight

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965F_initial

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965f_initial

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuousOn_jr1965F

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.continuousOn_jr1965f

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965F_integral_recurrence

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965f_integral_recurrence

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.hasDerivAt_mul_jr1965F

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.hasDerivAt_mul_jr1965f

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965F_pos

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965f_nonneg

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965F_eq_of_le_three

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_nontrivial_instance234

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_pointwise_instance234

#print axioms LeanLab.BS2022GRH.DecompC169d.weightedModel_eq_rosserPrimeModel

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_model_upper_of_prime

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_model_lower_of_prime

#print axioms LeanLab.BS2022GRH.DecompC169d.RosserDelay234.jr1965f_eq_on_two_four

#print axioms LeanLab.BS2022GRH.DecompC169d.sum_powerset_split234

#print axioms LeanLab.BS2022GRH.DecompC169d.rosserPrimeModel_factor

#print axioms LeanLab.BS2022GRH.DecompC169d.rosserPrimeModel_exact_of_small

#print axioms LeanLab.BS2022GRH.DecompC169d.weightedModel_exact_of_small

#print axioms LeanLab.BS2022GRH.DecompC169d.rosser_selected_models_of_small234

#print axioms LeanLab.BS2022GRH.DecompC169d.mem_rosserSupport_iff

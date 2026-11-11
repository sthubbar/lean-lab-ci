/- AI wrote this Lean code for CODEX task327. Goldbach is open.
Finite stopping terms for the two sealed Rosser model leaves.
BJS arXiv 2207.09452 Section 2.4, current version pp. 10 and 14.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.DecompC169d
import LeanLab.BS2022GRH.Envelope327

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d
noncomputable section

/-- The finite first stopping term T_n of BJS p. 10 display 28.
A decreasing subset is stopped at its last prime. All earlier tests of the
same parity pass. Zero is excluded. The terminal test is non-strict. -/
def stoppingTerm (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ T ∈ S.powerset.filter (fun T => 0 < n ∧ T.card = n ∧
      D ≤ ((∏ p ∈ T, p : ℕ) : ℝ) * (((T.sort (· ≥ ·)).getD (n - 1) 0 : ℝ) ^ 2) ∧
      ∀ k < n - 1, k % 2 = (n - 1) % 2 →
        ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
          (((T.sort (· ≥ ·)).getD k 0 : ℝ) ^ 3) < D),
    (∏ p ∈ T, g p) *
      ∏ p ∈ S.filter (fun p => p < (T.sort (· ≥ ·)).getD (n - 1) 0), (1 - g p)

/-- The individual delay terms of BJS p. 6 displays 15 to 17.
Index zero is unused. The odd terms use the lower endpoint max of s and three.
The integrals are ordinary integrals on the upper half line. -/
def delayTerm : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => max (3 - s) 0 / s
  | n + 2, s =>
      (∫ t in Set.Ioi (if (n + 2) % 2 = 1 then max s 3 else s),
        delayTerm (n + 1) (t - 1)) / s

/-- Nonnegative prime densities give nonnegative stopping terms.
BJS p. 10 display 28. -/
theorem stoppingTerm_nonneg (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (n : ℕ)
    (hg : ∀ p ∈ S, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ stoppingTerm S D g n := by
  unfold stoppingTerm
  apply sum_nonneg
  intro T hT
  have hsub := mem_powerset.mp (mem_filter.mp hT).1
  apply mul_nonneg
  · exact prod_nonneg (fun p hp => (hg p (hsub hp)).1)
  · exact prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_filter.mp hp).1).2)

/-- A stopping term beyond the size of the finite prime set is zero.
BJS p. 10 display 28. -/
theorem stoppingTerm_eq_zero_of_card_lt (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ)
    (n : ℕ) (hn : S.card < n) : stoppingTerm S D g n = 0 := by
  unfold stoppingTerm
  apply sum_eq_zero
  intro T hT
  obtain ⟨hTS, _, hcard, _⟩ := mem_filter.mp hT
  have := card_le_card (mem_powerset.mp hTS)
  omega

/-- The unused stopping term at index zero is zero, p. 10 display 28. -/
theorem stoppingTerm_zero (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) :
    stoppingTerm S D g 0 = 0 := by simp [stoppingTerm]

/-- The delay terms are nonnegative on the parity domains in the paper.
BJS p. 6 displays 15 to 17. -/
theorem delayTerm_nonneg (n : ℕ) (s : ℝ)
    (hs : if n % 2 = 1 then 1 ≤ s else 2 ≤ s) : 0 ≤ delayTerm n s := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => simp [delayTerm]
  | one =>
      norm_num at hs
      simp only [delayTerm]
      positivity
  | more n ih0 ih1 =>
      rw [delayTerm]
      apply div_nonneg
      · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        intro t ht
        have ht' := Set.mem_Ioi.mp ht
        apply ih1
        by_cases ho : (n + 2) % 2 = 1
        · have hp : (n + 1) % 2 ≠ 1 := by omega
          rw [if_neg hp]
          rw [if_pos ho] at ht'
          have := le_max_right s 3
          linarith
        · have hp : (n + 1) % 2 = 1 := by omega
          rw [if_pos hp]
          rw [if_neg ho] at ht' hs
          linarith
      · split_ifs at hs <;> linarith

/-- Each delay term vanishes at and above its finite support endpoint.
BJS p. 8 discussion before display 21. -/
theorem delayTerm_eq_zero_of_endpoint (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 2 ≤ s) :
    delayTerm n s = 0 := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => simp [delayTerm]
  | one =>
      simp only [Nat.cast_one] at hs
      simp [delayTerm, max_eq_right (by linarith : 3 - s ≤ 0)]
  | more n ih0 ih1 =>
      rw [delayTerm, MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero, zero_div]
      intro t ht
      apply ih1
      have ht' := Set.mem_Ioi.mp ht
      by_cases ho : (n + 2) % 2 = 1
      · rw [if_pos ho] at ht'
        have := le_max_left s 3
        push_cast at hs ⊢
        linarith
      · rw [if_neg ho] at ht'
        push_cast at hs ⊢
        linarith

/-- LEAF. Scalar partial sums of the individual delay functions.
BJS p. 6 displays 13 and 14 and p. 5 display 8.
Positivity and the infinite series give these finite inequalities.
There is no prime set, density premise, Rosser coefficient or error constant. -/
theorem delay_partial_sums (s : ℝ) (N : ℕ) :
    (1 ≤ s → s ≤ 3 →
      (∑ n ∈ range N, if n % 2 = 1 then delayTerm n s else 0) ≤
        2 * exp eulerMascheroniConstant / s - 1) ∧
    (2 ≤ s → s ≤ 4 →
      (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) ≤
        1 - 2 * exp eulerMascheroniConstant * log (s - 1) / s) := by
  sorry

/-! ## The descending list of a prime set -/

/-- Inserting a new least element appends it to the descending list. -/
private theorem sort_insert_min (T : Finset ℕ) (p : ℕ) (hp : p ∉ T)
    (hlt : ∀ q ∈ T, p < q) :
    (insert p T).sort (· ≥ ·) = T.sort (· ≥ ·) ++ [p] := by
  have hpair : (T.sort (· ≥ ·) ++ [p]).Pairwise (· ≥ ·) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort T (· ≥ ·), by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact (hlt a ((Finset.mem_sort (· ≥ ·)).mp ha)).le
  have hnd : (T.sort (· ≥ ·) ++ [p]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.sort_nodup T (· ≥ ·), by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact (hlt a ((Finset.mem_sort (· ≥ ·)).mp ha)).ne.symm
  have hto : (T.sort (· ≥ ·) ++ [p]).toFinset = insert p T := by
    rw [List.toFinset_append, Finset.sort_toFinset]
    simp
  have h := (List.toFinset_sort (· ≥ ·) hnd).mpr hpair
  rwa [hto] at h

/-- The product of the descending list is the product over the set. -/
private theorem prod_sort (T : Finset ℕ) :
    (T.sort (· ≥ ·)).prod = ∏ p ∈ T, p :=
  (Finset.sort_perm_toList T (· ≥ ·)).prod_eq.trans (Finset.prod_toList T)

/-- Earlier entries of the descending list survive appending a smaller element. -/
private theorem getD_append_lt (L : List ℕ) (p k : ℕ) (hk : k < L.length) :
    (L ++ [p]).getD k 0 = L.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hk]

/-- The last entry of the extended descending list is the new element. -/
private theorem getD_append_length (L : List ℕ) (p : ℕ) :
    (L ++ [p]).getD L.length 0 = p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Prefix products survive appending a smaller element. -/
private theorem prod_take_append (L : List ℕ) (p k : ℕ) (hk : k ≤ L.length) :
    ((L ++ [p]).take k).prod = (L.take k).prod := by
  rw [List.take_append_of_le_length hk]

/-- Appending an element multiplies the list product. -/
private theorem prod_append_eq (L : List ℕ) (p : ℕ) :
    (L ++ [p]).prod = L.prod * p := by
  rw [List.prod_append]
  simp

/-- The last entry of the descending list is a member of the set. -/
private theorem getD_last_mem (T : Finset ℕ) (n : ℕ) (hn : 0 < n) (hc : T.card = n) :
    (T.sort (· ≥ ·)).getD (n - 1) 0 ∈ T := by
  have hlen : (T.sort (· ≥ ·)).length = n := by
    rw [Finset.length_sort, hc]
  have hidx : n - 1 < (T.sort (· ≥ ·)).length := by omega
  rw [List.getD_eq_getElem (T.sort (· ≥ ·)) 0 hidx]
  exact (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hidx)

/-! ## The Rosser weight of a set of distinct primes -/

/-- The Rosser weight of a set of distinct primes is its Moebius sign exactly
when every parity-selected cube test passes. -/
private theorem rosserWeight_prime_set (T : Finset ℕ) (D : ℝ) (b : Bool)
    (hprime : ∀ q ∈ T, q.Prime) :
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ q ∈ T, q) =
      if (∀ k < T.card, (b = true ↔ k % 2 = 0) →
        ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
          ((((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3) < D)
      then (-1 : ℝ) ^ T.card else 0 := by
  have hs := prime_subset_squarefree T hprime
  have hmu := moebius_prime_subset T hprime
  have hpf := Nat.primeFactors_prod hprime
  unfold LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight
  simp only [hs, true_and, LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes, hpf,
    Finset.length_sort, hmu]

/-- Adding a new least prime to a set of distinct primes, upper weight. -/
private theorem rosserWeight_mul_min_true (T : Finset ℕ) (D : ℝ) (p : ℕ)
    (hp : p ∉ T) (hlt : ∀ q ∈ T, p < q) (hprime : ∀ q ∈ T, q.Prime)
    (hpp : p.Prime) :
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true ((∏ q ∈ T, q) * p) =
      if (T.card % 2 = 0 → ((∏ q ∈ T, q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D)
        then -LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ q ∈ T, q)
        else 0 := by
  have hd := prime_subset_squarefree T hprime
  have hmin : ∀ q ∈ (∏ q ∈ T, q).primeFactors, p < q := by
    rw [Nat.primeFactors_prod hprime]
    exact hlt
  rw [LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight_mul_smallest D true hd hpp hmin]
  simp only [LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes, Nat.primeFactors_prod hprime,
    Finset.length_sort, true_iff]

/-- Adding a new least prime to a set of distinct primes, lower weight. -/
private theorem rosserWeight_mul_min_false (T : Finset ℕ) (D : ℝ) (p : ℕ)
    (hp : p ∉ T) (hlt : ∀ q ∈ T, p < q) (hprime : ∀ q ∈ T, q.Prime)
    (hpp : p.Prime) :
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false ((∏ q ∈ T, q) * p) =
      if (¬(T.card % 2 = 0) → ((∏ q ∈ T, q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D)
        then -LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ q ∈ T, q)
        else 0 := by
  have hd := prime_subset_squarefree T hprime
  have hmin : ∀ q ∈ (∏ q ∈ T, q).primeFactors, p < q := by
    rw [Nat.primeFactors_prod hprime]
    exact hlt
  rw [LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight_mul_smallest D false hd hpp hmin]
  simp only [LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes, Nat.primeFactors_prod hprime,
    Finset.length_sort, Bool.false_eq_true, false_iff]

/-- A shifted Euler product splits off the new least prime. -/
private theorem prod_filter_lt_insert (T : Finset ℕ) (g : ℕ → ℝ) (p m : ℕ)
    (hp : p ∉ T) (hpm : p < m) :
    ∏ q ∈ (insert p T).filter (fun q => q < m), (1 - g q) =
      (1 - g p) * ∏ q ∈ T.filter (fun q => q < m), (1 - g q) := by
  rw [Finset.filter_insert, if_pos hpm, Finset.prod_insert]
  intro h
  rw [Finset.mem_filter] at h
  exact hp h.1

/-- The stopping predicate of the enlarged set is the predicate on the smaller
set with the last cube test moved to the new least prime. -/
private theorem stopPred_insert (T : Finset ℕ) (D : ℝ) (p n : ℕ)
    (hp : p ∉ T) (hlt : ∀ q ∈ T, p < q) :
    (0 < n ∧ (insert p T).card = n ∧
        D ≤ ((∏ q ∈ insert p T, q : ℕ) : ℝ) *
          (((((insert p T).sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2) ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          (((((insert p T).sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((((insert p T).sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3) < D)
      ↔ (0 < n ∧ T.card = n - 1 ∧
        D ≤ ((∏ q ∈ T, q : ℕ) : ℝ) * (p : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            ((((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3) < D) := by
  have hsort := sort_insert_min T p hp hlt
  rw [hsort]
  have hprod : ((∏ q ∈ insert p T, q : ℕ) : ℝ) = ((∏ q ∈ T, q : ℕ) : ℝ) * (p : ℝ) := by
    rw [Finset.prod_insert hp]
    push_cast
    ring
  have hcard : (insert p T).card = T.card + 1 := Finset.card_insert_of_notMem hp
  have hget : ∀ m : ℕ, T.card = m - 1 →
      ((T.sort (· ≥ ·) ++ [p]).getD (m - 1) 0) = p := by
    intro m hm
    rw [show m - 1 = (T.sort (· ≥ ·)).length from by
      rw [Finset.length_sort]
      omega]
    exact getD_append_length (T.sort (· ≥ ·)) p
  have hDterm : ∀ m : ℕ, T.card = m - 1 →
      ((∏ q ∈ insert p T, q : ℕ) : ℝ) *
        ((((T.sort (· ≥ ·) ++ [p]).getD (m - 1) 0 : ℕ) : ℝ) ^ 2) =
        ((∏ q ∈ T, q : ℕ) : ℝ) * (p : ℝ) ^ 3 := by
    intro m hm
    rw [hprod, hget m hm]
    ring
  constructor
  · rintro ⟨h0, hc, hD, hk⟩
    have hn : T.card = n - 1 := by omega
    refine ⟨h0, hn, ?_, ?_⟩
    · rw [hDterm n hn] at hD
      exact hD
    · intro k hk' hpar
      have hkr : k < (T.sort (· ≥ ·)).length := by
        rw [Finset.length_sort]
        omega
      have hkle : k ≤ (T.sort (· ≥ ·)).length := le_of_lt hkr
      have h1 := hk k hk' hpar
      rwa [prod_take_append (T.sort (· ≥ ·)) p k hkle,
        getD_append_lt (T.sort (· ≥ ·)) p k hkr] at h1
  · rintro ⟨h0, hc, hD, hk⟩
    refine ⟨h0, by omega, ?_, ?_⟩
    · rw [hDterm n hc]
      exact hD
    · intro k hk' hpar
      have hkr : k < (T.sort (· ≥ ·)).length := by
        rw [Finset.length_sort]
        omega
      have hkle : k ≤ (T.sort (· ≥ ·)).length := le_of_lt hkr
      have h1 := hk k hk' hpar
      rwa [prod_take_append (T.sort (· ≥ ·)) p k hkle,
        getD_append_lt (T.sort (· ≥ ·)) p k hkr]

/-- A stopping term beyond the size of the finite prime set is zero. -/
private theorem stoppZero (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ)
    (n : ℕ) (hn : S.card < n) : stoppingTerm S D g n = 0 := by
  unfold stoppingTerm
  apply sum_eq_zero
  intro T hT
  obtain ⟨hTS, _, hcard, _⟩ := mem_filter.mp hT
  have := card_le_card (mem_powerset.mp hTS)
  omega

/-- Every stopping term of the empty prime set vanishes. -/
private theorem stopp_empty (D : ℝ) (g : ℕ → ℝ) : ∀ n, stoppingTerm ∅ D g n = 0
  | 0 => by simp [stoppingTerm]
  | (k + 1) => stoppZero ∅ D g (k + 1) (by simp)

/-- The Rosser weight at one is one. -/
private theorem rosserWeight_one (D : ℝ) (b : Bool) : LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b 1 = 1 := by
  have h0 : LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes 1 = [] := by
    simp [LeanLab.AlmostPrimeSums.Decomp1527b.decPrimes]
  unfold LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight
  rw [h0]
  simp

/-- The stopping term of the enlarged prime set splits into the inherited
part and the newly stopped sets. -/
private theorem stoppingTerm_insert (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r n : ℕ)
    (hp : r ∉ T) (hlt : ∀ q ∈ T, r < q) :
    stoppingTerm (insert r T) D g n =
      (1 - g r) * stoppingTerm T D g n +
        g r * (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) := by
  have hU : (∑ T' ∈ T.powerset, (if (0 < n ∧ T'.card = n ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (((T'.sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
        then (∏ p ∈ T', g p) * ∏ p ∈ (insert r T).filter (fun p => p < (T'.sort (· ≥ ·)).getD (n - 1) 0), (1 - g p) else 0)) =
      ∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (((U.sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p) * ∏ p ∈ (insert r T).filter (fun p => p < (T'.sort (· ≥ ·)).getD (n - 1) 0), (1 - g p) := by
    simp only [Finset.sum_filter]
  have h1 : (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (((U.sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p) * ∏ p ∈ (insert r T).filter (fun p => p < (T'.sort (· ≥ ·)).getD (n - 1) 0), (1 - g p)) =
      (1 - g r) * (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (((U.sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p) * ∏ p ∈ T.filter (fun p => p < (T'.sort (· ≥ ·)).getD (n - 1) 0), (1 - g p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T' hT'
    have hP : (0 < n ∧ T'.card = n ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (((T'.sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) := (Finset.mem_filter.mp hT').2
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT').1
    have hm : (T'.sort (· ≥ ·)).getD (n - 1) 0 ∈ T' := getD_last_mem T' n hP.1 hP.2.1
    have hrm : r < (T'.sort (· ≥ ·)).getD (n - 1) 0 := hlt _ (hsub hm)
    rw [prod_filter_lt_insert T g r ((T'.sort (· ≥ ·)).getD (n - 1) 0) hp hrm]
    ring
  have hU2 : (∑ T' ∈ T.powerset, (if (0 < n ∧ (insert r T').card = n ∧
        D ≤ ((∏ p ∈ (insert r T'), p : ℕ) : ℝ) * ((((insert r T').sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          (((((insert r T').sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            ((((insert r T').sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ (insert r T'), g p) * ∏ p ∈ (insert r T).filter (fun p => p < ((insert r T').sort (· ≥ ·)).getD (n - 1) 0), (1 - g p) else 0)) =
      ∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ (insert r U).card = n ∧
        D ≤ ((∏ p ∈ (insert r U), p : ℕ) : ℝ) * ((((insert r U).sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          (((((insert r U).sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            ((((insert r U).sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ (insert r T'), g p) * ∏ p ∈ (insert r T).filter (fun p => p < ((insert r T').sort (· ≥ ·)).getD (n - 1) 0), (1 - g p) := by
    simp only [Finset.sum_filter]
  have hfil : T.powerset.filter (fun U => 0 < n ∧ (insert r U).card = n ∧
        D ≤ ((∏ p ∈ (insert r U), p : ℕ) : ℝ) * ((((insert r U).sort (· ≥ ·)).getD (n - 1) 0 : ℕ) : ℝ) ^ 2 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          (((((insert r U).sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            ((((insert r U).sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) =
      T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) := by
    apply Finset.filter_congr
    intro U hU
    exact stopPred_insert U D r n (Finset.notMem_of_mem_powerset_of_notMem hU hp)
      (fun q hq => hlt q (Finset.mem_powerset.mp hU hq))
  have h2 : (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ (insert r T'), g p) * ∏ p ∈ (insert r T).filter (fun p => p < ((insert r T').sort (· ≥ ·)).getD (n - 1) 0), (1 - g p)) =
      g r * (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T' hT'
    have hP : (0 < n ∧ T'.card = n - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) := (Finset.mem_filter.mp hT').2
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT').1
    have hpr : r ∉ T' := Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp hT').1 hp
    have hge : ((insert r T').sort (· ≥ ·)).getD (n - 1) 0 = r := by
      rw [sort_insert_min T' r hpr (fun q hq => hlt q (hsub hq))]
      rw [show n - 1 = (T'.sort (· ≥ ·)).length from by
        rw [Finset.length_sort]; omega]
      exact getD_append_length (T'.sort (· ≥ ·)) r
    have hf : (insert r T).filter
        (fun p => p < ((insert r T').sort (· ≥ ·)).getD (n - 1) 0) = ∅ := by
      rw [hge, Finset.filter_eq_empty_iff]
      intro p hp'
      rw [Finset.mem_insert] at hp'
      rcases hp' with rfl | hp'
      · exact not_lt.mpr le_rfl
      · exact not_lt.mpr (le_of_lt (hlt p hp'))
    rw [hf, Finset.prod_empty, mul_one, Finset.prod_insert hpr]
    try ring
  unfold stoppingTerm
  conv_lhs => rw [Finset.sum_filter]
  rw [Finset.sum_powerset_insert hp, hU, hU2, hfil, h1, h2]

/-- The upper Rosser weight of a set of distinct primes. -/
private theorem rosserWeight_prime_set_true (T : Finset ℕ) (D : ℝ)
    (hprime : ∀ q ∈ T, q.Prime) :
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T, p) =
      if (∀ k < T.card, k % 2 = 0 → ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      then (-1 : ℝ) ^ T.card else 0 := by
  rw [rosserWeight_prime_set T D true hprime]
  simp

/-- The lower Rosser weight of a set of distinct primes. -/
private theorem rosserWeight_prime_set_false (T : Finset ℕ) (D : ℝ)
    (hprime : ∀ q ∈ T, q.Prime) :
    LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T, p) =
      if (∀ k < T.card, ¬(k % 2 = 0) → ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      then (-1 : ℝ) ^ T.card else 0 := by
  rw [rosserWeight_prime_set T D false hprime]
  simp

/-- The signed weight of one prime set splits over a new least prime,
upper case. -/
private theorem summand_upper (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r : ℕ)
    (hp : r ∉ T) (hlt : ∀ q ∈ T, r < q) (hprime : ∀ q ∈ T, q.Prime)
    (hpp : r.Prime) :
    (∏ p ∈ T, g p) * (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T, p) +
          g r * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true ((∏ p ∈ T, p) * r)) =
      (1 - g r) * ((∏ p ∈ T, g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T, p)) +
        g r * (if (T.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T.card, k % 2 = 0 →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T, g p) else 0) := by
  rw [rosserWeight_mul_min_true T D r hp hlt hprime hpp,
    rosserWeight_prime_set_true T D hprime]
  by_cases hc : T.card % 2 = 0
  · by_cases ht : ((∏ p ∈ T, p : ℕ) : ℝ) * (r : ℝ) ^ 3 < D
    · by_cases hP : (∀ k < T.card, k % 2 = 0 →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hP, if_pos (fun _ => ht),
          if_neg (fun h => absurd h.2.1 (not_le_of_gt ht))]
        have hone : (-1 : ℝ) ^ T.card = 1 := by
          rw [neg_one_pow_eq_pow_mod_two, hc, pow_zero]
        rw [hone]
        ring
      · rw [if_neg hP, if_pos (fun _ => ht),
          if_neg (fun h => absurd h.2.2 hP)]
        ring
    · by_cases hP : (∀ k < T.card, k % 2 = 0 →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hP, if_neg (fun h => absurd (h hc) ht),
          if_pos ⟨hc, not_lt.mp ht, hP⟩]
        have hone : (-1 : ℝ) ^ T.card = 1 := by
          rw [neg_one_pow_eq_pow_mod_two, hc, pow_zero]
        rw [hone]
        ring
      · rw [if_neg hP, if_neg (fun h => absurd (h hc) ht),
          if_neg (fun h => absurd h.2.2 hP)]
        ring
  · by_cases hP : (∀ k < T.card, k % 2 = 0 →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
    · rw [if_pos hP, if_pos (fun h => absurd h hc),
        if_neg (fun h => absurd h.1 hc)]
      ring
    · rw [if_neg hP, if_pos (fun h => absurd h hc),
        if_neg (fun h => absurd h.1 hc)]
      ring

/-- The signed weight of one prime set splits over a new least prime,
lower case. -/
private theorem summand_lower (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r : ℕ)
    (hp : r ∉ T) (hlt : ∀ q ∈ T, r < q) (hprime : ∀ q ∈ T, q.Prime)
    (hpp : r.Prime) :
    (∏ p ∈ T, g p) * (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T, p) +
          g r * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false ((∏ p ∈ T, p) * r)) =
      (1 - g r) * ((∏ p ∈ T, g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T, p)) +
        g r * (if (¬(T.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T.card, ¬(k % 2 = 0) →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then -(∏ p ∈ T, g p) else 0) := by
  rw [rosserWeight_mul_min_false T D r hp hlt hprime hpp,
    rosserWeight_prime_set_false T D hprime]
  by_cases hc : T.card % 2 = 0
  · by_cases hP : (∀ k < T.card, ¬(k % 2 = 0) →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
    · rw [if_pos hP, if_pos (fun h => absurd hc h),
        if_neg (fun h => absurd hc h.1)]
      ring
    · rw [if_neg hP, if_pos (fun h => absurd hc h),
        if_neg (fun h => absurd hc h.1)]
      ring
  · by_cases ht : ((∏ p ∈ T, p : ℕ) : ℝ) * (r : ℝ) ^ 3 < D
    · by_cases hP : (∀ k < T.card, ¬(k % 2 = 0) →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hP, if_pos (fun _ => ht),
          if_neg (fun h => absurd h.2.1 (not_le_of_gt ht))]
        have hneg : (-1 : ℝ) ^ T.card = -1 := by
          rw [neg_one_pow_eq_pow_mod_two]
          rw [show T.card % 2 = 1 by omega]
          norm_num
        rw [hneg]
        ring
      · rw [if_neg hP, if_pos (fun _ => ht),
          if_neg (fun h => absurd h.2.2 hP)]
        ring
    · by_cases hP : (∀ k < T.card, ¬(k % 2 = 0) →
          ((((T.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hP, if_neg (fun h => absurd (h hc) ht),
          if_pos ⟨hc, not_lt.mp ht, hP⟩]
        have hneg : (-1 : ℝ) ^ T.card = -1 := by
          rw [neg_one_pow_eq_pow_mod_two]
          rw [show T.card % 2 = 1 by omega]
          norm_num
        rw [hneg]
        ring
      · rw [if_neg hP, if_neg (fun h => absurd (h hc) ht),
          if_neg (fun h => absurd h.2.2 hP)]
        ring

/-- Sums of the newly stopped sets, upper parity. -/
private theorem extra_upper_sum (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r : ℕ) :
    (∑ n ∈ range (T.card + 4), (if n % 2 = 1 then
      (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0))
      = ∑ T' ∈ T.powerset, (if (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
  have key1 : (∑ n ∈ range (T.card + 4), (if n % 2 = 1 then
      (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0))
      = ∑ n ∈ range (T.card + 4), ∑ T' ∈ T.powerset,
          (if n % 2 = 1 ∧ (0 < n ∧ T'.card = n - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ho : n % 2 = 1
    · rw [if_pos ho, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T' _
      by_cases hq : (0 < n ∧ T'.card = n - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hq, if_pos ⟨ho, hq⟩]
      · rw [if_neg hq, if_neg (fun h => hq h.2)]
    · rw [if_neg ho]
      symm
      apply Finset.sum_eq_zero
      intro T' _
      rw [if_neg (fun h => ho h.1)]
  rw [key1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T' hT'
  have hle : T'.card ≤ T.card := Finset.card_le_card (Finset.mem_powerset.mp hT')
  refine (Finset.sum_eq_single (T'.card + 1) ?_ ?_).trans ?_
  · intro n hn hne
    rw [if_neg]
    rintro ⟨-, hP⟩
    exact hne (by omega)
  · intro hmem
    rw [Finset.mem_range] at hmem
    omega
  by_cases hc : T'.card % 2 = 0
  · have hodd : (T'.card + 1) % 2 = 1 := by omega
    by_cases hb : ((T'.card + 1) % 2 = 1 ∧ (0 < (T'.card + 1) ∧ T'.card = (T'.card + 1) - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < (T'.card + 1) - 1, k % 2 = ((T'.card + 1) - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D))
    · rw [if_pos hb, if_pos (show (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) from
        ⟨hc, hb.2.2.2.1, fun k hk hk2 => hb.2.2.2.2 k (by omega) (by omega)⟩)]
    · rw [if_neg hb, if_neg (show ¬(T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) from fun hEU =>
        hb ⟨hodd, ⟨by omega, by omega, hEU.2.1,
          fun k hk hk2 => hEU.2.2 k (by omega) (by omega)⟩⟩)]
  · have hodd : ¬((T'.card + 1) % 2 = 1) := by omega
    rw [if_neg (fun h => hodd h.1), if_neg (fun hEU => hc hEU.1)]

/-- Sums of the newly stopped sets, lower parity. -/
private theorem extra_lower_sum (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r : ℕ) :
    (∑ n ∈ range (T.card + 4), (if 0 < n ∧ n % 2 = 0 then
      (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0))
      = ∑ T' ∈ T.powerset, (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
  have key1 : (∑ n ∈ range (T.card + 4), (if 0 < n ∧ n % 2 = 0 then
      (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0))
      = ∑ n ∈ range (T.card + 4), ∑ T' ∈ T.powerset,
          (if 0 < n ∧ n % 2 = 0 ∧ (0 < n ∧ T'.card = n - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ho : 0 < n ∧ n % 2 = 0
    · rw [if_pos ho, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T' _
      by_cases hq : (0 < n ∧ T'.card = n - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
      · rw [if_pos hq, if_pos ⟨ho.1, ho.2, hq⟩]
      · rw [if_neg hq, if_neg (fun h => hq h.2.2)]
    · rw [if_neg ho]
      symm
      apply Finset.sum_eq_zero
      intro T' _
      rw [if_neg (fun h => ho ⟨h.1, h.2.1⟩)]
  rw [key1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T' hT'
  have hle : T'.card ≤ T.card := Finset.card_le_card (Finset.mem_powerset.mp hT')
  refine (Finset.sum_eq_single (T'.card + 1) ?_ ?_).trans ?_
  · intro n hn hne
    rw [if_neg]
    rintro ⟨-, -, hP⟩
    exact hne (by omega)
  · intro hmem
    rw [Finset.mem_range] at hmem
    omega
  by_cases hc : T'.card % 2 = 0
  · have hodd : ¬(0 < T'.card + 1 ∧ (T'.card + 1) % 2 = 0) := by omega
    rw [if_neg (fun h => hodd ⟨h.1, h.2.1⟩), if_neg (fun hEU => hEU.1 hc)]
  · by_cases hb : (0 < T'.card + 1 ∧ (T'.card + 1) % 2 = 0 ∧ (0 < (T'.card + 1) ∧ T'.card = (T'.card + 1) - 1 ∧
        D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < (T'.card + 1) - 1, k % 2 = ((T'.card + 1) - 1) % 2 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D))
    · rw [if_pos hb, if_pos (show (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) from
        ⟨hc, hb.2.2.2.2.1, fun k hk hk2 => hb.2.2.2.2.2 k (by omega) (by omega)⟩)]
    · rw [if_neg hb, if_neg (show ¬(¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) from fun hEL =>
        hb ⟨by omega, by omega, ⟨by omega, by omega, hEL.2.1,
          fun k hk hk2 => hEL.2.2 k (by omega) (by omega)⟩⟩)]

/-- One summand of the odd stopping sum after adding a least prime. -/
private theorem stopp_summand_split (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r n : ℕ)
    (hp : r ∉ T) (hlt : ∀ q ∈ T, r < q) :
    (if n % 2 = 1 then stoppingTerm (insert r T) D g n else 0) =
      (1 - g r) * (if n % 2 = 1 then stoppingTerm T D g n else 0) +
        g r * (if n % 2 = 1 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
  by_cases h : n % 2 = 1
  · rw [if_pos h, if_pos h, if_pos h, stoppingTerm_insert T D g r n hp hlt]
    try ring
  · rw [if_neg h, if_neg h, if_neg h]
    try ring

/-- One summand of the even stopping sum after adding a least prime. -/
private theorem stopp_summand_split' (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r n : ℕ)
    (hp : r ∉ T) (hlt : ∀ q ∈ T, r < q) :
    (if 0 < n ∧ n % 2 = 0 then stoppingTerm (insert r T) D g n else 0) =
      (1 - g r) * (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0) +
        g r * (if 0 < n ∧ n % 2 = 0 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
  by_cases h : 0 < n ∧ n % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, stoppingTerm_insert T D g r n hp hlt]
    try ring
  · rw [if_neg h, if_neg h, if_neg h]
    try ring

/-- The Rosser prime model is a signed sum over the prime subsets. -/
private theorem model_powerset (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (b : Bool) :
    rosserPrimeModel T ∅ D b g =
      ∑ T' ∈ T.powerset, (∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T', p) := by
  unfold rosserPrimeModel
  apply Finset.sum_congr rfl
  intro T' hT'
  simp only [Finset.inter_empty, Finset.card_empty, pow_zero, Finset.sdiff_empty, one_mul]
  ring

/-- Adding a new least prime to the Rosser prime model. -/
private theorem model_insert (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (r : ℕ) (b : Bool)
    (hp : r ∉ T) :
    rosserPrimeModel (insert r T) ∅ D b g =
      ∑ T' ∈ T.powerset, (∏ p ∈ T', g p) *
        (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b (∏ p ∈ T', p) + g r * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D b ((∏ p ∈ T', p) * r)) := by
  rw [model_powerset, Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T' hT'
  have hpr : r ∉ T' := Finset.notMem_of_mem_powerset_of_notMem hT' hp
  have hpc : r * (∏ p ∈ T', p) = (∏ p ∈ T', p) * r := Nat.mul_comm _ _
  rw [Finset.prod_insert hpr, Finset.prod_insert hpr, hpc]
  ring

/-- The odd stopping sum can be shortened beyond the size of the prime set. -/
private theorem stopp_range_trim (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) :
    ∀ j : ℕ, T.card < j →
    (∑ n ∈ range (j + 1), (if n % 2 = 1 then stoppingTerm T D g n else 0)) =
      ∑ n ∈ range j, (if n % 2 = 1 then stoppingTerm T D g n else 0) := by
  intro j hj
  rw [Finset.sum_range_succ, stoppZero T D g j hj]
  try simp

/-- The even stopping sum can be shortened beyond the size of the prime set. -/
private theorem stopp_range_trim' (T : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) :
    ∀ j : ℕ, T.card < j →
    (∑ n ∈ range (j + 1), (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0)) =
      ∑ n ∈ range j, (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0) := by
  intro j hj
  rw [Finset.sum_range_succ, stoppZero T D g j hj]
  try simp

/-- The finite stopping expansion of both ordinary Rosser models,
by induction on the least prime. -/
private theorem stopping_expansion_aux (D : ℝ) (g : ℕ → ℝ) :
    ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (rosserPrimeModel T ∅ D true g = (∏ p ∈ T, (1 - g p)) +
        ∑ n ∈ range (T.card + 3), (if n % 2 = 1 then stoppingTerm T D g n else 0)) ∧
      (rosserPrimeModel T ∅ D false g = (∏ p ∈ T, (1 - g p)) -
        ∑ n ∈ range (T.card + 3), (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0)) := by
  intro T
  induction T using Finset.induction_on_min with
  | empty =>
    intro _
    constructor
    · rw [model_powerset, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty,
        Finset.prod_empty, one_mul, rosserWeight_one, Finset.prod_empty]
      simp [stopp_empty]
    · rw [model_powerset, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty,
        Finset.prod_empty, one_mul, rosserWeight_one, Finset.prod_empty]
      simp [stopp_empty]
  | insert r T hlt ih =>
    intro hS
    have hpr : r ∉ T := fun h => absurd (hlt r h) (lt_irrefl r)
    have hprimeT : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hrt : r.Prime := hS r (Finset.mem_insert_self r T)
    have hcard : (insert r T).card = T.card + 1 := Finset.card_insert_of_notMem hpr
    obtain ⟨ihU, ihL⟩ := ih hprimeT
    constructor
    · have hpt : ∀ T' ∈ T.powerset, (∏ p ∈ T', g p) *
            (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T', p) + g r * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true ((∏ p ∈ T', p) * r)) =
          (1 - g r) * ((∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T', p)) +
            g r * (if (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
        intro T' hT'
        exact summand_upper T' D g r (Finset.notMem_of_mem_powerset_of_notMem hT' hpr)
          (fun q hq => hlt q (Finset.mem_powerset.mp hT' hq))
          (fun q hq => hprimeT q (Finset.mem_powerset.mp hT' hq)) hrt
      have hL : rosserPrimeModel (insert r T) ∅ D true g =
          (1 - g r) * rosserPrimeModel T ∅ D true g +
            g r * ∑ T' ∈ T.powerset, (if (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
        rw [model_insert T D g r true hpr, Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
        have e1 : (∑ T' ∈ T.powerset,
              (1 - g r) * ((∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T', p))) =
            (1 - g r) * ∑ T' ∈ T.powerset, (∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T', p) := by
          rw [Finset.mul_sum]
        have e2 : (∑ T' ∈ T.powerset, g r * (if (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0)) =
            g r * ∑ T' ∈ T.powerset, (if (T'.card % 2 = 0 ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, k % 2 = 0 →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
          rw [Finset.mul_sum]
        rw [e1, e2, show (∑ T' ∈ T.powerset, (∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D true (∏ p ∈ T', p)) =
          rosserPrimeModel T ∅ D true g from (model_powerset T D g true).symm]
        try ring
      have hR : (∏ p ∈ insert r T, (1 - g p)) +
            ∑ n ∈ range ((insert r T).card + 3),
              (if n % 2 = 1 then stoppingTerm (insert r T) D g n else 0) =
          (1 - g r) * ((∏ p ∈ T, (1 - g p)) +
              ∑ n ∈ range (T.card + 3), (if n % 2 = 1 then stoppingTerm T D g n else 0)) +
            g r * ∑ n ∈ range (T.card + 4),
              (if n % 2 = 1 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
        rw [Finset.prod_insert hpr,
          show (insert r T).card + 3 = T.card + 4 from by rw [hcard]]
        rw [Finset.sum_congr rfl (fun n _ => stopp_summand_split T D g r n hpr hlt),
          Finset.sum_add_distrib]
        have e1 : (∑ n ∈ range (T.card + 4),
              (1 - g r) * (if n % 2 = 1 then stoppingTerm T D g n else 0)) =
            (1 - g r) * ∑ n ∈ range (T.card + 4),
              (if n % 2 = 1 then stoppingTerm T D g n else 0) := by
          rw [Finset.mul_sum]
        have e2 : (∑ n ∈ range (T.card + 4),
              g r * (if n % 2 = 1 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0)) =
            g r * ∑ n ∈ range (T.card + 4),
              (if n % 2 = 1 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
          rw [Finset.mul_sum]
        rw [e1, e2, stopp_range_trim T D g (T.card + 3) (by omega)]
        try ring
      rw [hL, hR, ihU, extra_upper_sum T D g r]
      try ring
    · have hpt : ∀ T' ∈ T.powerset, (∏ p ∈ T', g p) *
            (LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T', p) + g r * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false ((∏ p ∈ T', p) * r)) =
          (1 - g r) * ((∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T', p)) +
            g r * (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then -(∏ p ∈ T', g p) else 0) := by
        intro T' hT'
        exact summand_lower T' D g r (Finset.notMem_of_mem_powerset_of_notMem hT' hpr)
          (fun q hq => hlt q (Finset.mem_powerset.mp hT' hq))
          (fun q hq => hprimeT q (Finset.mem_powerset.mp hT' hq)) hrt
      have hneg : (∑ T' ∈ T.powerset, (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then -(∏ p ∈ T', g p) else 0)) =
          -∑ T' ∈ T.powerset, (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro T' _
        by_cases h : (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D)
        · rw [if_pos h, if_pos h]
          try ring
        · rw [if_neg h, if_neg h]
          try ring
      have hL : rosserPrimeModel (insert r T) ∅ D false g =
          (1 - g r) * rosserPrimeModel T ∅ D false g -
            g r * ∑ T' ∈ T.powerset, (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then (∏ p ∈ T', g p) else 0) := by
        rw [model_insert T D g r false hpr, Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
        have e1 : (∑ T' ∈ T.powerset,
              (1 - g r) * ((∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T', p))) =
            (1 - g r) * ∑ T' ∈ T.powerset, (∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T', p) := by
          rw [Finset.mul_sum]
        have e2 : (∑ T' ∈ T.powerset, g r * (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then -(∏ p ∈ T', g p) else 0)) =
            g r * ∑ T' ∈ T.powerset, (if (¬(T'.card % 2 = 0) ∧
            D ≤ ((∏ p ∈ T', p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
            ∀ k < T'.card, ¬(k % 2 = 0) →
          ((((T'.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
              (((T'.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D) then -(∏ p ∈ T', g p) else 0) := by
          rw [Finset.mul_sum]
        rw [e1, e2, hneg,
          show (∑ T' ∈ T.powerset, (∏ p ∈ T', g p) * LeanLab.AlmostPrimeSums.Decomp1527b.rosserWeight D false (∏ p ∈ T', p)) =
            rosserPrimeModel T ∅ D false g from (model_powerset T D g false).symm]
        try ring
      have hR : (∏ p ∈ insert r T, (1 - g p)) -
            ∑ n ∈ range ((insert r T).card + 3),
              (if 0 < n ∧ n % 2 = 0 then stoppingTerm (insert r T) D g n else 0) =
          (1 - g r) * ((∏ p ∈ T, (1 - g p)) -
              ∑ n ∈ range (T.card + 3),
                (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0)) -
            g r * ∑ n ∈ range (T.card + 4),
              (if 0 < n ∧ n % 2 = 0 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
        rw [Finset.prod_insert hpr,
          show (insert r T).card + 3 = T.card + 4 from by rw [hcard]]
        rw [Finset.sum_congr rfl (fun n _ => stopp_summand_split' T D g r n hpr hlt),
          Finset.sum_add_distrib]
        have e1 : (∑ n ∈ range (T.card + 4),
              (1 - g r) * (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0)) =
            (1 - g r) * ∑ n ∈ range (T.card + 4),
              (if 0 < n ∧ n % 2 = 0 then stoppingTerm T D g n else 0) := by
          rw [Finset.mul_sum]
        have e2 : (∑ n ∈ range (T.card + 4),
              g r * (if 0 < n ∧ n % 2 = 0 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0)) =
            g r * ∑ n ∈ range (T.card + 4),
              (if 0 < n ∧ n % 2 = 0 then (∑ T' ∈ T.powerset.filter (fun U => 0 < n ∧ U.card = n - 1 ∧
        D ≤ ((∏ p ∈ U, p : ℕ) : ℝ) * (r : ℝ) ^ 3 ∧
        ∀ k < n - 1, k % 2 = (n - 1) % 2 →
          ((((U.sort (· ≥ ·)).take k).prod : ℕ) : ℝ) *
            (((U.sort (· ≥ ·)).getD k 0 : ℕ) : ℝ) ^ 3 < D), (∏ p ∈ T', g p)) else 0) := by
          rw [Finset.mul_sum]
        rw [e1, e2, stopp_range_trim' T D g (T.card + 3) (by omega)]
        try ring
      rw [hL, hR, ihL, extra_lower_sum T D g r]
      try ring

/-- LEAF. Finite stopping expansion of both ordinary Rosser models.
BJS p. 14 Proposition 13 proof, citing Nathanson Lemma 9.3.
This is a finite polynomial identity. It has no dimension premise, delay
function, numerical constant, sequence support or exceptional prime factor. -/
theorem stopping_expansion (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime) (hD : 1 < D) :
    (rosserPrimeModel S ∅ D true g = (∏ p ∈ S, (1 - g p)) +
      ∑ n ∈ range (S.card + 3), if n % 2 = 1 then stoppingTerm S D g n else 0) ∧
    (rosserPrimeModel S ∅ D false g = (∏ p ∈ S, (1 - g p)) -
      ∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then stoppingTerm S D g n else 0) :=
  stopping_expansion_aux D g S hS

/-- The first stopping term is a single prime sum with a cube cutoff.
BJS p. 10 display 28 specialized to n equal to one. -/
theorem stoppingTerm_one (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) :
    stoppingTerm S D g 1 =
      ∑ p ∈ S.filter (fun p : ℕ => D ≤ (p : ℝ) ^ 3),
        g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q) := by
  unfold stoppingTerm
  symm
  apply sum_bij (fun p _ => ({p} : Finset ℕ))
  · intro p hp
    obtain ⟨hpS, hpd⟩ := mem_filter.mp hp
    simp only [mem_filter, mem_powerset]
    simpa [pow_succ, mul_assoc] using And.intro (singleton_subset_iff.mpr hpS) hpd
  · intro p hp q hq heq
    exact singleton_injective heq
  · intro T hT
    obtain ⟨hTS, hn, hcard, hcut, hprev⟩ := mem_filter.mp hT
    obtain ⟨p, rfl⟩ := card_eq_one.mp hcard
    refine ⟨p, mem_filter.mpr ⟨singleton_subset_iff.mp (mem_powerset.mp hTS), ?_⟩, rfl⟩
    simpa [pow_succ, mul_assoc] using hcut
  · intro p hp
    simp

/-- The ordered finite product telescopes into its prime removal sum.
Use Mathlib prod_add_ordered rather than reproving a product expansion.
Auxiliary identity for the n equal to one case on BJS p. 11. -/
theorem ordered_removal_sum (S : Finset ℕ) (g : ℕ → ℝ) :
    (∑ p ∈ S, g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q)) =
      1 - ∏ p ∈ S, (1 - g p) := by
  have h := prod_add_ordered' S (fun p => (1 : ℝ) - g p) g
  simp only [sub_add_cancel, prod_const_one, mul_one] at h
  linarith

/-- A cutoff removal sum is the difference of two Euler products.
Auxiliary finite telescoping identity for BJS p. 11 first induction step. -/
theorem cutoff_removal_sum (S : Finset ℕ) (g : ℕ → ℝ) (w : ℝ) :
    (∑ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)),
      g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q)) =
      (∏ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w), (1 - g p)) -
        ∏ p ∈ S, (1 - g p) := by
  have hlo :
      (∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w),
        g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q)) =
        1 - ∏ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w), (1 - g p) := by
    rw [← ordered_removal_sum]
    apply sum_congr rfl
    intro p hp
    congr 2
    ext q
    simp only [mem_filter]
    have hpw := (mem_filter.mp hp).2
    constructor
    · rintro ⟨hq, hqp⟩
      exact ⟨⟨hq, lt_trans (by exact_mod_cast hqp) hpw⟩, hqp⟩
    · tauto
  have hsplit :
      (∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w),
        g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q)) +
      (∑ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)),
        g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q)) =
      ∑ p ∈ S, g p * ∏ q ∈ S.filter (fun q => q < p), (1 - g q) := by
    simp_rw [sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    rcases lt_or_ge (p : ℝ) w with h | h <;> simp [h, not_le_of_gt, not_lt_of_ge]
  rw [hlo, ordered_removal_sum] at hsplit
  linarith

/-- LEAF. The first stopping term only, from the product condition.
BJS pp. 10 and 11, Lemma 11 proof with n equal to one and display 33.
The coefficient three is tau_1. This contains no higher stopping terms
and no constant from Table 1. Journal pp. 1218 and 1219. -/
theorem first_stopping_bound (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    stoppingTerm (siftingPrimes P z \ Q) D g 1 ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        (3 / (log D / log z) - 1 +
          (1 / 8349 : ℝ) * 3 * exp 2 * hS (log D / log z)) := by
  let S := siftingPrimes P z \ Q
  let w := exp (log D / 3)
  have hzpos : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hD : 1 < D := by linarith
  have hlD : 0 < log D := log_pos hD
  have hw : 1 < w := one_lt_exp_iff.mpr (by positivity)
  have hwpos : 0 < w := by linarith
  have hwle : w ≤ z := by
    rw [show z = exp (log z) by rw [exp_log hzpos]]
    apply exp_le_exp.mpr
    have hh := (div_le_iff₀ hlz).mp hs
    linarith
  have hwcube : w ^ 3 = D := by
    dsimp [w]
    rw [← exp_nat_mul]
    norm_num
    rw [show 3 * (log D / 3) = log D by ring, exp_log (by linarith)]
  have hcubes : S.filter (fun p : ℕ => D ≤ (p : ℝ) ^ 3) =
      S.filter (fun p : ℕ => w ≤ (p : ℝ)) := by
    ext p
    simp only [mem_filter, ← hwcube]
    exact and_congr_right (fun _ => pow_le_pow_iff_left₀ hwpos.le (Nat.cast_nonneg p) (by norm_num))
  have hfilter : S.filter (fun p : ℕ => w ≤ (p : ℝ)) =
      (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
    ext p
    simp only [S, siftingPrimes, mem_filter, mem_sdiff]
    tauto
  have hbound : (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹) ≤
      (1 + (1 / 8349 : ℝ)) * (log z / log w) := by
    by_cases hwlt : w < z
    · rw [hfilter]
      exact hprod w hw hwlt
    · have he : w = z := le_antisymm hwle (le_of_not_gt hwlt)
      have hempty : S.filter (fun p : ℕ => w ≤ (p : ℝ)) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro p hp hpw
        have hpz := (mem_filter.mp (mem_sdiff.mp hp).1).2.2
        linarith
      rw [hempty, prod_empty, he, div_self hlz.ne']
      norm_num
  have hgp : ∀ p ∈ S, 0 < 1 - g p := by
    intro p hp
    exact sub_pos.mpr (hg p (mem_filter.mp (mem_sdiff.mp hp).1).2.1).2
  have hv : 0 ≤ ∏ p ∈ S, (1 - g p) := (prod_pos hgp).le
  have hparts :
      (∏ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w), (1 - g p)) *
      (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)) =
        ∏ p ∈ S, (1 - g p) := by
    simpa only [not_lt] using prod_filter_mul_prod_filter_not S
      (fun p : ℕ => (p : ℝ) < w) (fun p => 1 - g p)
  have hnonzero : (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)) ≠ 0 :=
    ne_of_gt (prod_pos (fun p hp => hgp p (mem_filter.mp hp).1))
  have hid :
      (∏ p ∈ S, (1 - g p)) *
        (∏ p ∈ S.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹) =
        ∏ p ∈ S.filter (fun p : ℕ => (p : ℝ) < w), (1 - g p) := by
    rw [← hparts, prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hnonzero, mul_one]
  have hratio : log z / log w = 3 / (log D / log z) := by
    rw [show log w = log D / 3 by dsimp [w]; rw [log_exp]]
    field_simp
  have hb := mul_le_mul_of_nonneg_left hbound hv
  rw [hid, hratio] at hb
  have hslo : (1 : ℝ) ≤ log D / log z := by
    apply (le_div_iff₀ hlz).2
    simpa using log_le_log hzpos hzD
  have hscale : 3 / (log D / log z) ≤ 3 * exp 2 * hS (log D / log z) := by
    have haux := Envelope327.three_div_mul_hS_two_le hslo hs
    have he2 : exp 2 * hS 2 = 1 := by simp [hS, ← exp_add]
    calc
      _ = exp 2 * (3 / (log D / log z) * hS 2) := by
        rw [mul_left_comm, he2, mul_one]
      _ ≤ exp 2 * (3 * hS (log D / log z)) :=
        mul_le_mul_of_nonneg_left haux (exp_pos _).le
      _ = _ := by ring
  change stoppingTerm S D g 1 ≤ _
  rw [stoppingTerm_one, hcubes, cutoff_removal_sum]
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hscale (show (0 : ℝ) ≤ 1 / 8349 by norm_num)) hv
  linear_combination hb + hh

/-- Odd stopping sums split off their first term.
Finite bookkeeping for BJS p. 14 Proposition 13. -/
theorem odd_sum_split (N : ℕ) (hN : 1 < N) (t : ℕ → ℝ) :
    (∑ n ∈ range N, if n % 2 = 1 then t n else 0) =
      t 1 + ∑ n ∈ range N, if 3 ≤ n ∧ n % 2 = 1 then t n else 0 := by
  have he (n : ℕ) : (if n % 2 = 1 then t n else 0) =
      (if n = 1 then t 1 else 0) + (if 3 ≤ n ∧ n % 2 = 1 then t n else 0) := by
    by_cases h1 : n = 1
    · subst n; norm_num
    · by_cases ho : n % 2 = 1
      · have hn : 3 ≤ n := by omega
        simp [h1, ho, hn]
      · simp [h1, ho]
  simp_rw [he]
  rw [sum_add_distrib]
  simp [hN]

/-- Even positive stopping sums split off their second term.
Finite bookkeeping for BJS p. 14 Proposition 13. -/
theorem even_sum_split (N : ℕ) (hN : 2 < N) (t : ℕ → ℝ) :
    (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then t n else 0) =
      t 2 + ∑ n ∈ range N, if 4 ≤ n ∧ n % 2 = 0 then t n else 0 := by
  have he (n : ℕ) : (if 0 < n ∧ n % 2 = 0 then t n else 0) =
      (if n = 2 then t 2 else 0) + (if 4 ≤ n ∧ n % 2 = 0 then t n else 0) := by
    by_cases h2 : n = 2
    · subst n; norm_num
    · by_cases ho : 0 < n ∧ n % 2 = 0
      · have hn : 4 ≤ n := by omega
        simp [h2, ho, hn, ho.2]
      · have hn : ¬ (4 ≤ n ∧ n % 2 = 0) := by omega
        simp [h2, ho, hn]
  simp_rw [he]
  rw [sum_add_distrib]
  simp [hN]

/-- A bound on the ordinary model transfers through exact exceptional primes.
BJS p. 14 Proposition 13 and journal p. 1219. -/
theorem upper_transfer (S Q : Finset ℕ) (D C : ℝ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ S, g p ≤ 1)
    (h : rosserPrimeModel (S \ Q) ∅ D true g ≤ C * ∏ p ∈ S \ Q, (1 - g p)) :
    rosserPrimeModel S Q D true g ≤ C * ∏ p ∈ S, (1 - g p) := by
  rw [rosserPrimeModel_factor]
  have hp : 0 ≤ ∏ p ∈ S ∩ Q, (1 - g p) :=
    prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_inter.mp hp).1))
  calc
    _ ≤ (∏ p ∈ S ∩ Q, (1 - g p)) * (C * ∏ p ∈ S \ Q, (1 - g p)) :=
      mul_le_mul_of_nonneg_left h hp
    _ = _ := by rw [← mul_assoc, mul_comm _ C, mul_assoc, prod_inter_mul_prod_sdiff]

/-- A lower bound transfers through the same nonnegative exceptional factors.
BJS p. 14 Proposition 13 and journal p. 1219. -/
theorem lower_transfer (S Q : Finset ℕ) (D C : ℝ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ S, g p ≤ 1)
    (h : C * (∏ p ∈ S \ Q, (1 - g p)) ≤ rosserPrimeModel (S \ Q) ∅ D false g) :
    C * (∏ p ∈ S, (1 - g p)) ≤ rosserPrimeModel S Q D false g := by
  rw [rosserPrimeModel_factor]
  have hp : 0 ≤ ∏ p ∈ S ∩ Q, (1 - g p) :=
    prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_inter.mp hp).1))
  calc
    _ = (∏ p ∈ S ∩ Q, (1 - g p)) * (C * ∏ p ∈ S \ Q, (1 - g p)) := by
      rw [← mul_assoc, mul_comm _ C, mul_assoc, prod_inter_mul_prod_sdiff]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp

#print axioms stoppingTerm_nonneg
#print axioms stoppingTerm_eq_zero_of_card_lt
#print axioms stoppingTerm_zero
#print axioms delayTerm_nonneg
#print axioms delayTerm_eq_zero_of_endpoint
#print axioms delay_partial_sums
#print axioms stopping_expansion
#print axioms stoppingTerm_one
#print axioms ordered_removal_sum
#print axioms cutoff_removal_sum
#print axioms first_stopping_bound
#print axioms odd_sum_split
#print axioms even_sum_split
#print axioms upper_transfer
#print axioms lower_transfer

end
end LeanLab.BS2022GRH.Decomp327a

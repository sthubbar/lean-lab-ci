/-
Rosser coefficients from bounded descending prime prefixes.
Source: Iwaniec, Rosser's sieve, pages 178 and 179, formulas 3.1 to 3.7.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LeanLab.KumchevLiu2007.Task558a

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 179 formula 3.6, the upper gate kills an odd prefix at its level threshold.
The exponent beta is real as in the source. The empty prefix has gate one. -/
noncomputable def prefixGate (D : ℝ) (β : ℝ) (l : List ℕ) : ℝ :=
  if Odd l.length ∧ D ≤ (l.prod : ℝ) * (l.getLastD 1 : ℝ) ^ β then 0 else 1

/-- Page 178 before formula 3.1, rho is the product of all prefix gates. -/
noncomputable def prefixRho (D : ℝ) (β : ℝ) (l : List ℕ) : ℝ :=
  (l.inits.map (prefixGate D β)).prod

/-- Page 179 formulas 3.4 and 3.6, multiply rho by the Moebius sign.
The factor list is descending and retains multiplicities. Nonsquarefree inputs vanish. -/
noncomputable def rosserWeight (D : ℝ) (β : ℝ) (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * prefixRho D β d.primeFactorsList.reverse

/-- Page 179 formula 3.6, every gate is either zero or one. -/
theorem prefixGate_binary (D : ℝ) (β : ℝ) (l : List ℕ) :
    prefixGate D β l = 0 ∨ prefixGate D β l = 1 := by
  unfold prefixGate
  split_ifs <;> simp

/-- Page 178 prefix product, a product of zero or one gates is zero or one. -/
theorem prefixRho_binary (D : ℝ) (β : ℝ) (l : List ℕ) :
    prefixRho D β l = 0 ∨ prefixRho D β l = 1 := by
  have h : ∀ t : List (List ℕ), (t.map (prefixGate D β)).prod = 0 ∨
      (t.map (prefixGate D β)).prod = 1 := by
    intro t
    induction t with
    | nil => simp
    | cons a t ih =>
      rcases prefixGate_binary D β a with ha | ha <;>
        rcases ih with ih | ih <;> simp [ha, ih]
  exact h l.inits

/-- Page 178, the coefficient of the empty prime prefix is one. -/
theorem prefixRho_nil (D : ℝ) (β : ℝ) : prefixRho D β [] = 1 := by
  simp [prefixRho, prefixGate]

/-- Page 178 prefix product, adjoining the next prime multiplies by its gate. -/
theorem prefixRho_append (D : ℝ) (β : ℝ) (l : List ℕ) (p : ℕ) :
    prefixRho D β (l ++ [p]) = prefixRho D β l * prefixGate D β (l ++ [p]) := by
  simp [prefixRho, List.inits_append]

/-- Page 179 formula 3.6, killing the last gate kills the coefficient. -/
theorem prefixRho_zero_of_gate (D : ℝ) (β : ℝ) (l : List ℕ)
    (h : prefixGate D β l = 0) : prefixRho D β l = 0 := by
  unfold prefixRho
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨l, by simp, h⟩

/-- Page 179 formula 3.7, the signed prefix coefficients have absolute value at most one. -/
theorem rosserWeight_abs_le_one (D : ℝ) (β : ℝ) (d : ℕ) : |rosserWeight D β d| ≤ 1 := by
  unfold rosserWeight
  rcases prefixRho_binary D β d.primeFactorsList.reverse with h | h
  · simp [h]
  · simpa [h] using (show |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d))

/-- Page 178 normalization, the weight at one is one. -/
theorem rosserWeight_one (D : ℝ) (β : ℝ) : rosserWeight D β 1 = 1 := by
  simp [rosserWeight, prefixRho_nil]

/-- Page 178, nonsquarefree arguments have zero signed coefficient. -/
theorem rosserWeight_not_squarefree (D : ℝ) (β : ℝ) (d : ℕ) (hd : ¬ Squarefree d) :
    rosserWeight D β d = 0 := by
  simp [rosserWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- Page 178, a killed gate at any prefix kills the full product. -/
theorem prefixRho_zero_of_prefix (D : ℝ) (β : ℝ) (t l : List ℕ)
    (ht : t <+: l) (hg : prefixGate D β t = 0) : prefixRho D β l = 0 := by
  unfold prefixRho
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨t, (List.mem_inits t l).mpr ht, hg⟩

/-- Page 179 after formula 3.6, a descending nonempty prefix of size at least D
is killed. Odd length uses the last gate. Even length uses the penultimate gate. -/
theorem prefixRho_support_append (D : ℝ) (β : ℝ) (hβ : 1 ≤ β)
    (l : List ℕ) (p : ℕ) (hp : 1 ≤ p)
    (hsort : (l ++ [p]).Pairwise (· ≥ ·))
    (hD : D ≤ ((l ++ [p]).prod : ℝ)) : prefixRho D β (l ++ [p]) = 0 := by
  have hpp : (1 : ℝ) ≤ p := by exact_mod_cast hp
  by_cases ho : Odd (l ++ [p]).length
  · apply prefixRho_zero_of_gate
    unfold prefixGate
    apply ite_eq_left
    refine ⟨ho, hD.trans ?_⟩
    rw [List.getLastD_concat]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hpp (by linarith))
  · have hlodd : Odd l.length := by
      simp only [List.length_append, List.length_singleton, Nat.odd_iff] at ho ⊢
      omega
    have hlne : l ≠ [] := by
      intro he
      simp [he] at hlodd
    have hqmem : l.getLastD 1 ∈ l := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hlne]
      exact List.getLast_mem hlne
    have hpq : p ≤ l.getLastD 1 :=
      (List.pairwise_append.mp hsort).2.2 _ hqmem p (by simp)
    have hq : (1 : ℝ) ≤ l.getLastD 1 := by exact_mod_cast hp.trans hpq
    have hpqR : (p : ℝ) ≤ (l.getLastD 1 : ℝ) ^ β :=
      (show (p : ℝ) ≤ (l.getLastD 1 : ℝ) by exact_mod_cast hpq).trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq hβ)
    apply prefixRho_zero_of_prefix D β l _ (by exact ⟨[p], rfl⟩)
    unfold prefixGate
    apply ite_eq_left
    refine ⟨hlodd, hD.trans ?_⟩
    simp only [List.prod_append, List.prod_singleton, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hpqR (Nat.cast_nonneg _)

/-- Page 179 formula 3.7, every nonempty descending prime list above the level vanishes. -/
theorem prefixRho_support (D : ℝ) (β : ℝ) (hβ : 1 ≤ β)
    (l : List ℕ) (hl : l ≠ []) (hpos : ∀ p ∈ l, 1 ≤ p)
    (hsort : l.Pairwise (· ≥ ·)) (hD : D ≤ (l.prod : ℝ)) :
    prefixRho D β l = 0 := by
  have he := List.dropLast_append_getLast hl
  have hp := hpos (l.getLast hl) (List.getLast_mem hl)
  have h := prefixRho_support_append D β hβ l.dropLast (l.getLast hl) hp
  rw [he] at h
  exact h hsort hD

/-- Page 179 formula 3.7, the signed coefficients vanish strictly above D. -/
theorem rosserWeight_support (D : ℝ) (β : ℝ) (hβ : 1 ≤ β) (hD : 1 ≤ D)
    (d : ℕ) (hd : D < (d : ℝ)) : rosserWeight D β d = 0 := by
  by_cases hd0 : d = 0
  · simp [rosserWeight, hd0]
  have hd1 : d ≠ 1 := by intro h; subst d; norm_num at hd; linarith
  have hprod : d.primeFactorsList.reverse.prod = d := by
    rw [List.prod_reverse, Nat.prod_primeFactorsList hd0]
  have hl : d.primeFactorsList.reverse ≠ [] := by
    intro he
    rw [he, List.prod_nil] at hprod
    exact hd1 hprod.symm
  have hr := prefixRho_support D β hβ d.primeFactorsList.reverse hl
    (fun p hp => (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)).one_lt.le)
    (List.pairwise_reverse.mpr (Nat.isChain_primeFactorsList d).pairwise)
    (by simpa only [hprod] using hd.le)
  simp [rosserWeight, hr]

/-- Page 179 formula 3.7, the source strict support also kills the equality
endpoint whenever D exceeds one. -/
theorem rosserWeight_support_ge (D β : ℝ) (hβ : 1 ≤ β) (hD : 1 < D)
    (d : ℕ) (hd : D ≤ (d : ℝ)) : rosserWeight D β d = 0 := by
  have hd0 : d ≠ 0 := by intro he; subst d; norm_num at hd; linarith
  have hd1 : d ≠ 1 := by intro he; subst d; norm_num at hd; linarith
  have hprod : d.primeFactorsList.reverse.prod = d := by
    rw [List.prod_reverse, Nat.prod_primeFactorsList hd0]
  have hl : d.primeFactorsList.reverse ≠ [] := by
    intro he
    rw [he, List.prod_nil] at hprod
    exact hd1 hprod.symm
  have hr := prefixRho_support D β hβ d.primeFactorsList.reverse hl
    (fun p hp => (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)).one_lt.le)
    (List.pairwise_reverse.mpr (Nat.isChain_primeFactorsList d).pairwise)
    (by simpa only [hprod] using hd)
  simp [rosserWeight, hr]

/-- Page 178 before formula 3.1, the stop weight of a list prefix. -/
noncomputable def prefixStop (D β : ℝ) (l : List ℕ) : ℝ :=
  if l = [] then 0 else (1 - prefixGate D β l) * prefixRho D β l.dropLast

/-- Page 179 formula 3.6, a singleton prime prefix has exactly its first gate. -/
theorem prefixRho_singleton (D β : ℝ) (p : ℕ) :
    prefixRho D β [p] = if D ≤ (p : ℝ) * (p : ℝ) ^ β then 0 else 1 := by
  simp [prefixRho, prefixGate]

/-- Page 179 formula 3.6, the explicit upper coefficient at a prime. -/
theorem rosserWeight_prime (D β : ℝ) (p : ℕ) (hp : p.Prime) :
    rosserWeight D β p = if D ≤ (p : ℝ) * (p : ℝ) ^ β then 0 else -1 := by
  rw [rosserWeight, Nat.primeFactorsList_prime hp]
  simp only [List.reverse_singleton, prefixRho_singleton, ArithmeticFunction.moebius_apply_prime hp]
  split_ifs <;> norm_num

/-- Page 178 prefix products, adjoining a prime gives the next stop weight. -/
theorem prefixStop_append (D β : ℝ) (l : List ℕ) (p : ℕ) :
    prefixStop D β (l ++ [p]) = (1 - prefixGate D β (l ++ [p])) * prefixRho D β l := by
  simp [prefixStop]

/-- Page 178 formula 3.1, the first stop weights telescope exactly.
This identity is on a single chain of prefixes and uses no divisors or analytic input. -/
theorem prefix_stop_telescope (D β : ℝ) (l : List ℕ) :
    prefixRho D β l + (l.inits.map (prefixStop D β)).sum = 1 := by
  induction l using List.reverseRecOn with
  | nil => simp [prefixRho_nil, prefixStop]
  | append_singleton l p ih =>
    have hsum : ((l ++ [p]).inits.map (prefixStop D β)).sum =
        (l.inits.map (prefixStop D β)).sum + prefixStop D β (l ++ [p]) := by
      simp [List.inits_append]
    rw [prefixRho_append, hsum, prefixStop_append]
    nlinarith

/-- Page 178 before formula 3.1, sigma records the first failed gate.
The coefficient at one is zero. -/
noncomputable def stopRho (D : ℝ) (β : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then 0 else
    (1 - prefixGate D β d.primeFactorsList.reverse) *
      prefixRho D β d.primeFactorsList.reverse.dropLast

/-- Page 178, the remainder sieve of a singleton is zero or one.
It tests primes strictly below the smallest prime divisor of d. -/
noncomputable def singletonSift (n d : ℕ) : ℝ :=
  if ∀ p : ℕ, p.Prime → p < d.minFac → ¬ p ∣ n then 1 else 0

/-- Page 178 before formula 3.1, sigma is nonnegative. -/
theorem stopRho_nonneg (D : ℝ) (β : ℝ) (d : ℕ) : 0 ≤ stopRho D β d := by
  unfold stopRho
  split_ifs
  · exact le_rfl
  · rcases prefixGate_binary D β d.primeFactorsList.reverse with h | h <;>
      rcases prefixRho_binary D β d.primeFactorsList.reverse.dropLast with k | k <;>
        simp only [h, k] <;> norm_num

/-- Page 179 formula 3.2, the signed first failure has nonpositive sign. -/
theorem moebius_mul_stopRho_nonpos (D : ℝ) (β : ℝ) (d : ℕ) :
    (ArithmeticFunction.moebius d : ℝ) * stopRho D β d ≤ 0 := by
  by_cases hd : Squarefree d
  · by_cases hd1 : d = 1
    · simp [stopRho, hd1]
    rcases prefixGate_binary D β d.primeFactorsList.reverse with hg | hg
    · have ho : Odd d.primeFactorsList.length := by
        unfold prefixGate at hg
        split_ifs at hg with h
        · simpa only [List.length_reverse] using h.1
        · norm_num at hg
      have hmu : (ArithmeticFunction.moebius d : ℝ) = -1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hd, Int.cast_pow, Int.cast_neg,
          Int.cast_one, ArithmeticFunction.cardFactors_apply]
        exact ho.neg_one_pow
      rw [hmu]
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (stopRho_nonneg D β d)
    · simp [stopRho, hd1, hg]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- Page 178 formula 3.1, each singleton remainder sieve is nonnegative. -/
theorem singletonSift_nonneg (n d : ℕ) : 0 ≤ singletonSift n d := by
  unfold singletonSift
  split_ifs <;> norm_num

/-- Page 178 formula 3.1, pair a sublist with the same sublist followed
by the smallest prime. Odd stops have an even length parent and a positive sign. -/
theorem signed_prefix_pair_nonneg (D β : ℝ) (l : List ℕ) (p : ℕ) :
    0 ≤ (-1 : ℝ) ^ l.length * prefixRho D β l +
      (-1 : ℝ) ^ (l ++ [p]).length * prefixRho D β (l ++ [p]) := by
  rw [prefixRho_append]
  rcases prefixGate_binary D β (l ++ [p]) with hg | hg
  · have ho : Odd (l ++ [p]).length := by
      unfold prefixGate at hg
      split_ifs at hg with h
      · exact h.1
      · norm_num at hg
    have he : Even l.length := by
      simp only [List.length_append, List.length_singleton, Nat.odd_iff] at ho
      rw [Nat.even_iff]
      omega
    rw [hg, he.neg_one_pow]
    rcases prefixRho_binary D β l with hr | hr <;> simp [hr]
  · rw [hg]
    simp only [List.length_append, List.length_singleton, pow_succ, mul_one]
    ring_nf
    exact le_rfl

/-- Page 179 formula 3.4, density weighted pairing keeps the residual
factor one minus density times the extension gate. -/
theorem weighted_prefix_pair_identity (D β a : ℝ) (l : List ℕ) (p : ℕ) :
    (-1 : ℝ) ^ l.length * prefixRho D β l +
      (-1 : ℝ) ^ (l ++ [p]).length * prefixRho D β (l ++ [p]) * a =
        (-1 : ℝ) ^ l.length * prefixRho D β l *
          (1 - a * prefixGate D β (l ++ [p])) := by
  rw [prefixRho_append]
  simp only [List.length_append, List.length_singleton, pow_succ]
  ring

/-- Page 179 formula 3.4, the unweighted nonnegative pairing argument does
not transfer termwise to the density weighted main sum. This is a route
obstruction, not a claim about the paper. -/
theorem weighted_pair_negative :
    (-1 : ℝ) ^ ([7] : List ℕ).length * prefixRho 100 1 [7] +
      (-1 : ℝ) ^ ([7, 5] : List ℕ).length * prefixRho 100 1 [7, 5] * (1 / 2) < 0 := by
  norm_num [prefixRho, prefixGate, Nat.odd_iff]

/-- Page 178 formula 3.1, pairing at the smallest prime gives a nonnegative
truncated inclusion exclusion sum on every nonempty list. -/
theorem signed_sublists_upper (D β : ℝ) (l : List ℕ) :
    (if l = [] then 1 else 0) ≤
      (l.sublists.map (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t)).sum := by
  induction l using List.reverseRecOn with
  | nil => simp [prefixRho_nil]
  | append_singleton l p ih =>
    simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ite_false]
    rw [List.sublists_concat, List.map_append, List.sum_append, List.map_map]
    rw [← List.sum_map_add]
    apply List.sum_nonneg
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact signed_prefix_pair_nonneg D β t p

/-- Page 178 prime prefix convention, descending primes give the exact factor list. -/
theorem descending_prime_factorization (l : List ℕ) (hp : ∀ p ∈ l, Nat.Prime p)
    (hs : l.Pairwise (· ≥ ·)) : l.prod.primeFactorsList.reverse = l := by
  have hperm : l.reverse.Perm l.prod.primeFactorsList :=
    Nat.primeFactorsList_unique (by simp) (fun p hp' => hp p (List.mem_reverse.mp hp'))
  have heq := hperm.eq_of_pairwise' (List.pairwise_reverse.mpr hs)
    (Nat.isChain_primeFactorsList l.prod).pairwise
  simpa using (congrArg List.reverse heq).symm

/-- Page 178 prime prefix convention, a distinct prime list has squarefree product. -/
theorem descending_prime_product_squarefree (l : List ℕ) (hp : ∀ p ∈ l, Nat.Prime p)
    (hs : l.Pairwise (· ≥ ·)) (hn : l.Nodup) : Squarefree l.prod := by
  have h0 : l.prod ≠ 0 := by
    intro hh
    exact (hp 0 (List.prod_eq_zero_iff.mp hh)).ne_zero rfl
  rw [Nat.squarefree_iff_nodup_primeFactorsList h0]
  have h := descending_prime_factorization l hp hs
  apply List.nodup_reverse.mp
  rw [h]
  exact hn

/-- Page 178 formula 3.1, on a distinct prime list the signed weight is its
alternating sign times the prefix gate product. -/
theorem rosserWeight_prod (D β : ℝ) (l : List ℕ) (hp : ∀ p ∈ l, Nat.Prime p)
    (hs : l.Pairwise (· ≥ ·)) (hn : l.Nodup) :
    rosserWeight D β l.prod = (-1 : ℝ) ^ l.length * prefixRho D β l := by
  have hf := descending_prime_factorization l hp hs
  have hsf := descending_prime_product_squarefree l hp hs hn
  have hlen : l.prod.primeFactorsList.length = l.length := by
    simpa only [List.length_reverse] using congrArg List.length hf
  unfold rosserWeight
  rw [hf, ArithmeticFunction.moebius_apply_of_squarefree hsf, Int.cast_pow,
    Int.cast_neg, Int.cast_one, ArithmeticFunction.cardFactors_apply, hlen]

/-- LEAF: Iwaniec page 178 Lemma 1 formula 3.1, the squarefree divisor
change of variables. Distinct descending prime sublists enumerate exactly
the divisors with nonzero Moebius coefficient. This identity has no analytic
hypothesis, no inequality and no sieve estimate. -/
theorem divisor_prefix_expansion (D β : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, rosserWeight D β d) =
      (n.primeFactorsList.dedup.reverse.sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t)).sum := by
  let L := n.primeFactorsList.dedup.reverse
  have hLnodup : L.Nodup := List.nodup_reverse.mpr (List.nodup_dedup _)
  have hLsort : L.Pairwise (· ≥ ·) := List.pairwise_reverse.mpr
    ((Nat.isChain_primeFactorsList n).pairwise.sublist (List.dedup_sublist _))
  have hLprime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp (List.mem_reverse.mp hp))
  have hLdvd : L.prod ∣ n := by
    have hd := (List.dedup_sublist n.primeFactorsList).prod_dvd_prod
    rw [Nat.prod_primeFactorsList hn] at hd
    simpa only [L, List.prod_reverse] using hd
  have hprops : ∀ t ∈ L.sublists.toFinset,
      (∀ p ∈ t, Nat.Prime p) ∧ t.Pairwise (· ≥ ·) ∧ t.Nodup := by
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    exact ⟨fun p hp => hLprime p (hsub.subset hp), hLsort.sublist hsub, hLnodup.sublist hsub⟩
  have hsum : (∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod) =
      ∑ d ∈ n.divisors.filter Squarefree, rosserWeight D β d := by
    apply Finset.sum_bij (fun t ht => t.prod)
    · intro t ht
      obtain ⟨hp, hs, hnd⟩ := hprops t ht
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hsub.prod_dvd_prod.trans hLdvd, hn⟩,
        descending_prime_product_squarefree t hp hs hnd⟩
    · intro t ht u hu he
      obtain ⟨htp, hts, htnd⟩ := hprops t ht
      obtain ⟨hup, hus, hund⟩ := hprops u hu
      have htF := descending_prime_factorization t htp hts
      have huF := descending_prime_factorization u hup hus
      rw [he] at htF
      exact htF.symm.trans huF
    · intro d hd
      obtain ⟨hdiv, hsq⟩ := Finset.mem_filter.mp hd
      have hdn : d ≠ 0 := (Nat.pos_of_mem_divisors hdiv).ne'
      have htnd : d.primeFactorsList.reverse.Nodup :=
        List.nodup_reverse.mpr ((Nat.squarefree_iff_nodup_primeFactorsList hdn).mp hsq)
      have hts : d.primeFactorsList.reverse.Pairwise (· ≥ ·) :=
        List.pairwise_reverse.mpr (Nat.isChain_primeFactorsList d).pairwise
      have hsubset : d.primeFactorsList.reverse ⊆ L := by
        intro p hp
        apply List.mem_reverse.mpr
        apply List.mem_dedup.mpr
        exact (Nat.primeFactorsList_sublist_of_dvd (Nat.dvd_of_mem_divisors hdiv) hn).subset
          (List.mem_reverse.mp hp)
      have htL : List.Sublist d.primeFactorsList.reverse L :=
        List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htnd hsubset) hts hLsort
      refine ⟨d.primeFactorsList.reverse, List.mem_toFinset.mpr (List.mem_sublists.mpr htL), ?_⟩
      rw [List.prod_reverse, Nat.prod_primeFactorsList hdn]
    · intro t ht
      rfl
  have hfilter : (∑ d ∈ n.divisors.filter Squarefree, rosserWeight D β d) =
      ∑ d ∈ n.divisors, rosserWeight D β d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnsq : ¬ Squarefree d := by simpa only [Finset.mem_filter, hd, true_and] using hnot
    exact rosserWeight_not_squarefree D β d hnsq
  rw [← hfilter, ← hsum]
  have he : (∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod) =
      ∑ t ∈ L.sublists.toFinset, (-1 : ℝ) ^ t.length * prefixRho D β t := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hp, hs, hnd⟩ := hprops t ht
    exact rosserWeight_prod D β t hp hs hnd
  rw [he, List.sum_toFinset _ (List.nodup_sublists.mpr hLnodup)]

/-- Pages 178 and 179 formulas 3.1 to 3.6, prime sublist pairing implies
upper Moebius domination from the exact divisor expansion. -/
theorem rosserWeight_upper (D : ℝ) (β : ℝ) :
    BoundingSieve.IsUpperMoebius (rosserWeight D β) := by
  intro n
  by_cases hn : n = 0
  · simp [hn]
  rw [divisor_prefix_expansion D β n hn]
  have h := signed_sublists_upper D β n.primeFactorsList.dedup.reverse
  by_cases hn1 : n = 1
  · subst n
    simpa using h
  · have hl : n.primeFactorsList.dedup.reverse ≠ [] := by
      intro he
      have hf := (List.dedup_eq_nil _).mp (List.reverse_eq_nil_iff.mp he)
      exact (not_or.mpr ⟨hn, hn1⟩) ((Nat.primeFactorsList_eq_nil n).mp hf)
    simpa only [ite_eq_right_iff.mpr (fun he => (hl he).elim), ite_eq_right hn1] using h

/-- Pages 178 and 179 formulas 3.4, 3.6 and 3.7, the explicit construction
has all three algebraic coefficient properties. -/
theorem rosser_coefficients (D : ℝ) (β : ℝ) (hD : 1 ≤ D) (hβ : 1 ≤ β) :
    BoundingSieve.IsUpperMoebius (rosserWeight D β) ∧
      (∀ d : ℕ, D < (d : ℝ) → rosserWeight D β d = 0) ∧
      (∀ d : ℕ, |rosserWeight D β d| ≤ 1) := by
  exact ⟨rosserWeight_upper D β, rosserWeight_support D β hβ hD,
    rosserWeight_abs_le_one D β⟩

end LeanLab.KumchevLiu2007.Task558a



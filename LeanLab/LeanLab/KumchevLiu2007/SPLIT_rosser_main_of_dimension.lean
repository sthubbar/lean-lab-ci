/-
Split of the Rosser main sum dimension estimate of Decomp558b.
The target is carved into two exact identities on the coefficient sum and one
main estimate on the prime chain sum.  The identities transport the divisor sum
of the model into an alternating sum of prefix products, and transport the
product over the prime factors of the sieve product into the strict product.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp558b

namespace LeanLab.KumchevLiu2007.Task558b

open Real Task506b Task506d Task506e Task558a
open scoped BigOperators Topology

/- ===== private helpers (WIP pass 2026-11-17) ===== -/

/-- The local factor product over the sieve support.  The split's leaf one
ranges over `(primeProduct X δ n).primeFactorsList.dedup.toFinset`, which is
that support; a support prime carries positive density and every strict-cutoff
prime outside it carries density zero, so the two products agree. -/
private theorem strictProduct_eq_prod_primeSupport (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n = ∏ p ∈ primeSupport X δ n, (1 - density n p) := by
  classical
  unfold strictProduct primeSupport
  symm
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    obtain ⟨hmem, hprime, hpz, hpos⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hprime⟩, hpz⟩
  · intro p hp hnot
    obtain ⟨hpT, hpz⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := (Finset.mem_filter.mp hpT).2
    have hzero : density n p = 0 := by
      have hnp : ¬ (0 < density n p) := fun hpos =>
        hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, hprime, hpz, hpos⟩)
      linarith [density_nonneg n p]
    rw [hzero, sub_zero]

/-- The prime factor set of the sifting product is the sieve support. -/
private theorem primeFactors_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactors = primeSupport X δ n := by
  classical
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    exact prime_mem_of_dvd_product X δ n p hp hdvd
  · intro hp
    refine ⟨(Finset.mem_filter.mp hp).2.1, Finset.dvd_prod_of_mem _ hp, ?_⟩
    exact (primeProduct_squarefree X δ n).ne_zero

/-- The distinct prime factors of the sifting product, as a finset, are the
sieve support: `primeFactors` is `primeFactorsList.toFinset`, so `dedup` is
harmless.  This is the index set of the split's leaf one. -/
private theorem primeFactorsList_dedup_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactorsList.dedup.toFinset = primeSupport X δ n := by
  rw [List.toFinset_dedup, Nat.toFinset_factors, primeFactors_primeProduct]

/-- Iwaniec page 179 formula 3.4 with the density weight: the Rosser main sum of
a `BoundingSieve` is the alternating sum over the distinct descending prime
sublists of its sifting product, each term carrying the product of the local
densities over the sublist. -/
private theorem mainSum_eq_sublists (s : BoundingSieve) (D β : ℝ) :
    s.mainSum (rosserWeight D β) =
      ((s.prodPrimes.primeFactorsList.dedup.reverse).sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t *
          ∏ p ∈ t.toFinset, s.nu p)).sum := by
  classical
  have hn : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  let L := s.prodPrimes.primeFactorsList.dedup.reverse
  have hLnodup : L.Nodup := List.nodup_reverse.mpr (List.nodup_dedup _)
  have hLsort : L.Pairwise (· ≥ ·) := List.pairwise_reverse.mpr
    ((Nat.isChain_primeFactorsList s.prodPrimes).pairwise.sublist (List.dedup_sublist _))
  have hLprime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp (List.mem_reverse.mp hp))
  have hLdvd : L.prod ∣ s.prodPrimes := by
    have hd := (List.dedup_sublist s.prodPrimes.primeFactorsList).prod_dvd_prod
    rw [Nat.prod_primeFactorsList hn] at hd
    simpa only [L, List.prod_reverse] using hd
  have hprops : ∀ t ∈ L.sublists.toFinset,
      (∀ p ∈ t, Nat.Prime p) ∧ t.Pairwise (· ≥ ·) ∧ t.Nodup := by
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    exact ⟨fun p hp => hLprime p (hsub.subset hp), hLsort.sublist hsub, hLnodup.sublist hsub⟩
  have hbij : (∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod) =
      ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d := by
    apply Finset.sum_bij (fun t _ => t.prod)
    · intro t ht
      obtain ⟨hp, hs, hnd⟩ := hprops t ht
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hsub.prod_dvd_prod.trans hLdvd, hn⟩,
          descending_prime_product_squarefree t hp hs hnd⟩
    · intro t ht u hu he
      obtain ⟨htp, hts, htnd⟩ := hprops t ht
      obtain ⟨hup, hus, hund⟩ := hprops u hu
      have htF := descending_prime_factorization t htp hts
      have huF := descending_prime_factorization u hup hus
      rw [he] at htF
      exact htF.symm.trans huF
    · intro d hd
      obtain ⟨hdiv, hdSq⟩ := Finset.mem_filter.mp hd
      have hdn : d ≠ 0 := (Nat.pos_of_mem_divisors hdiv).ne'
      have htnd : d.primeFactorsList.reverse.Nodup :=
        List.nodup_reverse.mpr ((Nat.squarefree_iff_nodup_primeFactorsList hdn).mp hdSq)
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
  have hfilter : (∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d) =
      ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnsq : ¬ Squarefree d := by simpa only [Finset.mem_filter, hd, true_and] using hnot
    rw [rosserWeight_not_squarefree D β d hnsq, zero_mul]
  have hterm : ∀ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod =
      (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p := by
    intro t ht
    obtain ⟨htp, hts, htnd⟩ := hprops t ht
    rw [rosserWeight_prod D β t htp hts htnd]
    have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
      have h := List.prod_toFinset (f := id) htnd
      simpa using h
    have hndid : ∏ p ∈ t.toFinset, s.nu p = s.nu (∏ p ∈ t.toFinset, p) :=
      (ArithmeticFunction.IsMultiplicative.map_prod_of_prime s.nu_mult t.toFinset
        (fun p hp => htp p (List.mem_toFinset.mp hp))).symm
    rw [hndid, hprod]
  calc s.mainSum (rosserWeight D β)
      = ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := rfl
    _ = ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d :=
        hfilter.symm
    _ = ∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod := hbij.symm
    _ = ∑ t ∈ L.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p :=
        Finset.sum_congr rfl hterm
    _ = _ := List.sum_toFinset _ (List.nodup_sublists.mpr hLnodup)

/-- LEAF: step one of the proof, the local product identity.  The strict
product below the close cutoff equals the product of the one minus local
factors taken over the distinct prime factors of the squarefree sieve product.
A prime outside the sieve support carries density zero, so its factor is one
on both sides and the two products agree.  This is an identity in the
definitions alone: it names no main sum, no level and no dimension estimate. -/
theorem strictProduct_eq_primeFactors_prod (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n =
      ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset, (1 - density n p) := by
  rw [strictProduct_eq_prod_primeSupport, primeFactorsList_dedup_primeProduct]

/-- LEAF: step two of the proof, the weighted divisor to chain identity.  The
main sum of the explicit weights over the divisors of the sieve product equals
the alternating sum of prefix products over the distinct prime sublists, each
sublist carrying its own local factor at the product of the sublist.  This is
the weighted form of the squarefree divisor change of variables, so it is an
identity and it mentions no inequality, no constant and no level condition. -/
theorem mainSum_eq_chain_sum (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β)
      = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod := by
  classical
  have h := mainSum_eq_sublists (sieveModel X B δ ε n hn) D β
  rw [show (sieveModel X B δ ε n hn).prodPrimes = primeProduct X δ n from rfl] at h
  rw [h]
  rw [← List.sum_toFinset _
    (List.nodup_sublists.mpr (List.nodup_reverse.mpr (List.nodup_dedup _)))]
  apply Finset.sum_congr rfl
  intro t ht
  have hnu : ∀ p : ℕ, (sieveModel X B δ ε n hn).nu p = density n p := fun p => rfl
  simp only [hnu]
  have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
  have hnd : t.Nodup :=
    (List.nodup_reverse.mpr (List.nodup_dedup _)).sublist hsub
  have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactorsList
      (List.mem_dedup.mp (List.mem_reverse.mp (hsub.subset hp)))
  have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
    have hh := List.prod_toFinset (f := id) hnd
    simpa using hh
  have hndid : ∏ p ∈ t.toFinset, density n p = density n t.prod := by
    rw [← hprod]
    exact (ArithmeticFunction.IsMultiplicative.map_prod_of_prime (density_isMultiplicative n)
      (f := densityFunction n) t.toFinset
      (fun p hp => hprime p (List.mem_toFinset.mp hp))).symm
  rw [hndid]

/- ===== WIP pass 2026-11-17 (second): the crude majorant of the chain sum ===== -/

/-- Summing `∏ p ∈ t, f p` over all sublists of a nodup list multiplies out to
`∏ p ∈ L, (1 + f p)`.  This is the list form of `Finset.prod_one_add`. -/
private theorem sum_sublists_prod (L : List ℕ) (hL : L.Nodup) (f : ℕ → ℝ) :
    (∑ t ∈ L.sublists.toFinset, ∏ p ∈ t.toFinset, f p) = ∏ p ∈ L.toFinset, (1 + f p) := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL' : L.Nodup := (List.nodup_cons.mp hL).2
    have ha : a ∉ L := (List.nodup_cons.mp hL).1
    have hset : (a :: L).sublists.toFinset
        = L.sublists.toFinset ∪ (L.sublists.map (List.cons a)).toFinset := by
      rw [← List.toFinset_append]
      exact List.toFinset_eq_of_perm _ _ (List.sublists_cons_perm_append a L)
    have hdisj : Disjoint L.sublists.toFinset (L.sublists.map (List.cons a)).toFinset := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      rw [List.mem_toFinset, List.mem_map] at ht2
      obtain ⟨u, -, rfl⟩ := ht2
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht1)
      exact ha (hsub.subset (List.mem_cons_self : a ∈ a :: u))
    have hmapset : (L.sublists.map (List.cons a)).toFinset
        = L.sublists.toFinset.image (List.cons a) := by
      ext t
      simp [List.mem_toFinset, List.mem_map]
    have hmap : (∑ t ∈ (L.sublists.map (List.cons a)).toFinset, ∏ p ∈ t.toFinset, f p)
        = f a * ∑ u ∈ L.sublists.toFinset, ∏ p ∈ u.toFinset, f p := by
      rw [hmapset, Finset.sum_image (fun u _ v _ h => (List.cons.inj h).2), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hau : a ∉ u := fun hmem =>
        ha ((List.mem_sublists.mp (List.mem_toFinset.mp hu)).subset hmem)
      rw [List.toFinset_cons, Finset.prod_insert (by simpa using hau)]
    rw [hset, Finset.sum_union hdisj, ih hL', hmap, ih hL', List.toFinset_cons,
      Finset.prod_insert (by simpa using ha)]
    ring

/-- The density of a product of distinct primes is the product of the densities. -/
private theorem density_prod_eq_of_nodup {t : List ℕ} (hnd : t.Nodup)
    (hp : ∀ p ∈ t, Nat.Prime p) (n : ℕ) :
    density n t.prod = ∏ p ∈ t.toFinset, density n p := by
  have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
    have h := List.prod_toFinset (f := id) hnd
    simpa using h
  rw [← hprod]
  exact ArithmeticFunction.IsMultiplicative.map_prod_of_prime (density_isMultiplicative n)
    (f := densityFunction n) t.toFinset (fun p hp' => hp p (List.mem_toFinset.mp hp'))

/-- The crude majorant of the Rosser chain sum: dropping the sign and the prefix
weights bounds the main sum by the product of `1 + density` over the sieve
support.  On the dimension-two band `∏ (1 + density)` exceeds `∏ (1 - density)`
by a factor of order `(log z)^4`, so this is a starting point, not the leaf. -/
private theorem mainSum_le_prod_one_add (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β)
      ≤ ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset, (1 + density n p) := by
  classical
  have hLnodup : (primeProduct X δ n).primeFactorsList.dedup.reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_dedup _)
  rw [mainSum_eq_chain_sum X B δ ε D β n hn]
  have hterm : ∀ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
      (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod
        ≤ ∏ p ∈ t.toFinset, density n p := by
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    have hnd : t.Nodup := hLnodup.sublist hsub
    have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactorsList
        (List.mem_dedup.mp (List.mem_reverse.mp (hsub.subset hp)))
    have hg := density_prod_eq_of_nodup hnd hprime n
    have hsign : (-1 : ℝ) ^ t.length ≤ 1 := by
      rcases neg_one_pow_eq_or ℝ t.length with h | h <;> rw [h] <;> norm_num
    have hρle : prefixRho D β t ≤ 1 := by
      rcases prefixRho_binary D β t with h | h <;> rw [h] <;> norm_num
    have hρnn : (0 : ℝ) ≤ prefixRho D β t := by
      rcases prefixRho_binary D β t with h | h <;> rw [h] <;> norm_num
    calc (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod
        ≤ 1 * 1 * density n t.prod := by
          refine mul_le_mul (mul_le_mul hsign hρle hρnn zero_le_one) le_rfl
            (density_nonneg n t.prod) (by norm_num)
      _ = ∏ p ∈ t.toFinset, density n p := by rw [one_mul, one_mul, hg]
  refine (Finset.sum_le_sum hterm).trans ?_
  calc ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
        ∏ p ∈ t.toFinset, density n p
      ≤ ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.toFinset,
          (1 + density n p) := (sum_sublists_prod _ hLnodup (density n)).le
    _ = ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
          (1 + density n p) := by rw [List.toFinset_reverse]

/- ===== WIP pass 2026-11-17 (second): the dominating-level end, exactly ===== -/

/-- Every prefix of the descending factor list of a squarefree `d` has product at
most `d`. -/
private theorem prod_le_of_sublist_primeFactors {d : ℕ} (hsq : Squarefree d) {t : List ℕ}
    (h : t <+: d.primeFactorsList.reverse) : t.prod ≤ d := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hnd : d.primeFactorsList.reverse.Nodup := by
    rw [List.nodup_reverse]
    exact (Nat.squarefree_iff_nodup_primeFactorsList hd0).mp hsq
  have hnd' : t.Nodup := h.nodup hnd
  have hsub : t.toFinset ⊆ d.primeFactorsList.reverse.toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr (h.subset (List.mem_toFinset.mp hp))
  have hone : ∀ p ∈ d.primeFactorsList.reverse.toFinset, p ∉ t.toFinset → 1 ≤ p := by
    intro p hp _
    have hp' : p ∈ d.primeFactorsList.reverse := List.mem_toFinset.mp hp
    exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp')).one_lt.le
  have h1 : t.prod = ∏ p ∈ t.toFinset, p := by
    have hprod := List.prod_toFinset (f := id) hnd'
    simp only [List.map_id] at hprod
    simpa using hprod.symm
  have h2 : (∏ p ∈ d.primeFactorsList.reverse.toFinset, p) = d.primeFactorsList.reverse.prod := by
    have hprod := List.prod_toFinset (f := id) hnd
    simp only [List.map_id] at hprod
    simpa using hprod
  calc t.prod = ∏ p ∈ t.toFinset, p := h1
    _ ≤ ∏ p ∈ d.primeFactorsList.reverse.toFinset, p :=
        Finset.prod_le_prod_of_subset_of_one_le hsub hone
    _ = d.primeFactorsList.reverse.prod := h2
    _ = d := by rw [List.prod_reverse, Nat.prod_primeFactorsList hd0]

/-- The last entry of such a prefix is at most `d`. -/
private theorem getLastD_le_of_sublist_primeFactors {d : ℕ} (hsq : Squarefree d) {t : List ℕ}
    (h : t <+: d.primeFactorsList.reverse) : t.getLastD 1 ≤ d := by
  have hdvd : ∀ p ∈ t, p ∣ d := fun p hp =>
    Nat.dvd_of_mem_primeFactorsList (List.mem_reverse.mp (h.subset hp))
  have hdpos : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  rcases List.eq_nil_or_concat t with rfl | ⟨l, a, rfl⟩
  · exact hdpos
  · have hne : l.concat a ≠ [] := by simp
    have hmem : (l.concat a).getLastD 1 ∈ l.concat a := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      exact List.getLast_mem hne
    exact Nat.le_of_dvd hdpos (hdvd _ hmem)

/-- A list all of whose prefix gates are open has prefix product one. -/
private theorem prefixRho_eq_one_of_gates {D β : ℝ} {l : List ℕ}
    (h : ∀ t ∈ l.inits, prefixGate D β t = 1) : prefixRho D β l = 1 := by
  unfold prefixRho
  have hmap : l.inits.map (prefixGate D β) = l.inits.map (fun _ => 1) := List.map_congr_left h
  rw [hmap]
  simp

/-- Iwaniec page 179 formula 3.7, dominating level: when `D` exceeds
`(prod P)^(1+beta)` no prefix gate fires, so the Rosser weight is the plain
Moebius weight on every divisor of the sifting product and the main sum is
exactly the local product. -/
private theorem mainSum_rosserWeight_eq_prod_of_dominating (s : BoundingSieve) (D β : ℝ)
    (hβ : 1 ≤ β) (hdom : (s.prodPrimes : ℝ) * (s.prodPrimes : ℝ) ^ β < D) :
    s.mainSum (rosserWeight D β) = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  classical
  have hsqP : Squarefree s.prodPrimes := s.prodPrimes_squarefree
  have hPpos : 0 < s.prodPrimes := Nat.pos_of_ne_zero hsqP.ne_zero
  have hPnn : (0 : ℝ) ≤ (s.prodPrimes : ℝ) := Nat.cast_nonneg _
  have hw : ∀ d ∈ s.prodPrimes.divisors,
      rosserWeight D β d = (ArithmeticFunction.moebius d : ℝ) := by
    intro d hd
    have hdvd : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
    have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd hsqP
    have hdle : d ≤ s.prodPrimes := Nat.le_of_dvd hPpos hdvd
    have hgate : ∀ t ∈ d.primeFactorsList.reverse.inits, prefixGate D β t = 1 := by
      intro t ht
      have hsub : t <+: d.primeFactorsList.reverse := (List.mem_inits t _).mp ht
      have hprod : (t.prod : ℝ) ≤ (s.prodPrimes : ℝ) := by
        exact_mod_cast (prod_le_of_sublist_primeFactors hsqd hsub).trans hdle
      have hlast : (t.getLastD 1 : ℝ) ≤ (s.prodPrimes : ℝ) := by
        exact_mod_cast (getLastD_le_of_sublist_primeFactors hsqd hsub).trans hdle
      have hlastnn : (0 : ℝ) ≤ (t.getLastD 1 : ℝ) := Nat.cast_nonneg _
      have hpow : (t.getLastD 1 : ℝ) ^ β ≤ (s.prodPrimes : ℝ) ^ β :=
        Real.rpow_le_rpow hlastnn hlast (by linarith)
      have hle : (t.prod : ℝ) * (t.getLastD 1 : ℝ) ^ β ≤
          (s.prodPrimes : ℝ) * (s.prodPrimes : ℝ) ^ β :=
        mul_le_mul hprod hpow (Real.rpow_nonneg hlastnn β) hPnn
      unfold prefixGate
      rw [ite_eq_right]
      rintro ⟨-, hDle⟩
      linarith
    have hrho := prefixRho_eq_one_of_gates hgate
    simp only [rosserWeight, hrho, mul_one]
  calc s.mainSum (rosserWeight D β)
      = ∑ d ∈ s.prodPrimes.divisors, (ArithmeticFunction.moebius d : ℝ) * s.nu d := by
        unfold BoundingSieve.mainSum
        exact Finset.sum_congr rfl fun d hd => by rw [hw d hd]
    _ = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
        rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
          s.nu s.nu_mult hsqP]

/-- The dominating-level end in the shape of the leaf: `mainSum` equals the strict
product, so the chain estimate holds there with `C = 1`. -/
private theorem mainSum_eq_strictProduct_of_dominating (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n)
    (hβ : 1 ≤ β)
    (hdom : (primeProduct X δ n : ℝ) * (primeProduct X δ n : ℝ) ^ β < D) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β) = strictProduct X δ n := by
  have h := mainSum_rosserWeight_eq_prod_of_dominating (sieveModel X B δ ε n hn) D β hβ hdom
  rw [show (sieveModel X B δ ε n hn).prodPrimes = primeProduct X δ n from rfl] at h
  have hnu : ∀ p : ℕ, (sieveModel X B δ ε n hn).nu p = density n p := fun p => rfl
  rw [h, primeFactors_primeProduct]
  simp only [hnu]
  rw [← strictProduct_eq_prod_primeSupport]

/-- The bottom of the level range: for `D ≤ 1` the first gate of every nonempty
sublist is already shut, so the chain sum is exactly its `t = []` term, `1`. -/
private theorem mainSum_eq_one_of_level_le_one (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n)
    (hβ : 1 ≤ β) (hD : D ≤ 1) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β) = 1 := by
  classical
  have hLnodup : (primeProduct X δ n).primeFactorsList.dedup.reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_dedup _)
  have hgate : ∀ p : ℕ, p.Prime → prefixGate D β [p] = 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := hp.two_le
      exact_mod_cast this
    have hpow : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
    have hpow' : (p : ℝ) ≤ (p : ℝ) ^ β := by
      simpa only [Real.rpow_one] using hpow
    have hmul : (p : ℝ) * (p : ℝ) ≤ (p : ℝ) * (p : ℝ) ^ β :=
      mul_le_mul_of_nonneg_left hpow' (by linarith)
    have hprod : (p : ℝ) * (p : ℝ) ^ β ≥ 4 := by nlinarith
    unfold prefixGate
    rw [ite_eq_left]
    refine ⟨by simp, ?_⟩
    have hlast : ([p] : List ℕ).getLastD 1 = p := rfl
    simp only [List.prod_singleton, hlast]
    linarith
  have hzero : ∀ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
      t ≠ [] → (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod = 0 := by
    intro t ht hne
    obtain ⟨p, e, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hprime : p.Prime := by
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
      exact Nat.prime_of_mem_primeFactorsList
        (List.mem_dedup.mp (List.mem_reverse.mp (hsub.subset (List.mem_cons_self))))
    have hsub : [p] <+: p :: e := ⟨e, rfl⟩
    rw [prefixRho_zero_of_prefix D β [p] (p :: e) hsub (hgate p hprime)]
    simp
  rw [mainSum_eq_chain_sum X B δ ε D β n hn]
  have hmem : ([] : List ℕ)
      ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset := by
    simp
  rw [Finset.sum_eq_single ([] : List ℕ) (fun b hb hne => hzero b hb hne)
    (fun hnot => absurd hmem hnot)]
  simp [prefixRho_nil, density_one]

/-- LEAF: step three of the proof, the chain main estimate.  For the dimension
constant it chooses a real exponent at least one, a positive constant and a
positive level exponent, and then the alternating chain sum of prefix products
over the distinct prime sublists is at most the constant times the product of
one minus the local factors, uniformly in the level, whenever the level
exponent dominates the cutoff, the cutoff is at least two, and the band
estimate for the inverse local product holds below the cutoff.  This is one
inequality about the chain sum: it carries no sieve model, no sequence, no B
and no upper divisor input. -/
theorem chain_sum_le_support_prod (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X δ D : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ D →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
            (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod) ≤
          C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
            (1 - density n p) := by
  sorry

/-- The sealed target statement, assembled from the three leaves with no
admission and without the target theorem.  The existential parameters and the
constant come from the chain estimate.  The weighted divisor to chain identity
rewrites the main sum into the chain sum, and the local product identity
rewrites the chain bound into the strict product bound. -/
theorem rosser_main_of_dimension_split (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X B δ ε : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ Y X ε ^ (1 / 9 : ℝ) →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β) ≤
          C * strictProduct X δ n := by
  obtain ⟨β, C, s, hβ, hC, hs, hcore⟩ := chain_sum_le_support_prod K hK
  refine ⟨β, C, s, hβ, hC, hs, ?_⟩
  intro X B δ ε n hn hz hlev hband
  calc
    (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β)
        = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
              (-1 : ℝ) ^ t.length * prefixRho (Y X ε ^ (1 / 9 : ℝ)) β t *
                density n t.prod :=
          mainSum_eq_chain_sum X B δ ε (Y X ε ^ (1 / 9 : ℝ)) β n hn
    _ ≤ C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
          (1 - density n p) :=
          hcore X δ (Y X ε ^ (1 / 9 : ℝ)) n hn hz hlev hband
    _ = C * strictProduct X δ n := by rw [strictProduct_eq_primeFactors_prod]

end LeanLab.KumchevLiu2007.Task558b

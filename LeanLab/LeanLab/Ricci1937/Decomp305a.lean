import LeanLab.Ricci1937.DecompJ365

/-!
Ricci 1937, decreasing sieve count bridges.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Second memoir pages 106 and 107 formula 24.5.
The finite decreasing sieve uses the actual pair densities and periodic counts. -/
lemma decomp305_pair_decreasing_lower (h N : ℕ) (P J : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (cutoff level : ℕ → ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ P, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := P.powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) -
      L * (1 + Real.log L) ^ 2 ≤
      #{i ∈ range N | ∀ p ∈ P, ¬ p ∣ i * (i + h)} := by
  apply decompJ365_decreasing_lower_explicit (range N) P J
    (fun i => i * (i + h)) hP cutoff level h N (nuN h) ?_ L hL hlevel
  intro S hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hd : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hprime p hp).pos)
  have hdensity : (cnt h (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) =
      ∏ p ∈ S, nuN h p := by
    rw [cnt_prod_primes h S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN h p) =
      (cnt h (∏ p ∈ S, p) : ℝ) * N / (∏ p ∈ S, p) := by
    rw [← hdensity]
    ring
  rw [hmain]
  exact decompJ365_pair_periodic_remainder h N (∏ p ∈ S, p) hd


example :
    (12 : ℝ) * (∑ S ∈ ({2} : Finset ℕ).powerset,
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN 2 p) - 2 * (1 + Real.log 2) ^ 2 ≤
      #{i ∈ range 12 | ∀ p ∈ ({2} : Finset ℕ), ¬ p ∣ i * (i + 2)} := by
  simpa using decomp305_pair_decreasing_lower 2 12 {2} ∅
    (by intro p hp; have hp2 := mem_singleton.mp hp; subst p; exact Nat.prime_two)
    (fun _ => 0) (fun _ => 0) 2 (by norm_num)
    (by
      intro S hS _
      have hs : S = ∅ ∨ S = {2} := Finset.subset_singleton_iff.mp hS
      rcases hs with rfl | rfl <;> norm_num)

/-- First memoir pages 75, 88 and 89.
A pair sieve at the absolute gap injects into Z for either sign of the shift.
The shortened interval keeps both natural values below xi. -/
lemma decomp305_pair_survivors_le_zCount (a b ξ N t : ℕ) (m : ℤ)
    (ht : 2 ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (t : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t) :
    #{y ∈ range N | ∀ p ∈ Nat.primesLE t, ¬ p ∣ y * (y + 2 * m.natAbs)} ≤
      zCount a b m ξ := by
  let h := 2 * m.natAbs
  let f : ℕ → ℕ := fun y => if 0 ≤ m then y else y + h
  have hgap : (h : ℤ) = 2 * |m| := by simp [h, Int.natCast_natAbs]
  have hvalues (y : ℕ) :
      (f y : ℤ) + 2 * m = if 0 ≤ m then (y + h : ℕ) else y := by
    dsimp [f]
    split_ifs with hm
    · rw [abs_of_nonneg hm] at hgap
      push_cast
      omega
    · rw [abs_of_neg (lt_of_not_ge hm)] at hgap
      push_cast
      omega
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    obtain ⟨hyN, hsieve⟩ := mem_filter.mp hy
    have hylt := mem_range.mp hyN
    have hy0 : 0 < y := by
      by_contra hy
      have hz : y = 0 := by omega
      have htwo : 2 ∈ Nat.primesLE t := Nat.mem_primesLE.mpr ⟨ht, Nat.prime_two⟩
      exact hsieve 2 htwo (by simp [hz])
    have hyξ : y + h ≤ ξ := by dsimp [h]; omega
    have hx1 : 1 ≤ f y := by dsimp [f]; split_ifs <;> omega
    have hxξ : f y ≤ ξ := by dsimp [f]; split_ifs <;> omega
    have hbpos : 0 < (f y : ℤ) + 2 * m := by
      rw [hvalues]
      split_ifs <;> positivity
    have hrough (z : ℕ) (hz : z = y ∨ z = y + h) :
        ∀ p ∈ z.primeFactorsList, (t : ℝ) < p := by
      intro p hp
      have hz0 : z ≠ 0 := by rcases hz with rfl | rfl <;> omega
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hz0).mp hp
      by_contra htp
      have hpt : p ≤ t := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ t)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      apply hsieve p hpP
      rcases hz with rfl | rfl
      · exact dvd_mul_of_dvd_left hpdvd _
      · exact dvd_mul_of_dvd_right hpdvd _
    have hfy : f y = y ∨ f y = y + h := by dsimp [f]; split_ifs <;> simp
    have hbval : ((f y : ℤ) + 2 * m).toNat = if 0 ≤ m then y + h else y := by
      rw [hvalues]
      split_ifs <;> norm_cast
    have hb1 : 1 ≤ ((f y : ℤ) + 2 * m).toNat := by rw [hbval]; split_ifs <;> omega
    have hbξ : ((f y : ℤ) + 2 * m).toNat ≤ ξ := by rw [hbval]; split_ifs <;> omega
    have hbchoices : ((f y : ℤ) + 2 * m).toNat = y ∨
        ((f y : ℤ) + 2 * m).toNat = y + h := by rw [hbval]; split_ifs <;> simp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    have hA := almostGT_of_pow_bound hx1 ht1 (hrough (f y) hfy)
      ((by exact_mod_cast hxξ : (f y : ℝ) ≤ ξ).trans_lt hsizeA)
    have hB := almostGT_of_pow_bound hb1 ht1 (hrough _ hbchoices)
      ((by exact_mod_cast hbξ : (((f y : ℤ) + 2 * m).toNat : ℝ) ≤ ξ).trans_lt hsizeB)
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hx1, hxξ⟩, almostGT_mono hA le_rfl ?_, hbpos,
      almostGT_mono hB le_rfl ?_⟩
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthA
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthB
  · intro y _ z _ heq
    dsimp [f] at heq
    split_ifs at heq <;> omega


/-- Second memoir page 98 formula 16.2, before the next cardinality truncation.
Adjoining a disjoint block multiplies the retained signed main sum by its density product. -/
lemma decomp305_block_extension (x : ℕ → ℝ) (P B : Finset ℕ) (hPB : Disjoint P B)
    (A : Finset ℕ → Prop) [DecidablePred A] :
    (∑ S ∈ (P ∪ B).powerset.filter (fun S => A (S ∩ P)),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      (∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) *
        ∏ p ∈ B, (1 - x p) := by
  induction B using Finset.induction_on with
  | empty =>
    simp only [union_empty, prod_empty, mul_one, sum_filter]
    apply sum_congr rfl
    intro S hS
    rw [inter_eq_left.mpr (mem_powerset.mp hS)]
  | @insert p B hp ih =>
    have hpP : p ∉ P := fun h => (Finset.disjoint_left.mp hPB) h (mem_insert_self p B)
    have hPB' : Disjoint P B := hPB.mono_right (subset_insert p B)
    have hpU : p ∉ P ∪ B := by simp [hpP, hp]
    have hU : P ∪ insert p B = insert p (P ∪ B) := by ext q; simp [or_left_comm, or_assoc, or_comm]
    rw [hU, sum_filter, sum_powerset_insert hpU]
    have hterm (S : Finset ℕ) (hS : S ∈ (P ∪ B).powerset) :
        (if A (insert p S ∩ P) then
          (-1 : ℝ) ^ (insert p S).card * ∏ q ∈ insert p S, x q else 0) =
        -x p * (if A (S ∩ P) then (-1 : ℝ) ^ S.card * ∏ q ∈ S, x q else 0) := by
      have hpS : p ∉ S := fun h => hpU (mem_powerset.mp hS h)
      have hint : insert p S ∩ P = S ∩ P := by ext q; simp only [mem_inter, mem_insert]; aesop
      rw [hint, card_insert_of_notMem hpS, prod_insert hpS, pow_succ]
      split_ifs <;> ring
    rw [sum_congr rfl hterm, ← mul_sum, ← sum_filter, ih hPB', prod_insert hp]
    ring


/-- Second memoir page 98 formula 15.6, auxiliary disjoint block expansion.
Every subset has a unique old part and a unique new part. -/
lemma decomp305_disjoint_powerset_sum (P B : Finset ℕ) (hPB : Disjoint P B)
    (g : Finset ℕ → ℝ) :
    (∑ V ∈ (P ∪ B).powerset, g V) =
      ∑ S ∈ P.powerset, ∑ T ∈ B.powerset, g (S ∪ T) := by
  have hparts (S T : Finset ℕ) (hS : S ⊆ P) (hT : T ⊆ B) :
      (S ∪ T) ∩ P = S ∧ (S ∪ T) ∩ B = T := by
    have hd : ∀ q ∈ P, q ∉ B := fun q hq hb => Finset.disjoint_left.mp hPB hq hb
    constructor <;> ext q <;> simp only [mem_inter, mem_union]
    · constructor
      · rintro ⟨hq | hq, hqP⟩
        · exact hq
        · exact False.elim (hd q hqP (hT hq))
      · intro hq; exact ⟨Or.inl hq, hS hq⟩
    · constructor
      · rintro ⟨hq | hq, hqB⟩
        · exact False.elim (hd q (hS hq) hqB)
        · exact hq
      · intro hq; exact ⟨Or.inr hq, hT hq⟩
  rw [← sum_product P.powerset B.powerset (fun ST => g (ST.1 ∪ ST.2))]
  symm
  apply sum_bij (fun ST _ => ST.1 ∪ ST.2)
  · intro ST hST
    obtain ⟨hS, hT⟩ := mem_product.mp hST
    exact mem_powerset.mpr (union_subset_union (mem_powerset.mp hS) (mem_powerset.mp hT))
  · intro ST hST UV hUV heq
    obtain ⟨hS, hT⟩ := mem_product.mp hST
    obtain ⟨hU, hV⟩ := mem_product.mp hUV
    obtain ⟨hSP, hTB⟩ := hparts ST.1 ST.2 (mem_powerset.mp hS) (mem_powerset.mp hT)
    obtain ⟨hUP, hVB⟩ := hparts UV.1 UV.2 (mem_powerset.mp hU) (mem_powerset.mp hV)
    apply Prod.ext
    · rw [← hSP, ← hUP, heq]
    · rw [← hTB, ← hVB, heq]
  · intro V hV
    refine ⟨(V ∩ P, V ∩ B), mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,
      mem_powerset.mpr inter_subset_right⟩, ?_⟩
    have hv := mem_powerset.mp hV
    ext q
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hq
      rcases mem_union.mp (hv hq) with hP | hB
      · exact Or.inl ⟨hq, hP⟩
      · exact Or.inr ⟨hq, hB⟩
  · intro ST hST
    rfl



/-- Second memoir page 98 formula 15.6 with the lower cardinality cutoff.
This identifies the actual retained family with its block convolution. -/
lemma decomp305_retained_block_expansion (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (A : Finset ℕ → Prop) [DecidablePred A] (r : ℕ)
    (hcard : ∀ S ⊆ P, A S → S.card ≤ r) :
    (∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card ≤ r),
      (-1 : ℝ) ^ V.card * ∏ p ∈ V, x p) =
      ∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
  rw [sum_filter, decomp305_disjoint_powerset_sum P B hPB, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := mem_powerset.mp hS
  by_cases hAS : A S
  · rw [if_pos hAS, mul_sum]
    rw [sum_filter]
    apply sum_congr rfl
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have hTP : Disjoint T P := (hPB.mono_right hTB).symm
    have hint : (S ∪ T) ∩ P = S := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    rw [hint, card_union_of_disjoint hST, prod_union hST]
    have hc : S.card + T.card ≤ r ↔ T.card ≤ r - S.card := by
      have := hcard S hSP hAS
      omega
    simp only [hAS, true_and, hc, pow_add]
    split_ifs <;> ring
  · rw [if_neg hAS]
    apply sum_eq_zero
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hTP : Disjoint T P := (hPB.mono_right hTB).symm
    have hint : (S ∪ T) ∩ P = S := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    simp [hint, hAS]


/-- Second memoir page 99 formula 17.4, auxiliary lower recurrence.
The next truncation loses at most its first omitted unsigned coefficient. -/
lemma decomp305_truncated_block_lower (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p)
    (U : Finset (Finset ℕ)) (B : Finset ℕ) (hx1 : ∀ p ∈ B, x p ≤ 1) (r : ℕ)
    (hcard : ∀ S ∈ U, S.card ≤ r) :
    (∏ p ∈ B, (1 - x p)) *
        (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
      (∑ S ∈ U, (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1)) ≤
      ∑ S ∈ U, (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
  let y : ℕ → ℝ := fun p => if p ∈ B then x p else 0
  have hy0 : ∀ p, 0 ≤ y p := by
    intro p
    dsimp [y]
    split_ifs
    · exact hx0 p
    · norm_num
  have hy1 : ∀ p, y p ≤ 1 := by
    intro p
    dsimp [y]
    split_ifs with hp
    · exact hx1 p hp
    · norm_num
  have hprod (T : Finset ℕ) (hT : T ⊆ B) :
      (∏ p ∈ T, y p) = ∏ p ∈ T, x p :=
    prod_congr rfl (fun p hp => if_pos (hT hp))
  have hpi : (∏ p ∈ B, (1 - y p)) = ∏ p ∈ B, (1 - x p) :=
    prod_congr rfl (fun p hp => by simp only [y, if_pos hp])
  have hterm (S : Finset ℕ) (hS : S ∈ U) :
      |(∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) - ∏ p ∈ B, (1 - x p)| ≤
      LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) := by
    have hd := LeanLab.PNTSieve.Bonferroni.weighted_dev y hy0 hy1 B (r - S.card)
    change _ ≤ LeanLab.PNTSieve.Bonferroni.esymm y B (r - S.card + 1) at hd
    rw [hpi] at hd
    have hs : (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, y p) =
        ∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
      apply sum_congr rfl
      intro T hT
      rw [hprod T (mem_powerset.mp (mem_filter.mp hT).1)]
    have he : LeanLab.PNTSieve.Bonferroni.esymm y B (r - S.card + 1) =
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) := by
      unfold LeanLab.PNTSieve.Bonferroni.esymm
      exact sum_congr rfl (fun T hT => hprod T (mem_powersetCard.mp hT).1)
    rwa [hs, he] at hd
  have hbound (S : Finset ℕ) (hS : S ∈ U) :
      (∏ p ∈ B, (1 - x p)) * ((-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
        (∏ p ∈ S, x p) * LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) ≤
      (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
    have hdev := hterm S hS
    have hwt : 0 ≤ ∏ p ∈ S, x p := prod_nonneg (fun p _ => hx0 p)
    have habs := mul_le_mul_of_nonneg_left hdev hwt
    have hsgn : |(-1 : ℝ) ^ S.card| = 1 := by simp
    have hmin := neg_abs_le ((-1 : ℝ) ^ S.card *
      ((∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) - ∏ p ∈ B, (1 - x p)))
    rw [abs_mul, hsgn, one_mul] at hmin
    have hmul := mul_le_mul_of_nonneg_left hmin hwt
    change (∏ p ∈ S, x p) * |(_ : ℝ)| ≤
      (∏ p ∈ S, x p) * LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) at habs
    nlinarith
  have hh := sum_le_sum hbound
  simpa only [sum_sub_distrib, ← mul_sum] using hh


/-- Second memoir page 99 formula 17.4 for an actual retained subset family.
The boundary is the unsigned convolution coefficient at the first omitted degree. -/
lemma decomp305_retained_step_lower (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p)
    (P B : Finset ℕ) (hPB : Disjoint P B) (hx1 : ∀ p ∈ B, x p ≤ 1)
    (A : Finset ℕ → Prop) [DecidablePred A] (r : ℕ)
    (hcard : ∀ S ⊆ P, A S → S.card ≤ r) :
    (∏ p ∈ B, (1 - x p)) *
        (∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
      (∑ S ∈ P.powerset.filter A, (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1)) ≤
      ∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card ≤ r),
        (-1 : ℝ) ^ V.card * ∏ p ∈ V, x p := by
  rw [decomp305_retained_block_expansion x P B hPB A r hcard]
  exact decomp305_truncated_block_lower x hx0 (P.powerset.filter A) B hx1 r
    (fun S hS => hcard S (mem_powerset.mp (mem_filter.mp hS).1) (mem_filter.mp hS).2)


/-- Second memoir pages 92, 93 and 106.
The actual nested odd cap family on primes between the current cutoff and w. -/
def decomp305PrimeFamily (w : ℕ) (c : ℕ → ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  ((Ioc (c n) w).filter Nat.Prime).powerset.filter (fun S =>
    ∀ j ∈ range (n + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1)


/-- Second memoir page 97 formula 14.8, the last cap bounds the whole retained set. -/
lemma decomp305_prime_family_card (w : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (S : Finset ℕ) (hS : S ∈ decomp305PrimeFamily w c n) : S.card ≤ 2 * n + 1 := by
  simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hS
  obtain ⟨hSP, hcaps⟩ := hS
  have hfilter : S.filter (fun p => c n < p) = S := by
    apply filter_eq_self.mpr
    intro p hp
    exact (mem_Ioc.mp (mem_filter.mp (hSP hp)).1).1
  simpa only [hfilter] using hcaps n (mem_range.mpr (by omega))


/-- Second memoir pages 97 and 98 formulas 15.6 and 16.2.
The next actual prime family is obtained by adjoining the next block and imposing its odd cap. -/
lemma decomp305_prime_family_step (w : ℕ) (c : ℕ → ℕ) (hc : Antitone c)
    (n : ℕ) (hw : c n ≤ w) :
    decomp305PrimeFamily w c (n + 1) =
      (((Ioc (c n) w).filter Nat.Prime) ∪
        ((Ioc (c (n + 1)) (c n)).filter Nat.Prime)).powerset.filter
        (fun V => (V ∩ ((Ioc (c n) w).filter Nat.Prime)) ∈ decomp305PrimeFamily w c n ∧
          V.card ≤ 2 * (n + 1) + 1) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let Q := (Ioc (c (n + 1)) w).filter Nat.Prime
  have hPsub : P ⊆ Q := by
    intro p hp
    obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := mem_Ioc.mp hpI
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hc (by omega : n ≤ n + 1)).trans_lt hpl, hpu⟩, hpprime⟩
  have hPQ : P ∪ ((Ioc (c (n + 1)) (c n)).filter Nat.Prime) = Q := by
    ext p
    simp only [P, Q, mem_union, mem_filter, mem_Ioc]
    have hcn := hc (by omega : n ≤ n + 1)
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp [hp]
  rw [hPQ]
  ext V
  simp only [decomp305PrimeFamily, mem_filter, mem_powerset]
  have hfilters (hV : V ⊆ Q) (j : ℕ) (hj : j ≤ n) :
      (V ∩ P).filter (fun p => c j < p) = V.filter (fun p => c j < p) := by
    ext p
    simp only [mem_filter, mem_inter]
    constructor
    · tauto
    · rintro ⟨hpV, hpj⟩
      have hpQ := mem_filter.mp (hV hpV)
      have hcn : c n ≤ c j := hc hj
      refine ⟨⟨hpV, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hcn.trans_lt hpj,
        (mem_Ioc.mp hpQ.1).2⟩, hpQ.2⟩⟩, hpj⟩
  constructor
  · rintro ⟨hV, hcaps⟩
    refine ⟨hV, ⟨inter_subset_right, ?_⟩, ?_⟩
    · intro j hj
      rw [hfilters hV j (by have := mem_range.mp hj; omega)]
      exact hcaps j (mem_range.mpr (by have := mem_range.mp hj; omega))
    · have hlast : V.filter (fun p => c (n + 1) < p) = V := by
        apply filter_eq_self.mpr
        intro p hp
        exact (mem_Ioc.mp (mem_filter.mp (hV hp)).1).1
      simpa only [hlast] using hcaps (n + 1) (mem_range.mpr (by omega))
  · rintro ⟨hV, ⟨_, hcaps⟩, hcard⟩
    refine ⟨hV, ?_⟩
    intro j hj
    have hjn := mem_range.mp hj
    by_cases hje : j = n + 1
    · subst j
      exact (card_filter_le _ _).trans hcard
    · rw [← hfilters hV j (by omega)]
      exact hcaps j (mem_range.mpr (by omega))


/-- Second memoir page 99 formula 17.4 with the actual prime blocks and pair densities.
The boundary coefficient is explicit. No positive main estimate is assumed. -/
lemma decomp305_pair_prime_recurrence (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (n : ℕ) (hw : c n ≤ w) :
    let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
    (∏ p ∈ B, (1 - nuN h p)) *
        (∑ S ∈ decomp305PrimeFamily w c n,
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) -
      (∑ S ∈ decomp305PrimeFamily w c n, (∏ p ∈ S, nuN h p) *
        LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B
          (2 * (n + 1) + 1 - S.card + 1)) ≤
      ∑ S ∈ decomp305PrimeFamily w c (n + 1),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hpP hpB
    have hP := mem_Ioc.mp (mem_filter.mp hpP).1
    have hB := mem_Ioc.mp (mem_filter.mp hpB).1
    omega
  have hx1 : ∀ p ∈ B, nuN h p ≤ 1 := fun p hp =>
    (nuN_lt_one heven (mem_filter.mp hp).2).le
  have hUeq : P.powerset.filter (fun S => S ∈ decomp305PrimeFamily w c n) =
      decomp305PrimeFamily w c n := by
    ext S
    simp only [mem_filter, mem_powerset]
    constructor
    · exact And.right
    · intro hS
      refine ⟨?_, hS⟩
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hS
      exact hS.1
  have hcard : ∀ S ⊆ P, S ∈ decomp305PrimeFamily w c n →
      S.card ≤ 2 * (n + 1) + 1 := by
    intro S _ hS
    have := decomp305_prime_family_card w c n S hS
    omega
  have hraw := decomp305_retained_step_lower (nuN h) (nuN_nonneg h) P B hPB hx1
    (fun S => S ∈ decomp305PrimeFamily w c n) (2 * (n + 1) + 1) hcard
  rw [hUeq, ← decomp305_prime_family_step w c hc n hw] at hraw
  exact hraw


/-- Second memoir page 99 formula 18.3 with actual prime blocks and pair densities.
This instantiates the normalized iteration with the retained family and its boundary. -/
lemma decomp305_pair_prime_normalized (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (s n : ℕ) :
    let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
    let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
    let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
    let Φ := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i), (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
        (2 * (s + i + 1) + 1 - S.card + 1)
    E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
      E n / (∏ j ∈ range n, v j) := by
  dsimp only
  apply decompJ365_normalized_lower_iteration
    (fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p)
    (fun i => ∏ p ∈ (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime, (1 - nuN h p))
    (fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i), (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h)
        ((Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime)
        (2 * (s + i + 1) + 1 - S.card + 1)) ?_ ?_ n
  · intro i
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  · intro i
    exact decomp305_pair_prime_recurrence h w heven c hc (s + i) ((hc (Nat.zero_le (s + i))).trans hw)


/-- First memoir pages 88 and 89 and second memoir pages 106 and 107.
The finite decreasing pair sieve bounds the actual Z count for either shift sign. -/
lemma decomp305_zCount_finite_lower (a b ξ N t : ℕ) (m : ℤ)
    (ht : 2 ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (t : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (2 * m.natAbs) p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by
  apply (decomp305_pair_decreasing_lower (2 * m.natAbs) N (Nat.primesLE t) J
    (fun p hp => (Nat.mem_primesLE.mp hp).2) cutoff level L hL hlevel).trans
  exact_mod_cast decomp305_pair_survivors_le_zCount a b ξ N t m ht hN
    hsizeA hsizeB hthA hthB


/-- First memoir pages 88 and 89 and second memoir pages 106 and 107.
The finite decreasing sieve bounds the actual W count at a common prime cutoff. -/
lemma decomp305_wCount_finite_lower (a b N t : ℕ) (ht : 2 ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN N p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
      |(#{i ∈ range N | (∏ p ∈ S, p) ∣ i * (N - i)} : ℝ) -
        (N : ℝ) * ∏ p ∈ S, nuN N p| ≤ cnt N (∏ p ∈ S, p) := by
    have hc := LeanLab.SchnirelmannGoldbach.PureSieve.multiples_error N S
      (fun p hp => hP p (hS hp))
    have hν : (∏ p ∈ S, (LeanLab.SchnirelmannGoldbach.S1.wt N p / p)) =
        ∏ p ∈ S, nuN N p :=
      prod_congr rfl (fun p hp => (nuN_prime (hP p (hS hp))).symm)
    rw [hν] at hc
    rw [cnt_prod_primes N S (fun p hp => hP p (hS hp))]
    simpa only [LeanLab.SchnirelmannGoldbach.PureSieve.multiples] using hc
  have hraw := decompJ365_decreasing_lower_explicit (range N) (Nat.primesLE t) J
    (fun i => i * (N - i)) hP cutoff level N N (nuN N) herror L hL hlevel
  apply hraw.trans
  have hincl := decompJ365_mixed_survivors_le_wCount a b N t t ht le_rfl hthA hthB
  have hincl' : #{i ∈ range N | ∀ p ∈ Nat.primesLE t, ¬ p ∣ i * (N - i)} ≤
      wCount a b N := by simpa using hincl
  exact_mod_cast hincl' 

/-- Second memoir pages 98 and 106 formulas 16.2 and 24.6.
The primes below the final cutoff enter without a further cardinality cap. -/
lemma decomp305_prime_family_complete (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (n : ℕ) (hw : c n ≤ w) :
    (∑ S ∈ (Nat.primesLE w).powerset.filter (fun S => ∀ j ∈ range (n + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      (∑ S ∈ decomp305PrimeFamily w c n, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) *
        ∏ p ∈ Nat.primesLE (c n), (1 - x p) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := Nat.primesLE (c n)
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hpP hpB
    have hP := mem_Ioc.mp (mem_filter.mp hpP).1
    have hB := (Nat.mem_primesLE.mp hpB).1
    omega
  have hfullP : P ∪ B = Nat.primesLE w := by
    ext p
    simp only [P, B, mem_union, mem_filter, mem_Ioc, Nat.mem_primesLE]
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp [hp]
  have hmem (V : Finset ℕ) : V ∈ decomp305PrimeFamily w c n ↔ V ⊆ P ∧
      ∀ j ∈ range (n + 1), (V.filter (fun p => c j < p)).card ≤ 2 * j + 1 := by
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset, P]
  have hfilter (S : Finset ℕ) (hS : S ⊆ Nat.primesLE w) (j : ℕ) (hj : j ≤ n) :
      (S ∩ P).filter (fun p => c j < p) = S.filter (fun p => c j < p) := by
    ext p
    simp only [mem_filter, mem_inter]
    constructor
    · tauto
    · rintro ⟨hpS, hpj⟩
      have hpw := Nat.mem_primesLE.mp (hS hpS)
      exact ⟨⟨hpS, mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hc hj).trans_lt hpj, hpw.1⟩,
        hpw.2⟩⟩, hpj⟩
  have hUeq : P.powerset.filter (fun S => S ∈ decomp305PrimeFamily w c n) =
      decomp305PrimeFamily w c n := by
    ext S
    simp only [mem_filter, mem_powerset]
    exact ⟨And.right, fun hS => ⟨((hmem S).mp hS).1, hS⟩⟩
  have hcomplete : (P ∪ B).powerset.filter
      (fun S => S ∩ P ∈ decomp305PrimeFamily w c n) =
      (Nat.primesLE w).powerset.filter (fun S => ∀ j ∈ range (n + 1),
        (S.filter (fun p => c j < p)).card ≤ 2 * j + 1) := by
    rw [hfullP]
    ext S
    simp only [mem_filter, mem_powerset, hmem]
    constructor
    · rintro ⟨hS, _, hcaps⟩
      refine ⟨hS, ?_⟩
      intro j hj
      rw [← hfilter S hS j (by have := mem_range.mp hj; omega)]
      exact hcaps j hj
    · rintro ⟨hS, hcaps⟩
      refine ⟨hS, inter_subset_right, ?_⟩
      intro j hj
      rw [hfilter S hS j (by have := mem_range.mp hj; omega)]
      exact hcaps j hj
  have hh := decomp305_block_extension x P B hPB (fun S => S ∈ decomp305PrimeFamily w c n)
  rw [hcomplete, hUeq] at hh
  exact hh

/-- First memoir pages 75, 88 and 89 and second memoir page 99 formula 18.3.
The normalized actual prime family iteration feeds directly into the actual Z count.
The boundary remains explicit and is not assumed to have a positive balance. -/
lemma decomp305_zCount_normalized_lower (a b ξ N t : ℕ) (m : ℤ)
    (ht : 2 ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (t : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ t) (s n : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (s + n + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let h := 2 * m.natAbs
    let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
    let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
    let E := fun i => ∑ S ∈ decomp305PrimeFamily t c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
    let Φ := fun i => ∑ S ∈ decomp305PrimeFamily t c (s + i), (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
        (2 * (s + i + 1) + 1 - S.card + 1)
    let z := ∏ p ∈ Nat.primesLE (c (s + n)), (1 - nuN h p)
    (N : ℝ) * z * (∏ j ∈ range n, v j) *
        (E 0 - ∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by
  let h := 2 * m.natAbs
  let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
  let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
  let E := fun i => ∑ S ∈ decomp305PrimeFamily t c (s + i),
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
  let Φ := fun i => ∑ S ∈ decomp305PrimeFamily t c (s + i), (∏ p ∈ S, nuN h p) *
    LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
      (2 * (s + i + 1) + 1 - S.card + 1)
  let z := ∏ p ∈ Nat.primesLE (c (s + n)), (1 - nuN h p)
  have heven : Even h := ⟨m.natAbs, by dsimp [h]; omega⟩
  have hv : 0 < ∏ j ∈ range n, v j := by
    apply prod_pos
    intro j hj
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  have hnorm := decomp305_pair_prime_normalized h t heven c hc hw s n
  change E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
    E n / (∏ j ∈ range n, v j) at hnorm
  have hmain := (le_div_iff₀ hv).mp hnorm
  have hz0 : 0 ≤ z := prod_nonneg (fun p hp =>
    (sub_pos.mpr (nuN_lt_one heven (Nat.mem_primesLE.mp hp).2)).le)
  have hmul := mul_le_mul_of_nonneg_left hmain
    (mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hz0)
  have hraw := decomp305_zCount_finite_lower a b ξ N t m ht hN hsizeA hsizeB
    hthA hthB (range (s + n + 1)) c id L hL hlevel
  dsimp only [id] at hraw
  change (N : ℝ) * (∑ S ∈ (Nat.primesLE t).powerset.filter
    (fun S => ∀ j ∈ range (s + n + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) -
    L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ at hraw
  rw [decomp305_prime_family_complete (nuN h) t c hc (s + n)
    ((hc (Nat.zero_le (s + n))).trans hw)] at hraw
  change (N : ℝ) * (E n * z) - L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ at hraw
  change (N : ℝ) * z * (∏ j ∈ range n, v j) *
      (E 0 - ∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ
  nlinarith


/-- The printed lower masses scaled by one hundred, first memoir page 89. -/
def decomp305HeadMass : ℕ → ℕ
  | 0 => 90
  | 1 => 56
  | 2 => 52
  | _ => 50

/-- Auxiliary scaled factorial convolution for second memoir page 97 formula 15.7.
Only degrees below twice the new block count are retained. -/
def decomp305HeadStep (t : ℕ) (a : List ℕ) (n : ℕ) : List ℕ :=
  (List.range (2*n)).map fun k => ∑ j ∈ range (k+1), (k.factorial / (j.factorial * (k-j).factorial)) * a[j]?.getD 0 * t^(k-j)

/-- The scaled integer coefficients of the finite factorial lower head.
This is the repeated convolution model for second memoir page 97 formula 15.7. -/
def decomp305HeadCoeff : ℕ → List ℕ
  | 0 => [1]
  | n+1 => decomp305HeadStep (decomp305HeadMass n) (decomp305HeadCoeff n) (n+1)

/-- The finite signed factorial head, with the integer scaling removed. -/
def decomp305HeadValue : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ k ∈ range (2 * (n + 1)),
      (-1 : ℚ)^k * ((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℚ) /
        ((100 : ℚ)^k * (k.factorial : ℚ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The coefficient model reproduces the printed three block lower head.
First memoir page 81 formula 2.6 and second memoir page 97 formula 15.7. -/
lemma decomp305_head_three_eq :
    decomp305HeadValue 3 = Ebar3 (90 / 100) (56 / 100) (52 / 100) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Auxiliary twenty block certificate at the printed lower masses.
This certifies the factorial coefficient model and does not assert a sieve count. -/
theorem decomp305_head20_positive : (13 / 10000000 : ℚ) < decomp305HeadValue 20 := by
  change (∑ k ∈ range 40, (-1 : ℚ)^k * ((decomp305HeadCoeff 20)[k]?.getD 0 : ℚ) /
    ((100 : ℚ)^k * (k.factorial : ℚ))) > 13/10000000
  have h1 : decomp305HeadCoeff 1 = [1, 90] := by
    decide +kernel
  have h2 : decomp305HeadCoeff 2 = [1, 146, 13216, 1022336] := by
    rw [decomp305HeadCoeff, h1]
    decide +kernel
  have h3 : decomp305HeadCoeff 3 = [1, 198, 31104, 4408992, 516488960, 51944402432] := by
    rw [decomp305HeadCoeff, h2]
    decide +kernel
  have h4 : decomp305HeadCoeff 4 = [1, 248, 53404, 10684592, 1970097360, 336671442432, 49277011729600, 6177744827680000] := by
    rw [decomp305HeadCoeff, h3]
    decide +kernel
  have h5 : decomp305HeadCoeff 5 = [1, 298, 80704, 20680192, 5038325760, 1171128082432, 256355825459200, 52434750110720000, 9351040116668000000, 1431721657242200000000] := by
    rw [decomp305HeadCoeff, h4]
    decide +kernel
  have h6 : decomp305HeadCoeff 6 = [1, 348, 113004, 35145792, 10540174160, 3058219322432, 856472321188800, 230772975549120000, 59071124962624000000, 14200720099494400000000, 3001686005682520000000000, 544780283561168000000000000] := by
    rw [decomp305HeadCoeff, h5]
    decide +kernel
  have h7 : decomp305HeadCoeff 7 = [1, 398, 150304, 54831392, 19444642560, 6724350162432, 2268321378918400, 745676638842880000, 238018943790012000000, 73418051964918600000000, 21612182339001040000000000, 5991303958972278000000000000, 1467011015292012150000000000000, 308264866778414632500000000000000] := by
    rw [decomp305HeadCoeff, h6]
    decide +kernel
  have h8 : decomp305HeadCoeff 8 = [1, 448, 192604, 80486992, 32870730960, 13156925602432, 5166731878648000, 1990712865692000000, 751677412030976000000, 277592242575641600000000, 99859418719345560000000000, 34801498531423620000000000000, 11605036095758616800000000000000, 3649978204519320080000000000000000, 1016740147634251084000000000000000000, 242900617680353793875000000000000000000] := by
    rw [decomp305HeadCoeff, h7]
    decide +kernel
  have h9 : decomp305HeadCoeff 9 = [1, 498, 239904, 112862592, 52087439360, 23641850642432, 10566591700377600, 4652537339796480000, 2017608839497660000000, 861028500188755000000000, 361013135478785680000000000, 148352241986672264000000000000, 59498136379619943750000000000000, 23153336001508718407500000000000000, 8635021521480622078000000000000000000, 3040266057639516635175000000000000000000, 949754944663889455890781250000000000000000, 254294173805276680721539062500000000000000000] := by
    rw [decomp305HeadCoeff, h8]
    decide +kernel
  have h10 : decomp305HeadCoeff 10 = [1, 548, 292204, 152708192, 78513767760, 39801030282432, 19918022724107200, 9846242452856320000, 4808649608582208000000, 2319454008187315200000000, 1104208811767303000000000000, 518220324678411000000000000000, 239316653813165500800000000000000, 108461386130380179840000000000000000, 48033961000901033184000000000000000000, 20661416148180765478275000000000000000000, 8526494157777529669240000000000000000000000, 3323809267809991956438000000000000000000000000, 1151045828033111662247421875000000000000000000000, 341447237960909427682010468750000000000000000000000] := by
    rw [decomp305HeadCoeff, h9]
    decide +kernel
  have h11 : decomp305HeadCoeff 11 = [1, 598, 349504, 200773792, 113718716160, 63629869522432, 35212805829836800, 19285985454571520000, 10457168862456764000000, 5613291024711343400000000, 2982151733713523520000000000, 1567130606795777598000000000000, 813855771530975117750000000000000, 417137498236419838062500000000000000, 210594340752157931533000000000000000000, 104434678773184679183300000000000000000000, 50649258270585402158470781250000000000000000, 23874677961789471852972867187500000000000000000, 10804808388074604196747265625000000000000000000000, 4620860811837047402350698828125000000000000000000000, 1757163139178724887501957730468750000000000000000000000, 572074261088096952902087421289062500000000000000000000000] := by
    rw [decomp305HeadCoeff, h10]
    decide +kernel
  have h12 : decomp305HeadCoeff 12 = [1, 648, 411804, 257809392, 159421284560, 97534773362432, 59102055897566400, 35494834102642080000, 21135290703273472000000, 12479349919228825600000000, 7306138773010950040000000000, 4240171856334529388000000000000, 2438229865700825042400000000000000, 1388203955499603363120000000000000000, 781762893561331259020000000000000000000, 434831980842965740021875000000000000000000, 238400698641023142950000000000000000000000000, 128467790872843349860568000000000000000000000000, 67742909595261862068897421875000000000000000000000, 34736020100938831482838762031250000000000000000000000, 17109540087840069573868826500000000000000000000000000000, 7966012102453531445209591878125000000000000000000000000000, 3300071158363421619966347011464843750000000000000000000000000, 1169927804204789298848272271735351562500000000000000000000000000] := by
    rw [decomp305HeadCoeff, h11]
    decide +kernel
  have h13 : decomp305HeadCoeff 13 = [1, 698, 479104, 324564992, 217490472960, 144370646802432, 95025146807296000, 62057767312768000000, 40227554400364476000000, 25888773425546712600000000, 16541756767399694560000000000, 10492862007341408160000000000000, 6606117108483723380550000000000000, 4126384858336965373117500000000000000, 2555741408681415918789000000000000000000, 1568354041909008580633875000000000000000000, 952529309276266546170050781250000000000000000, 571709441033841661790950195312500000000000000000, 338399611931493742700729121875000000000000000000000, 196961037073546175007633463437500000000000000000000000, 112226994324876639710193769183593750000000000000000000000, 62203497076146823401761029713867187500000000000000000000000, 33131612177137646644996870430781250000000000000000000000000000, 16683937418367294084358552544349609375000000000000000000000000000, 7479364435270197658723881714083172607421875000000000000000000000000, 2868199345330820914624465262861198425292968750000000000000000000000000] := by
    rw [decomp305HeadCoeff, h12]
    decide +kernel
  have h14 : decomp305HeadCoeff 14 = [1, 748, 551404, 401790592, 289945281360, 207478394842432, 147349886439025600, 103921768308649280000, 72814062108441920000000, 50696831290761920000000000, 35079444478013710680000000000, 24123041677097220384000000000000, 16484444345415659072000000000000000, 11191505238452253470720000000000000000, 7546279380604620482848000000000000000000, 5051343060892563076652675000000000000000000, 3354572100336861001592040000000000000000000000, 2208299308212767749180614000000000000000000000000, 1439387612646320606068875421875000000000000000000000, 927545465362092265911810933593750000000000000000000000, 589672890844066225326917824125000000000000000000000000000, 368746946325019867210269485487500000000000000000000000000000, 225813404264542539205668817868027343750000000000000000000000000, 134551012676795191067318489602151367187500000000000000000000000000, 77065974092009181965958161722482812500000000000000000000000000000000, 41737609182868933468892693892618945312500000000000000000000000000000000, 20131966739866575936198926741282628784179687500000000000000000000000000000, 8303633855976014688977448324739619232177734375000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h13]
    decide +kernel
  have h15 : decomp305HeadCoeff 15 = [1, 798, 628704, 490236192, 378954709760, 290722422482432, 221523941672755200, 167746947771985920000, 126283738595797948000000, 94538641149652328200000000, 70388994319563526000000000000, 52126527896350157750000000000000, 38393791217195138594550000000000000, 28123308490874944315252500000000000000, 20483038849739919142174000000000000000000, 14829453396773552288696400000000000000000000, 10668255702585246269664390781250000000000000000, 7622176003751329715610669523437500000000000000000, 5404952040713476671734173968750000000000000000000000, 3800595731030056475057642696015625000000000000000000000, 2647002223550193634997724512792968750000000000000000000000, 1823166929021837804244094791333007812500000000000000000000000, 1239193713557069497469065446855703125000000000000000000000000000, 828712963294529323449044771583101562500000000000000000000000000000, 542848289351309557829814840201205828857421875000000000000000000000000, 346064883813082631552944773785238075256347656250000000000000000000000000, 212116730647606742377637690605686380004882812500000000000000000000000000000, 122949483115215012851739350502975976974487304687500000000000000000000000000000, 63492357085202893901376027551626458284378051757812500000000000000000000000000000, 28028600133436915191533703194832764982051849365234375000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h14]
    decide +kernel
  have h16 : decomp305HeadCoeff 16 = [1, 848, 711004, 590651792, 486837758160, 398528134722432, 324237513388484800, 262312634492477920000, 211098902482504704000000, 169034076854007782400000000, 134696374792824474520000000000, 106824300217456883028000000000000, 84319298013801924588000000000000000, 66238421416843912866000000000000000000, 51781618599426440416908000000000000000000, 40276580509719064932822675000000000000000000, 31162963531864182955537120000000000000000000000, 23977089558978338356885344000000000000000000000000, 18337723228058230949588945421875000000000000000000000, 13933248056020356242770635685156250000000000000000000000, 10510322708401441465754642680875000000000000000000000000000, 7864044216449865201330727136990625000000000000000000000000000, 5829468177610147535160478886145214843750000000000000000000000000, 4274478760356324131407938241144848632812500000000000000000000000000, 3093660784420144609976523513031501562500000000000000000000000000000000, 2203437394279316775507214219387227343750000000000000000000000000000000000, 1537519497766415992428942659524206242065429687500000000000000000000000000000, 1044274847429937883482373262862414057769775390625000000000000000000000000000000, 682066511529821320608092079359424235498046875000000000000000000000000000000000000, 421315129400227485407980883728550399386596679687500000000000000000000000000000000000, 231928284248700752056102027699594113241445159912109375000000000000000000000000000000000, 109109371827557864535493865606053702928344001770019531250000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h15]
    decide +kernel
  have h17 : decomp305HeadCoeff 17 = [1, 898, 798304, 703787392, 616063426560, 535919436562432, 463597261466214400, 398982371017825280000, 341733923488614332000000, 291375019636401092600000000, 247355329169900429040000000000, 209094244656334906248000000000000, 176010164145445080590150000000000000, 147539860108285788157107500000000000000, 123150753811990442617840000000000000000000, 102348138582506624186384375000000000000000000, 84678827079314966418152050781250000000000000000, 69732307226345453525556490851562500000000000000000, 57140186440746744013192537406250000000000000000000000, 46574508018263326724209614398750000000000000000000000000, 37745342418341074089350570114683593750000000000000000000000, 30397977405790382841122379577072460937500000000000000000000000, 24309886558208935361706827821568203125000000000000000000000000000, 19287692559871151843122824859684435546875000000000000000000000000000, 15164114263953997705598355840789111297607421875000000000000000000000000, 11795193756493896664282149392258206748962402343750000000000000000000000000, 9057392137075357832222077671401900100708007812500000000000000000000000000000, 6845547963462290675748852840876848371154785156250000000000000000000000000000000, 5069566972258535669940376682129283832286453247070312500000000000000000000000000000, 3654796705222841719950081622569750931245975494384765625000000000000000000000000000000, 2534180117630638935861607012102363015934970092773437500000000000000000000000000000000000, 1661904659515242804176863091855288665729247322082519531250000000000000000000000000000000000, 971503927168750457146082898295828670570581730127334594726562500000000000000000000000000000000, 485214438518968135820439635287084344026221919929981231689453125000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h16]
    decide +kernel
  have h18 : decomp305HeadCoeff 18 = [1, 948, 890604, 830392992, 769250714960, 708556233002432, 649311479785944000, 592231751803728000000, 537812315192358976000000, 486378710387899033600000000, 438125404866233033560000000000, 393145868186725776200000000000000, 351456177760284966076800000000000000, 313013667807687864689280000000000000000, 277731725744597170181344000000000000000000, 245491567532396557697023875000000000000000000, 216151619147817228254471000000000000000000000000, 189554992069189444296731750000000000000000000000000, 165535425131105241293047666621875000000000000000000000, 143921993268067672219000305776718750000000000000000000000, 124542808196962670254350010924750000000000000000000000000000, 107227909089003623373623544485750000000000000000000000000000000, 91811472010024488933673316312108027343750000000000000000000000000, 78133494366112699904246353927318827148437500000000000000000000000000, 66040988007018484394376969578219831250000000000000000000000000000000000, 55388887890248301890203112814185352539062500000000000000000000000000000000, 46040488997871210122835752089048540206909179687500000000000000000000000000000, 37868008278093670334463664751819953197479248046875000000000000000000000000000000, 30752120470595644987408647760231893683666992187500000000000000000000000000000000000, 24583277122033914679124006261318097361887207031250000000000000000000000000000000000000, 19258180115269878755676645318618631242997048187255859375000000000000000000000000000000000, 14688088591589433893257390546302950951743904685974121093750000000000000000000000000000000000, 10775808151940845005454163049992569454619108642578125000000000000000000000000000000000000000000, 7477368621704160172569189445787764721100314520263671875000000000000000000000000000000000000000000, 4625998448821021285071726996654853793538014264864921569824218750000000000000000000000000000000000000, 2444627697519840756397320185375430632104427761038541793823242187500000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h17]
    decide +kernel
  have h19 : decomp305HeadCoeff 19 = [1, 998, 987904, 971218592, 949168623360, 922771929042432, 892886521227673600, 860243041363886080000, 825468187798350780000000, 789102272979213345000000000, 751612745454326435680000000000, 713404833536914612254000000000000, 674830067310061715997750000000000000, 636193203541201557748282500000000000000, 597757925495970682488243000000000000000000, 559751594278459175786823300000000000000000000, 522369257359415819352214790781250000000000000000, 485777074607126269656991118179687500000000000000000, 450115281869461812970612166234375000000000000000000000, 415500789902595573478203604173828125000000000000000000000, 382029487503541090171492565585355468750000000000000000000000, 349778312210846432033017590611582226562500000000000000000000000, 318807120467917508229595414522645468750000000000000000000000000000, 289160409742415098732101300935734031250000000000000000000000000000000, 260868880950083977039426371186683855828857421875000000000000000000000000, 233950929532022735669740903532949639094543457031250000000000000000000000000, 208413936398528241722120949605244585146484375000000000000000000000000000000000, 184255670571955389043984986504173314150863647460937500000000000000000000000000000, 161465140561125942684379770598856075474702835083007812500000000000000000000000000000, 140024449625734998934576686634024114908469676971435546875000000000000000000000000000000, 119907928197695620977798653746291924329728086853027343750000000000000000000000000000000000, 101087876678816909919888615799596160775226749725341796875000000000000000000000000000000000000, 83522714123157727320084356475382162479349313846826553344726562500000000000000000000000000000000, 67192603057291882470340382169268990800615828662431240081787109375000000000000000000000000000000000, 52001586042483559512744554077103418624141801506676673889160156250000000000000000000000000000000000000, 38066384427159014292583838778558097219997963086097359657287597656250000000000000000000000000000000000000, 24848486197228392846321147241042897551814070228014981746673583984375000000000000000000000000000000000000000, 13852177166574025163211608950655332530106044393691212534904479980468750000000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h18]
    decide +kernel
  have h20 : decomp305HeadCoeff 20 = [1, 1048, 1090204, 1127014192, 1158736151760, 1185610929682432, 1207834472671403200, 1225570509919999520000, 1238959560415781888000000, 1248125498954791731200000000, 1253180487807657519000000000000, 1254228761543497501500000000000000, 1251369566088934479000800000000000000, 1244699449288048608685040000000000000000, 1234314035046330706322764000000000000000000, 1220309376398450276311908275000000000000000000, 1202782957369291588328815440000000000000000000000, 1181834400327337366996946328000000000000000000000000, 1157565923452372688147615169421875000000000000000000000, 1130082589184150321831392820768281250000000000000000000000, 1099492375471916128946470712643750000000000000000000000000000, 1065906104131038443233803968186328125000000000000000000000000000, 1029437247296603965393595243748698964843750000000000000000000000000, 990201647422748959806058473230703711914062500000000000000000000000000, 948317152468925488106947823324607746875000000000000000000000000000000000, 903903224785247625663950966870814921875000000000000000000000000000000000000, 857080461317690210254904439711579279367065429687500000000000000000000000000000, 807970208815825745599392810823684300030548095703125000000000000000000000000000000, 756693911894588107002361505523355772889038085937500000000000000000000000000000000000, 703373072389933513694169129443079818324013061523437500000000000000000000000000000000000, 648127739041144563270369280431798588715324306488037109375000000000000000000000000000000000, 591078764573651401265793699663844678845875191688537597656250000000000000000000000000000000000, 532340259093233864771352590719584893185318642333984375000000000000000000000000000000000000000000, 472038758103797535244940901642796368684307925219726562500000000000000000000000000000000000000000000, 410257502602942685925477129730485743397732568851656913757324218750000000000000000000000000000000000000, 347198020444364054168557098241786205201132634933030366897583007812500000000000000000000000000000000000000, 282691628384004294806178633568078040475546967013246154785156250000000000000000000000000000000000000000000000, 217716189792922609935666503918285744049821222202065224647521972656250000000000000000000000000000000000000000000, 149543403362924358124434504780357400926553298842425744384527206420898437500000000000000000000000000000000000000000, 87704323539661630437993157750912985212893339560154279817640781402587890625000000000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h19]
    decide +kernel
  rw [h20]
  norm_num [sum_range_succ, Nat.factorial]

/-- First memoir page 89, the cumulative printed lower mass from the third block onward. -/
lemma decomp305_head_mass_sum {b : ℕ} (hb : 3 ≤ b) :
    (∑ i ∈ range b, (decomp305HeadMass i : ℝ) / 100) = (b : ℝ) / 2 + 0.48 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [sum_range_add]
  have htail (i : ℕ) : decomp305HeadMass (3 + i) = 50 := by
    rw [show 3 + i = i + 3 by omega]
    rfl
  simp_rw [htail]
  norm_num [sum_range_succ, decomp305HeadMass]
  <;> ring

/-- Auxiliary larger factorial tail for second memoir page 99 formula 18.3.
The shifted mass bounds the printed cumulative masses from the third block onward. -/
def decomp305CrudeTerm (b : ℕ) : ℝ :=
  exp (((b : ℝ) + 1) / 2) * (((b : ℝ) + 1) / 2) ^ (2 * b) /
    ((2 * b).factorial : ℝ)

/-- Exact consecutive ratio for the auxiliary later tail. -/
lemma decomp305_crude_succ (b : ℕ) :
    decomp305CrudeTerm (b + 1) = decomp305CrudeTerm b * exp (1 / 2 : ℝ) *
      (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) *
      (((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1))) := by
  have hb : (b : ℝ) + 1 ≠ 0 := by positivity
  have hf : ((2 * b).factorial : ℝ) ≠ 0 := by positivity
  have hfac : (2 * (b + 1)).factorial = (2 * b + 2) * (2 * b + 1) * (2 * b).factorial := by
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    ring
  have he : (((b + 1 : ℕ) : ℝ) + 1) / 2 = ((b : ℝ) + 1) / 2 + 1 / 2 := by
    push_cast
    ring
  have hp : (((b : ℝ) + 1) / 2) ^ (2 * b) *
      (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) =
      (((b : ℝ) + 2) / 2) ^ (2 * b) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp : exp ((((b + 1 : ℕ) : ℝ) + 1) / 2) =
      exp (((b : ℝ) + 1) / 2) * exp (1 / 2 : ℝ) := by rw [he, exp_add]
  unfold decomp305CrudeTerm
  rw [hexp, hfac, show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
  push_cast
  rw [show (((b : ℝ) + 1 + 1) / 2) = ((b : ℝ) + 2) / 2 by ring]
  rw [← hp]
  field_simp
  <;> ring


/-- A geometric ratio valid after the twentieth block.
This is an auxiliary replacement for the late part of the corrected cyclic estimate. -/
lemma decomp305_crude_ratio {b : ℕ} (hb : 20 ≤ b) :
    decomp305CrudeTerm (b + 1) ≤ (0.86 : ℝ) * decomp305CrudeTerm b := by
  have hbR : (20 : ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
  have hbase : ((b : ℝ) + 2) / ((b : ℝ) + 1) ≤ exp (1 / ((b : ℝ) + 1)) := by
    have hh := add_one_le_exp (1 / ((b : ℝ) + 1))
    convert hh using 1 <;> field_simp <;> ring
  have hpower : (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) ≤ exp 2 := by
    calc
      _ ≤ exp (1 / ((b : ℝ) + 1)) ^ (2 * b) := pow_le_pow_left₀ (by positivity) hbase _
      _ = exp ((2 * (b : ℝ)) / ((b : ℝ) + 1)) := by
        rw [← exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ exp 2 := exp_le_exp.mpr ((div_le_iff₀ (by positivity)).mpr (by linarith))
  have hfactor : ((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1)) ≤ 0.0705 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) - 20 by linarith) (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have he05 : exp (1 / 2 : ℝ) ≤ 1.649 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have he2 : exp (2 : ℝ) ≤ 7.39 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos (1 : ℝ)]
  have hD : 0 ≤ decomp305CrudeTerm b := by unfold decomp305CrudeTerm; positivity
  rw [decomp305_crude_succ]
  have h1 := mul_le_mul he05 (hpower.trans he2) (by positivity : (0 : ℝ) ≤
    (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b)) (by norm_num : (0 : ℝ) ≤ 1.649)
  have h2 := mul_le_mul h1 hfactor (by positivity : (0 : ℝ) ≤
    ((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1)))
    (by norm_num : (0 : ℝ) ≤ 1.649 * 7.39)
  have h3 := mul_le_mul_of_nonneg_left h2 hD
  nlinarith


/-- The auxiliary crude tail from block twenty one onward is below 0.018.
This bounds only the scalar majorant, not the retained sieve main sum. -/
lemma decomp305_crude_tail_lt :
    (∑' k : ℕ, decomp305CrudeTerm (21 + k)) < 0.018 := by
  have he11 : exp (11 : ℝ) ≤ 61000 := by
    calc
      exp (11 : ℝ) = exp (1 : ℝ) ^ (11 : ℕ) := by
        rw [← exp_nat_mul]
        norm_num
      _ ≤ (2.719 : ℝ) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) _
      _ ≤ 61000 := by norm_num
  have h21 : decomp305CrudeTerm 21 < 0.0024 := by
    unfold decomp305CrudeTerm
    norm_num only [Nat.cast_ofNat, show ((21 : ℝ) + 1) / 2 = 11 by norm_num]
    have hmul := mul_le_mul_of_nonneg_right he11 (show 0 ≤ (11 : ℝ) ^ (42 : ℕ) by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul
      (show 0 ≤ ((42 : ℕ).factorial : ℝ) by positivity)
    have hnum : (61000 : ℝ) * 11 ^ (42 : ℕ) / ((42 : ℕ).factorial : ℝ) < 0.0024 := by
      norm_num [Nat.factorial]
    convert hdiv.trans_lt hnum using 1 <;> norm_num [Nat.factorial]
  have hshift (k : ℕ) : decomp305CrudeTerm (21 + k) ≤ decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        decomp305CrudeTerm (21 + (k + 1)) ≤ 0.86 * decomp305CrudeTerm (21 + k) := by
          simpa only [Nat.add_assoc] using decomp305_crude_ratio (b := 21 + k) (by omega)
        _ ≤ 0.86 * (decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k) := by gcongr
        _ = decomp305CrudeTerm 21 * (0.86 : ℝ) ^ (k + 1) := by ring
  have hdom : Summable (fun k : ℕ => decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hsum : Summable (fun k : ℕ => decomp305CrudeTerm (21 + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold decomp305CrudeTerm; positivity) hshift
  have hle := hsum.tsum_le_tsum hshift hdom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(0.86 : ℝ)| < 1)] at hle
  have hupper : decomp305CrudeTerm 21 * (1 - (0.86 : ℝ))⁻¹ < 0.018 := by
    norm_num
    linarith
  exact hle.trans_lt hupper

/-- Auxiliary longer head certificate for second memoir page 99 formula 18.3.
The exact factorial head minus the full later scalar majorant is positive.
No comparison with the actual sieve boundary is assumed or asserted here. -/
lemma decomp305_long_head_certificate :
    (0.02 : ℝ) < exp (10.48 : ℝ) * (decomp305HeadValue 20 : ℝ) -
      ∑' k : ℕ, decomp305CrudeTerm (21 + k) := by
  have hE : (13 / 10000000 : ℝ) < (decomp305HeadValue 20 : ℝ) := by
    have hh : ((13 / 10000000 : ℚ) : ℝ) < (decomp305HeadValue 20 : ℝ) :=
      Rat.cast_lt.mpr decomp305_head20_positive
    norm_num at hh
    exact hh
  have he10 : (2.718 : ℝ) ^ (10 : ℕ) ≤ exp (10 : ℝ) := by
    calc
      (2.718 : ℝ) ^ (10 : ℕ) ≤ exp (1 : ℝ) ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
      _ = exp (10 : ℝ) := by rw [← exp_nat_mul]; norm_num
  have he048 : (1.48 : ℝ) ≤ exp (0.48 : ℝ) := by linarith [add_one_le_exp (0.48 : ℝ)]
  have he : (30000 : ℝ) ≤ exp (10.48 : ℝ) := by
    calc
      (30000 : ℝ) ≤ 2.718 ^ (10 : ℕ) * 1.48 := by norm_num
      _ ≤ exp (10 : ℝ) * exp (0.48 : ℝ) :=
        mul_le_mul he10 he048 (by norm_num) (exp_pos _).le
      _ = exp (10.48 : ℝ) := by rw [← exp_add]; norm_num
  have hprod := mul_le_mul he hE.le (by norm_num : (0 : ℝ) ≤ 13 / 10000000)
    (exp_pos (10.48 : ℝ)).le
  norm_num at hprod
  linarith [decomp305_crude_tail_lt]

/-- Second memoir page 99 formula 18.3 and page 109, actual density normalization.
The square mass loss above a fixed lower prime cutoff is uniform in the upper cutoff and gap. -/
lemma decomp305_pair_product_lower (h y w : ℕ) (hy : 4 ≤ y) :
    exp (-(∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) - 8 / (y : ℝ)) ≤
      ∏ p ∈ (Ioc y w).filter Nat.Prime, (1 - nuN h p) := by
  let P := (Ioc y w).filter Nat.Prime
  have hy0 : y ≠ 0 := by omega
  have hlocal (p : ℕ) (hp : p ∈ P) :
      0 ≤ nuN h p ∧ nuN h p ≤ 2 / (p : ℝ) ∧ nuN h p ≤ 1 / 2 := by
    have hprime := (mem_filter.mp hp).2
    have hpy := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have hp0 : (0 : ℝ) < p := by positivity
    have hu : nuN h p ≤ 2 / (p : ℝ) := by
      rw [nuN_prime hprime]
      exact div_le_div_of_nonneg_right (wt_le_two h p) (Nat.cast_nonneg p)
    refine ⟨nuN_nonneg h p, hu, hu.trans ?_⟩
    rw [div_le_iff₀ hp0]
    linarith
  have hsq : (∑ p ∈ P, (nuN h p) ^ 2) ≤ 4 / (y : ℝ) := by
    by_cases hyw : y ≤ w
    · have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) hy0 hyw
      have htail' : (∑ p ∈ Ioc y w, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (y : ℝ) := by
        simp only [one_div] at htail ⊢
        have hw0 : (0 : ℝ) ≤ (w : ℝ)⁻¹ := by positivity
        linarith
      have hterm : ∀ p ∈ P, (nuN h p) ^ 2 ≤ 4 * (1 / (p : ℝ) ^ 2) := by
        intro p hp
        have hh := pow_le_pow_left₀ (hlocal p hp).1 (hlocal p hp).2.1 2
        simpa only [div_pow, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, mul_one_div] using hh
      have hsub : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Ioc y w, (1 : ℝ) / (p : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)
      calc
        _ ≤ ∑ p ∈ P, 4 * (1 / (p : ℝ) ^ 2) := sum_le_sum hterm
        _ = 4 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ 4 * (1 / (y : ℝ)) := mul_le_mul_of_nonneg_left (hsub.trans htail') (by norm_num)
        _ = 4 / (y : ℝ) := by ring
    · have hP : P = ∅ := by simp [P, Ioc_eq_empty (by omega : ¬ y < w)]
      simp only [hP, sum_empty]
      positivity
  have hp := LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp P (nuN h)
    (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2.2)
  apply le_trans (exp_le_exp.mpr ?_) hp
  change -(∑ p ∈ P, nuN h p) - 8 / (y : ℝ) ≤
    -(∑ p ∈ P, nuN h p + 2 * ∑ p ∈ P, (nuN h p) ^ 2)
  have hh : 2 * (∑ p ∈ P, (nuN h p) ^ 2) ≤ 8 / (y : ℝ) := by
    calc
      _ ≤ 2 * (4 / (y : ℝ)) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 8 / (y : ℝ) := by ring
  linarith only [hh]

/-- Second memoir pages 95 and 97 formula 15.6, unsigned block coefficient expansion. -/
lemma decomp305_esymm_block_convolution (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (r : ℕ) :
    LeanLab.PNTSieve.Bonferroni.esymm x (P ∪ B) r =
      ∑ S ∈ P.powerset.filter (fun S => S.card ≤ r), (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card) := by
  change (∑ V ∈ (P ∪ B).powersetCard r, ∏ p ∈ V, x p) = _
  rw [powersetCard_eq_filter, sum_filter, decomp305_disjoint_powerset_sum P B hPB, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := mem_powerset.mp hS
  by_cases hSr : S.card ≤ r
  · rw [if_pos hSr]
    unfold LeanLab.PNTSieve.Bonferroni.esymm
    rw [powersetCard_eq_filter, sum_filter, mul_sum]
    apply sum_congr rfl
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have heq : S.card + T.card = r ↔ T.card = r - S.card := by omega
    simp only [card_union_of_disjoint hST, prod_union hST, heq, mul_ite, mul_zero]
  · rw [if_neg hSr]
    apply sum_eq_zero
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have hne : S.card + T.card ≠ r := by omega
    simp only [card_union_of_disjoint hST, hne, ite_false]


/-- Second memoir pages 95 and 99, a crude unsigned boundary bound.
Discarding the old prefix restrictions bounds the coefficient by the full factorial monomial. -/
lemma decomp305_boundary_factorial_upper (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p)
    (P B : Finset ℕ) (hPB : Disjoint P B) (U : Finset (Finset ℕ)) (r : ℕ)
    (hU : ∀ S ∈ U, S ⊆ P) (hcard : ∀ S ∈ U, S.card ≤ r) :
    (∑ S ∈ U, (∏ p ∈ S, x p) * LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card)) ≤
      (∑ p ∈ P ∪ B, x p) ^ r / (r.factorial : ℝ) := by
  have hsub : U ⊆ P.powerset.filter (fun S => S.card ≤ r) := by
    intro S hS
    exact mem_filter.mpr ⟨mem_powerset.mpr (hU S hS), hcard S hS⟩
  calc
    _ ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ r), (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro S _ _
      exact mul_nonneg (prod_nonneg (fun p _ => hx p))
        (LeanLab.PNTSieve.Bonferroni.esymm_nonneg x hx B _)
    _ = LeanLab.PNTSieve.Bonferroni.esymm x (P ∪ B) r :=
      (decomp305_esymm_block_convolution x P B hPB r).symm
    _ ≤ _ := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)]
      have hh := LeanLab.PNTSieve.Bonferroni.factorial_mul_esymm_le x hx (P ∪ B) r
      nlinarith

/-- Second memoir pages 95 and 99, actual normalized unsigned coefficient bound.
A cumulative mass budget bounds the real prime coefficient by the later scalar majorant. -/
lemma decomp305_pair_coefficient_normalized (h y w b : ℕ) (hy : 4 ≤ y)
    (hmass : (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ ((b : ℝ) + 1) / 2) :
    LeanLab.PNTSieve.Bonferroni.esymm (nuN h) ((Ioc y w).filter Nat.Prime) (2 * b) /
        (∏ p ∈ (Ioc y w).filter Nat.Prime, (1 - nuN h p)) ≤
      exp (8 / (y : ℝ)) * decomp305CrudeTerm b := by
  let P := (Ioc y w).filter Nat.Prime
  let M := ∑ p ∈ P, nuN h p
  have hM : 0 ≤ M := sum_nonneg (fun p _ => nuN_nonneg h p)
  have hprod := decomp305_pair_product_lower h y w hy
  have hprod0 : 0 < ∏ p ∈ P, (1 - nuN h p) :=
    (exp_pos _).trans_le hprod
  have he : LeanLab.PNTSieve.Bonferroni.esymm (nuN h) P (2 * b) ≤
      M ^ (2 * b) / ((2 * b).factorial : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have hh := LeanLab.PNTSieve.Bonferroni.factorial_mul_esymm_le
      (nuN h) (nuN_nonneg h) P (2 * b)
    nlinarith
  have hbound : exp M * (M ^ (2 * b) / ((2 * b).factorial : ℝ)) ≤ decomp305CrudeTerm b := by
    have hh := mul_le_mul (exp_le_exp.mpr hmass) (pow_le_pow_left₀ hM hmass (2 * b))
      (pow_nonneg hM _) (exp_pos (((b : ℝ) + 1) / 2)).le
    have hd := div_le_div_of_nonneg_right hh
      (show 0 ≤ ((2 * b).factorial : ℝ) by positivity)
    simpa only [decomp305CrudeTerm, mul_div_assoc] using hd
  change LeanLab.PNTSieve.Bonferroni.esymm (nuN h) P (2 * b) /
    (∏ p ∈ P, (1 - nuN h p)) ≤ exp (8 / (y : ℝ)) * decomp305CrudeTerm b
  calc
    _ ≤ (M ^ (2 * b) / ((2 * b).factorial : ℝ)) /
        (∏ p ∈ P, (1 - nuN h p)) := div_le_div_of_nonneg_right he hprod0.le
    _ ≤ (M ^ (2 * b) / ((2 * b).factorial : ℝ)) / exp (-M - 8 / (y : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hprod
    _ = exp (8 / (y : ℝ)) * (exp M * (M ^ (2 * b) / ((2 * b).factorial : ℝ))) := by
      rw [div_eq_mul_inv, ← exp_neg, show -(-M - 8 / (y : ℝ)) = M + 8 / (y : ℝ) by ring, exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (exp_pos _).le

/-- Second memoir page 99 formula 18.3, exact identification of successive density products. -/
lemma decomp305_prime_product_iteration (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (hw : c 0 ≤ w) (s n : ℕ) :
    (∏ p ∈ (Ioc (c (s + n)) w).filter Nat.Prime, (1 - x p)) =
      (∏ p ∈ (Ioc (c s) w).filter Nat.Prime, (1 - x p)) *
        ∏ j ∈ range n, ∏ p ∈ (Ioc (c (s + j + 1)) (c (s + j))).filter Nat.Prime,
          (1 - x p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcur : c (s + n) ≤ w := (hc (Nat.zero_le _)).trans hw
    have hnext : c (s + n + 1) ≤ c (s + n) := hc (by omega)
    have hsets : (Ioc (c (s + n + 1)) w).filter Nat.Prime =
        ((Ioc (c (s + n)) w).filter Nat.Prime) ∪
          ((Ioc (c (s + n + 1)) (c (s + n))).filter Nat.Prime) := by
      ext p
      simp only [mem_filter, mem_Ioc, mem_union]
      by_cases hp : p.Prime
      · simp only [hp, and_true]
        omega
      · simp [hp]
    have hdisj : Disjoint ((Ioc (c (s + n)) w).filter Nat.Prime)
        ((Ioc (c (s + n + 1)) (c (s + n))).filter Nat.Prime) := by
      apply disjoint_left.mpr
      intro p hp hq
      have hp' := mem_Ioc.mp (mem_filter.mp hp).1
      have hq' := mem_Ioc.mp (mem_filter.mp hq).1
      omega
    rw [show s + (n + 1) = s + n + 1 by omega, hsets, prod_union hdisj, ih, prod_range_succ]
    ring

/-- Second memoir pages 95, 99 and 109, the actual first omitted boundary.
The full cumulative mass budget gives the shifted factorial scalar majorant. -/
lemma decomp305_pair_boundary_normalized (h w : ℕ) (c : ℕ → ℕ) (hc : Antitone c)
    (i : ℕ) (hw : c i ≤ w) (hy : 4 ≤ c (i + 1))
    (hmass : (∑ p ∈ (Ioc (c (i + 1)) w).filter Nat.Prime, nuN h p) ≤
      (((i + 2 : ℕ) : ℝ) + 1) / 2) :
    (∑ S ∈ decomp305PrimeFamily w c i, (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h)
        ((Ioc (c (i + 1)) (c i)).filter Nat.Prime)
        (2 * (i + 1) + 1 - S.card + 1)) /
      (∏ p ∈ (Ioc (c (i + 1)) w).filter Nat.Prime, (1 - nuN h p)) ≤
      exp (8 / (c (i + 1) : ℝ)) * decomp305CrudeTerm (i + 2) := by
  let P := (Ioc (c i) w).filter Nat.Prime
  let B := (Ioc (c (i + 1)) (c i)).filter Nat.Prime
  let Q := (Ioc (c (i + 1)) w).filter Nat.Prime
  let U := decomp305PrimeFamily w c i
  have hnext : c (i + 1) ≤ c i := hc (by omega)
  have hsets : P ∪ B = Q := by
    dsimp [P, B, Q]
    rw [← filter_union, union_comm, Ioc_union_Ioc_eq_Ioc hnext hw]
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := mem_Ioc.mp (mem_filter.mp hp).1
    have hq' := mem_Ioc.mp (mem_filter.mp hq).1
    omega
  have hsub : U ⊆ P.powerset.filter (fun S => S.card ≤ 2 * (i + 2)) := by
    intro S hS
    have hcard := decomp305_prime_family_card w c i S hS
    have hSP : S ⊆ P := by
      have hs : S ∈ decomp305PrimeFamily w c i := hS
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
      exact hs.1
    exact mem_filter.mpr ⟨mem_powerset.mpr hSP, by omega⟩
  have hPhi : (∑ S ∈ U, (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B
        (2 * (i + 1) + 1 - S.card + 1)) ≤
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) Q (2 * (i + 2)) := by
    calc
      _ = ∑ S ∈ U, (∏ p ∈ S, nuN h p) *
          LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 2) - S.card) := by
        apply sum_congr rfl
        intro S hS
        have hcard := decomp305_prime_family_card w c i S hS
        rw [show 2 * (i + 1) + 1 - S.card + 1 = 2 * (i + 2) - S.card by omega]
      _ ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * (i + 2)), (∏ p ∈ S, nuN h p) *
          LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 2) - S.card) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro S _ _
        exact mul_nonneg (prod_nonneg (fun p _ => nuN_nonneg h p))
          (LeanLab.PNTSieve.Bonferroni.esymm_nonneg (nuN h) (nuN_nonneg h) B _)
      _ = LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (P ∪ B) (2 * (i + 2)) :=
        (decomp305_esymm_block_convolution (nuN h) P B hPB _).symm
      _ = _ := by rw [hsets]
  have hprod0 : 0 < ∏ p ∈ Q, (1 - nuN h p) :=
    (exp_pos _).trans_le (decomp305_pair_product_lower h (c (i + 1)) w hy)
  change (∑ S ∈ U, (∏ p ∈ S, nuN h p) *
    LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 1) + 1 - S.card + 1)) /
      (∏ p ∈ Q, (1 - nuN h p)) ≤ _
  exact (div_le_div_of_nonneg_right hPhi hprod0.le).trans
    (decomp305_pair_coefficient_normalized h (c (i + 1)) w (i + 2) hy hmass)

end
end LeanLab.Ricci1937

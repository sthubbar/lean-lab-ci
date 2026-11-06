import LeanLab.Ricci1937.Decomp305a

/-!
Ricci 1937, finite retained head limits.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.PNTSieve.Bonferroni

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary degree form of second memoir page 97 formula 15.7.
The retained old coefficient convolves with the new block symmetric coefficient. -/
lemma decomp338_retained_degree_convolution (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (A : Finset ℕ → Prop) [DecidablePred A] (k : ℕ) :
    (∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card = k),
      ∏ p ∈ V, x p) =
      ∑ j ∈ range (k + 1),
        (∑ S ∈ P.powerset.filter (fun S => A S ∧ S.card = j), ∏ p ∈ S, x p) *
          esymm x B (k - j) := by
  rw [sum_filter, decomp305_disjoint_powerset_sum P B hPB]
  have hleft : (∑ S ∈ P.powerset, ∑ T ∈ B.powerset,
      if A ((S ∪ T) ∩ P) ∧ (S ∪ T).card = k then ∏ p ∈ S ∪ T, x p else 0) =
      ∑ S ∈ P.powerset.filter (fun S => A S ∧ S.card ≤ k),
        (∏ p ∈ S, x p) * esymm x B (k - S.card) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro S hS
    have hSP := mem_powerset.mp hS
    have hint (T : Finset ℕ) (hT : T ∈ B.powerset) : (S ∪ T) ∩ P = S := by
      have hTP := (hPB.mono_right (mem_powerset.mp hT)).symm
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    by_cases hAS : A S ∧ S.card ≤ k
    · rw [if_pos hAS]
      unfold esymm
      rw [powersetCard_eq_filter, sum_filter, mul_sum]
      apply sum_congr rfl
      intro T hT
      have hST := hPB.mono hSP (mem_powerset.mp hT)
      have hcard : S.card + T.card = k ↔ T.card = k - S.card := by omega
      rw [hint T hT, card_union_of_disjoint hST, prod_union hST]
      simp only [hAS.1, true_and, hcard, mul_ite, mul_zero]
    · rw [if_neg hAS]
      apply sum_eq_zero
      intro T hT
      have hST := hPB.mono hSP (mem_powerset.mp hT)
      rw [hint T hT, card_union_of_disjoint hST]
      apply if_neg
      intro h
      exact hAS ⟨h.1, by omega⟩
  rw [hleft]
  symm
  calc
    _ = ∑ j ∈ range (k + 1),
        ∑ S ∈ (P.powerset.filter (fun S => A S ∧ S.card ≤ k)).filter
            (fun S => S.card = j), (∏ p ∈ S, x p) * esymm x B (k - S.card) := by
      apply sum_congr rfl
      intro j hj
      rw [sum_mul]
      apply sum_congr
      · ext S
        simp only [mem_filter]
        have hjk : j ≤ k := by have := mem_range.mp hj; omega
        aesop
      · intro S hS
        have hSj := (mem_filter.mp hS).2
        simp only [hSj]
    _ = _ := sum_fiberwise_of_maps_to
      (fun S hS => mem_range.mpr (by have := (mem_filter.mp hS).2.2; omega)) _


/-- Auxiliary block limit for second memoir pages 97 and 111 formula 28.11.
Convergence of every old degree coefficient and of the new block moments gives
convergence of the next retained degree coefficient. -/
lemma decomp338_retained_degree_tendsto (x : ℕ → ℕ → ℝ)
    (P B : ℕ → Finset ℕ) (hPB : ∀ n, Disjoint (P n) (B n))
    (A : ℕ → Finset ℕ → Prop) [∀ n, DecidablePred (A n)]
    (hx : ∀ n p, 0 ≤ x n p) (a : ℕ → ℝ) (t : ℝ) (k : ℕ)
    (ha : ∀ j ≤ k, Tendsto (fun n =>
      ∑ S ∈ (P n).powerset.filter (fun S => A n S ∧ S.card = j), ∏ p ∈ S, x n p)
      atTop (nhds (a j)))
    (ht : Tendsto (fun n => ∑ p ∈ B n, x n p) atTop (nhds t))
    (hq : Tendsto (fun n => ∑ p ∈ B n, (x n p) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => ∑ V ∈ ((P n) ∪ (B n)).powerset.filter
      (fun V => A n (V ∩ P n) ∧ V.card = k), ∏ p ∈ V, x n p)
      atTop (nhds (∑ j ∈ range (k + 1), a j * (t ^ (k - j) / ((k - j).factorial : ℝ)))) := by
  have hh : (fun n => ∑ V ∈ ((P n) ∪ (B n)).powerset.filter
      (fun V => A n (V ∩ P n) ∧ V.card = k), ∏ p ∈ V, x n p) =
      (fun n => ∑ j ∈ range (k + 1),
        (∑ S ∈ (P n).powerset.filter (fun S => A n S ∧ S.card = j), ∏ p ∈ S, x n p) *
          esymm (x n) (B n) (k - j)) := by
    funext n
    exact decomp338_retained_degree_convolution (x n) (P n) (B n) (hPB n) (A n) k
  rw [hh]
  apply tendsto_finsetSum
  intro j hj
  exact (ha j (by have := mem_range.mp hj; omega)).mul
    (decompJ365_esymm_tendsto x B hx t ht hq (k - j))


/-- Actual retained prime degree coefficient from second memoir page 97 formula 14.8.
The odd prefix caps are those of decomp305PrimeFamily. -/
def decomp338PrimeCoeff (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ S ∈ (decomp305PrimeFamily w c n).filter (fun S => S.card = k), ∏ p ∈ S, x p

/-- Second memoir page 97 formula 15.7 for the actual decreasing prime family. -/
lemma decomp338_prime_coeff_step (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (n k : ℕ) (hw : c n ≤ w) (hk : k ≤ 2 * (n + 1) + 1) :
    decomp338PrimeCoeff x w c (n + 1) k =
      ∑ j ∈ range (k + 1), decomp338PrimeCoeff x w c n j *
        esymm x ((Ioc (c (n + 1)) (c n)).filter Nat.Prime) (k - j) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpI := mem_Ioc.mp (mem_filter.mp hp).1
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
    omega
  have hfilter : (decomp305PrimeFamily w c (n + 1)).filter (fun S => S.card = k) =
      (P ∪ B).powerset.filter (fun V => V ∩ P ∈ decomp305PrimeFamily w c n ∧ V.card = k) := by
    rw [decomp305_prime_family_step w c hc n hw]
    ext V
    simp only [mem_filter, P, B]
    constructor
    · rintro ⟨⟨hV, hA, hcap⟩, hVk⟩
      exact ⟨hV, hA, hVk⟩
    · rintro ⟨hV, hA, hVk⟩
      exact ⟨⟨hV, hA, by omega⟩, hVk⟩
  unfold decomp338PrimeCoeff
  rw [hfilter, decomp338_retained_degree_convolution x P B hPB]
  apply sum_congr rfl
  intro j hj
  congr 1
  congr 1
  ext S
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hSP, hS, hj⟩
    exact ⟨hS, hj⟩
  · rintro ⟨hS, hj⟩
    have hSP : S ⊆ P := by
      have hs := hS
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
      exact hs.1
    exact ⟨hSP, hS, hj⟩

/-- Second memoir page 97 formula 15.5 for the actual retained prime family.
Grouping by degree keeps the signed head exact. -/
lemma decomp338_prime_head_by_degree (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    (∑ S ∈ decomp305PrimeFamily w c n, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      ∑ k ∈ range (2 * (n + 1)), (-1 : ℝ) ^ k * decomp338PrimeCoeff x w c n k := by
  symm
  calc
    _ = ∑ k ∈ range (2 * (n + 1)),
        ∑ S ∈ (decomp305PrimeFamily w c n).filter (fun S => S.card = k),
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p := by
      apply sum_congr rfl
      intro k hk
      rw [decomp338PrimeCoeff, mul_sum]
      apply sum_congr rfl
      intro S hS
      rw [(mem_filter.mp hS).2]
    _ = _ := sum_fiberwise_of_maps_to (fun S hS => mem_range.mpr
      (by have := decomp305_prime_family_card w c n S hS; omega)) _


/-- Auxiliary scaling identity for second memoir page 97 formula 15.7.
The integer convolution becomes the factorial convolution after removing its scale. -/
lemma decomp338_scaled_convolution (a : ℕ → ℕ) (t k : ℕ) :
    ((∑ j ∈ range (k + 1),
      (k.factorial / (j.factorial * (k - j).factorial)) * a j * t ^ (k - j) : ℕ) : ℝ) /
      ((100 : ℝ) ^ k * (k.factorial : ℝ)) =
      ∑ j ∈ range (k + 1),
        ((a j : ℝ) / ((100 : ℝ) ^ j * (j.factorial : ℝ))) *
          (((t : ℝ) / 100) ^ (k - j) / ((k - j).factorial : ℝ)) := by
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := mem_range.mp hj; omega
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hjk) (by positivity)]
  push_cast
  have hp : (100 : ℝ) ^ k = 100 ^ j * 100 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk]
  rw [hp, div_pow]
  field_simp <;> ring

/-- Auxiliary coefficient recurrence for second memoir page 97 formula 15.7.
The existing integer list has the exact factorial convolution at every retained degree. -/
lemma decomp338_head_coeff_step (n k : ℕ) (hk : k < 2 * (n + 1)) :
    (((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
      ((100 : ℝ) ^ k * (k.factorial : ℝ)) =
      ∑ j ∈ range (k + 1),
        ((((decomp305HeadCoeff n)[j]?.getD 0 : ℕ) : ℝ) /
          ((100 : ℝ) ^ j * (j.factorial : ℝ))) *
        (((decomp305HeadMass n : ℝ) / 100) ^ (k - j) / ((k - j).factorial : ℝ)) := by
  rw [decomp305HeadCoeff, decomp305HeadStep, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  exact decomp338_scaled_convolution _ _ _

/-- Auxiliary support of the integer coefficient list for second memoir page 97 formula 15.7. -/
lemma decomp338_head_coeff_length (n : ℕ) :
    (decomp305HeadCoeff (n + 1)).length = 2 * (n + 1) := by
  simp [decomp305HeadCoeff, decomp305HeadStep]


/-- Second memoir page 97 formula 14.8, the last odd cap removes every higher degree. -/
lemma decomp338_prime_coeff_eq_zero (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (n k : ℕ) (hk : 2 * n + 1 < k) : decomp338PrimeCoeff x w c n k = 0 := by
  unfold decomp338PrimeCoeff
  apply sum_eq_zero
  intro S hS
  obtain ⟨hS, hSk⟩ := mem_filter.mp hS
  have := decomp305_prime_family_card w c n S hS
  omega

/-- Second memoir page 97 formula 15.7 at the first odd cap.
The initial retained coefficient is the unrestricted symmetric coefficient through degree one. -/
lemma decomp338_prime_coeff_initial (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (k : ℕ) (hk : k ≤ 1) :
    decomp338PrimeCoeff x w c 0 k = esymm x ((Ioc (c 0) w).filter Nat.Prime) k := by
  unfold decomp338PrimeCoeff esymm
  congr 1
  ext S
  constructor
  · intro h
    obtain ⟨hS, hSk⟩ := mem_filter.mp h
    have hs := hS
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
    exact mem_powersetCard.mpr ⟨hs.1, hSk⟩
  · intro h
    obtain ⟨hSP, hSk⟩ := mem_powersetCard.mp h
    apply mem_filter.mpr
    refine ⟨?_, hSk⟩
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset]
    refine ⟨hSP, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simpa using mem_range.mp hj
    subst j
    exact (card_filter_le _ _).trans (by omega)


/-- Prime blocks in the lower decreasing sieve of second memoir pages 92 and 97.
Block zero is above the first cutoff. Each later block lies between consecutive cutoffs. -/
def decomp338PrimeBlock (w : ℕ) (c : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => (Ioc (c 0) w).filter Nat.Prime
  | i + 1 => (Ioc (c (i + 1)) (c i)).filter Nat.Prime

/-- Auxiliary finite head limit in second memoir page 111 formula 28.11.
Every actual retained degree coefficient tends to its scaled integer factorial model. -/
lemma decomp338_prime_coeff_tendsto (x : ℕ → ℕ → ℝ)
    (w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (hx : ∀ q p, 0 ≤ x q p)
    (ht : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, x q p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hq : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (x q p) ^ 2)
      atTop (nhds 0)) (n k : ℕ) :
    Tendsto (fun q => decomp338PrimeCoeff (x q) (w q) (c q) n k) atTop
      (nhds ((((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
        ((100 : ℝ) ^ k * (k.factorial : ℝ)))) := by
  induction n generalizing k with
  | zero =>
    by_cases hk : k ≤ 1
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) 0 k) =
          (fun q => esymm (x q) (decomp338PrimeBlock (w q) (c q) 0) k) := by
        funext q
        exact decomp338_prime_coeff_initial (x q) (w q) (c q) k hk
      rw [heq]
      have hl := decompJ365_esymm_tendsto x
        (fun q => decomp338PrimeBlock (w q) (c q) 0) hx
        ((decomp305HeadMass 0 : ℝ) / 100) (ht 0) (hq 0) k
      convert hl using 1
      interval_cases k <;> norm_num [decomp305HeadCoeff, decomp305HeadStep,
        decomp305HeadMass, sum_range_succ]
    · have hk' : 1 < k := by omega
      have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) 0 k) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext q
        exact decomp338_prime_coeff_eq_zero (x q) (w q) (c q) 0 k (by omega)
      rw [heq, List.getElem?_eq_none (by rw [decomp338_head_coeff_length]; omega)]
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  | succ n ih =>
    by_cases hk : k < 2 * (n + 1 + 1)
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) (n + 1) k) =
          (fun q => ∑ j ∈ range (k + 1),
            decomp338PrimeCoeff (x q) (w q) (c q) n j *
              esymm (x q) (decomp338PrimeBlock (w q) (c q) (n + 1)) (k - j)) := by
        funext q
        exact decomp338_prime_coeff_step (x q) (w q) (c q) (hc q) n k
          ((hc q (Nat.zero_le n)).trans (hw q)) (by omega)
      rw [heq, decomp338_head_coeff_step (n + 1) k hk]
      apply tendsto_finsetSum
      intro j hj
      exact (ih j).mul (decompJ365_esymm_tendsto x
        (fun q => decomp338PrimeBlock (w q) (c q) (n + 1)) hx
        ((decomp305HeadMass (n + 1) : ℝ) / 100) (ht (n + 1)) (hq (n + 1)) (k - j))
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) (n + 1) k) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext q
        exact decomp338_prime_coeff_eq_zero (x q) (w q) (c q) (n + 1) k (by omega)
      rw [heq, List.getElem?_eq_none (by rw [decomp338_head_coeff_length]; omega)]
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))


/-- Auxiliary finite head limit in second memoir page 111 formula 28.11.
At every fixed block count the actual signed retained head tends to its exact factorial model. -/
lemma decomp338_prime_head_tendsto (x : ℕ → ℕ → ℝ)
    (w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (hx : ∀ q p, 0 ≤ x q p)
    (ht : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, x q p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hq : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (x q p) ^ 2)
      atTop (nhds 0)) (n : ℕ) :
    Tendsto (fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) n,
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x q p) atTop (nhds (decomp305HeadValue (n + 1) : ℝ)) := by
  have heq : (fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) n,
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x q p) =
      (fun q => ∑ k ∈ range (2 * (n + 1)),
        (-1 : ℝ) ^ k * decomp338PrimeCoeff (x q) (w q) (c q) n k) := by
    funext q
    exact decomp338_prime_head_by_degree (x q) (w q) (c q) n
  have hv : (decomp305HeadValue (n + 1) : ℝ) =
      ∑ k ∈ range (2 * (n + 1)), (-1 : ℝ) ^ k *
        ((((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
          ((100 : ℝ) ^ k * (k.factorial : ℝ))) := by
    rw [decomp305HeadValue]
    push_cast
    apply sum_congr rfl
    intro k hk
    ring
  rw [heq, hv]
  apply tendsto_finsetSum
  intro k hk
  exact tendsto_const_nhds.mul
    (decomp338_prime_coeff_tendsto x w c hc hw hx ht hq n k)

end
end LeanLab.Ricci1937

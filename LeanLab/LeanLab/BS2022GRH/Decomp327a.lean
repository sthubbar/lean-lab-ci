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

/-- LEAF. Finite stopping expansion of both ordinary Rosser models.
BJS p. 14 Proposition 13 proof, citing Nathanson Lemma 9.3.
This is a finite polynomial identity. It has no dimension premise, delay
function, numerical constant, sequence support or exceptional prime factor. -/
theorem stopping_expansion (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime) (hD : 1 < D) :
    (rosserPrimeModel S ∅ D true g = (∏ p ∈ S, (1 - g p)) +
      ∑ n ∈ range (S.card + 3), if n % 2 = 1 then stoppingTerm S D g n else 0) ∧
    (rosserPrimeModel S ∅ D false g = (∏ p ∈ S, (1 - g p)) -
      ∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then stoppingTerm S D g n else 0) := by
  sorry

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

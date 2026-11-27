/-
P0069 Baker, Harman, Pintz 1997, pages 47 to 50, burst-20261122 session S130, tag
upD_lemma34_52-p3. Split of the two Lemma 33 case 5.13 LEAFs of the upD52 wave,
`upD52_leaf_lemma33_block` and `upD52_leaf_gs_pair_big`, one step further.

Page 47, the remarks before Lemma 33: for G = N M with Y^eps < N < Y^c1 and M satisfying 3.2,
Lemma 32 with j = 8 gives, through 5.10 to 5.12, the bound for one interval of length T2, and
"the contribution to M_j(G) from any interval [k T2, (k + 1) T2] is << Y T2^(-2) (k^2 + 1)^(-1)
L^(-A). Accordingly, (5.1) and (5.2) hold." Case 5.13 of Lemma 33 is exactly these remarks.

Here the step "accordingly 5.2 holds" is PROVED, uniformly in an index, as
`s130w_of_wellspaced_indexed`, by the same unit block and consecutive block summation as
`upD52_gbig_of_wellspaced` on main. What remains in each LEAF is the one interval bound, in the
well spaced form the lab already uses in `kept52_wellspaced` and `upD52_gbig_of_wellspaced`.

No new definition, no existing statement changed. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52BigBlocks
import LeanLab.BHP1997.Prep1122UpD52SmallStep

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 47, the sentence "Accordingly, (5.1) and (5.2) hold" before Lemma 33, for 5.2 of
page 43 and the principal character, uniform in an index i ranging over the pairs with R x i:
a well spaced bound on every interval of length T2 in the range T0 <= |t| <= Y, with one
constant for all admissible i, gives 5.2 with one constant for all admissible i. PROVED, the
proof of `upD52_gbig_of_wellspaced` with the index carried along. -/
theorem s130w_of_wellspaced_indexed {ε : ℝ} {ι : Type*} (R : ℝ → ι → Prop)
    (c : ℝ → ι → ℕ → ℝ)
    (hws : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ i : ι, R x i →
      ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ i : ι, R x i →
      ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := hws A hA
  refine ⟨max (12 * max C 0) (max C 1), fun x hx i hi q hq1 hqQ => ?_⟩
  have hxC : C ≤ x := (le_max_left C 1).trans (hx.trans' (le_max_right _ _))
  have hx1 : 1 ≤ x := (le_max_right C 1).trans (hx.trans' (le_max_right _ _))
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set T0 := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hT0def
  set T2 := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT2def
  set Lg := Real.log x ^ (-A) with hLg
  set F : ℝ → ℝ := fun t => ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
    with hFdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ Lg := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hQ1 : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hqQ
  have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT2 : 0 < T2 := by rw [hT2def]; positivity
  have hT0 : 0 ≤ T0 := (Real.exp_pos _).le
  have hFc : Continuous F := kept52_continuous ε x q (c x i)
  have hF0 : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  set M := max C 0 with hM
  have hV : 0 ≤ 2 * (M * Y * Lg) := by positivity
  have hblock : ∀ a b : ℝ, a ≤ b → b - a ≤ T2 →
      ((T0 ≤ a ∧ b ≤ Y) ∨ (-Y ≤ a ∧ b ≤ -T0)) → ∫ t in a..b, F t ≤ 2 * (M * Y * Lg) := by
    intro a b hab hba hrange
    have h1 := kept52_block_le_two_wellspaced F hFc hF0 hab
      (hC x hxC i hi q hq1 hqQ a b hab hba hrange)
    have h2 : C * Y * Lg ≤ M * Y * Lg :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hL0
    linarith
  have hpos : ∫ t in T0..Y, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
    kept52_block_sum F hFc hF0 hT0 hT2 hV fun a b ha hab hb hba =>
      hblock a b hab hba (Or.inl ⟨ha, hb⟩)
  have hneg : ∫ t in -Y..-T0, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 := by
    have hc := intervalIntegral.integral_comp_neg (a := T0) (b := Y)
      (fun t => F t / (T2 ^ 2 + t ^ 2))
    simp only [neg_sq] at hc
    rw [← hc]
    refine kept52_block_sum (fun t => F (-t)) (hFc.comp continuous_neg) (fun t => hF0 _)
      hT0 hT2 hV fun a b ha hab hb hba => ?_
    have hc2 := intervalIntegral.integral_comp_neg (a := a) (b := b) F
    rw [hc2]
    exact hblock (-b) (-a) (by linarith) (by linarith) (Or.inr ⟨by linarith, by linarith⟩)
  have hmain : 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 =
      12 * M * (Y / T2 ^ 2) * Lg := by ring
  have hfin : 12 * M * (Y / T2 ^ 2) * Lg ≤ max (12 * M) (max C 1) * (Y / T2 ^ 2) * Lg :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hL0
  calc _ ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
        add_le_add hneg hpos
    _ = 12 * M * (Y / T2 ^ 2) * Lg := hmain
    _ ≤ _ := hfin

/-- P0069 page 49, the Buchstab prime sum in g_m. Restricting its prime factors leaves a sum
between zero and one, since only the least prime factor contributes. -/
theorem s130w_rough_subsum_le_one (k : ℕ) (s : Finset ℕ) (hs : s ⊆ k.primeFactors) :
    ∑ p ∈ s, upperRough (k / p) (p : ℝ) ≤ 1 := by
  have hfull : ∑ p ∈ k.primeFactors, upperRough (k / p) (p : ℝ) ≤ 1 := by
    have hbuch := upper_rough_buchstab_step k
      (z1 := 0) (z2 := (k : ℝ) + 1) (by positivity)
    have hfilter : k.primeFactors.filter
        (fun p : ℕ => (0 : ℝ) ≤ p ∧ (p : ℝ) < (k : ℝ) + 1) = k.primeFactors := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have hpk : (p : ℝ) ≤ k := by exact_mod_cast Nat.le_of_mem_primeFactors hp
      exact ⟨Nat.cast_nonneg _, by linarith⟩
    rw [hfilter] at hbuch
    have hzero : upperRough k 0 = 1 := by
      simp only [upperRough]
      rw [ite_eq_left (fun p _ => Nat.cast_nonneg p)]
    rw [hzero] at hbuch
    linarith [upperRough_nonneg k ((k : ℝ) + 1)]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun p _ _ => upperRough_nonneg _ _)).trans hfull

/-- P0069 page 49, the block h_m of the proof of Lemma 34. Its absolute value is at most
the sum of the absolute values of the n coefficients, with no loss for the prime filter. -/
theorem s130w_block_abs_le (a : ℕ → ℝ) (k : ℕ) (ns : Finset ℕ)
    (ps : ℕ → Finset ℕ) (hps : ∀ n ∈ ns, ps n ⊆ (k / n).primeFactors) :
    |∑ n ∈ ns, a n * ∑ p ∈ ps n, upperRough (k / n / p) (p : ℝ)| ≤
      ∑ n ∈ ns, |a n| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hnonneg : 0 ≤ ∑ p ∈ ps n, upperRough (k / n / p) (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => upperRough_nonneg _ _)
  rw [abs_mul, abs_of_nonneg hnonneg]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (s130w_rough_subsum_le_one (k / n) (ps n) (hps n hn)) (abs_nonneg (a n))

/-- P0069 pages 11 and 49, condition 3.1 for a divisor block h_m. A divisor bound with
exponent B gives exponent max B 0 plus one, uniformly in both filters. -/
theorem s130w_block_divisor_bound (a : ℕ → ℝ) (k : ℕ) (ns : Finset ℕ)
    (ps : ℕ → Finset ℕ) (hns : ns ⊆ k.divisors)
    (hps : ∀ n ∈ ns, ps n ⊆ (k / n).primeFactors) {C B : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C * (n.divisors.card : ℝ) ^ B) :
    |∑ n ∈ ns, a n * ∑ p ∈ ps n, upperRough (k / n / p) (p : ℝ)| ≤
      C * (k.divisors.card : ℝ) ^ (max B 0 + 1) := by
  by_cases hk : k = 0
  · subst k
    have hns0 : ns = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have := hns hn
      simp at this
    simp only [hns0, Finset.sum_empty, abs_zero]
    positivity
  have hdpos : 0 < k.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk⟩
  have hd : 0 < (k.divisors.card : ℝ) := by exact_mod_cast hdpos
  have hterm : ∀ n ∈ ns, |a n| ≤ C * (k.divisors.card : ℝ) ^ max B 0 := by
    intro n hn
    have hnk := (Nat.mem_divisors.mp (hns hn)).1
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      exact hk (by simpa using hnk)
    have hncard : 1 ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩)
    have hcard : (n.divisors.card : ℝ) ≤ k.divisors.card := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk hnk)
    apply (ha n).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact (Real.rpow_le_rpow_of_exponent_le hncard (le_max_left B 0)).trans
      (Real.rpow_le_rpow (by positivity) hcard (le_max_right B 0))
  calc
    _ ≤ ∑ n ∈ ns, |a n| := s130w_block_abs_le a k ns ps hps
    _ ≤ ∑ n ∈ ns, C * (k.divisors.card : ℝ) ^ max B 0 :=
      Finset.sum_le_sum hterm
    _ = (ns.card : ℝ) * (C * (k.divisors.card : ℝ) ^ max B 0) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k.divisors.card : ℝ) * (C * (k.divisors.card : ℝ) ^ max B 0) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hns) (by positivity)
    _ = C * (k.divisors.card : ℝ) ^ (max B 0 + 1) := by
      rw [Real.rpow_add hd, Real.rpow_one]
      ring

/-- LEAF: P0069 pages 47 and 49 to 50, Lemma 33 case 5.13 for the block h_m of page 49, the one
interval bound of the remarks before Lemma 33: N(s, chi) the sum over P <= p1 < 2P,
Y^eps <= p1, of chi(p1) p1^(-s), satisfying 3.2 by Lemma 5, times the n and psi factor
satisfying 3.1; Lemma 32 with j = 8 and 5.10 to 5.12 bound the mean square over any well
spaced set S in one interval of length T2 = Y/(q Q) inside T0 <= |t| <= Y by Y L^(-A), with one
constant for all P with 1 <= P <= Y^c1. Principal character. CONDITIONAL on the cited Theorem 4
and Lemma 9. Class HARD. Same coefficient as `upD52_leaf_lemma33_block`, with its notes on the
boundary Y^eps of case 5.13 and on the coupling of n1 and p1 through psi(n1, p1). -/
theorem s130w_leaf_lemma33_block_wellspaced (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x P k, c x P k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ P : ℕ, 1 ≤ P →
      (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ u v : ℝ, u ≤ v → v - u ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ u ∧ v ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ u ∧ v ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, u ≤ t ∧ t ≤ v) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x P m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨Ca, hCa⟩ := ha
  have hcoeff : ∀ x P k, |c x P k| ≤
      max Ca 0 * (k.divisors.card : ℝ) ^ (max B 0 + 1) := by
    intro x P k
    rw [hc]
    apply s130w_block_divisor_bound (a x) k _ _
      (Finset.filter_subset _ _) (fun n _ => Finset.filter_subset _ _)
      (le_max_right Ca 0)
    intro n
    exact (hCa x n).trans (mul_le_mul_of_nonneg_right (le_max_left Ca 0)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  -- The divisor bound supplies no logarithmic saving. Lemma 5 and the Lemma 32 moment bound
  -- remain necessary for the nonzero polynomial.
  sorry

/-- P0069 pages 47 to 50, Lemma 33 case 5.13 for the block h_m, with the exact statement of
`upD52_leaf_lemma33_block`. PROVED from the LEAF `s130w_leaf_lemma33_block_wellspaced` by
`s130w_of_wellspaced_indexed`, indexed by P. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem s130w_lemma33_block : type_of% @upD52_leaf_lemma33_block := by
  intro h4 h9 ε hε hε8 a B ha c hc
  have key := s130w_of_wellspaced_indexed (ε := ε)
    (fun x (P : ℕ) => 1 ≤ P ∧ (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε) c
    (fun A hA => by
      obtain ⟨C, hC⟩ := s130w_leaf_lemma33_block_wellspaced h4 h9 hε hε8 a ha c hc A hA
      exact ⟨C, fun x hx P hP => hC x hx P hP.1 hP.2⟩)
  intro A hA
  obtain ⟨C, hC⟩ := key A hA
  exact ⟨C, fun x hx P hP1 hP2 => hC x hx P ⟨hP1, hP2⟩⟩

/-- LEAF: P0069 pages 47 and 50, Lemma 33 case 5.13 for the pair part of the second Buchstab
step, the one interval bound of the remarks before Lemma 33: p1 p2 is the variable, of size
between Y^eps and Y^(2 eps) < Y^c1, its Dirichlet polynomial satisfying 3.2 by Lemma 5, the n
and psi factor satisfying 3.1; Lemma 32 with j = 8 and 5.10 to 5.12 bound the mean square over
any well spaced set S in one interval of length T2 = Y/(q Q) inside T0 <= |t| <= Y by Y L^(-A).
Principal character. Same coefficient as `upD52_leaf_gs_pair_big`. CONDITIONAL on the cited
Theorem 4 and Lemma 9. Class HARD. -/
theorem s130w_leaf_gs_pair_big_wellspaced (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ u v : ℝ, u ≤ v → v - u ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ u ∧ v ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ u ∧ v ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, u ≤ t ∧ t ≤ v) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 50, the pair part with Y^eps <= p1 p2, with the exact statement of
`upD52_leaf_gs_pair_big`. PROVED from the LEAF `s130w_leaf_gs_pair_big_wellspaced` by
`upD52_gbig_of_wellspaced` of main. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem s130w_gs_pair_big : type_of% @upD52_leaf_gs_pair_big := by
  intro h4 h9 ε hε hε8 a B ha c hc
  exact upD52_gbig_of_wellspaced c
    (s130w_leaf_gs_pair_big_wellspaced h4 h9 hε hε8 a ha c hc)

end LeanLab.BHP1997.DecompC165d

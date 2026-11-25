/-
P0069 Baker Harman Pintz 1997, Lemma 30 on pages 44 and 45, for one dyadic block n ~ 2^j.
Burst burst-20261122, session S130, tag upD_lemma34_51-p3. Split of the HARD leaf
`l34L_f_block` of Prep1122Lemma34Leaves51. The theorem `l30s_f_block` below has the exact
statement of that leaf, written as type_of%, and no open goal of its own.

The paper's proof on page 44: "As in the proof of Lemma 12, b_m = sum over n, d <= gamma,
ndr = m of a_n mu(d) plus sum over nl = m of a_n t_gamma(l), where gamma = x^(eps/2)", the
sum over d running over d | P(w). Thus G = G1 + G2. Here psi(l, w) is `upperRough l w`, the
Moebius sum over d | l, d | P(w) truncated at gamma is written out with `Thm2.primorialBelow w`
for P(w), the same body as `Decomp312a.truncatedMobiusWeight`, and t_gamma(l) is psi(l, w)
minus that truncated sum, exactly the paper's definition of t_gamma.

PROVED here: `l30s_sumU`, the summation step `l34L_sum` of Prep1122Lemma34Leaves51 made uniform
in an extra parameter k, here the block index j; `l30s_f_block`, the leaf, from the two LEAFs
by G = G1 + G2 and `l30s_sumU` with two pieces.
LEAF `l30s_G1_block`, HARD: 5.1 with G1 in place of G, page 45, cases j = 0 and j = 1, from
display 3.3 and Lemma 9 after the dyadic split d ~ D, r ~ R = Y/(ND).
LEAF `l30s_G2_block`, HARD: 5.1 with G2 in place of G, page 45 last paragraph, from 3.3 and
the coefficient sum of 4.13, with |t_gamma(l)| bounded by the band count, PROVED here as
`l30s_tgamma_band` from the lab's `Decomp312a.fundamental_sifted_truncation`, with
`l30s_upperRough_sifted`.
New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122Lemma34Leaves51
import LeanLab.BHP1997.Decomp312a

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 43, the summation of 5.1 over at most log^e x pieces, `l34L_sum` of
Prep1122Lemma34Leaves51 with the same proof, uniform in an extra parameter k. PROVED. -/
theorem l30s_sumU {ε : ℝ} {κ ι : Type*} (e : ℕ) (Ix : ℝ → Finset ι) (u : κ → ι → ℝ → ℕ → ℝ)
    (w : κ → ℝ → ℕ → ℝ)
    (hI : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ((Ix x).card : ℝ) ≤ Real.log x ^ e)
    (hw : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ∀ k : κ, ∀ m ∈ rightInterval ε x,
      w k x m = ∑ i ∈ Ix x, u k i x m)
    (hu : ∃ E : κ → ι → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : κ, ∀ i ∈ Ix x, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E k i A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E k i A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) :
    ∃ E : κ → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : κ, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E k A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E k A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (w k x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨CI, hI⟩ := hI
  obtain ⟨C0, hw⟩ := hw
  obtain ⟨E, hE⟩ := hu
  refine ⟨fun k A x q => (Ix x).biUnion (fun i => E k i (A + e) x q), fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE (A + e) (by positivity) (A' + 2 * e) (by positivity)
  refine ⟨max (max C |C|) (max (max CI C0) (Real.exp 1)), fun x hx k q hq1 hq2 => ?_⟩
  have hxC : C ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hCa : |C| ≤ max (max C |C|) (max (max CI C0) (Real.exp 1)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hxI : CI ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx0 : C0 ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hxe : Real.exp 1 ≤ x :=
    le_trans (le_trans (le_max_right (max CI C0) _) (le_max_right (max C |C|) _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hxpos]; exact hxe
  have hL0 : 0 < Real.log x := by linarith
  have hK : ((Ix x).card : ℝ) ≤ Real.log x ^ e := hI x hxI
  have hP : 0 < Real.log x ^ (2 * e) := pow_pos hL0 _
  have hK2 : ((Ix x).card : ℝ) ≤ Real.log x ^ (2 * e) :=
    hK.trans (pow_le_pow_right₀ hL1 (by omega))
  have hKK : ((Ix x).card : ℝ) * (Ix x).card ≤ Real.log x ^ (2 * e) := by
    rw [two_mul, pow_add]
    exact mul_le_mul hK hK (Nat.cast_nonneg _) (pow_nonneg hL0.le _)
  have hr1 : Real.log x ^ (-2 * (A + (e : ℝ))) =
      Real.log x ^ (-2 * A) * (Real.log x ^ (2 * e))⁻¹ := by
    rw [show -2 * (A + (e : ℝ)) = -2 * A + -((2 * e : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hL0, Real.rpow_neg hL0.le, Real.rpow_natCast]
  have hr2 : Real.log x ^ (-(A' + 2 * (e : ℝ))) =
      Real.log x ^ (-A') * (Real.log x ^ (2 * e))⁻¹ := by
    rw [show -(A' + 2 * (e : ℝ)) = -A' + -((2 * e : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hL0, Real.rpow_neg hL0.le ((2 * e : ℕ) : ℝ), Real.rpow_natCast]
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  have hQ : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hq2
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hk : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) :=
    div_pos hY (mul_pos (by linarith) (by linarith))
  have hKq : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hL0.le _)
  have hX : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
      Real.log x ^ (-A') :=
    mul_nonneg (div_nonneg hY.le (sq_nonneg _)) (Real.rpow_nonneg hL0.le _)
  have hfrac : ((Ix x).card : ℝ) * (Real.log x ^ (2 * e))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hP]; exact hK2
  have hfrac2 : ((Ix x).card : ℝ) * (Ix x).card * (Real.log x ^ (2 * e))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hP]; exact hKK
  constructor
  · calc (((Ix x).biUnion fun i => E k i (A + e) x q).card : ℝ)
          ≤ ∑ i ∈ Ix x, ((E k i (A + e) x q).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Ix x, C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * (A + (e : ℝ))) :=
          Finset.sum_le_sum (fun i hi => (hC x hxC k i hi q hq1 hq2).1)
      _ = ((Ix x).card : ℝ) * (Real.log x ^ (2 * e))⁻¹ *
            (C * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hr1]; ring
      _ ≤ ((Ix x).card : ℝ) * (Real.log x ^ (2 * e))⁻¹ *
            (|C| * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hKq)
            (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hP.le))
      _ ≤ 1 * (|C| * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))) :=
          mul_le_mul_of_nonneg_right hfrac (mul_nonneg (abs_nonneg _) hKq)
      _ ≤ _ := by
          rw [one_mul, mul_assoc (max (max C |C|) (max (max CI C0) (Real.exp 1)))]
          exact mul_le_mul_of_nonneg_right hCa hKq
  · have hpt : ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (w k x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        ((Ix x).card : ℝ) * ∑ i ∈ Ix x, ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro χ
      have e1 : (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ((Ix x).card : ℝ) * ∑ i ∈ Ix x,
            ‖∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) =
          ((Ix x).card : ℝ) * ∑ i ∈ Ix x, ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
          (fun i _ => (l34s_cont ε x q χ (u k i x) hk).intervalIntegrable _ _)]
      rw [← e1]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((l34s_cont ε x q χ (w k x) hk).intervalIntegrable _ _)
        (((continuous_finsetSum _ (fun i _ => l34s_cont ε x q χ (u k i x) hk)).const_mul
          _).intervalIntegrable _ _) (fun t _ => ?_)
      have hd : 0 < (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg t)
      have hsum : ∑ m ∈ rightInterval ε x, (w k x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
          ∑ i ∈ Ix x, ∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [hw x hx0 k m hm]; push_cast; rw [Finset.sum_mul, Finset.sum_div]
      rw [hsum]
      exact l34L_pt _ _ hd
    have hsub : ∀ i ∈ Ix x,
        ((Finset.univ : Finset (DirichletCharacter ℂ q)) \
          (Ix x).biUnion (fun i => E k i (A + e) x q)).filter (· ≠ 1) ⊆
        ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E k i (A + e) x q).filter (· ≠ 1) := by
      intro i hi χ hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ,
        true_and, not_exists, not_and] at hχ ⊢
      exact ⟨fun h => hχ.1 i hi h, hχ.2⟩
    have hnn : ∀ i (χ : DirichletCharacter ℂ q),
        0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (u k i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro i χ
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine (Finset.sum_le_sum (fun χ _ => hpt χ)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (Finset.sum_le_sum_of_subset_of_nonneg (hsub i hi) (fun χ _ _ => hnn i χ)).trans
        (hC x hxC k i hi q hq1 hq2).2)) (Nat.cast_nonneg _)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, hr2]
    have h1 : ((Ix x).card : ℝ) * ((Ix x).card *
        (C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          (Real.log x ^ (-A') * (Real.log x ^ (2 * e))⁻¹))) =
        ((Ix x).card * (Ix x).card * (Real.log x ^ (2 * e))⁻¹) *
          (C * ((x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A'))) := by ring
    rw [h1]
    have h5 : 0 ≤ ((Ix x).card : ℝ) * (Ix x).card * (Real.log x ^ (2 * e))⁻¹ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (inv_nonneg.2 hP.le)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hX) h5).trans
      ((mul_le_mul_of_nonneg_right hfrac2 (mul_nonneg (abs_nonneg _) hX)).trans ?_)
    rw [one_mul, mul_assoc (max (max C |C|) (max (max CI C0) (Real.exp 1)))]
    exact mul_le_mul_of_nonneg_right hCa hX

/-- P0069 page 25: psi(l, w), all prime factors of l at least w, is the lab's sifted weight
with sifting limit the ceiling of w, for l >= 1. PROVED. -/
theorem l30s_upperRough_sifted (l : ℕ) (hl : 1 ≤ l) (w : ℝ) :
    upperRough l w = siftedWeight l ⌈w⌉₊ := by
  unfold upperRough siftedWeight
  rcases Nat.eq_or_lt_of_le hl with h1 | h2
  · subst h1; simp
  · have hne : l ≠ 1 := by omega
    have hmf : l.minFac.Prime := Nat.minFac_prime hne
    have key : (∀ p ∈ l.primeFactors, w ≤ (p : ℝ)) ↔ ⌈w⌉₊ ≤ l.minFac := by
      rw [Nat.ceil_le]
      constructor
      · intro h
        exact h _ (Nat.mem_primeFactors.2 ⟨hmf, Nat.minFac_dvd l, by omega⟩)
      · intro h p hp
        have hp' := Nat.mem_primeFactors.1 hp
        exact h.trans (by exact_mod_cast Nat.minFac_le_of_dvd hp'.1.two_le hp'.2.1)
    simp only [key, hne, false_or]

/-- P0069 page 44, the bound |t_gamma(l)| <= the number of d | l, d | P(w), gamma <= d < w gamma,
for t_gamma(l) = psi(l, w) minus the Moebius sum truncated at gamma, from Lemma 15 of
Heath-Brown as proved in the lab, `Decomp312a.fundamental_sifted_truncation`. The input to the
G2 LEAF. PROVED. -/
theorem l30s_tgamma_band (l : ℕ) (hl : 1 ≤ l) (w γ : ℝ) (hγ : 1 ≤ γ) :
    |upperRough l w - ∑ d ∈ (Thm2.primorialBelow w).divisors.filter
        (fun d : ℕ => d ∣ l ∧ (d : ℝ) ≤ γ), (ArithmeticFunction.moebius d : ℝ)| ≤
      (((Thm2.primorialBelow w).divisors.filter
        (fun d : ℕ => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) := by
  rw [l30s_upperRough_sifted l hl w]
  exact Decomp312a.fundamental_sifted_truncation l w γ hγ

/-- LEAF: P0069 page 45, proof of Lemma 30, "In the case j = 0 ... from (3.3) and Lemma 9 ...
we obtain (5.1) with G1 in place of G", for one dyadic block n ~ 2^j with N as in 5.5, the
contribution G1 of the n, d, r with ndr = m, d | P(w), d <= gamma = x^(eps/2), coefficient
a_n mu(d), w = exp(log^(9/10) x) from page 25; 5.1 on page 43 with the page 19 set E and its
size from page 3. The paper splits d ~ D, r ~ R = Y/(ND), |t| in [T-1, 2T], display 5.6.
Uniform in j. CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem l30s_G1_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℕ → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ j : ℕ, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E j A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E j A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ (m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
                    (fun n : ℕ => Nat.log 2 n = j),
                  a x n * (∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter
                      (fun d : ℕ => d ∣ m / n ∧ (d : ℝ) ≤ x ^ (ε / 2)),
                    (ArithmeticFunction.moebius d : ℝ)) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 45, proof of Lemma 30, "As for G2, the analogous bounds are a
straightforward consequence of (3.3) and the estimate for the sum of the moduli of the
coefficients of G2 implicit in (4.13)", for one dyadic block n ~ 2^j, the contribution G2 of
nl = m with coefficient a_n t_gamma(l), t_gamma(l) = psi(l, w) minus the Moebius sum over
d | l, d | P(w), d <= gamma = x^(eps/2), page 44; 5.1 on page 43 with the page 19 set E and
its size from page 3. Uniform in j. CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem l30s_G2_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℕ → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ j : ℕ, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E j A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E j A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ (m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
                    (fun n : ℕ => Nat.log 2 n = j),
                  a x n * (upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) -
                  ∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter
                      (fun d : ℕ => d ∣ m / n ∧ (d : ℝ) ≤ x ^ (ε / 2)),
                    (ArithmeticFunction.moebius d : ℝ)) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 page 44, Lemma 30 for one dyadic block: the exact statement of the leaf
`l34L_f_block` of Prep1122Lemma34Leaves51. PROVED from the LEAFs `l30s_G1_block` and
`l30s_G2_block` by G = G1 + G2 and `l30s_sumU`. CONDITIONAL on the cited Theorem 4 and
Lemma 9. -/
theorem l30s_f_block : type_of% @l34L_f_block := by
  intro h4 h9 ε hε hε8 a B ha
  obtain ⟨E1, hE1⟩ := l30s_G1_block h4 h9 hε hε8 a ha
  obtain ⟨E2, hE2⟩ := l30s_G2_block h4 h9 hε hε8 a ha
  let g1 : ℕ → ℝ → ℕ → ℝ := fun j x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
          (fun n : ℕ => Nat.log 2 n = j),
      a x n * (∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter
          (fun d : ℕ => d ∣ m / n ∧ (d : ℝ) ≤ x ^ (ε / 2)), (ArithmeticFunction.moebius d : ℝ))
  let g2 : ℕ → ℝ → ℕ → ℝ := fun j x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
          (fun n : ℕ => Nat.log 2 n = j),
      a x n * (upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) - ∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter
          (fun d : ℕ => d ∣ m / n ∧ (d : ℝ) ≤ x ^ (ε / 2)), (ArithmeticFunction.moebius d : ℝ))
  refine l30s_sumU (ε := ε) (κ := ℕ) (ι := Fin 2) 1 (fun _ => Finset.univ)
    (fun j i x m => if i = 0 then g1 j x m else g2 j x m)
    (fun j x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
          (fun n : ℕ => Nat.log 2 n = j),
      a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    ⟨Real.exp 2, fun x hx => ?_⟩ ⟨0, fun x _ j m _ => ?_⟩
    ⟨fun j i A x q => if i = 0 then E1 j A x q else E2 j A x q, fun A hA A' hA' => ?_⟩
  · have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
    have : 2 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
    simp only [Finset.card_univ, Fintype.card_fin, pow_one]; push_cast; exact this
  · rw [Fin.sum_univ_two]
    simp only [Fin.isValue, show ((1 : Fin 2) = 0) = False by decide, ↓reduceIte, g1, g2]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  · obtain ⟨C1, hC1⟩ := hE1 A hA A' hA'
    obtain ⟨C2, hC2⟩ := hE2 A hA A' hA'
    refine ⟨max (max |C1| |C2|) (Real.exp 1), fun x hx j i _ q hq1 hq2 => ?_⟩
    have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hL0 : 0 < Real.log x := by
      have : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
      linarith
    have hm1 : |C1| ≤ max (max |C1| |C2|) (Real.exp 1) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hm2 : |C2| ≤ max (max |C1| |C2|) (Real.exp 1) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
    have hK1 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hL0.le _)
    have hK2 : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
        Real.log x ^ (-A') :=
      mul_nonneg (div_nonneg hY.le (sq_nonneg _)) (Real.rpow_nonneg hL0.le _)
    fin_cases i
    · have h := hC1 x ((le_abs_self C1).trans (hm1.trans hx)) j q hq1 hq2
      simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      refine ⟨h.1.trans ?_, h.2.trans ?_⟩
      · rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_abs_self C1).trans hm1) hK1
      · rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_abs_self C1).trans hm1) hK2
    · have h := hC2 x ((le_abs_self C2).trans (hm2.trans hx)) j q hq1 hq2
      simp only [Fin.mk_one, Fin.isValue, show ((1 : Fin 2) = 0) = False by decide, ↓reduceIte]
      refine ⟨h.1.trans ?_, h.2.trans ?_⟩
      · rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_abs_self C2).trans hm2) hK1
      · rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_abs_self C2).trans hm2) hK2


end LeanLab.BHP1997.DecompC165d

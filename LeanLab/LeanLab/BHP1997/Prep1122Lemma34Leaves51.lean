/-
P0069 Baker Harman Pintz 1997, Lemma 34 on pages 49 and 50, conclusion 5.1 on page 43.
Burst burst-20261122, session S49, wave 3. Split of the three HARD leaves `l34s_f_lemma30`,
`l34s_g_big_lemma33` and `l34s_g_small_iterate` of Prep1122Lemma34Split51 on the branch
claude/BHP1997-upD_lemma34_51. The results `l34L_f_lemma30`, `l34L_g_big_lemma33` and
`l34L_g_small_iterate` below have the exact statements of those leaves and no sorry of their own.

The paper works one dyadic block at a time: Lemma 30 on page 44 is stated for n ~ N, and on
page 49 "Let h_m be the contribution to g_m from n ~ N, p1 ~ P". Each leaf is reduced here to
its dyadic blocks, n ~ 2^j and p1 ~ 2^i read as Nat.log 2 n = j and Nat.log 2 p1 = i.

PROVED here: `l34L_sum`, 5.1 with E and its size passes to a sum of at most log^e x pieces
with E the union, by Cauchy's inequality; `l34L_card`, there are at most log^2 x dyadic blocks
below 2Y; `l34L_mem`; `l34L_g_decomp`, the double dyadic split of g_m; the three leaf statements.
LEAF: one HARD leaf per unit, the paper's statement for one dyadic block, uniform in the block.
QUESTION: the paper's proofs of these blocks use Lemma 2, display 3.3 and Lemma 5 besides
Theorem 4 and Lemma 9; the leaves take only Theorem 4 and Lemma 9 as hypotheses.
New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122Lemma34Split51

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- Cauchy's inequality for the integrand of 5.1, a sum of finitely many Dirichlet polynomials.
PROVED. -/
theorem l34L_pt {ι : Type*} (s : Finset ι) (z : ι → ℂ) {d : ℝ} (hd : 0 < d) :
    ‖∑ i ∈ s, z i‖ ^ 2 / d ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 / d := by
  rw [← Finset.sum_div, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hd.le
  calc ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- A divisor or prime factor of `m` in J has its dyadic index below `log2 2Y + 1`. PROVED. -/
theorem l34L_mem {ε x : ℝ} {m k : ℕ} (hm : m ∈ rightInterval ε x) (hk : k ≤ m) :
    Nat.log 2 k ∈ Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1) := by
  unfold rightInterval at hm
  exact Finset.mem_range.2 (Nat.lt_succ_of_le
    (Nat.log_mono_right (hk.trans (Finset.mem_Ioc.1 hm).2)))

/-- P0069 page 49: there are `O(log x)` dyadic blocks below `2Y`, here at most `log^2 x` of
them for large x. PROVED. -/
theorem l34L_card {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 9 / 20) : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x →
    (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 ≤ Real.log x ^ 2 := by
  refine ⟨Real.exp 4, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 4 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hx1 : 1 ≤ x := le_trans (by have := Real.add_one_le_exp 4; linarith) hx
  have hY : x ^ (11 / 20 + ε) ≤ x := by
    calc x ^ (11 / 20 + ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog : (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * (Real.log 2 + Real.log x) := by
    rcases Nat.eq_zero_or_pos ⌊2 * x ^ (11 / 20 + ε)⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right]; push_cast; linarith
    · have h1 := Nat.pow_log_le_self 2 hpos.ne'
      have h2 : ((2 : ℝ) ^ (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊)) ≤
          ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x :=
        (Nat.floor_le (by linarith)).trans (by linarith)
      have h4 : (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) * Real.log 2 ≤
          Real.log 2 + Real.log x := by
        rw [← Real.log_pow, ← Real.log_mul (by norm_num) hx0.ne']
        exact Real.log_le_log (by positivity) (h2.trans h3)
      nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊)]
  nlinarith

/-- P0069 page 43: if 5.1 with E and its size holds for each of at most `log^e x` pieces,
uniformly in the piece, and `w` is their sum on J for large x, then 5.1 holds for `w`, with E
the union of the pieces' sets taken at `A + e`. This is how the paper sums its dyadic
contributions on pages 44 and 49. PROVED. -/
theorem l34L_sum {ε : ℝ} {ι : Type*} (e : ℕ) (Ix : ℝ → Finset ι) (u : ι → ℝ → ℕ → ℝ)
    (w : ℝ → ℕ → ℝ)
    (hI : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ((Ix x).card : ℝ) ≤ Real.log x ^ e)
    (hw : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ∀ m ∈ rightInterval ε x,
      w x m = ∑ i ∈ Ix x, u i x m)
    (hu : ∃ E : ι → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ i ∈ Ix x, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E i A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E i A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (w x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨CI, hI⟩ := hI
  obtain ⟨C0, hw⟩ := hw
  obtain ⟨E, hE⟩ := hu
  refine ⟨fun A x q => (Ix x).biUnion (fun i => E i (A + e) x q), fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE (A + e) (by positivity) (A' + 2 * e) (by positivity)
  refine ⟨max (max C |C|) (max (max CI C0) (Real.exp 1)), fun x hx q hq1 hq2 => ?_⟩
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
  · calc (((Ix x).biUnion fun i => E i (A + e) x q).card : ℝ)
          ≤ ∑ i ∈ Ix x, ((E i (A + e) x q).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Ix x, C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * (A + (e : ℝ))) :=
          Finset.sum_le_sum (fun i hi => (hC x hxC i hi q hq1 hq2).1)
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
          ‖∑ m ∈ rightInterval ε x, (w x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        ((Ix x).card : ℝ) * ∑ i ∈ Ix x, ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro χ
      have e1 : (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ((Ix x).card : ℝ) * ∑ i ∈ Ix x,
            ‖∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) =
          ((Ix x).card : ℝ) * ∑ i ∈ Ix x, ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
          (fun i _ => (l34s_cont ε x q χ (u i x) hk).intervalIntegrable _ _)]
      rw [← e1]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((l34s_cont ε x q χ (w x) hk).intervalIntegrable _ _)
        (((continuous_finsetSum _ (fun i _ => l34s_cont ε x q χ (u i x) hk)).const_mul
          _).intervalIntegrable _ _) (fun t _ => ?_)
      have hd : 0 < (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg t)
      have hsum : ∑ m ∈ rightInterval ε x, (w x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
          ∑ i ∈ Ix x, ∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [hw x hx0 m hm]; push_cast; rw [Finset.sum_mul, Finset.sum_div]
      rw [hsum]
      exact l34L_pt _ _ hd
    have hsub : ∀ i ∈ Ix x,
        ((Finset.univ : Finset (DirichletCharacter ℂ q)) \
          (Ix x).biUnion (fun i => E i (A + e) x q)).filter (· ≠ 1) ⊆
        ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E i (A + e) x q).filter (· ≠ 1) := by
      intro i hi χ hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ,
        true_and, not_exists, not_and] at hχ ⊢
      exact ⟨fun h => hχ.1 i hi h, hχ.2⟩
    have hnn : ∀ i (χ : DirichletCharacter ℂ q),
        0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (u i x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro i χ
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine (Finset.sum_le_sum (fun χ _ => hpt χ)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
      (Finset.sum_le_sum_of_subset_of_nonneg (hsub i hi) (fun χ _ _ => hnn i χ)).trans
        (hC x hxC i hi q hq1 hq2).2)) (Nat.cast_nonneg _)).trans ?_
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

/-- P0069 page 49: the double dyadic split of g_m, by n ~ 2^j and p1 ~ 2^i, the h_m of page 49.
PROVED. -/
theorem l34L_g_decomp {ε x : ℝ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (a : ℕ → ℝ) (g : ℕ → ℕ → ℝ) {m : ℕ} (hm : m ∈ rightInterval ε x) :
    ∑ n ∈ m.divisors.filter P, a n * ∑ p ∈ (m / n).primeFactors.filter Q, g n p =
      ∑ ji ∈ Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1) ×ˢ
          Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1),
        ∑ n ∈ (m.divisors.filter P).filter (fun n : ℕ => Nat.log 2 n = ji.1),
          a n * ∑ p ∈ ((m / n).primeFactors.filter Q).filter (fun p : ℕ => Nat.log 2 p = ji.2),
            g n p := by
  symm
  rw [Finset.sum_product]
  calc _ = ∑ j ∈ Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1),
        ∑ n ∈ (m.divisors.filter P).filter (fun n : ℕ => Nat.log 2 n = j),
          a n * ∑ p ∈ (m / n).primeFactors.filter Q, g n p := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        dsimp only
        symm
        calc _ = ∑ n ∈ (m.divisors.filter P).filter (fun n : ℕ => Nat.log 2 n = j),
              ∑ y ∈ Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1),
                a n * ∑ p ∈ ((m / n).primeFactors.filter Q).filter
                  (fun p : ℕ => Nat.log 2 p = y), g n p := by
              refine Finset.sum_congr rfl (fun n hn => ?_)
              rw [← Finset.mul_sum]
              congr 1
              refine (Finset.sum_fiberwise_of_maps_to (fun p hp => l34L_mem hm ?_) _).symm
              exact (Nat.le_of_mem_primeFactors (Finset.mem_filter.1 hp).1).trans
                (Nat.div_le_self m n)
          _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun n hn => l34L_mem hm (Nat.divisor_le (Finset.mem_filter.1 hn).1)) _

/-- LEAF: P0069 page 44, Lemma 30 for one dyadic block n ~ N, N = 2^j, as used on page 49,
"Here f_m satisfies (5.1) and (5.2) by Lemma 30", the part for 5.1 on page 43 with the page 19
set E and its size from page 3. The coefficients are b_m = sum over nl = m, n ~ N,
n <= Y^(1/2 + theta2/4 - 2 eps), of a_n psi(l, w), w = exp(log^(9/10) x) from page 25, so N
satisfies 5.5. Uniform in j, as the Remark on page 3 makes implied constants depend on A only.
The proof on pages 44 and 45 uses Lemma 9, display 3.3 and the estimate 4.13. CONDITIONAL on
the cited Theorem 4 and Lemma 9. HARD. -/
theorem l34L_f_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
                  a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, h_m, "the contribution to g_m from n ~ N,
p1 ~ P", with N = 2^j, P = 2^i and Y^eps <= p1 < Y^c1: "we know from Lemma 5 that (3.2) holds,
and of course if P >= Y^eps we may obtain (5.1) and (5.2) from Lemma 33", case 5.13 on page 48,
for 5.1 on page 43 with the page 19 set E and its size from page 3. Uniform in i and j. Lemma 33
in case 5.13 rests on Lemma 32, which uses Lemma 2. CONDITIONAL on the cited Theorem 4 and
Lemma 9. HARD. -/
theorem l34L_g_big_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℕ × ℕ → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ji : ℕ × ℕ, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E ji A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E ji A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ (m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
                    (fun n : ℕ => Nat.log 2 n = ji.1),
                  a x n * ∑ p ∈ ((m / n).primeFactors.filter (fun p : ℕ =>
                      (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε)).filter
                      (fun p : ℕ => Nat.log 2 p = ji.2),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, h_m, the contribution to g_m from n ~ N, p1 ~ P,
with N = 2^j, P = 2^i and w <= p1 < Y^eps: "For w <= P <= Y^eps, we iterate the decomposition
in the same fashion as case (ii) of Lemma 13 ... The process terminates after O(L^(1/10))
steps", for 5.1 on page 43 with the page 19 set E and its size from page 3, w =
exp(log^(9/10) x) from page 25. Uniform in i and j. Case ii of Lemma 13 is on page 26; the
finished terms are handled by Lemma 30 and by Lemma 33 with Lemma 5. CONDITIONAL on the cited
Theorem 4 and Lemma 9. HARD. -/
theorem l34L_g_small_block (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℕ × ℕ → ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ji : ℕ × ℕ, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E ji A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E ji A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ (m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
                    (fun n : ℕ => Nat.log 2 n = ji.1),
                  a x n * ∑ p ∈ ((m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε)).filter
                      (fun p : ℕ => Nat.log 2 p = ji.2),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- P0069 page 49, the exact statement of the leaf `l34s_f_lemma30` of Prep1122Lemma34Split51:
f_m satisfies 5.1 by Lemma 30. PROVED from the LEAF `l34L_f_block` by the dyadic split of n and
`l34L_sum`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem l34L_f_lemma30 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  have hε1 : ε ≤ 9 / 20 := by norm_num at hε8 ⊢; linarith
  obtain ⟨C0, hC0⟩ := l34L_card hε hε1
  obtain ⟨E, hE⟩ := l34L_f_block h4 h9 hε hε8 a ha
  refine l34L_sum (ε := ε) 2 (fun x => Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1))
    (fun j x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
        (fun n : ℕ => Nat.log 2 n = j),
      a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    ⟨C0, fun x hx => by rw [Finset.card_range]; push_cast; exact hC0 x hx⟩
    ⟨0, fun x _ m hm => (Finset.sum_fiberwise_of_maps_to
      (fun n hn => l34L_mem hm (Nat.divisor_le (Finset.mem_filter.1 hn).1)) _).symm⟩
    ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  exact ⟨C, fun x hx j _ q hq1 hq2 => hC x hx j q hq1 hq2⟩

/-- `(K : ℝ)^2 ≤ log^4 x` from `K ≤ log^2 x`, for the double dyadic split. PROVED. -/
theorem l34L_card2 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 9 / 20) : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x →
    (((Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1) ×ˢ
      Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1)).card : ℕ) : ℝ) ≤
      Real.log x ^ 4 := by
  obtain ⟨C0, hC0⟩ := l34L_card hε hε1
  refine ⟨C0, fun x hx => ?_⟩
  rw [Finset.card_product, Finset.card_range]
  push_cast
  have h := hC0 x hx
  have h0 : (0 : ℝ) ≤ (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 := by positivity
  calc ((Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1) *
        ((Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1) ≤ Real.log x ^ 2 * Real.log x ^ 2 :=
        mul_le_mul h h h0 (h0.trans h)
    _ = Real.log x ^ 4 := by ring

/-- P0069 pages 49 and 50, the exact statement of the leaf `l34s_g_big_lemma33` of
Prep1122Lemma34Split51. PROVED from the LEAF `l34L_g_big_block` by the double dyadic split
`l34L_g_decomp` and `l34L_sum`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem l34L_g_big_lemma33 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  have hε1 : ε ≤ 9 / 20 := by norm_num at hε8 ⊢; linarith
  obtain ⟨E, hE⟩ := l34L_g_big_block h4 h9 hε hε8 a ha
  refine l34L_sum (ε := ε) 4 (fun x => Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1) ×ˢ
      Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1))
    (fun ji x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
        (fun n : ℕ => Nat.log 2 n = ji.1),
      a x n * ∑ p ∈ ((m / n).primeFactors.filter (fun p : ℕ =>
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε)).filter
          (fun p : ℕ => Nat.log 2 p = ji.2),
        upperRough (m / n / p : ℕ) (p : ℝ))
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε),
        upperRough (m / n / p : ℕ) (p : ℝ))
    (l34L_card2 hε hε1)
    ⟨0, fun x _ m hm => l34L_g_decomp _ _ (a x) (fun n p => upperRough (m / n / p : ℕ) (p : ℝ)) hm⟩
    ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  exact ⟨C, fun x hx ji _ q hq1 hq2 => hC x hx ji q hq1 hq2⟩

/-- P0069 page 50, the exact statement of the leaf `l34s_g_small_iterate` of
Prep1122Lemma34Split51. PROVED from the LEAF `l34L_g_small_block` by the double dyadic split
`l34L_g_decomp` and `l34L_sum`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem l34L_g_small_iterate (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x,
                ((∑ n ∈ m.divisors.filter (fun n : ℕ =>
                    (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
                  a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
                      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
                    upperRough (m / n / p : ℕ) (p : ℝ) : ℝ) : ℂ) *
                χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  have hε1 : ε ≤ 9 / 20 := by norm_num at hε8 ⊢; linarith
  obtain ⟨E, hE⟩ := l34L_g_small_block h4 h9 hε hε8 a ha
  refine l34L_sum (ε := ε) 4 (fun x => Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1) ×ˢ
      Finset.range (Nat.log 2 ⌊2 * x ^ (11 / 20 + ε)⌋₊ + 1))
    (fun ji x m => ∑ n ∈ (m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).filter
        (fun n : ℕ => Nat.log 2 n = ji.1),
      a x n * ∑ p ∈ ((m / n).primeFactors.filter (fun p : ℕ =>
          Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε)).filter
          (fun p : ℕ => Nat.log 2 p = ji.2),
        upperRough (m / n / p : ℕ) (p : ℝ))
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
        upperRough (m / n / p : ℕ) (p : ℝ))
    (l34L_card2 hε hε1)
    ⟨0, fun x _ m hm => l34L_g_decomp _ _ (a x) (fun n p => upperRough (m / n / p : ℕ) (p : ℝ)) hm⟩
    ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  exact ⟨C, fun x hx ji _ q hq1 hq2 => hC x hx ji q hq1 hq2⟩

end LeanLab.BHP1997.DecompC165d

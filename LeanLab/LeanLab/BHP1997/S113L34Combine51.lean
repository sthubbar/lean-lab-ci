/-
P0069 Baker Harman Pintz 1997, pages 43 to 50, the dyadic bookkeeping behind the uses of 5.1 in
the proof of Lemma 34. Burst burst-20261122, session S113, step l34s51-s113, on the leaves of
`l34s_lemma34_51` in `Prep1122Lemma34Split51`.

PROVED here, no sorry: `s113_combine_blocks`, the rule that 5.1 of page 43 with the page 19
set E and its size passes from at most log x pieces to their sum, with E the union of the
pieces' sets. This is the 5.1 twin of `upD52_combine_blocks` of session S50. The count of
pieces costs L in the size of E and L^2 in the integral, absorbed since A and A' are arbitrary.
Pointwise it is Cauchy's inequality `upD52_sq_sum_le`.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122Lemma34Split51
import LeanLab.BHP1997.Prep1122UpD52Combine

namespace LeanLab.BHP1997.S113L34Combine51
open Classical Complex Decomp132 DecompC165b LeanLab.BHP1997.DecompC165d

/-- One character of 5.1 for a sum of J pieces: if c is the sum of d_0, ..., d_(J-1) on the
interval J of page 43, the integral of c over -Y <= t <= Y is at most J times the sum of the
integrals of the pieces. PROVED. -/
theorem s113_int_blocks (ε x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ) (J : ℕ)
    (d : ℕ → ℕ → ℝ) (hb : ∀ m ∈ rightInterval ε x, c m = ∑ j ∈ Finset.range J, d j m)
    {k : ℝ} (hk : 0 < k) {Y : ℝ} (hY : 0 ≤ Y) :
    (∫ t in (-Y)..Y, ‖∑ m ∈ rightInterval ε x, (c m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, (∫ t in (-Y)..Y,
        ‖∑ m ∈ rightInterval ε x, (d j m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)) := by
  have Id : ∀ j ∈ Finset.range J, IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ rightInterval ε x, (d j m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)) MeasureTheory.volume
        (-Y) Y :=
    fun j _ => (l34s_cont ε x q χ (d j) hk).intervalIntegrable _ _
  have Isum : IntervalIntegrable (fun t : ℝ => ∑ j ∈ Finset.range J,
      ‖∑ m ∈ rightInterval ε x, (d j m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)) MeasureTheory.volume
        (-Y) Y := by
    have := IntervalIntegrable.sum (Finset.range J) Id
    convert this using 1
    funext t
    simp [Finset.sum_apply]
  rw [← intervalIntegral.integral_finsetSum Id, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by linarith)
    ((l34s_cont ε x q χ c hk).intervalIntegrable _ _) (Isum.const_mul _) (fun t _ => ?_)
  have hsum : (∑ m ∈ rightInterval ε x, (c m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑ j ∈ Finset.range J, ∑ m ∈ rightInterval ε x, (d j m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hb m hm]
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hsum]
  have hd : 0 ≤ k ^ 2 + t ^ 2 := by positivity
  have hcs := upD52_sq_sum_le (Finset.range J) (fun j => ∑ m ∈ rightInterval ε x,
    (d j m : ℂ) * χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))
  rw [Finset.card_range] at hcs
  calc ‖∑ j ∈ Finset.range J, ∑ m ∈ rightInterval ε x, (d j m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)
      ≤ ((J : ℝ) * ∑ j ∈ Finset.range J, ‖∑ m ∈ rightInterval ε x, (d j m : ℂ) *
          χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) / (k ^ 2 + t ^ 2) := by
        gcongr
    _ = (J : ℝ) * ∑ j ∈ Finset.range J, ‖∑ m ∈ rightInterval ε x, (d j m : ℂ) *
          χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2) := by
        rw [mul_div_assoc, Finset.sum_div]

/-- P0069 page 49 and the proof of Lemma 30 on page 44: 5.1 of page 43 with the page 19 set E
and its size passes from dyadic pieces to their sum. If on J, for all large x, c is the sum of
the J(x) pieces d_0, ..., d_(J(x)-1) with J(x) at most log x, and the pieces satisfy 5.1 with
sets E_j and one constant, then c satisfies 5.1 with E the union of the E_j. PROVED. -/
theorem s113_combine_blocks {ε : ℝ} (c : ℝ → ℕ → ℝ) (d : ℝ → ℕ → ℕ → ℝ) (J : ℝ → ℕ)
    (hsplit : ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → (J x : ℝ) ≤ Real.log x ∧
      ∀ k ∈ rightInterval ε x, c x k = ∑ j ∈ Finset.range (J x), d x j k)
    (hd : ∃ E : ℝ → ℝ → ℕ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ j < J x, ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x j q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x j q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ (m : ZMod q) /
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
            ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨X0, hX0⟩ := hsplit
  obtain ⟨Eb, hEb⟩ := hd
  refine ⟨fun A x q => (Finset.range (J x)).biUnion (fun j => Eb (A + 1) x j q),
    fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hEb (A + 1) (by linarith) (A' + 2) (by linarith)
  refine ⟨max (max X0 (max C 3)) |C|, fun x hx q hq1 hqQ => ?_⟩
  have hX : max X0 (max C 3) ≤ x := le_trans (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_left _ _) hX
  have hCx : C ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hCabs : |C| ≤ max (max X0 (max C 3)) |C| := le_max_right _ _
  set Cbig := max (max X0 (max C 3)) |C| with hCbigdef
  obtain ⟨hJ, hb⟩ := hX0 x hX0x
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < Real.log x := by linarith
  have hJ0 : (0 : ℝ) ≤ J x := Nat.cast_nonneg _
  have hJL2 : (J x : ℝ) ≤ Real.log x ^ 2 := by nlinarith
  have hJsq : (J x : ℝ) * J x ≤ Real.log x ^ 2 := by nlinarith
  have hpow : ∀ B : ℝ, Real.log x ^ 2 * Real.log x ^ (-(B + 2)) = Real.log x ^ (-B) := by
    intro B
    rw [show (Real.log x) ^ 2 = Real.log x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hLpos]
    congr 1; ring
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hQ : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hqQ
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hk : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) :=
    div_pos hY (mul_pos (by linarith) (by linarith))
  set R := x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 with hRdef
  have hR : 0 ≤ R := by positivity
  set K := (q : ℝ) ^ (1 / 2 : ℝ) with hKdef
  have hK : 0 ≤ K := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hblk := fun j (hj : j ∈ Finset.range (J x)) => hC x hCx j (Finset.mem_range.mp hj) q hq1 hqQ
  constructor
  · have h1 : (((Finset.range (J x)).biUnion (fun j => Eb (A + 1) x j q)).card : ℝ) ≤
        ∑ j ∈ Finset.range (J x), ((Eb (A + 1) x j q).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ j ∈ Finset.range (J x), ((Eb (A + 1) x j q).card : ℝ) ≤
        ∑ j ∈ Finset.range (J x), C * K * Real.log x ^ (-2 * (A + 1)) :=
      Finset.sum_le_sum (fun j hj => (hblk j hj).1)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have hLA : 0 ≤ Real.log x ^ (-2 * (A + 1)) := Real.rpow_nonneg hLpos.le _
    have hLA0 : 0 ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hLpos.le _
    have h3 : C * K * Real.log x ^ (-2 * (A + 1)) ≤ |C| * K * Real.log x ^ (-2 * (A + 1)) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hK hLA)
    have h4 : 0 ≤ |C| * K * Real.log x ^ (-2 * (A + 1)) := by positivity
    have hp2 : Real.log x ^ 2 * Real.log x ^ (-2 * (A + 1)) = Real.log x ^ (-2 * A) := by
      rw [show -2 * (A + 1) = -(2 * A + 2) by ring, hpow, show -(2 * A) = -2 * A by ring]
    calc _ ≤ (J x : ℝ) * (C * K * Real.log x ^ (-2 * (A + 1))) := h1.trans h2
      _ ≤ (J x : ℝ) * (|C| * K * Real.log x ^ (-2 * (A + 1))) :=
          mul_le_mul_of_nonneg_left h3 hJ0
      _ ≤ Real.log x ^ 2 * (|C| * K * Real.log x ^ (-2 * (A + 1))) :=
          mul_le_mul_of_nonneg_right hJL2 h4
      _ = |C| * K * (Real.log x ^ 2 * Real.log x ^ (-2 * (A + 1))) := by ring
      _ = |C| * K * Real.log x ^ (-2 * A) := by rw [hp2]
      _ ≤ Cbig * K * Real.log x ^ (-2 * A) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hCabs (mul_nonneg hK hLA0)
  · set F := ((Finset.univ : Finset (DirichletCharacter ℂ q)) \
        (Finset.range (J x)).biUnion (fun j => Eb (A + 1) x j q)).filter (· ≠ 1) with hFdef
    have hnn : ∀ (c' : ℕ → ℝ) (χ : DirichletCharacter ℂ q),
        0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c' m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro c' χ
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hpt := fun χ (_ : χ ∈ F) => s113_int_blocks ε x q χ (c x) (J x) (d x) hb hk hY.le
    have hS1 := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum, Finset.sum_comm] at hS1
    have hsub : ∀ j ∈ Finset.range (J x), F ⊆
        ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ Eb (A + 1) x j q).filter (· ≠ 1) := by
      intro j hj χ hχ
      rw [hFdef] at hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ,
        true_and, not_exists, not_and] at hχ ⊢
      exact ⟨hχ.1 j hj, hχ.2⟩
    have hS2 : ∑ j ∈ Finset.range (J x), ∑ χ ∈ F, (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        ∑ j ∈ Finset.range (J x), C * R * Real.log x ^ (-(A' + 2)) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hsub j hj)
        (fun χ _ _ => hnn (d x j) χ)) ?_
      exact (hblk j hj).2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hS2
    have hLA2 : 0 ≤ Real.log x ^ (-(A' + 2)) := Real.rpow_nonneg hLpos.le _
    have hLA : 0 ≤ Real.log x ^ (-A') := Real.rpow_nonneg hLpos.le _
    have h1 : C * R * Real.log x ^ (-(A' + 2)) ≤ |C| * R * Real.log x ^ (-(A' + 2)) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hR hLA2)
    have h2 : 0 ≤ |C| * R * Real.log x ^ (-(A' + 2)) := by positivity
    calc _ ≤ (J x : ℝ) * ∑ j ∈ Finset.range (J x), ∑ χ ∈ F,
            (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := hS1
      _ ≤ (J x : ℝ) * ((J x : ℝ) * (C * R * Real.log x ^ (-(A' + 2)))) :=
          mul_le_mul_of_nonneg_left hS2 hJ0
      _ ≤ (J x : ℝ) * J x * (|C| * R * Real.log x ^ (-(A' + 2))) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.log x ^ 2 * (|C| * R * Real.log x ^ (-(A' + 2))) :=
          mul_le_mul_of_nonneg_right hJsq h2
      _ = |C| * R * (Real.log x ^ 2 * Real.log x ^ (-(A' + 2))) := by ring
      _ = |C| * R * Real.log x ^ (-A') := by rw [hpow]
      _ ≤ Cbig * R * Real.log x ^ (-A') := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hCabs (mul_nonneg hR hLA)

end LeanLab.BHP1997.S113L34Combine51

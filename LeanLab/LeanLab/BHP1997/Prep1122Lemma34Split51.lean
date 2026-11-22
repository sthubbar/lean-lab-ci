/-
P0069 Baker Harman Pintz 1997, Lemma 34 on pages 49 and 50, conclusion 5.1 on page 43.
Burst burst-20261122, unit P1122-0085. Split of the open leaf `upD_lemma34_51` of the branch
claude/BHP1997-upper_normalized_raw_conditions_slack-p2, file Prep1121DUpslackPieces there.
The result `l34s_lemma34_51` below has the exact statement of that leaf and no sorry of its own.

The proof on pages 49 and 50, read from the page images of papers/P0069-original.pdf:
By Buchstab's identity, b_m = f_m - g_m, where f_m is the sum over nl = k, n <= Y^(1/2 + theta2/4 - 2 eps),
of a_n psi(l, w), and g_m the sum over n p1 n1 = k, w <= p1 < Y^c1, of a_n psi(n1, p1), with
w = exp(log^(9/10) x) from page 25. Here f_m satisfies 5.1 and 5.2 by Lemma 30. For p1 ~ P,
Lemma 5 gives 3.2 for the prime polynomial, and if P >= Y^eps Lemma 33 gives 5.1 and 5.2. For
w <= P <= Y^eps the decomposition is iterated as in case ii of Lemma 13, and it ends after
O(L^(1/10)) steps.

PROVED here: the Buchstab step with the p1 range split at Y^eps, b = f - g_big - g_small on J for
large x; that 5.1 with E and its size passes to sums and to negatives, with E the union; the
eventual bound w <= Y^eps. LEAF: one HARD leaf per sentence of the paper's proof, f by Lemma 30,
g_big by Lemma 5 and Lemma 33, g_small by the iteration.
New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312
import LeanLab.BHP1997.Thm4Statement

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 49, Buchstab's identity behind f_m - g_m, with the p1 range of g_m split at z,
here z = Y^eps as on page 50. PROVED from `upper_rough_buchstab_step`. -/
theorem l34s_buchstab (l : ℕ) {w z y : ℝ} (hwz : w ≤ z) (hzy : z ≤ y) :
    upperRough l y = upperRough l w -
      (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        upperRough (l / p : ℕ) (p : ℝ)) -
      (∑ p ∈ l.primeFactors.filter (fun p : ℕ => z ≤ (p : ℝ) ∧ (p : ℝ) < y),
        upperRough (l / p : ℕ) (p : ℝ)) := by
  rw [upper_rough_buchstab_step l (z1 := w) (z2 := y) (hwz.trans hzy)]
  have hs : (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < y),
        upperRough (l / p : ℕ) (p : ℝ)) =
      (∑ p ∈ l.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        upperRough (l / p : ℕ) (p : ℝ)) +
      (∑ p ∈ l.primeFactors.filter (fun p : ℕ => z ≤ (p : ℝ) ∧ (p : ℝ) < y),
        upperRough (l / p : ℕ) (p : ℝ)) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rcases lt_or_ge (p : ℝ) z with h2 | h2
    · have h3 : (p : ℝ) < y := h2.trans_le hzy
      by_cases h1 : w ≤ (p : ℝ) <;> simp [h1, h2, h3, not_le.mpr h2]
    · have h1 : w ≤ (p : ℝ) := hwz.trans h2
      by_cases h3 : (p : ℝ) < y <;> simp [h1, h2, h3, not_lt.mpr h2]
  rw [hs]; ring

/-- P0069 page 25 and page 50: `w = exp(log^(9/10) x)` is eventually at most `x^c` for every
`c > 0`, so `w <= Y^eps` for large x. PROVED. -/
theorem l34s_w_le {c : ℝ} (hc : 0 < c) : ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ x ^ c := by
  refine ⟨Real.exp (max 1 ((1 / c) ^ (10 : ℕ))), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : max 1 ((1 / c) ^ (10 : ℕ)) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hL1 : 1 ≤ Real.log x := le_trans (le_max_left _ _) hL
  have hL0 : 0 < Real.log x := by linarith
  have h10 : 1 / c ≤ Real.log x ^ (1 / 10 : ℝ) := by
    have h1 : ((1 / c) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = 1 / c := by
      rw [show (1 / 10 : ℝ) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hL) (by norm_num)
  have hsplit : Real.log x ^ (9 / 10 : ℝ) * Real.log x ^ (1 / 10 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL0]; norm_num
  have key : Real.log x ^ (9 / 10 : ℝ) ≤ Real.log x * c := by
    have h1 : Real.log x ^ (9 / 10 : ℝ) * (1 / c) ≤
        Real.log x ^ (9 / 10 : ℝ) * Real.log x ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left h10 (Real.rpow_nonneg hL0.le _)
    rw [hsplit] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * (Real.log x ^ (9 / 10 : ℝ) * (1 / c)) = Real.log x ^ (9 / 10 : ℝ) := by
      field_simp
    rw [h3] at h2
    linarith
  rw [Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.mpr key

/-- `Y = x^(11/20 + eps)` is at least 2 once `x >= 4`. PROVED. -/
theorem l34s_two_le {ε x : ℝ} (hε : 0 < ε) (hx : 4 ≤ x) : 2 ≤ x ^ (11 / 20 + ε) := by
  have h1 : x ^ (1 / 2 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : 2 ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [← h4]; exact Real.sqrt_le_sqrt hx
  linarith

/-- The integrand of 5.1 is continuous in t, for any real coefficients on J and `k > 0`. PROVED. -/
theorem l34s_cont (ε x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ) {k : ℝ}
    (hk : 0 < k) :
    Continuous (fun t : ℝ => ‖∑ m ∈ rightInterval ε x, (c m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (k ^ 2 + t ^ 2)) := by
  refine Continuous.div ?_ ((continuous_const.pow 2).add (continuous_id.pow 2))
    (fun t => (add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg t)).ne')
  refine (Continuous.norm ?_).pow 2
  refine continuous_finsetSum _ (fun m hm => ?_)
  have hm0 : (m : ℂ) ≠ 0 := by
    have h := (Finset.mem_Ioc.mp hm).1
    have : 0 < m := lt_of_le_of_lt (Nat.zero_le _) h
    exact_mod_cast this.ne'
  refine continuous_const.div ?_ (fun t h => hm0 ((Complex.cpow_eq_zero_iff _ _).mp h).1)
  exact Continuous.const_cpow
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) (Or.inl hm0)

/-- An interval integral inequality for continuous integrands. PROVED. -/
theorem l34s_int_le {Y : ℝ} (hY : 0 ≤ Y) (Fw Fu Fv : ℝ → ℝ) (hwc : Continuous Fw)
    (huc : Continuous Fu) (hvc : Continuous Fv) (h : ∀ t, Fw t ≤ 2 * Fu t + 2 * Fv t) :
    (∫ t in (-Y)..Y, Fw t) ≤ 2 * (∫ t in (-Y)..Y, Fu t) + 2 * (∫ t in (-Y)..Y, Fv t) := by
  have e1 : (∫ t in (-Y)..Y, (2 * Fu t + 2 * Fv t)) =
      2 * (∫ t in (-Y)..Y, Fu t) + 2 * (∫ t in (-Y)..Y, Fv t) := by
    rw [intervalIntegral.integral_add ((huc.const_mul 2).intervalIntegrable _ _)
      ((hvc.const_mul 2).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [← e1]
  exact intervalIntegral.integral_mono_on (by linarith) (hwc.intervalIntegrable _ _)
    (((huc.const_mul 2).add (hvc.const_mul 2)).intervalIntegrable _ _) (fun t _ => h t)

/-- P0069 page 43: if 5.1 with E and its size holds for u and for v, and `w = u + v` on J for
large x, then it holds for w, with E the union. Used for f_m - g_m on page 49. PROVED. -/
theorem l34s_add {ε : ℝ} (u v w : ℝ → ℕ → ℝ)
    (hw : ∃ C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ∀ m ∈ rightInterval ε x, w x m = u x m + v x m)
    (hu : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A'))
    (hv : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (v x m : ℂ) * χ (m : ZMod q) /
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
  obtain ⟨C0, hw⟩ := hw
  obtain ⟨Eu, hu⟩ := hu
  obtain ⟨Ev, hv⟩ := hv
  refine ⟨fun A x q => Eu A x q ∪ Ev A x q, fun A hA A' hA' => ?_⟩
  obtain ⟨Cu, hCu⟩ := hu A hA A' hA'
  obtain ⟨Cv, hCv⟩ := hv A hA A' hA'
  refine ⟨max (max Cu Cv) (max (max C0 1) (2 * (|Cu| + |Cv|))), fun x hx q hq1 hq2 => ?_⟩
  have hxu : Cu ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxv : Cv ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : C0 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx1 : (1 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hCC : 2 * (|Cu| + |Cv|) ≤ max (max Cu Cv) (max (max C0 1) (2 * (|Cu| + |Cv|))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨hEu, hIu⟩ := hCu x hxu q hq1 hq2
  obtain ⟨hEv, hIv⟩ := hCv x hxv q hq1 hq2
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hQ : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hq2
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hk : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) :=
    div_pos hY (mul_pos (by linarith) (by linarith))
  have hK : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hX : 0 ≤ (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
      Real.log x ^ (-A') :=
    mul_nonneg (div_nonneg hY.le (sq_nonneg _)) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have habs : Cu + Cv ≤ |Cu| + |Cv| := add_le_add (le_abs_self _) (le_abs_self _)
  have habs0 : 0 ≤ |Cu| + |Cv| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  constructor
  · calc ((Eu A x q ∪ Ev A x q).card : ℝ) ≤ (Eu A x q).card + (Ev A x q).card := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ Cu * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) +
          Cv * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := add_le_add hEu hEv
      _ = (Cu + Cv) * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by ring
      _ ≤ max (max Cu Cv) (max (max C0 1) (2 * (|Cu| + |Cv|))) *
          ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :=
        mul_le_mul_of_nonneg_right (by linarith) hK
      _ = _ := by ring
  · have hnn : ∀ (c : ℕ → ℝ) (χ : DirichletCharacter ℂ q),
        0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
      intro c χ
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hpt : ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (w x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        2 * (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (u x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        2 * (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (v x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
      intro χ
      refine l34s_int_le hY.le _ _ _ (l34s_cont ε x q χ (w x) hk) (l34s_cont ε x q χ (u x) hk)
        (l34s_cont ε x q χ (v x) hk) (fun t => ?_)
      have hsum : ∑ m ∈ rightInterval ε x, (w x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
          ∑ m ∈ rightInterval ε x, (u x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) +
          ∑ m ∈ rightInterval ε x, (v x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [hw x hx0 m hm]; push_cast; ring
      have hd : 0 < (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg t)
      rw [hsum, mul_div_assoc', mul_div_assoc', ← add_div]
      refine div_le_div_of_nonneg_right ?_ hd.le
      set a := ∑ m ∈ rightInterval ε x, (u x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
      set b := ∑ m ∈ rightInterval ε x, (v x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
      have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    have hsubu : ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ (Eu A x q ∪ Ev A x q)).filter
        (· ≠ 1) ⊆ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ Eu A x q).filter (· ≠ 1) := by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ,
        true_and] at hχ ⊢
      tauto
    have hsubv : ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ (Eu A x q ∪ Ev A x q)).filter
        (· ≠ 1) ⊆ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ Ev A x q).filter (· ≠ 1) := by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ,
        true_and] at hχ ⊢
      tauto
    have hS1 := Finset.sum_le_sum (fun χ (_ : χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \
      (Eu A x q ∪ Ev A x q)).filter (· ≠ 1)) => hpt χ)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hS1
    have hSu := Finset.sum_le_sum_of_subset_of_nonneg hsubu (fun χ _ _ => hnn (u x) χ)
    have hSv := Finset.sum_le_sum_of_subset_of_nonneg hsubv (fun χ _ _ => hnn (v x) χ)
    refine hS1.trans ?_
    calc _ ≤ 2 * (Cu * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) +
          2 * (Cv * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) := by linarith
      _ = (2 * (Cu + Cv)) * ((x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) := by ring
      _ ≤ max (max Cu Cv) (max (max C0 1) (2 * (|Cu| + |Cv|))) *
          ((x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A')) := mul_le_mul_of_nonneg_right (by linarith) hX
      _ = _ := by ring

/-- P0069 page 43: 5.1 with E and its size passes from u to -u, with the same E. PROVED. -/
theorem l34s_neg {ε : ℝ} (u : ℝ → ℕ → ℝ)
    (hu : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (u x m : ℂ) * χ (m : ZMod q) /
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
            ‖∑ m ∈ rightInterval ε x, ((-u x m : ℝ) : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  obtain ⟨E, hE⟩ := hu
  refine ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  refine ⟨C, fun x hx q hq1 hq2 => ?_⟩
  obtain ⟨h1, h2⟩ := hC x hx q hq1 hq2
  refine ⟨h1, le_of_eq_of_le ?_ h2⟩
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  congr 1
  funext t
  simp only [Complex.ofReal_neg, neg_mul, neg_div, Finset.sum_neg_distrib, norm_neg]

/-- LEAF: P0069 page 49, proof of Lemma 34, "Here f_m satisfies (5.1) and (5.2) by Lemma 30",
the part for 5.1 on page 43 with the page 19 set E and its size from page 3. f_m is the first
term of the Buchstab display on page 49, the sum over nl = m with n <= Y^(1/2 + theta2/4 - 2 eps)
of a_n psi(l, w), with w = exp(log^(9/10) x) from page 25. Lemma 30 on page 44 is applied to each
dyadic range n ~ N, where N << Y^(1/2 + theta2/4 - eps) is 5.5. CONDITIONAL on the cited
Theorem 4 and Lemma 9. HARD. -/
theorem l34s_f_lemma30 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  sorry

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, the part of g_m with P >= Y^eps: "With
N(s, chi) = sum over p1 ~ P of chi(p1) p1^(-s) we know from Lemma 5 that (3.2) holds, and of
course if P >= Y^eps we may obtain (5.1) and (5.2) from Lemma 33", in case 5.13 on page 48, for
5.1 on page 43 with the page 19 set E and its size from page 3. The terms are those of g_m, the
sum over n p1 n1 = m, n <= Y^(1/2 + theta2/4 - 2 eps), of a_n psi(n1, p1), with
Y^eps <= p1 < Y^c1. CONDITIONAL on the cited Theorem 4 and Lemma 9. HARD. -/
theorem l34s_g_big_lemma33 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, the part of g_m with w <= P <= Y^eps: "we iterate the
decomposition in the same fashion as case (ii) of Lemma 13. After j steps we have reached a
decomposition n p1 ... pj n_(j+1) where p1 ... p_(j-1) <= Y^eps, and need only decompose again if
p1 ... pj <= Y^eps. ... The process terminates after O(L^(1/10)) steps", for 5.1 on page 43 with
the page 19 set E and its size from page 3. The terms are those of g_m with w <= p1 < Y^eps,
w = exp(log^(9/10) x) from page 25. Case ii of Lemma 13 is on page 26. CONDITIONAL on the cited
Theorem 4 and Lemma 9. HARD. -/
theorem l34s_g_small_iterate (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  sorry

/-- P0069 page 49, Lemma 34, conclusion 5.1 on page 43 with the page 19 set E and its size. The
exact statement of the leaf `upD_lemma34_51` of Prep1121DUpslackPieces on the branch
claude/BHP1997-upper_normalized_raw_conditions_slack-p2. PROVED from the three LEAFs above by
Buchstab's identity b = f - g_big - g_small on J for large x. CONDITIONAL on the cited Theorem 4
and Lemma 9. -/
theorem l34s_lemma34_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a b : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  have hεc1 : ε ≤ upperC1 ε := by norm_num [upperC1]; linarith
  obtain ⟨Cw, hCw⟩ := l34s_w_le (c := (11 / 20 + ε) * ε) (by positivity)
  have hg := l34s_add (ε := ε)
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε),
        upperRough (m / n / p : ℕ) (p : ℝ))
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ ε),
        upperRough (m / n / p : ℕ) (p : ℝ))
    _ ⟨0, fun _ _ _ _ => rfl⟩
    (l34s_g_big_lemma33 h4 h9 hε hε8 a ha) (l34s_g_small_iterate h4 h9 hε hε8 a ha)
  have hng := l34s_neg _ hg
  refine l34s_add
    (fun x m => ∑ n ∈ m.divisors.filter (fun n : ℕ =>
        (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      a x n * upperRough (m / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))))
    _ b ⟨max 4 Cw, fun x hx m hm => ?_⟩ (l34s_f_lemma30 h4 h9 hε hε8 a ha) hng
  have hx4 : 4 ≤ x := le_trans (le_max_left _ _) hx
  have hY := l34s_two_le hε hx4
  have hw' : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (x ^ (11 / 20 + ε)) ^ ε := by
    rw [← Real.rpow_mul (by linarith)]
    exact hCw x (le_trans (le_max_right _ _) hx)
  have hz : (x ^ (11 / 20 + ε)) ^ ε ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hεc1
  rw [hrep x hY m hm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [l34s_buchstab (m / n) hw' hz]
  ring

end LeanLab.BHP1997.DecompC165d

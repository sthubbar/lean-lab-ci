/-
Split of the three OPEN leaves of LeanLab.BakerHarmanPintz1997.Decomp409b:
truncated_transfer, error_transfer and error_average. P0069 pages 26 and 27.
The sealed statements are unchanged and restated verbatim in the `_split` theorems.

truncated_transfer and error_transfer follow page 27 lines 1 to 12: "To get (4.10), apply
Lemma 10 and 11", and "We prove (4.11) in precisely the same way". The route is Lemma 11,
the cited theorem `lemma11` of Statements, applied to the coefficient family with its value
at k = 0 set to zero; that value never enters (4.2), since every window starts above 0.
Lemma 11 needs two inputs, so each transfer splits into a coefficient bound of shape (3.1),
MEDIUM, and the mean value bound (4.1), HARD, the place where Lemma 10 enters.

error_average follows display (4.13): a divisor rearrangement with interval counting, HARD,
the Hildebrand reciprocal smooth tail, HARD and cited, and an elementary size comparison of
x^0.96 with y1 x / L x ^ A, MEDIUM.

The `_split` theorems of the two transfers are also CONDITIONAL ON the cited `lemma11`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-! ### Proved helpers for the coefficient bounds (3.1), S117 -/

/-- `tau n` is the number of divisors of `n`. -/
theorem s409_tau_eq_card (n : ℕ) : tau n = (n.divisors.card : ℝ) := by
  simp [tau, ArithmeticFunction.sigma_zero_apply]

/-- A divisor of a nonzero `k` has at least one and at most `tau k` divisors. -/
theorem s409_one_le_tau {m : ℕ} (hm : m ≠ 0) : 1 ≤ tau m := by
  rw [s409_tau_eq_card]
  exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hm⟩⟩

theorem s409_tau_le_of_dvd {m k : ℕ} (hk : k ≠ 0) (h : m ∣ k) : tau m ≤ tau k := by
  rw [s409_tau_eq_card, s409_tau_eq_card]
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk h)

/-- The weight bound (3.1) at a divisor `m` of `k`: `tau m ^ B ≤ tau k ^ |B|`. -/
theorem s409_rpow_tau_le_of_dvd (B : ℝ) {m k : ℕ} (hk : k ≠ 0) (h : m ∣ k) :
    tau m ^ B ≤ tau k ^ |B| := by
  have hm : m ≠ 0 := by rintro rfl; exact hk (Nat.eq_zero_of_zero_dvd h)
  calc tau m ^ B ≤ tau m ^ |B| :=
        Real.rpow_le_rpow_of_exponent_le (s409_one_le_tau hm) (le_abs_self B)
    _ ≤ tau k ^ |B| :=
        Real.rpow_le_rpow (by linarith [s409_one_le_tau hm]) (s409_tau_le_of_dvd hk h) (abs_nonneg B)

/-- Counting the pairs `m, n` with `mn | k`: a double sum over them of terms at most `c`
is at most `c tau(k)^2`. -/
theorem s409_double_sum_dvd_le {k : ℕ} (hk : k ≠ 0) (S T : Finset ℕ) (f : ℕ → ℕ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ m n, m * n ∣ k → f m n ≤ c) :
    ∑ m ∈ S, ∑ n ∈ T, (if m * n ∣ k then f m n else 0) ≤ c * tau k * tau k := by
  have hstep : ∀ m ∈ S, ∑ n ∈ T, (if m * n ∣ k then f m n else 0) ≤
      if m ∣ k then c * tau k else 0 := by
    intro m _
    by_cases hm : m ∣ k
    · rw [if_pos hm]
      calc ∑ n ∈ T, (if m * n ∣ k then f m n else 0)
          ≤ ∑ n ∈ T, (if n ∣ k then c else 0) := by
            refine sum_le_sum fun n _ => ?_
            by_cases hmn : m * n ∣ k
            · rw [if_pos hmn, if_pos (Dvd.dvd.trans (Dvd.intro_left m rfl) hmn)]
              exact hf m n hmn
            · rw [if_neg hmn]; split_ifs <;> linarith
        _ = ∑ n ∈ T.filter (· ∣ k), c := (sum_filter _ _).symm
        _ ≤ ∑ n ∈ k.divisors, c := by
            refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hc)
            intro n hn
            exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hn).2, hk⟩
        _ = c * tau k := by rw [sum_const, nsmul_eq_mul, s409_tau_eq_card, mul_comm]
    · rw [if_neg hm]
      refine sum_eq_zero_iff_of_nonneg ?_ |>.mpr ?_ |>.le
      · intro n _; split_ifs with h
        · exact absurd (Dvd.dvd.trans (Dvd.intro n rfl) h) hm
        · exact le_rfl
      · intro n _; rw [if_neg]; exact fun h => hm (Dvd.dvd.trans (Dvd.intro n rfl) h)
  calc _ ≤ ∑ m ∈ S, (if m ∣ k then c * tau k else 0) := sum_le_sum hstep
    _ = ∑ m ∈ S.filter (· ∣ k), c * tau k := (sum_filter _ _).symm
    _ ≤ ∑ m ∈ k.divisors, c * tau k := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by
          have := s409_one_le_tau hk; positivity)
        intro n hn
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hn).2, hk⟩
    _ = c * tau k * tau k := by rw [sum_const, nsmul_eq_mul, s409_tau_eq_card, mul_comm]

theorem s409_norm_psiTrunc_le (l : ℕ) (hl : l ≠ 0) (w γ : ℝ) : ‖psiTrunc l w γ‖ ≤ tau l := by
  unfold psiTrunc
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ ≤ ∑ d ∈ l.divisors, (1 : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le_one)
        intro d hd
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2.1, hl⟩
    _ = tau l := by rw [sum_const, nsmul_eq_mul, mul_one, s409_tau_eq_card]

theorem s409_psiErr_le (l : ℕ) (hl : l ≠ 0) (w γ : ℝ) : psiErr l w γ ≤ tau l := by
  rw [psiErr, s409_tau_eq_card]
  refine Nat.cast_le.mpr (card_le_card ?_)
  intro d hd
  rw [mem_filter] at hd
  exact Nat.mem_divisors.mpr ⟨hd.2.1, hl⟩

theorem s409_psiErr_nonneg (l : ℕ) (w γ : ℝ) : 0 ≤ psiErr l w γ := by
  rw [psiErr]; positivity

/-- The exponent algebra: `t^|B| t^|B| t t t = t^(2|B|+3)` for `t ≥ 1`. -/
theorem s409_rpow_combine {t : ℝ} (ht : 1 ≤ t) (B : ℝ) :
    t ^ |B| * t ^ |B| * t * t * t = t ^ (2 * |B| + 3) := by
  have ht0 : 0 < t := by linarith
  rw [show 2 * |B| + 3 = |B| + |B| + 1 + 1 + 1 by ring, Real.rpow_add ht0, Real.rpow_add ht0,
    Real.rpow_add ht0, Real.rpow_add ht0, Real.rpow_one]


/-- The quotient `k/(mn)` of a nonzero `k` by a divisor `mn` is a nonzero divisor of `k`. -/
theorem s409_div_dvd_ne_zero {k m n : ℕ} (hk : k ≠ 0) (h : m * n ∣ k) :
    k / (m * n) ∣ k ∧ k / (m * n) ≠ 0 :=
  ⟨Nat.div_dvd_of_dvd h, fun h0 => hk (by
    rw [Nat.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [h0] at h; exact Nat.eq_zero_of_zero_dvd h
    · exact absurd h0 (not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)))⟩

/-- LEAF: page 27 line 4, the coefficients of M1 N L satisfy (3.1). MEDIUM.
For k at least 1, the pairs m, n with mn dividing k number at most tau k squared, each
weight is at most tau k to the power of the absolute value of B, and the truncated Moebius
sum over divisors of l = k/mn has absolute value at most tau l, which is at most tau k.
The value at k = 0 is set to zero, since tau 0 = 0. Non-vacuity: a = b = 0 meets the
hypotheses for every B. -/
theorem leaf_trunc_coeff_bound (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then 0 else conv2T a b M N w γ k)‖ ≤ tau k ^ B' := by
  refine ⟨2 * |B| + 3, fun a b M N w γ ha hb k => ?_⟩
  by_cases hk : k = 0
  · rw [if_pos hk, norm_zero]; exact Real.rpow_nonneg (by rw [tau]; positivity) _
  rw [if_neg hk]
  have ht := s409_one_le_tau hk
  rw [← s409_rpow_combine ht B]
  unfold conv2T
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (sum_le_sum fun m _ => norm_sum_le _ _) ?_
  have e : ∀ m n, ‖(if m * n ∣ k then a m * b n * psiTrunc (k / (m * n)) w γ else 0)‖ =
      if m * n ∣ k then ‖a m * b n * psiTrunc (k / (m * n)) w γ‖ else 0 := by
    intro m n; split_ifs <;> simp
  simp only [e]
  refine s409_double_sum_dvd_le hk _ _ _ (by positivity) fun m n hmn => ?_
  obtain ⟨hl, hl0⟩ := s409_div_dvd_ne_zero hk hmn
  have hm : m ∣ k := (Dvd.intro n rfl).trans hmn
  have hn : n ∣ k := (Dvd.intro_left m rfl).trans hmn
  rw [norm_mul, norm_mul]
  have h1 := (ha m).trans (s409_rpow_tau_le_of_dvd B hk hm)
  have h2 := (hb n).trans (s409_rpow_tau_le_of_dvd B hk hn)
  have h3 := (s409_norm_psiTrunc_le _ hl0 w γ).trans (s409_tau_le_of_dvd hk hl)
  have h0 : 0 ≤ tau k ^ |B| := Real.rpow_nonneg (by linarith) _
  calc ‖a m‖ * ‖b n‖ * ‖psiTrunc (k / (m * n)) w γ‖ ≤ tau k ^ |B| * tau k ^ |B| * tau k := by
        gcongr
    _ = _ := rfl

/-- LEAF: page 27 lines 1 to 10, display (4.1) for c prime, via Lemma 10 applied to
M1 N L summed over D = gamma 2^-j. HARD.
The truncated series of c prime on k ~ x has mean value at most x^(1/2) L^-A on both
half lines [T0, T1] and [-T1, -T0], uniformly in q at most L^A and chi mod q.
Non-vacuity: a = b = 0 gives the zero series. -/
theorem leaf_trunc_mean_value :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨fun k => if k = 0 then 0 else conv2T (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k,
            Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) ∧
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨fun k => if k = 0 then 0 else conv2T (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k,
            Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half (-t))‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) := by
  sorry

/-- LEAF: page 27 lines 11 and 12, the coefficients of the modified M1 N L satisfy (3.1).
MEDIUM. As in `leaf_trunc_coeff_bound`, with the error count psiErr l at most tau l.
Non-vacuity: a = b = 0. -/
theorem leaf_err_coeff_bound (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then (0 : ℂ) else ((conv2E a b M N w γ k : ℝ) : ℂ))‖ ≤ tau k ^ B' := by
  refine ⟨2 * |B| + 3, fun a b M N w γ ha hb k => ?_⟩
  by_cases hk : k = 0
  · rw [if_pos hk, norm_zero]; exact Real.rpow_nonneg (by rw [tau]; positivity) _
  rw [if_neg hk, Complex.norm_real, Real.norm_eq_abs]
  have ht := s409_one_le_tau hk
  rw [← s409_rpow_combine ht B]
  have hnn : 0 ≤ conv2E a b M N w γ k := by
    unfold conv2E
    refine sum_nonneg fun m _ => sum_nonneg fun n _ => ?_
    split_ifs
    · have := s409_psiErr_nonneg (k / (m * n)) w γ; positivity
    · exact le_rfl
  rw [abs_of_nonneg hnn]
  unfold conv2E
  refine s409_double_sum_dvd_le hk _ _ _ (by positivity) fun m n hmn => ?_
  obtain ⟨hl, hl0⟩ := s409_div_dvd_ne_zero hk hmn
  have hm : m ∣ k := (Dvd.intro n rfl).trans hmn
  have hn : n ∣ k := (Dvd.intro_left m rfl).trans hmn
  have h1 := (ha m).trans (s409_rpow_tau_le_of_dvd B hk hm)
  have h2 := (hb n).trans (s409_rpow_tau_le_of_dvd B hk hn)
  have h3 := (s409_psiErr_le _ hl0 w γ).trans (s409_tau_le_of_dvd hk hl)
  have h0 : 0 ≤ tau k ^ |B| := Real.rpow_nonneg (by linarith) _
  have h4 := s409_psiErr_nonneg (k / (m * n)) w γ
  calc ‖a m‖ * ‖b n‖ * psiErr (k / (m * n)) w γ ≤ tau k ^ |B| * tau k ^ |B| * tau k := by
        gcongr
    _ = _ := rfl

/-- LEAF: page 27 lines 11 and 12, display (4.1) for c double prime, Lemma 10 applied to
M1 with d restricted to d | P(w), gamma at most d below w gamma, d ~ D. HARD.
Non-vacuity: a = b = 0 gives the zero series. -/
theorem leaf_err_mean_value :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨fun k => if k = 0 then (0 : ℂ) else
              ((conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k : ℝ) : ℂ),
            Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) ∧
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨fun k => if k = 0 then (0 : ℂ) else
              ((conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k : ℝ) : ℂ),
            Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half (-t))‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) := by
  sorry

/-- LEAF: display (4.13), first inequality. HARD but elementary.
Swap the sums: the sum of c double prime over I1 is the sum over m, n and d | P(w) with
gamma at most d below gamma w of |a_m b_n| times the number of l with d | l and mnl in I1,
which is at most y1/(mnd) + 1. The main part gives y1 L^K times the reciprocal sum over d,
using sum over m ~ M of tau(m)^B / m at most L^K. The remainder is at most M N gamma w
times x^o(1), below x^0.96 under (4.8) or (4.9) once epsilon is small.
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_rearrange :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C K X0 : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊,
          conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k ≤
            C * (y1 x * L x ^ K *
              ∑ d ∈ (siftingProduct (wof x)).divisors.filter
                (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ))
              + x ^ (0.96 : ℝ)) := by
  sorry

/-- LEAF: display (4.13), second inequality, Theorem 1 of Hildebrand reference 13. HARD, CITED.
The reciprocal sum over w-smooth squarefree d at least gamma = x^(ε/12), w = exp(L^(9/10)),
is at most a constant times L exp(-u log u / 2) with u = (ε/12) L^(1/10), so below any
power L^-A. Non-vacuity: the sum is nonnegative and the statement has content for every A. -/
theorem leaf_hildebrand_tail (ε : ℝ) (hε : 0 < ε) (A : ℝ) (hA : 0 < A) :
    ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∑ d ∈ (siftingProduct (wof x)).divisors.filter
          (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) ≤
        C / L x ^ A := by
  sorry

/-- LEAF: page 24, y1 x = x exp(-3 L^(1/3)) exceeds x^0.96 L^A for large x. MEDIUM.
Equivalent to 0.04 L x at least 3 L^(1/3) + A log L, a routine growth comparison.
Non-vacuity: a single eventual inequality, true for every A. -/
theorem leaf_y1_dominates (A : ℝ) (hA : 0 < A) :
    ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → x ^ (0.96 : ℝ) ≤ y1 x / L x ^ A := by
  refine ⟨Real.exp ((25 * (3 + 2 * A)) ^ 2 + 1), fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set u := Real.log x with hu
  have hu1 : (25 * (3 + 2 * A)) ^ 2 + 1 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le hxpos]; exact hx
  have hupos : 0 < u := by nlinarith
  have hu1' : 1 ≤ u := by nlinarith
  have hL : L x = u := rfl
  -- key inequality on the log scale
  have hsq : 0 < u ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hupos _
  have hsq2 : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
    rw [← Real.rpow_add hupos]; norm_num
  have hlog : Real.log u ≤ 2 * u ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hupos.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith [show u ^ (1 / 2 : ℝ) / (1 / 2) = 2 * u ^ (1 / 2 : ℝ) by ring]
  have hthird : u ^ (1 / 3 : ℝ) ≤ u ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1' (by norm_num)
  have hbig : 25 * (3 + 2 * A) ≤ u ^ (1 / 2 : ℝ) := by
    by_contra h
    push Not at h
    have h0 : 0 ≤ 25 * (3 + 2 * A) := by linarith
    have : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) < (25 * (3 + 2 * A)) ^ 2 := by
      rw [sq]; exact mul_self_lt_mul_self hsq.le h
    linarith
  have hkey : 0.96 * u + A * Real.log u ≤ u + -3 * u ^ (1 / 3 : ℝ) := by
    have h1 : (3 + 2 * A) * u ^ (1 / 2 : ℝ) ≤ 0.04 * u := by
      have := mul_le_mul_of_nonneg_right hbig hsq.le
      nlinarith
    nlinarith
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos (by rw [hL]; exact hupos) _
  rw [le_div_iff₀ hLA]
  have e1 : x ^ (0.96 : ℝ) = Real.exp (0.96 * u) := by
    rw [Real.rpow_def_of_pos hxpos, hu, mul_comm]
  have e2 : L x ^ A = Real.exp (A * Real.log u) := by
    rw [hL, Real.rpow_def_of_pos hupos, mul_comm]
  have e3 : y1 x = Real.exp (u + -3 * u ^ (1 / 3 : ℝ)) := by
    rw [y1, Real.exp_add, Real.exp_log hxpos]
  rw [e1, e2, e3, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hkey

/-- Proved glue: a family and its copy vanishing at k = 0 have the same (4.2). -/
theorem holds42_of_zero_at_zero {ε : ℝ} {c : ℝ → ℕ → ℂ}
    (h : Holds42 ε fun x k => if k = 0 then 0 else c x k) : Holds42 ε c :=
  holds42_congr_ev ⟨0, fun x _ k hk => by simp [Nat.pos_iff_ne_zero.1 hk]⟩ h

/-- `truncated_transfer`, verbatim, CONDITIONAL ON `leaf_trunc_coeff_bound`,
`leaf_trunc_mean_value` and the cited `lemma11`. -/
theorem truncated_transfer_split :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      Holds42 ε fun x k => conv2T (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k := by
  obtain ⟨ε1, hε1, h11⟩ := lemma11
  obtain ⟨ε2, hε2, hmv⟩ := leaf_trunc_mean_value
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨B', hB'⟩ := leaf_trunc_coeff_bound B
  apply holds42_of_zero_at_zero
  exact h11 ε hε (hεs.trans_le (min_le_left _ _)) B'
    (fun x k => if k = 0 then 0 else conv2T (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k)
    (fun x k => hB' (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) (ha x) (hb x) k)
    (hmv ε hε (hεs.trans_le (min_le_right _ _)) B a b M N ha hb hr)

/-- `error_transfer`, verbatim, CONDITIONAL ON `leaf_err_coeff_bound`,
`leaf_err_mean_value` and the cited `lemma11`. -/
theorem error_transfer_split :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      Holds42 ε fun x k =>
        ((conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k : ℝ) : ℂ) := by
  obtain ⟨ε1, hε1, h11⟩ := lemma11
  obtain ⟨ε2, hε2, hmv⟩ := leaf_err_mean_value
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨B', hB'⟩ := leaf_err_coeff_bound B
  apply holds42_of_zero_at_zero
  exact h11 ε hε (hεs.trans_le (min_le_left _ _)) B'
    (fun x k => if k = 0 then (0 : ℂ) else
      ((conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k : ℝ) : ℂ))
    (fun x k => hB' (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) (ha x) (hb x) k)
    (hmv ε hε (hεs.trans_le (min_le_right _ _)) B a b M N ha hb hr)

/-- `error_average`, verbatim, CONDITIONAL ON `leaf_err_rearrange`, `leaf_hildebrand_tail`
and `leaf_y1_dominates`. -/
theorem error_average_split :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
        ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊,
          conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k ≤
            C * y1 x / L x ^ A := by
  obtain ⟨ε1, hε1, hre⟩ := leaf_err_rearrange
  refine ⟨ε1, hε1, ?_⟩
  intro ε hε hεs B a b M N ha hb hr A hA
  obtain ⟨C, K, X1, hC, hK, h1⟩ := hre ε hε hεs B a b M N ha hb hr
  obtain ⟨CB, X2, h2⟩ := leaf_hildebrand_tail ε hε (A + K) (by linarith)
  obtain ⟨X3, h3⟩ := leaf_y1_dominates A hA
  refine ⟨C * (CB + 1), max (max X1 X2) (max X3 3), ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hL : 0 < L x := Real.log_pos (by linarith)
  have hy : 0 < y1 x := y1_pos (by linarith)
  have hLK : 0 < L x ^ K := Real.rpow_pos_of_pos hL _
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos hL _
  set S := ∑ d ∈ (siftingProduct (wof x)).divisors.filter
    (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) with hS
  have hS2 : S ≤ CB / L x ^ (A + K) := h2 x hx2
  have hmain : y1 x * L x ^ K * S ≤ CB * y1 x / L x ^ A := by
    have e : y1 x * L x ^ K * (CB / L x ^ (A + K)) = CB * y1 x / L x ^ A := by
      rw [Real.rpow_add hL]
      field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hS2 (by positivity)
  have hsmall := h3 x hx3
  calc _ ≤ C * (y1 x * L x ^ K * S + x ^ (0.96 : ℝ)) := h1 x hx1
    _ ≤ C * (CB * y1 x / L x ^ A + y1 x / L x ^ A) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain hsmall) hC
    _ = C * (CB + 1) * y1 x / L x ^ A := by ring

#print axioms leaf_trunc_coeff_bound
#print axioms leaf_err_coeff_bound
#print axioms leaf_y1_dominates
#print axioms holds42_of_zero_at_zero
#print axioms truncated_transfer_split
#print axioms error_transfer_split
#print axioms error_average_split

end LeanLab.BakerHarmanPintz1997.Decomp409b

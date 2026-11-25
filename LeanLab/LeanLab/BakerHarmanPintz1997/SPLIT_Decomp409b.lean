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

/-- Proved helper: tau is monotone along divisibility. -/
theorem tau_le_of_dvd409 {m k : ℕ} (hk : k ≠ 0) (h : m ∣ k) : tau m ≤ tau k := by
  unfold tau
  simp only [ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk h)

/-- Proved helper: tau of a positive integer is at least 1. -/
theorem one_le_tau409 {m : ℕ} (hm : m ≠ 0) : 1 ≤ tau m := by
  unfold tau
  simp only [ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hm⟩

/-- Proved helper: a coefficient bound tau m ^ B for m dividing k is at most tau k ^ |B|. -/
theorem rpow_tau_le409 (B : ℝ) {m k : ℕ} (hk : k ≠ 0) (h : m ∣ k) :
    tau m ^ B ≤ tau k ^ |B| := by
  have hm : m ≠ 0 := fun h0 => hk (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have h1 := one_le_tau409 hm
  calc tau m ^ B ≤ tau m ^ |B| := Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self B)
    _ ≤ tau k ^ |B| := Real.rpow_le_rpow (by linarith) (tau_le_of_dvd409 hk h) (abs_nonneg B)

/-- Proved helper: the truncated Moebius sum of l has norm at most tau l. -/
theorem psiTrunc_norm_le409 {l : ℕ} (hl : l ≠ 0) (w γ : ℝ) : ‖psiTrunc l w γ‖ ≤ tau l := by
  unfold psiTrunc
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ ≤ tau l := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        unfold tau
        simp only [ArithmeticFunction.sigma_zero_apply]
        apply Nat.cast_le.2
        apply Finset.card_le_card
        intro d hd
        simp only [Finset.mem_filter] at hd
        exact Nat.mem_divisors.2 ⟨hd.2.1, hl⟩

/-- Proved helper: psiErr l counts divisors of l, so it is at most tau l. -/
theorem psiErr_le_tau409 {l : ℕ} (hl : l ≠ 0) (w γ : ℝ) : psiErr l w γ ≤ tau l := by
  unfold psiErr tau
  simp only [ArithmeticFunction.sigma_zero_apply]
  apply Nat.cast_le.2
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter] at hd
  exact Nat.mem_divisors.2 ⟨hd.2.1, hl⟩

/-- Proved helper: the number of m in a window dividing k is at most tau k. -/
theorem card_dvd_window_le409 {k : ℕ} (hk : k ≠ 0) (s : Finset ℕ) :
    ((s.filter (fun m => m ∣ k)).card : ℝ) ≤ tau k := by
  unfold tau
  simp only [ArithmeticFunction.sigma_zero_apply]
  apply Nat.cast_le.2
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm
  exact Nat.mem_divisors.2 ⟨hm.2, hk⟩

/-- Proved helper: the double window sum of the divisibility indicators times X is at most
tau k squared times X. -/
theorem window_sum_le409 {k : ℕ} (hk : k ≠ 0) (s t : Finset ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ s, ∑ n ∈ t, (if m ∣ k then (1 : ℝ) else 0) * ((if n ∣ k then (1 : ℝ) else 0) * X)
      ≤ tau k * (tau k * X) := by
  have e : ∑ m ∈ s, ∑ n ∈ t, (if m ∣ k then (1 : ℝ) else 0) * ((if n ∣ k then (1 : ℝ) else 0) * X)
      = ((s.filter (fun m => m ∣ k)).card : ℝ) * (((t.filter (fun n => n ∣ k)).card : ℝ) * X) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole]
  rw [e]
  have hT := one_le_tau409 hk
  exact mul_le_mul (card_dvd_window_le409 hk s)
    (mul_le_mul_of_nonneg_right (card_dvd_window_le409 hk t) hX) (by positivity) (by linarith)

/-- Proved helper: the exponent arithmetic tau k * (tau k * (T^|B| T^|B| T)) = T^(2|B|+3). -/
theorem tau_pow_eq409 {T : ℝ} (hT0 : 0 < T) (B : ℝ) :
    T * (T * (T ^ |B| * T ^ |B| * T)) = T ^ (2 * |B| + 3) := by
  have he : (2 * |B| + 3 : ℝ) = |B| + |B| + ((3 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_natCast]
  ring

/-- Proved helper: one term of either convolution, for m n dividing k, with coefficient bounds
and a weight at most tau of the cofactor. -/
theorem term_le409 (B : ℝ) {k m n : ℕ} (hk : k ≠ 0) (hmn : m * n ∣ k) {am bn p : ℝ}
    (ha : am ≤ tau m ^ B) (hb : bn ≤ tau n ^ B) (ha0 : 0 ≤ am) (hb0 : 0 ≤ bn) (hp0 : 0 ≤ p)
    (hp : p ≤ tau (k / (m * n))) :
    am * bn * p ≤ tau k ^ |B| * tau k ^ |B| * tau k := by
  have hm : m ∣ k := (Nat.dvd_mul_right m n).trans hmn
  have hn : n ∣ k := (Nat.dvd_mul_left n m).trans hmn
  have hT := one_le_tau409 hk
  have hpow : 0 ≤ tau k ^ |B| := Real.rpow_nonneg (by linarith) _
  have h3 : p ≤ tau k := hp.trans (tau_le_of_dvd409 hk (Nat.div_dvd_of_dvd hmn))
  have h1 := ha.trans (rpow_tau_le409 B hk hm)
  have h2 := hb.trans (rpow_tau_le409 B hk hn)
  exact mul_le_mul (mul_le_mul h1 h2 hb0 hpow) h3 hp0 (mul_nonneg hpow hpow)

/-- LEAF: page 27 line 4, the coefficients of M1 N L satisfy (3.1). MEDIUM.
For k at least 1, the pairs m, n with mn dividing k number at most tau k squared, each
weight is at most tau k to the power of the absolute value of B, and the truncated Moebius
sum over divisors of l = k/mn has absolute value at most tau l, which is at most tau k.
The value at k = 0 is set to zero, since tau 0 = 0. Non-vacuity: a = b = 0 meets the
hypotheses for every B. -/
theorem leaf_trunc_coeff_bound (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then 0 else conv2T a b M N w γ k)‖ ≤ tau k ^ B' := by
  refine ⟨2 * |B| + 3, ?_⟩
  intro a b M N w γ ha hb k
  by_cases hk : k = 0
  · simp only [if_pos hk, norm_zero]
    exact Real.rpow_nonneg (by unfold tau; positivity) _
  rw [if_neg hk]
  have hT : 1 ≤ tau k := one_le_tau409 hk
  have hX : 0 ≤ tau k ^ |B| * tau k ^ |B| * tau k := by
    have : 0 ≤ tau k ^ |B| := Real.rpow_nonneg (by linarith) _
    positivity
  rw [← tau_pow_eq409 (by linarith) B]
  unfold conv2T
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (window_sum_le409 hk (Ioc ⌊M⌋₊ ⌊2 * M⌋₊) (Ioc ⌊N⌋₊ ⌊2 * N⌋₊) hX)
  refine Finset.sum_le_sum fun m _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  by_cases hmn : m * n ∣ k
  · have hm : m ∣ k := (Nat.dvd_mul_right m n).trans hmn
    have hn : n ∣ k := (Nat.dvd_mul_left n m).trans hmn
    have hl : k / (m * n) ≠ 0 := by
      intro h0
      have := Nat.div_mul_cancel hmn
      rw [h0, zero_mul] at this
      exact hk this.symm
    rw [if_pos hmn, if_pos hm, if_pos hn, one_mul, one_mul, norm_mul, norm_mul]
    exact term_le409 B hk hmn (ha m) (hb n) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (psiTrunc_norm_le409 hl w γ)
  · rw [if_neg hmn, norm_zero]
    split_ifs <;> positivity

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
  refine ⟨2 * |B| + 3, ?_⟩
  intro a b M N w γ ha hb k
  by_cases hk : k = 0
  · simp only [if_pos hk, norm_zero]
    exact Real.rpow_nonneg (by unfold tau; positivity) _
  rw [if_neg hk]
  have hT : 1 ≤ tau k := one_le_tau409 hk
  set T := tau k with hTdef
  have hnn : 0 ≤ conv2E a b M N w γ k := by
    unfold conv2E
    refine Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => ?_
    split_ifs
    · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by unfold psiErr; positivity)
    · exact le_rfl
  rw [Complex.norm_real, Real.norm_of_nonneg hnn]
  have hterm : ∀ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∀ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      (if m * n ∣ k then ‖a m‖ * ‖b n‖ * psiErr (k / (m * n)) w γ else 0) ≤
        (if m ∣ k then (1 : ℝ) else 0) * ((if n ∣ k then (1 : ℝ) else 0) *
          (T ^ |B| * T ^ |B| * T)) := by
    intro m _ n _
    by_cases hmn : m * n ∣ k
    · have hm : m ∣ k := (Nat.dvd_mul_right m n).trans hmn
      have hn : n ∣ k := (Nat.dvd_mul_left n m).trans hmn
      have hl : k / (m * n) ≠ 0 := by
        intro h0
        have := Nat.div_mul_cancel hmn
        rw [h0, zero_mul] at this
        exact hk this.symm
      have hld : k / (m * n) ∣ k := Nat.div_dvd_of_dvd hmn
      rw [if_pos hmn, if_pos hm, if_pos hn, one_mul, one_mul]
      have h1 : ‖a m‖ ≤ T ^ |B| := (ha m).trans (rpow_tau_le409 B hk hm)
      have h2 : ‖b n‖ ≤ T ^ |B| := (hb n).trans (rpow_tau_le409 B hk hn)
      have h3 : psiErr (k / (m * n)) w γ ≤ T :=
        (psiErr_le_tau409 hl w γ).trans (tau_le_of_dvd409 hk hld)
      have h0 : 0 ≤ psiErr (k / (m * n)) w γ := by unfold psiErr; positivity
      have hp : 0 ≤ T ^ |B| := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hp) h3 h0 (mul_nonneg hp hp)
    · rw [if_neg hmn]
      have hp : 0 ≤ T ^ |B| := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ T ^ |B| * T ^ |B| * T := by positivity
      split_ifs <;> positivity
  calc conv2E a b M N w γ k
      ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
          (if m ∣ k then (1 : ℝ) else 0) * ((if n ∣ k then (1 : ℝ) else 0) *
            (T ^ |B| * T ^ |B| * T)) :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m hm n hn
    _ = ((Ioc ⌊M⌋₊ ⌊2 * M⌋₊).filter (fun m => m ∣ k)).card *
          (((Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n ∣ k)).card *
            (T ^ |B| * T ^ |B| * T)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole]
    _ ≤ T * (T * (T ^ |B| * T ^ |B| * T)) := by
        have hp : 0 ≤ T ^ |B| := Real.rpow_nonneg (by linarith) _
        have hc1 := card_dvd_window_le409 hk (Ioc ⌊M⌋₊ ⌊2 * M⌋₊)

        have hc2 := card_dvd_window_le409 hk (Ioc ⌊N⌋₊ ⌊2 * N⌋₊)

        have hX : 0 ≤ T ^ |B| * T ^ |B| * T := by positivity
        exact mul_le_mul hc1 (mul_le_mul_of_nonneg_right hc2 hX) (by positivity) (by linarith)
    _ = T ^ (2 * |B| + 3) := by
        have hT0 : 0 < T := by linarith
        have he : (2 * |B| + 3 : ℝ) = |B| + |B| + ((3 : ℕ) : ℝ) := by push_cast; ring
        rw [he, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_natCast]
        ring

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
  set K : ℝ := 75 * (A + 1) + 1 with hKdef
  have hK1 : 1 ≤ K := by linarith
  refine ⟨Real.exp (K ^ 3), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hl : K ^ 3 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hl0 : 0 < Real.log x := lt_of_lt_of_le (by positivity) hl
  have ht0 : 0 < Real.log x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hl0 _
  have ht3 : (Real.log x ^ (1 / 3 : ℝ)) ^ 3 = Real.log x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have htK : K ≤ Real.log x ^ (1 / 3 : ℝ) := by
    by_contra h
    push_neg at h
    have : (Real.log x ^ (1 / 3 : ℝ)) ^ 3 < K ^ 3 :=
      pow_lt_pow_left₀ h ht0.le (by norm_num)
    linarith
  have hlogl : Real.log (Real.log x) ≤ 3 * Real.log x ^ (1 / 3 : ℝ) := by
    have h := Real.log_le_rpow_div hl0.le (by norm_num : (0 : ℝ) < 1 / 3)
    have he : Real.log x ^ (1 / 3 : ℝ) / (1 / 3) = 3 * Real.log x ^ (1 / 3 : ℝ) := by ring
    linarith
  have ht2 : 75 * (A + 1) ≤ (Real.log x ^ (1 / 3 : ℝ)) ^ 2 := by nlinarith
  have h2 : 3 * (A + 1) * Real.log x ^ (1 / 3 : ℝ) ≤
      0.04 * (Real.log x ^ (1 / 3 : ℝ)) ^ 3 := by
    have := mul_le_mul_of_nonneg_left ht2 ht0.le
    nlinarith
  have h1 : A * Real.log (Real.log x) ≤ A * (3 * Real.log x ^ (1 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogl hA.le
  have hmain : Real.log x * 0.96 + Real.log (Real.log x) * A ≤
      Real.log x + -3 * Real.log x ^ (1 / 3 : ℝ) := by
    nlinarith
  unfold y1 L
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hl0 A), Real.rpow_def_of_pos hx0,
    Real.rpow_def_of_pos hl0, ← Real.exp_add]
  conv_rhs => rw [← Real.exp_log hx0]
  rw [← Real.exp_add, Real.log_exp]
  exact Real.exp_le_exp.mpr hmain

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

#print axioms holds42_of_zero_at_zero
#print axioms truncated_transfer_split
#print axioms error_transfer_split
#print axioms error_average_split

end LeanLab.BakerHarmanPintz1997.Decomp409b

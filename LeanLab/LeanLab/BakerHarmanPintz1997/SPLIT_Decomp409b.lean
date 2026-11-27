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

/-- LEAF: page 27 line 4, the coefficients of M1 N L satisfy (3.1). MEDIUM.
For k at least 1, the pairs m, n with mn dividing k number at most tau k squared, each
weight is at most tau k to the power of the absolute value of B, and the truncated Moebius
sum over divisors of l = k/mn has absolute value at most tau l, which is at most tau k.
The value at k = 0 is set to zero, since tau 0 = 0. Non-vacuity: a = b = 0 meets the
hypotheses for every B. -/
private theorem tau_one_le {k : ℕ} (hk : 0 < k) : 1 ≤ tau k := by
  have hc : 0 < k.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne'⟩
  have h1 : (1 : ℕ) ≤ k.divisors.card := hc
  simp only [tau, ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast h1

private theorem psiTrunc_norm_le_tau_409b (l : ℕ) (hl : 0 < l) (w γ : ℝ) :
    ‖psiTrunc l w γ‖ ≤ tau l := by
  have hmu : ∀ d : ℕ, ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    intro d
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hsub : (siftingProduct w).divisors.filter (fun d => d ∣ l ∧ (d : ℝ) < γ) ⊆ l.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2.1, hl.ne'⟩
  unfold psiTrunc
  calc _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, ‖(ArithmeticFunction.moebius d : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (1 : ℝ) :=
        sum_le_sum (fun d _ => hmu d)
    _ ≤ ∑ d ∈ l.divisors, (1 : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by simp [tau, ArithmeticFunction.sigma_zero_apply]

private theorem psiErr_le_tau_409b (l : ℕ) (hl : 0 < l) (w γ : ℝ) : psiErr l w γ ≤ tau l := by
  have hsub : (siftingProduct w).divisors.filter
      (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) ⊆ l.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2.1, hl.ne'⟩
  simpa only [psiErr, tau, ArithmeticFunction.sigma_zero_apply] using
    (show (((siftingProduct w).divisors.filter
      (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) ≤ (l.divisors.card : ℝ) by
        exact_mod_cast card_le_card hsub)

private theorem weighted_conv2_norm_le_tau_409b (a b g : ℕ → ℂ) (M N B C : ℝ) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ tau n ^ C) {k : ℕ} (hk : 0 < k) :
    ‖∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then a m * b n * g (k / (m * n)) else 0‖ ≤ tau k ^ (2 * B + C + 2) := by
  let S := (Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ×ˢ Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
    (fun u : ℕ × ℕ => u.1 * u.2 ∣ k)
  have hsub : S ⊆ k.divisors ×ˢ k.divisors := by
    intro u hu
    have hd := (mem_filter.mp hu).2
    apply mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨(dvd_mul_right u.1 u.2).trans hd, hk.ne'⟩,
      Nat.mem_divisors.mpr ⟨(dvd_mul_left u.2 u.1).trans hd, hk.ne'⟩⟩
  have htau : ∀ d, d ∣ k → tau d ≤ tau k := by
    intro d hd
    simp only [tau, ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hk.ne' hd)
  have htpos : 0 < tau k := by
    simp only [tau, ArithmeticFunction.sigma_zero_apply, Nat.cast_pos]
    exact card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne'⟩
  have hterm : ∀ u ∈ S, ‖a u.1 * b u.2 * g (k / (u.1 * u.2))‖ ≤ tau k ^ (B + B + C) := by
    intro u hu
    have hd := mem_product.mp (hsub hu)
    have ham : ‖a u.1‖ ≤ tau k ^ B :=
      (ha _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.1).1) hB)
    have hbn : ‖b u.2‖ ≤ tau k ^ B :=
      (hb _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.2).1) hB)
    have hdk : u.1 * u.2 ∣ k := (mem_filter.mp hu).2
    have hqk : k / (u.1 * u.2) ∣ k := Nat.div_dvd_of_dvd hdk
    have hq0 : 0 < k / (u.1 * u.2) := by
      apply Nat.div_pos (Nat.le_of_dvd hk hdk)
      have : u.1 * u.2 ≠ 0 := by intro he; simp [he] at hdk; omega
      omega
    have hgn : ‖g (k / (u.1 * u.2))‖ ≤ tau k ^ C :=
      (hg _ hq0).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ hqk) hC)
    rw [norm_mul, norm_mul, Real.rpow_add htpos, Real.rpow_add htpos]
    exact mul_le_mul (mul_le_mul ham hbn (norm_nonneg _) (Real.rpow_nonneg htpos.le _))
      hgn (norm_nonneg _) (by positivity)
  have heq : (∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then a m * b n * g (k / (m * n)) else 0) =
      ∑ u ∈ S, a u.1 * b u.2 * g (k / (u.1 * u.2)) := by
    simp [S, sum_filter, sum_product]
  rw [heq]
  calc _ ≤ ∑ u ∈ S, ‖a u.1 * b u.2 * g (k / (u.1 * u.2))‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S, tau k ^ (B + B + C) := sum_le_sum hterm
    _ ≤ ∑ u ∈ k.divisors ×ˢ k.divisors, tau k ^ (B + B + C) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.rpow_nonneg htpos.le _)
    _ = tau k ^ 2 * tau k ^ (B + B + C) := by
      simp [tau, ArithmeticFunction.sigma_zero_apply, pow_two]
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
      congr 1
      ring

private theorem conv2T_norm_le_tau_409b (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B) {k : ℕ} (hk : 0 < k) :
    ‖conv2T a b M N w γ k‖ ≤ tau k ^ (2 * B + 3) := by
  have hg : ∀ l, 0 < l → ‖psiTrunc l w γ‖ ≤ tau l ^ (1 : ℝ) := by
    intro l hl
    simpa only [Real.rpow_one] using psiTrunc_norm_le_tau_409b l hl w γ
  simpa only [conv2T, show 2 * B + 1 + 2 = 2 * B + 3 by ring] using
    weighted_conv2_norm_le_tau_409b a b (fun l => psiTrunc l w γ) M N B 1 hB (by norm_num) ha hb hg hk

private theorem conv2E_le_tau_409b (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B) {k : ℕ} (hk : 0 < k) :
    conv2E a b M N w γ k ≤ tau k ^ (2 * B + 3) := by
  have he0 : 0 ≤ conv2E a b M N w γ k := by
    unfold conv2E
    apply sum_nonneg
    intro m hm
    apply sum_nonneg
    intro n hn
    split_ifs
    · unfold psiErr
      positivity
    · positivity
  have ha' : ∀ n, ‖(‖a n‖ : ℂ)‖ ≤ tau n ^ B := by simpa using ha
  have hb' : ∀ n, ‖(‖b n‖ : ℂ)‖ ≤ tau n ^ B := by simpa using hb
  have hg : ∀ l, 0 < l → ‖(psiErr l w γ : ℂ)‖ ≤ tau l ^ (1 : ℝ) := by
    intro l hl
    rw [Complex.norm_of_nonneg (by unfold psiErr; positivity), Real.rpow_one]
    exact psiErr_le_tau_409b l hl w γ
  have h := weighted_conv2_norm_le_tau_409b (fun n => (‖a n‖ : ℂ)) (fun n => (‖b n‖ : ℂ))
    (fun l => (psiErr l w γ : ℂ)) M N B 1 hB (by norm_num) ha' hb' hg hk
  have heq : (∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then (‖a m‖ : ℂ) * (‖b n‖ : ℂ) * (psiErr (k / (m * n)) w γ : ℂ) else 0) =
      (conv2E a b M N w γ k : ℂ) := by
    simp only [conv2E, Complex.ofReal_sum]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    split_ifs <;> push_cast <;> rfl
  rw [heq, Complex.norm_of_nonneg he0] at h
  simpa only [show 2 * B + 1 + 2 = 2 * B + 3 by ring] using h

private theorem zero_rpow_le_max (B : ℝ) : (0 : ℝ) ^ B ≤ (0 : ℝ) ^ max B 0 := by
  rcases lt_trichotomy B 0 with h | h | h
  · rw [max_eq_right h.le, Real.zero_rpow h.ne]
    have h1 : (0 : ℝ) ^ (0 : ℝ) = 1 := by simp
    rw [h1]
    norm_num
  · subst h; simp
  · rw [max_eq_left h.le]

theorem leaf_trunc_coeff_bound (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then 0 else conv2T a b M N w γ k)‖ ≤ tau k ^ B' := by
  refine ⟨2 * max B 0 + 3, fun a b M N w γ ha hb k => ?_⟩
  have hB0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
  have ha0 : ∀ k, ‖a k‖ ≤ tau k ^ max B 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : tau 0 = 0 := by simp [tau]
      have h := ha 0
      rw [h0] at h ⊢
      exact h.trans (zero_rpow_le_max B)
    · exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le (tau_one_le hn) (le_max_left B 0))
  have hb0 : ∀ k, ‖b k‖ ≤ tau k ^ max B 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : tau 0 = 0 := by simp [tau]
      have h := hb 0
      rw [h0] at h ⊢
      exact h.trans (zero_rpow_le_max B)
    · exact (hb n).trans (Real.rpow_le_rpow_of_exponent_le (tau_one_le hn) (le_max_left B 0))
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hexp : (0 : ℝ) < 2 * max B 0 + 3 := by linarith
    have h0 : tau 0 = 0 := by simp [tau]
    rw [h0, Real.zero_rpow hexp.ne']
    simp
  · simpa only [if_neg hk.ne'] using conv2T_norm_le_tau_409b a b M N w γ (max B 0) hB0 ha0 hb0 hk

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
  refine ⟨2 * max B 0 + 3, fun a b M N w γ ha hb k => ?_⟩
  have hB0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
  have ha0 : ∀ n, ‖a n‖ ≤ tau n ^ max B 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : tau 0 = 0 := by simp [tau]
      have h := ha 0
      rw [h0] at h ⊢
      exact h.trans (zero_rpow_le_max B)
    · exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le (tau_one_le hn) (le_max_left B 0))
  have hb0 : ∀ n, ‖b n‖ ≤ tau n ^ max B 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : tau 0 = 0 := by simp [tau]
      have h := hb 0
      rw [h0] at h ⊢
      exact h.trans (zero_rpow_le_max B)
    · exact (hb n).trans (Real.rpow_le_rpow_of_exponent_le (tau_one_le hn) (le_max_left B 0))
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hexp : (0 : ℝ) < 2 * max B 0 + 3 := by linarith
    have h0 : tau 0 = 0 := by simp [tau]
    rw [h0, Real.zero_rpow hexp.ne']
    simp
  · have hE : conv2E a b M N w γ k ≤ tau k ^ (2 * max B 0 + 3) :=
      conv2E_le_tau_409b a b M N w γ (max B 0) hB0 ha0 hb0 hk
    have hnn : 0 ≤ conv2E a b M N w γ k := by
      unfold conv2E
      apply sum_nonneg
      intro m hm
      apply sum_nonneg
      intro n hn
      split_ifs
      · unfold psiErr
        positivity
      · positivity
    rw [if_neg hk.ne']
    rw [Complex.norm_of_nonneg hnn]
    exact hE

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
  refine ⟨Real.exp (max 1 (max 22500 ((100 * (A + 1)) ^ 2))), fun x hx => ?_⟩
  have ht : max 1 (max 22500 ((100 * (A + 1)) ^ 2)) ≤ L x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have ht1 : (1 : ℝ) ≤ L x := (le_max_left _ _).trans ht
  have h22500 : (22500 : ℝ) ≤ L x := by
    refine le_trans (le_trans (le_max_left (22500 : ℝ) ((100 * (A + 1)) ^ 2)) ?_) ht
    exact le_max_right 1 (max 22500 ((100 * (A + 1)) ^ 2))
  have h100 : (100 * (A + 1)) ^ 2 ≤ L x := by
    refine le_trans (le_trans (le_max_right (22500 : ℝ) ((100 * (A + 1)) ^ 2)) ?_) ht
    exact le_max_right 1 (max 22500 ((100 * (A + 1)) ^ 2))
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlogpos : 0 < L x := zero_lt_one.trans_le ht1
  set u : ℝ := L x ^ (1 / 2 : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hlogpos.le _
  have husq : u * u = L x := by
    rw [hu, ← Real.rpow_add hlogpos]
    norm_num
  have hsqrt : u = Real.sqrt (L x) := (Real.sqrt_eq_rpow (L x)).symm
  have hu150 : 150 ≤ u := by
    rw [hsqrt]
    calc (150 : ℝ) = Real.sqrt ((150 : ℝ) ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (L x) := Real.sqrt_le_sqrt (by linarith)
  have hu100 : 100 * (A + 1) ≤ u := by
    rw [hsqrt]
    calc 100 * (A + 1) = Real.sqrt ((100 * (A + 1)) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (L x) := Real.sqrt_le_sqrt h100
  have hthird : L x ^ (1 / 3 : ℝ) ≤ u :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have ha3 : 3 * L x ^ (1 / 3 : ℝ) ≤ 0.02 * L x := by
    nlinarith [hthird, hu150, hu0, husq]
  have hloglog : Real.log (L x) ≤ 2 * u := by
    have h := Real.log_le_rpow_div hlogpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have he : L x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * u := by
      rw [hu]
      ring
    linarith [h, he.le, he.ge]
  have hb2 : (A + 1) * Real.log (L x) ≤ 0.02 * L x := by
    nlinarith [hloglog, hu100, hu0, husq, hA]
  have key : 0.96 * L x + (A + 1) * Real.log (L x) ≤ L x - 3 * L x ^ (1 / 3 : ℝ) := by
    linarith [ha3, hb2]
  have hLHS : x ^ (0.96 : ℝ) = Real.exp (0.96 * L x) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    simp only [L]
    ring
  have hRHS : y1 x / L x ^ A = Real.exp (L x - 3 * L x ^ (1 / 3 : ℝ) - A * Real.log (L x)) := by
    have hy : y1 x = x * Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) := rfl
    rw [hy, Real.rpow_def_of_pos hlogpos, show x = Real.exp (L x) by
      rw [show L x = Real.log x from rfl, Real.exp_log hx0]]
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    simp only [L, Real.log_exp]
    ring
  rw [hLHS, hRHS, Real.exp_le_exp]
  have hlogLx : 0 ≤ Real.log (L x) := Real.log_nonneg ht1
  linarith [key, hlogLx]

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

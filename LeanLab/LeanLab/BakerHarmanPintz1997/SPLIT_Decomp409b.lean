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
import LeanLab.BakerHarmanPintz1997.CoefficientBounds

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
theorem leaf_trunc_coeff_bound (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then 0 else conv2T a b M N w γ k)‖ ≤ tau k ^ B' := by
  refine ⟨2 * max B 0 + 3, ?_⟩
  intro a b M N w γ ha hb k
  by_cases hk : k = 0
  · subst k
    simp [tau]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hB : 0 ≤ max B 0 := le_max_right _ _
    have htau : 1 ≤ tau k := by
      simp only [tau, sigma_zero_apply]
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0.ne'⟩
    have ha' : ∀ n, ‖a n‖ ≤ tau n ^ max B 0 := by
      intro n
      by_cases hn : n = 0
      · subst n
        simp [tau]
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        have htaun : 1 ≤ tau n := by
          simp only [tau, sigma_zero_apply]
          exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0.ne'⟩
        exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le htaun (le_max_left _ _))
    have hb' : ∀ n, ‖b n‖ ≤ tau n ^ max B 0 := by
      intro n
      by_cases hn : n = 0
      · subst n
        simp [tau]
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        have htaun : 1 ≤ tau n := by
          simp only [tau, sigma_zero_apply]
          exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0.ne'⟩
        exact (hb n).trans (Real.rpow_le_rpow_of_exponent_le htaun (le_max_left _ _))
    have hconv := conv2T_norm_le_tau a b M N w γ (max B 0) hB ha' hb' hk0
    have htau_le : tau k ^ (2 * max B 0 + 3) ≤ tau k ^ (2 * B + 3) :=
      Real.rpow_le_rpow_of_exponent_le htau (by gcongr <;> linarith)
    simpa only [if_neg hk] using hconv.trans htau_le

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
  refine ⟨2 * max B 0 + 3, ?_⟩
  intro a b M N w γ ha hb k
  by_cases hk : k = 0
  · subst k
    simp [tau]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hB : 0 ≤ max B 0 := le_max_right _ _
    have htau : 1 ≤ tau k := by
      simp only [tau, sigma_zero_apply]
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0.ne'⟩
    have ha' : ∀ n, ‖a n‖ ≤ tau n ^ max B 0 := by
      intro n
      by_cases hn : n = 0
      · subst n
        simp [tau]
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        have htaun : 1 ≤ tau n := by
          simp only [tau, sigma_zero_apply]
          exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0.ne'⟩
        exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le htaun (le_max_left _ _))
    have hb' : ∀ n, ‖b n‖ ≤ tau n ^ max B 0 := by
      intro n
      by_cases hn : n = 0
      · subst n
        simp [tau]
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        have htaun : 1 ≤ tau n := by
          simp only [tau, sigma_zero_apply]
          exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0.ne'⟩
        exact (hb n).trans (Real.rpow_le_rpow_of_exponent_le htaun (le_max_left _ _))
    have hconv := conv2E_le_tau a b M N w γ (max B 0) hB ha' hb' hk0
    have htau_le : tau k ^ (2 * max B 0 + 3) ≤ tau k ^ (2 * B + 3) :=
      Real.rpow_le_rpow_of_exponent_le htau (by gcongr <;> linarith)
    have hnorm : ‖((conv2E a b M N w γ k : ℝ) : ℂ)‖ = conv2E a b M N w γ k :=
      Complex.norm_of_nonneg (by unfold conv2E; positivity)
    simpa only [if_neg hk, hnorm] using hconv.trans htau_le

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
  sorry

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

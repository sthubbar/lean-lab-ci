/-
Unit U-1535, run 20261026T0004Z-24325. Second decomposition file for the weighted ternary
statement of State1535: the arc geometry from Dirichlet's theorem, the local factors of the
singular series, the singular integral count, the prime power excess, and the size of the
thresholds exp(exp(9.715)) for 1996 and exp(exp(11.503)) for 1989. Page references are to
Liu-Wang 2002, Acta Arith. 105, pp. 133-175, and to the 1996 abstract. The elementary leaves are proved.
The threshold transfer retains its explicit ternary hypothesis.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
AI wrote the task183 proofs, Codex, 2026-10-30.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.State1535

namespace LeanLab.Ternary.U1535

open LeanLab.Ternary

/-! ### Leaves -/

/-- LEAF. Unit U-1535. Dirichlet's approximation: for `Q ≥ 1` every real `α` has
`1 ≤ q ≤ Q` and an integer `a` with `|α - a/q| ≤ 1/(q(Q+1))`; Liu-Wang 2002 p. 144,
eq. 3.2. -/
theorem dirichlet_cover (α : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ∃ a : ℤ, |α - a / q| ≤ 1 / (q * ((Q : ℝ) + 1)) := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α (by omega : 0 < Q)
  refine ⟨r.den, r.pos, hden, r.num, ?_⟩
  simpa only [Rat.cast_def, mul_comm] using hr

/-- LEAF. Unit U-1535. Disjoint arcs: if `q, q' ≤ P`, `2P < Q` and `a/q ≠ a'/q'`, then
the arcs of radius `1/(qQ)` and `1/(q'Q)` around them are disjoint, since the centres are
more than the sum of the radii apart; Liu-Wang 2002 p. 144, below eq. 3.2. -/
theorem arcs_disjoint {P Q q q' : ℕ} {a a' : ℤ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqP : q ≤ P) (hq'P : q' ≤ P) (hPQ : 2 * P < Q) (hne : (a : ℝ) / q ≠ a' / q') :
    1 / ((q : ℝ) * Q) + 1 / ((q' : ℝ) * Q) < |(a : ℝ) / q - a' / q'| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hdet : a * (q' : ℤ) - a' * (q : ℤ) ≠ 0 := by
    intro h
    apply hne
    apply (div_eq_div_iff hq0.ne' hq'0.ne').mpr
    exact_mod_cast (sub_eq_zero.mp h)
  have hsep : (1 : ℝ) ≤ |(a : ℝ) * q' - a' * q| := by
    exact_mod_cast (Int.one_le_abs hdet)
  have hsum : (q : ℝ) + q' < Q := by
    exact_mod_cast (show q + q' < Q by omega)
  have heq : |(a : ℝ) / q - a' / q'| =
      |(a : ℝ) * q' - a' * q| / ((q : ℝ) * q') := by
    rw [div_sub_div _ _ hq0.ne' hq'0.ne', abs_div, abs_of_pos (mul_pos hq0 hq'0), mul_comm (q : ℝ) (a' : ℝ)]
  rw [heq]
  apply (lt_div_iff₀ (mul_pos hq0 hq'0)).mpr
  have hmul : (1 / ((q : ℝ) * Q) + 1 / ((q' : ℝ) * Q)) * (q * q') =
      ((q : ℝ) + q') / Q := by
    field_simp [hq0.ne', hq'0.ne', hQ0.ne']
    ring
  rw [hmul]
  exact ((div_lt_one hQ0).mpr hsum).trans_le hsep

/-- LEAF. Unit U-1535. Ramanujan's sum at a prime: the sum of `e(aN/p)` over
`1 ≤ a ≤ p - 1` is `p - 1` if `p` divides `N` and `-1` otherwise; the local factor of the
singular series, Liu-Wang 2002 p. 145, eq. 3.14 with principal character. -/
theorem ramanujan_prime (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∑ a ∈ Finset.Ico 1 p, Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * N / p : ℝ) : ℂ)) =
      if p ∣ N then ((p : ℂ) - 1) else -1 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((N : ℂ) / p))
  have hterm (a : ℕ) :
      Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * N / p : ℝ) : ℂ)) = z ^ a := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  by_cases hdiv : p ∣ N
  · rw [ite_eq_left hdiv]
    have hz : z = 1 := by
      apply Complex.exp_eq_one_iff.mpr
      obtain ⟨k, hk⟩ := hdiv
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
    simp [hz, Nat.cast_sub hp.one_le]
  · rw [ite_eq_right hdiv]
    have hroot : IsPrimitiveRoot z p :=
      Complex.isPrimitiveRoot_exp_of_coprime N p hp.ne_zero
        (hp.coprime_iff_not_dvd.mpr hdiv).symm
    rw [Finset.sum_Ico_eq_sub _ hp.one_le, hroot.geom_sum_eq_zero hp.one_lt]
    simp

/-- LEAF. Unit U-1535. The singular integral count: the number of ordered triples of
positive integers with sum `N` is `(N - 1)(N - 2)/2`; the main term of the major arc
integral, Liu-Wang 2002 p. 156, Lemma 4.3. -/
theorem triple_count (N : ℕ) :
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = N)).card = (N - 1) * (N - 2) / 2 := by
  have hbij : ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = N)).card =
      (((Finset.Icc 1 (N - 1)) ×ˢ Finset.Icc 1 (N - 1)).filter
        (fun x : ℕ × ℕ => x.1 < x.2)).card := by
    apply Finset.card_bij (fun x _ => (x.1, x.1 + x.2.1))
    · rintro ⟨a, b, c⟩ hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
      omega
    · rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy heq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx hy
      simp only [Prod.mk.injEq] at heq ⊢
      omega
    · rintro ⟨a, b⟩ hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
      refine ⟨(a, b - a, N - b), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        omega
      · dsimp at hx ⊢
        congr 1; omega
  rw [hbij, Finset.card_product_filter_lt]
  simp only [Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_two_right]
  congr 2

/-- Finite telescoping comparison for the local factors. Derived from the singular
series factors on Liu and Wang 2002 page 151. -/
theorem singular_tail_product (X : ℕ) (hX : 10 ≤ X) :
    (∏ p ∈ Finset.Icc 11 X, (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      9 * X / (10 * ((X : ℝ) - 1)) := by
  induction X, hX using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    have hn0 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn1 : (n : ℝ) ≠ 0 := by linarith
    field_simp [hn0, hn1]
    ring

/-- LEAF. Unit U-1535. Singular series, dividing primes: the product of
`1 - 1/(p - 1)^2` over primes `3 ≤ p ≤ X` dividing `N` is at least `0.6`, since the full
product over odd primes is the twin prime constant `0.6601...`; Liu-Wang 2002 p. 156,
Lemma 4.3. -/
theorem singular_partial (N X : ℕ) :
    (0.6 : ℝ) ≤ ∏ p ∈ (Finset.Icc 3 X).filter (fun p => p.Prime ∧ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  let Y := max X 10
  let T := ({3, 5, 7} : Finset ℕ) ∪ Finset.Icc 11 Y
  have hY : 10 ≤ Y := le_max_right _ _
  have hY' : (10 : ℝ) ≤ Y := by exact_mod_cast hY
  have hT : ∀ p ∈ T, 3 ≤ p := by
    intro p hp
    simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Icc] at hp
    omega
  have hsub : (Finset.Icc 3 X).filter (fun p => p.Prime ∧ p ∣ N) ⊆ T := by
    intro p hp
    obtain ⟨hpI, hpprime, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp3, hpX⟩ := Finset.mem_Icc.mp hpI
    by_cases hp11 : 11 ≤ p
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨hp11, hpX.trans (le_max_left _ _)⟩)
    · have hsmall : p = 3 ∨ p = 5 ∨ p = 7 := by
        interval_cases p <;> norm_num at *
      exact Finset.mem_union_left _ (by simpa using hsmall)
  have hcompare := Finset.prod_le_prod_of_subset_of_le_one₀
    (f := fun p : ℕ => (1 - 1 / ((p : ℝ) - 1) ^ 2)) hsub
    (fun p hp => by
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hT p hp
      have hp1 : 0 < (p : ℝ) - 1 := by linarith
      have hsq : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have := (div_le_one (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)).mpr hsq
      linarith)
    (fun p hp _ => by
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hT p hp
      have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith)
  have hdisj : Disjoint ({3, 5, 7} : Finset ℕ) (Finset.Icc 11 Y) := by
    simp [Finset.disjoint_left]
  have hprod : (∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      (175 / 256 : ℝ) * (9 * Y / (10 * ((Y : ℝ) - 1))) := by
    rw [Finset.prod_union hdisj, singular_tail_product Y hY]
    norm_num
  have htail : (9 / 10 : ℝ) ≤ 9 * Y / (10 * ((Y : ℝ) - 1)) := by
    have hYm : 0 < (Y : ℝ) - 1 := by linarith
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  apply le_trans ?_ hcompare
  rw [hprod]
  nlinarith

/-- LEAF. Unit U-1535. Singular series, coprime primes: the product of `1 + 1/(p - 1)^3`
over primes `p ≤ X` not dividing `N` is at least `1`; Liu-Wang 2002 p. 156, Lemma 4.3. -/
theorem singular_coprime_factor (N X : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
      (1 + 1 / ((p : ℝ) - 1) ^ 3) := by
  apply Finset.one_le_prod₀
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith
  have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by positivity
  linarith

/-- LEAF. Unit U-1535. Prime powers: `ψ(N) - θ(N) ≤ 2 √N log N`, the cost of passing
from von Mangoldt weights to prime weights; Liu-Wang 2002 p. 145, below eq. 3.10. -/
theorem primePower_excess (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n - theta N ≤
      2 * Real.sqrt N * Real.log N := by
  by_cases hN : N = 0
  · subst N
    norm_num [theta, Finset.sum_filter]
  have hpsi : Chebyshev.psi (N : ℝ) =
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]
  have htheta : Chebyshev.theta (N : ℝ) = theta N := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]
    rfl
  rw [← hpsi, ← htheta]
  exact Chebyshev.psi_sub_theta_le (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN))

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

/-- LEAF. Unit U-1535. Size of the 1996 threshold, upper side: `exp(exp(9.715)) ≤ 10^7194`;
the abstract gives `exp(exp(9.715)) ≈ 10^7194`, and `exp(9.715)/log 10 ≈ 7193.75`. -/
theorem exp_exp_upper : Real.exp (Real.exp 9.715) ≤ (10 : ℝ) ^ (7194 : ℕ) := by
  have h1 : Real.exp (9.715 : ℝ) ≤ (33129 / 2 : ℝ) := by
    have he_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have ht1 : Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := by
      rw [← Real.exp_mul, one_mul]
    have ht2 : (Real.exp 1) ^ (9.715 : ℝ) ≤ (2.7182818286 : ℝ) ^ (9.715 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) he_lt.le (by positivity)
    have ht3 : (2.7182818286 : ℝ) ^ (9.715 : ℝ) ≤ 33129 / 2 := by
      have h_rpow : (2.7182818286 : ℝ) ^ (9.715 : ℝ) = ((2.7182818286 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        have : (9.715 : ℝ) = (1943 : ℝ) * (200 : ℝ)⁻¹ := by norm_num
        rw [this, Real.rpow_mul (by positivity)]
        congr 1
        exact Real.rpow_natCast _ _
      rw [h_rpow]
      have h_num : (13591409143 : ℕ) ^ 1943 * 2 ^ 200 ≤ (33129 : ℕ) ^ 200 * (5000000000 : ℕ) ^ 1943 := by
        decide
      have h1 : (13591409143 : ℝ) ^ 1943 * 2 ^ 200 ≤ (33129 : ℝ) ^ 200 * (5000000000 : ℝ) ^ 1943 := by
        exact_mod_cast h_num
      have h2 : (2.7182818286 : ℝ) ^ (1943 : ℕ) = (13591409143 : ℝ) ^ (1943 : ℕ) / (5000000000 : ℝ) ^ (1943 : ℕ) := by
        rw [← div_pow]
        norm_num
      have h3 : (13591409143 : ℝ) ^ (1943 : ℕ) / (5000000000 : ℝ) ^ (1943 : ℕ) ≤ (33129 / 2 : ℝ) ^ (200 : ℕ) := by
        rw [div_le_iff₀ (by positivity)]
        have h2' : (33129 / 2 : ℝ) ^ (200 : ℕ) = (33129 : ℝ) ^ (200 : ℕ) / (2 : ℝ) ^ 200 := by
          exact div_pow (33129 : ℝ) 2 200
        rw [h2']
        have ht : (33129 : ℝ) ^ 200 / 2 ^ 200 * 5000000000 ^ 1943 = (33129 : ℝ) ^ 200 * 5000000000 ^ 1943 / 2 ^ 200 := by ring
        rw [ht]
        have h1' : (13591409143 : ℝ) ^ (1943 : ℕ) * (2 : ℝ) ^ 200 ≤ (33129 : ℝ) ^ (200 : ℕ) * (5000000000 : ℝ) ^ (1943 : ℕ) := by exact h1
        exact (le_div_iff₀ (by positivity)).mpr h1'
      have h4 : (2.7182818286 : ℝ) ^ (1943 : ℕ) ≤ (33129 / 2 : ℝ) ^ (200 : ℕ) := by
        exact h2.le.trans h3
      have h5 : ((2.7182818286 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) ≤ ((33129 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) h4 (by positivity)
      have h6 : ((33129 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) = (33129 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by norm_num), Real.rpow_one]
      exact h5.trans h6.le
    calc
      Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := ht1
      _ ≤ (2.7182818286 : ℝ) ^ (9.715 : ℝ) := ht2
      _ ≤ 33129 / 2 := ht3
  have h2 : (33129 / 2 : ℝ) ≤ 7194 * Real.log 10 := by
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
    have ht : Real.log 10 = Real.log 2 + Real.log 5 := by
      have : (10 : ℝ) = 2 * 5 := by norm_num
      rw [this, Real.log_mul (by positivity) (by positivity)]
    rw [ht]
    calc (33129 / 2 : ℝ) ≤ 7194 * (0.6931471803 + 1.6094379123) := by norm_num
      _ ≤ 7194 * (Real.log 2 + Real.log 5) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  calc
    Real.exp (Real.exp 9.715) ≤ Real.exp (33129 / 2) := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp (7194 * Real.log 10) := Real.exp_le_exp.mpr h2
    _ = Real.exp (Real.log ((10 : ℝ) ^ (7194 : ℕ))) := by
      rw [Real.log_pow]; push_cast; ring
    _ = (10 : ℝ) ^ (7194 : ℕ) := Real.exp_log (by positivity)

/-- LEAF. Unit U-1535. Size of the 1996 threshold, lower side: `10^7193 ≤ exp(exp(9.715))`;
abstract, `exp(9.715)/log 10 ≈ 7193.75`. -/
theorem exp_exp_lower : (10 : ℝ) ^ (7193 : ℕ) ≤ Real.exp (Real.exp 9.715) := by
  have h1 : (16562.5 : ℝ) ≤ Real.exp (9.715 : ℝ) := by
    have he_gt : 2.7182818283 ≤ Real.exp 1 := by
      exact Real.exp_one_gt_d9.le
    have ht1 : Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := by
      rw [← Real.exp_mul, one_mul]
    have ht2 : (2.7182818283 : ℝ) ^ (9.715 : ℝ) ≤ (Real.exp 1) ^ (9.715 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) he_gt (by positivity)
    have ht3 : 16562.5 ≤ (2.7182818283 : ℝ) ^ (9.715 : ℝ) := by
      have h_rpow : (2.7182818283 : ℝ) ^ (9.715 : ℝ) = ((2.7182818283 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        have : (9.715 : ℝ) = (1943 : ℝ) * (200 : ℝ)⁻¹ := by norm_num
        rw [this, Real.rpow_mul (by positivity)]
        congr 1
        exact Real.rpow_natCast _ _
      rw [h_rpow]
      have h_num : (33125 : ℕ) ^ 200 * (10000000000 : ℕ) ^ 1943 ≤ (27182818283 : ℕ) ^ 1943 * 2 ^ 200 := by
        decide
      have h1 : (33125 : ℝ) ^ 200 * (10000000000 : ℝ) ^ 1943 ≤ (27182818283 : ℝ) ^ 1943 * 2 ^ 200 := by
        exact_mod_cast h_num
      have h2 : (2.7182818283 : ℝ) ^ (1943 : ℕ) = (27182818283 : ℝ) ^ (1943 : ℕ) / (10000000000 : ℝ) ^ (1943 : ℕ) := by
        rw [← div_pow]
        norm_num
      have h3 : (33125 / 2 : ℝ) ^ (200 : ℕ) ≤ (27182818283 : ℝ) ^ (1943 : ℕ) / (10000000000 : ℝ) ^ (1943 : ℕ) := by
        have h2' : (33125 / 2 : ℝ) ^ (200 : ℕ) = (33125 : ℝ) ^ (200 : ℕ) / (2 : ℝ) ^ 200 := by
          exact div_pow (33125 : ℝ) 2 200
        rw [h2']
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact h1
      have h4 : (33125 / 2 : ℝ) ^ (200 : ℕ) ≤ (2.7182818283 : ℝ) ^ (1943 : ℕ) := by
        exact h3.trans h2.symm.le
      have h5 : ((33125 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) ≤ ((2.7182818283 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) h4 (by positivity)
      have h6 : ((33125 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) = (33125 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by norm_num), Real.rpow_one]
      have ht : (16562.5 : ℝ) = 33125 / 2 := by norm_num
      rw [ht]
      exact h6.symm.le.trans h5
    calc
      16562.5 ≤ (2.7182818283 : ℝ) ^ (9.715 : ℝ) := ht3
      _ ≤ (Real.exp 1) ^ (9.715 : ℝ) := ht2
      _ = Real.exp 9.715 := ht1.symm
  have h2 : 7193 * Real.log 10 ≤ 16562.5 := by
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hl5 : Real.log 5 < 1.6094379126 := Real.log_five_lt_d9
    have ht : Real.log 10 = Real.log 2 + Real.log 5 := by
      have : (10 : ℝ) = 2 * 5 := by norm_num
      rw [this, Real.log_mul (by positivity) (by positivity)]
    rw [ht]
    calc 7193 * (Real.log 2 + Real.log 5) ≤ 7193 * (0.6931471808 + 1.6094379126) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ 16562.5 := by norm_num
  calc
    (10 : ℝ) ^ (7193 : ℕ) = Real.exp (Real.log ((10 : ℝ) ^ (7193 : ℕ))) := (Real.exp_log (by positivity)).symm
    _ = Real.exp (7193 * Real.log 10) := by
      rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.exp 16562.5 := Real.exp_le_exp.mpr h2
    _ ≤ Real.exp (Real.exp 9.715) := Real.exp_le_exp.mpr h1

set_option exponentiation.threshold 12000 in
/-- LEAF. Unit U-1535. Size of the 1989 threshold: `10^43000 ≤ exp(exp(11.503))`;
Liu-Wang 2002 p. 134 gives `exp(exp(11.503)) = 10^43000.5...`. -/
theorem exp_exp_1989 : (10 : ℝ) ^ (43000 : ℕ) ≤ Real.exp (Real.exp 11.503) := by
  have hnum : (99012 : ℕ) ^ 1000 * (10000000000 : ℕ) ^ 11503 ≤
      (27182818283 : ℕ) ^ 11503 := by decide
  have hpow : (99012 : ℝ) ^ 1000 ≤ (2.7182818283 : ℝ) ^ (11503 : ℕ) := by
    have hcast : (99012 : ℝ) ^ 1000 * (10000000000 : ℝ) ^ 11503 ≤
        (27182818283 : ℝ) ^ 11503 := by exact_mod_cast hnum
    have heq : (2.7182818283 : ℝ) ^ (11503 : ℕ) =
        (27182818283 : ℝ) ^ (11503 : ℕ) / (10000000000 : ℝ) ^ (11503 : ℕ) := by
      rw [← div_pow]
      congr 1
      norm_num
    rw [heq]
    exact (le_div_iff₀ (by positivity)).mpr hcast
  have hlow : (99012 : ℝ) ≤ Real.exp 11.503 := by
    apply le_of_pow_le_pow_left₀ (n := 1000) (by norm_num) (Real.exp_pos _).le
    calc
      (99012 : ℝ) ^ 1000 ≤ (2.7182818283 : ℝ) ^ (11503 : ℕ) := hpow
      _ ≤ (Real.exp 1) ^ (11503 : ℕ) :=
        pow_le_pow_left₀ (by positivity) Real.exp_one_gt_d9.le _
      _ = (Real.exp 11.503) ^ (1000 : ℕ) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        norm_num
  have hlog : (43000 : ℝ) * Real.log 10 ≤ 99012 := by
    have h2 := Real.log_two_lt_d9
    have h5 := Real.log_five_lt_d9
    have heq : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [heq]
    linarith
  calc
    (10 : ℝ) ^ (43000 : ℕ) = Real.exp (Real.log ((10 : ℝ) ^ (43000 : ℕ))) :=
      (Real.exp_log (by positivity)).symm
    _ = Real.exp (43000 * Real.log 10) := by
      rw [Real.log_pow]
      norm_num
    _ ≤ Real.exp 99012 := Real.exp_le_exp.mpr hlog
    _ ≤ Real.exp (Real.exp 11.503) := Real.exp_le_exp.mpr hlow

/-! ### Assemblies, zero sorry of their own -/

/-- Off the major arcs with `q ≤ P` the Dirichlet denominator exceeds `P`: the minor arc
dichotomy. -/
theorem minor_q_large {α : ℝ} {P Q : ℕ} (hQ : 1 ≤ Q)
    (hα : ∀ q : ℕ, 1 ≤ q → q ≤ P → ∀ a : ℤ, 1 / (q * ((Q : ℝ) + 1)) < |α - a / q|) :
    ∃ q : ℕ, P < q ∧ q ≤ Q ∧ ∃ a : ℤ, |α - a / q| ≤ 1 / (q * ((Q : ℝ) + 1)) := by
  obtain ⟨q, h1, h2, a, ha⟩ := dirichlet_cover α Q hQ
  refine ⟨q, ?_, h2, a, ha⟩
  by_contra hle
  exact absurd ha (not_le.mpr (hα q h1 (not_lt.mp hle) a))

/-- The 1996 threshold lies between `10^7193` and `10^7194`. -/
theorem chenWang_size :
    (10 : ℝ) ^ (7193 : ℕ) ≤ Real.exp (Real.exp 9.715) ∧
      Real.exp (Real.exp 9.715) ≤ (10 : ℝ) ^ (7194 : ℕ) :=
  ⟨exp_exp_lower, exp_exp_upper⟩

/-- Chen-Wang's bound in powers of ten: every odd `N ≥ 10^7194` is a sum of three primes.
CONDITIONAL ON the ternary hypothesis. -/
theorem ternaryAbove_10pow_of_chenWang (h : TernaryAbove (Real.exp (Real.exp 9.715))) :
    TernaryAbove ((10 : ℝ) ^ (7194 : ℕ)) :=
  ternaryAbove_mono exp_exp_upper h

/-- The 1996 threshold improves the 1989 one by a factor of at least `10^35806`:
`exp(exp(9.715)) · 10^35806 ≤ exp(exp(11.503))`. -/
theorem threshold_gap :
    Real.exp (Real.exp 9.715) * (10 : ℝ) ^ (35806 : ℕ) ≤ Real.exp (Real.exp 11.503) := by
  have h1 := mul_le_mul_of_nonneg_right exp_exp_upper
    (show (0 : ℝ) ≤ (10 : ℝ) ^ (35806 : ℕ) by positivity)
  rw [← pow_add] at h1
  exact h1.trans exp_exp_1989

/-- The closed major arc intervals are disjoint. Liu and Wang 2002 page 144,
below equation 3.2. -/
theorem major_arc_intervals_disjoint {P Q q q' : ℕ} {a a' : ℤ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : q ≤ P) (hq'P : q' ≤ P)
    (hPQ : 2 * P < Q) (hne : (a : ℝ) / q ≠ a' / q') :
    Disjoint
      (Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * Q))
        ((a : ℝ) / q + 1 / ((q : ℝ) * Q)))
      (Set.Icc ((a' : ℝ) / q' - 1 / ((q' : ℝ) * Q))
        ((a' : ℝ) / q' + 1 / ((q' : ℝ) * Q))) := by
  have hsep := arcs_disjoint hq hq' hqP hq'P hPQ hne
  simpa only [Real.closedBall_eq_Icc] using
    Metric.closedBall_disjoint_closedBall
      (x := (a : ℝ) / q) (y := (a' : ℝ) / q')
      (δ := 1 / ((q : ℝ) * Q)) (ε := 1 / ((q' : ℝ) * Q))
      (by simpa only [Real.dist_eq] using hsep)

/-- The factor at two doubles the coprime product for odd N. Derived from the
local product on Liu and Wang 2002 page 151 before equation 4.8. -/
theorem singular_coprime_factor_two (N X : ℕ) (hN : Odd N) (hX : 2 ≤ X) :
    (2 : ℝ) ≤ ∏ p ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
      (1 + 1 / ((p : ℝ) - 1) ^ 3) := by
  have hmem : 2 ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, hN.not_two_dvd_nat⟩
  have hprod := Finset.prod_le_prod_of_subset_of_one_le₀
    (f := fun p : ℕ => (1 + 1 / ((p : ℝ) - 1) ^ 3))
    (s := ({2} : Finset ℕ))
    (t := (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
    (Finset.singleton_subset_iff.mpr hmem)
    (by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      norm_num)
    (fun p hp _ => by
      have hprime := (Finset.mem_filter.mp hp).2.1
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith
      have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by positivity
      linarith)
  norm_num at hprod ⊢
  exact hprod

/-- The finite singular product for odd N is bounded away from zero. Derived
from the factorization on Liu and Wang 2002 page 151 before equation 4.8. -/
theorem singular_finite_lower (N X : ℕ) (hN : Odd N) (hX : 2 ≤ X) :
    (6 / 5 : ℝ) ≤ ∏ p ∈ (Finset.range (X + 1)).filter Nat.Prime,
      (if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
       else 1 + 1 / ((p : ℝ) - 1) ^ 3) := by
  rw [Finset.prod_ite]
  have hdivset : ((Finset.range (X + 1)).filter Nat.Prime).filter (fun p => p ∣ N) =
      (Finset.Icc 3 X).filter (fun p => p.Prime ∧ p ∣ N) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpX, hp⟩, hpd⟩
      have hp2 := hp.two_le
      have hpne : p ≠ 2 := by
        rintro rfl
        exact hN.not_two_dvd_nat hpd
      exact ⟨⟨by omega, by omega⟩, hp, hpd⟩
    · rintro ⟨⟨hp3, hpX⟩, hp, hpd⟩
      exact ⟨⟨by omega, hp⟩, hpd⟩
  have hcopset : ((Finset.range (X + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ N) =
      (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬p ∣ N) := by
    ext p
    simp [and_assoc]
  rw [hdivset, hcopset]
  have hdiv := singular_partial N X
  have hcop := singular_coprime_factor_two N X hN hX
  have hbound := mul_le_mul hdiv hcop (by norm_num : (0 : ℝ) ≤ 2) (by linarith)
  norm_num at hbound ⊢
  exact hbound

/-- The local factor at two vanishes for even N. Derived from the singular
product on Liu and Wang 2002 page 151 before equation 4.8. -/
theorem singular_finite_even_zero (N X : ℕ) (hN : 2 ∣ N) (hX : 2 ≤ X) :
    (∏ p ∈ (Finset.range (X + 1)).filter Nat.Prime,
      (if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2
       else 1 + 1 / ((p : ℝ) - 1) ^ 3)) = 0 := by
  apply Finset.prod_eq_zero (i := 2)
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  · norm_num [hN]

/-- Liu and Wang 2002 page 146 equation 3.22, with the parameter N explicit. -/
noncomputable def J (N : ℕ) (η : ℝ) : ℂ :=
  ∫ t in (0.001 * N : ℝ)..N, Complex.exp (2 * Real.pi * Complex.I * η * t)

/-- Liu and Wang 2002 page 146 equation 3.22 at zero frequency. -/
theorem J_zero (N : ℕ) : J N 0 = (0.999 * N : ℝ) := by
  simp [J, Complex.real_smul]
  ring

/-- The first bound in Liu and Wang 2002 page 149 equation 4.1. -/
theorem norm_J_le_length (N : ℕ) (η : ℝ) : ‖J N η‖ ≤ 0.999 * N := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
    (a := (0.001 * N : ℝ)) (b := (N : ℝ))
    (f := fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * η * t))
    (fun t _ => by simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])
  have heq : (N : ℝ) - 0.001 * N = 0.999 * N := by ring
  rw [heq, abs_of_nonneg (by positivity), one_mul] at h
  exact h

/-- The oscillatory bound in Liu and Wang 2002 page 149 equation 4.1.
The nonzero frequency hypothesis makes the reciprocal interpretation explicit. -/
theorem norm_J_le_reciprocal (N : ℕ) {η : ℝ} (hη : η ≠ 0) :
    ‖J N η‖ ≤ (Real.pi * |η|)⁻¹ := by
  let c : ℂ := 2 * Real.pi * Complex.I * η
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) (by exact_mod_cast hη)
  have hcnorm : ‖c‖ = 2 * Real.pi * |η| := by
    simp [c, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hformula : J N η =
      (Complex.exp (c * N) - Complex.exp (c * (0.001 * N : ℝ))) / c := by
    simpa only [J, Complex.ofReal_natCast] using
      (integral_exp_mul_complex (a := (0.001 * N : ℝ)) (b := (N : ℝ)) hc)
  rw [hformula, norm_div]
  have hnum : ‖Complex.exp (c * N) - Complex.exp (c * (0.001 * N : ℝ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (c * N)‖ + ‖Complex.exp (c * (0.001 * N : ℝ))‖ := norm_sub_le _ _
      _ = 2 := by norm_num [c, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  calc
    _ ≤ 2 / ‖c‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = (Real.pi * |η|)⁻¹ := by
      rw [hcnorm]
      field_simp

/-- Liu and Wang 2002 page 149 equation 4.1 for nonzero frequency. -/
theorem norm_J_le_min (N : ℕ) {η : ℝ} (hη : η ≠ 0) :
    ‖J N η‖ ≤ min (0.999 * (N : ℝ)) (Real.pi * |η|)⁻¹ :=
  le_min (norm_J_le_length N η) (norm_J_le_reciprocal N hη)

/-- The exact normalized simplex area in Liu and Wang 2002 page 150 equation 4.3. -/
theorem singular_simplex_area :
    (∫ x in (0.001 : ℝ)..0.998, ∫ _y in (0.001 : ℝ)..(0.999 - x), (1 : ℝ)) =
      0.997 ^ 2 / 2 := by
  have hinner (x : ℝ) : (∫ _y in (0.001 : ℝ)..(0.999 - x), (1 : ℝ)) = 0.998 - x := by
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  norm_num

end LeanLab.Ternary.U1535

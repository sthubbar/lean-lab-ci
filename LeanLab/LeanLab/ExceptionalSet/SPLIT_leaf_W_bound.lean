/-
Split of the sealed statement `leaf_W_bound` of `LeanLab.ExceptionalSet.KaracubaSplit`: the bound
on `W(a) = Σ_{y,z ≤ M} e(f(a + yz))`, `M = [P^{c1/2 - 1/(2n²(n+1))}]`, that the case `n ≥ n0` of
the proof of the source's Theorem 1 establishes on p. 245-248.

The statement to be split asks, for positive `c0, ..., c4` with `c0 < 1`, `c1 < 1`, `c2 + c4 < c1`,
for constants `A, γ, cc > 0` such that under the hypotheses of `KarHyp`, for `n ≥ karN0` and
`P ≥ exp(cc n²)` and every `a` in `[N, N+P-M²]`,

  ‖W(a)‖ ≤ A (M+1)² P^{-γ/n²}.

The proof of the source has three separable parts, and the split follows them.

* Taylor's formula to order `n` at the point `a`: the phase `f(a + yz)` is replaced by its Taylor
  polynomial of degree `n` at `a`, and the Lagrange remainder is bounded by the one derivative bound
  that `KarHyp` states, `|f^{(n+1)}/(n+1)!| ≤ P^{-c1(n+1)}`, together with `yz ≤ M² ≤ P^{c1-1/(n²(n+1))}`,
  which is exactly where the correction `-1/(2n²(n+1))` in `M` is spent. The error per term is
  `P^{-1/n²}`, and there are `(M+1)²` terms. This step uses no cancellation and is the first leaf.

* The Taylor polynomial sum, i.e. `Σ_{y,z} e(f(a) + Σ_{2 ≤ j ≤ n} f^{(j)}(a)/j! (yz)^j)`, is small:
  this is where the mean value theorem, the bound on `Σ min(U, 1/(αx+β))` and Holder's inequality
  enter, and it is the analytic core of the argument, the second leaf. Its exponent is left in the
  crude form produced by bounding the two integers `l` and `k` of that argument from above: with
  `ρ ≤ min(c1/3, c3, c4)` and `L = log(8/(ρ c0²))`, `l ≤ n L` and `k ≤ n²(4 + L²)`, so the exponent
  `ρ (s_1 + ... + s_r)/(8k²)` with `s_1 + ... + s_r ≥ c0² n²/4` is at least
  `ρ c0²/(32 n² (4 + L²)²)`. Stating the weaker exponent keeps this leaf weaker than the paper's
  display (8) and removes the choice of `l` from the assembly.

* The arithmetic that turns the two powers of `P` into one: with `γ = ρ c0²/(64(4+L²)²)` one has
  `γ ≤ 1`, so `P^{-1/n²} ≤ P^{-γ/n²}`, and `γ/n² ≤ ρ c0²/(32 n² (4+L²)²)`, so also
  `P^{-ρc0²/(32n²(4+L²)²)} ≤ P^{-γ/n²}`. This needs only `1 ≤ P` and the monotonicity of `x ↦ P^x`,
  and it is proved in the assembly, not assumed.

Degenerate values: `M = 0` is allowed and then both leaves are the identity `W(a) = e(f(a))`; the
Taylor sum's `yz = 0` term is `e(f(a))` in both leaves, so the difference is `0`. `n ≥ 2` is a
hypothesis of the statement, so `P^{-1/n²}` is not `P^{-1/0}`; `P ≥ 1` makes `P^x` monotone in `x`.
`ρ, c0 > 0` keep the exponents positive, and `4 + L² ≥ 4` keeps every denominator away from zero.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### First leaf: the Taylor reduction -/

/-! ### The Lipschitz bound on `eC` -/

/-- `eC s = exp (I * (2π s))`, the form in which Mathlib's trigonometric lemmas apply. -/
private theorem leafW_eC_eq (s : ℝ) : eC s = Complex.exp (Complex.I * ((2 * Real.pi * s : ℝ) : ℂ)) := by
  simp only [eC]
  congr 1
  push_cast
  ring

/-- `‖eC s - 1‖ ≤ 2π|s|`: the two points of the unit circle are at most the arc length apart. -/
private theorem leafW_norm_eC_sub_one_le (s : ℝ) : ‖eC s - 1‖ ≤ 2 * Real.pi * |s| := by
  rw [leafW_eC_eq, Complex.norm_exp_I_mul_ofReal_sub_one]
  have harg : 2 * Real.pi * s / 2 = Real.pi * s := by ring
  rw [harg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h1 := Real.abs_sin_le_abs (x := Real.pi * s)
  have h2 : |Real.pi * s| = Real.pi * |s| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [h2] at h1
  linarith

/-- The two points `eC u`, `eC v` differ by at most `2π` times the distance of `u`, `v`. -/
private theorem leafW_eC_sub_le (u v : ℝ) : ‖eC u - eC v‖ ≤ 2 * Real.pi * |u - v| := by
  have h : eC u - eC v = eC v * (eC (u - v) - 1) := by
    have hmul : eC v * eC (u - v) = eC u := by
      simp only [eC, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [mul_sub, mul_one, hmul]
  rw [h, norm_mul]
  have hv : ‖eC v‖ = 1 := by
    rw [leafW_eC_eq, Complex.norm_exp_I_mul_ofReal]
  rw [hv, one_mul]
  exact leafW_norm_eC_sub_one_le (u - v)

/-! ### `taylorWithinEval` written out -/

/-- The Taylor polynomial of order `n` of `f` at `a`, evaluated at `x`, is
`f a + Σ_{j=1}^{n} f^{(j)}(a)/j! (x - a)^j` once the derivatives can be taken on an open set
containing `a`; the `j = 0` term is `f a`. -/
private theorem leafW_taylor_eq_explicit {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} {a x : ℝ}
    (hUo : IsOpen U) (hC : ContDiffOn ℝ (n + 1) f U) (haU : a ∈ U) (hax : a < x) :
    taylorWithinEval f n (Set.uIcc a x) a x
      = f a + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f a / (j.factorial : ℝ) * (x - a) ^ j := by
  have hca : ContDiffAt ℝ (n + 1) f a := hC.contDiffAt (hUo.mem_nhds haU)
  have huniq : UniqueDiffOn ℝ (Set.uIcc a x) := by
    rw [Set.uIcc_of_le hax.le]
    exact uniqueDiffOn_Icc hax
  have hmem : a ∈ Set.uIcc a x := by
    rw [Set.uIcc_of_le hax.le]
    exact ⟨le_rfl, hax.le⟩
  have hsum : ∑ j ∈ Finset.Icc 1 n, iteratedDeriv j f a / (j.factorial : ℝ) * (x - a) ^ j
      = ∑ k ∈ Finset.range n,
          iteratedDeriv (k + 1) f a / ((k + 1).factorial : ℝ) * (x - a) ^ (k + 1) := by
    have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) :=
      (Finset.Ico_succ_right_eq_Icc (a := 1) (b := n)).symm
    rw [hI, Finset.sum_Ico_eq_sum_range (f := fun j => iteratedDeriv j f a / (j.factorial : ℝ)
        * (x - a) ^ j) (m := 1) (n := n + 1)]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]
  rw [taylor_within_apply, Finset.sum_range_succ', hsum]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    iteratedDerivWithin_zero]
  have hterms : ∀ k ∈ Finset.range n,
      ((↑(k + 1).factorial)⁻¹ * (x - a) ^ (k + 1)) • iteratedDerivWithin (k + 1) f (Set.uIcc a x) a
        = iteratedDeriv (k + 1) f a / ((k + 1).factorial : ℝ) * (x - a) ^ (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
      push_cast
      exact_mod_cast Nat.succ_le_succ hk.le
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hca.of_le hle) hmem, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterms]
  simp only [one_mul, one_smul]
  exact add_comm _ _


/-! ### The size of `M = karP2 c1 n P` -/

/-- `M^{2(n+1)} ≤ P^{c1(n+1) - 1/n²}`. The exponent loses exactly the `1/n²` that the remainder of
Taylor's formula has to pay for. -/
private theorem leafW_karP2_pow_le {c1 : ℝ} {n P : ℕ} (hP : 0 < P) (hn : 2 ≤ n) :
    ((karP2 c1 n P : ℝ)) ^ (2 * (n + 1)) ≤
      (P : ℝ) ^ (c1 * ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ) ^ 2) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  set e : ℝ := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) with he
  have hM : ((karP2 c1 n P : ℝ)) ≤ (P : ℝ) ^ e := by
    have h0 : (0 : ℝ) ≤ (P : ℝ) ^ e := Real.rpow_nonneg hPr.le e
    have := Nat.floor_le h0
    simpa [karP2, he] using this
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  refine (pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _) hM (2 * (n + 1))).trans ?_
  rw [← Real.rpow_natCast ((P : ℝ) ^ e) (2 * (n + 1)), ← Real.rpow_mul hPr.le]
  refine Real.rpow_le_rpow_of_exponent_le hP1 ?_
  rw [he]
  push_cast
  field_simp
  ring_nf
  exact le_refl _

/-- Every index of the inner sum of `W` lies in the interval on which the hypothesis class bounds
the derivative, and its displacement from `a` is at most `M²`. -/
private theorem leafW_index_mem {N P M a y z : ℕ}
    (hy : y ≤ M) (hz : z ≤ M) (ha : N ≤ a) (haP : a + M ^ 2 ≤ N + P) :
    N ≤ a + y * z ∧ a + y * z ≤ N + P ∧ ((y * z : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
  have hyz : y * z ≤ M ^ 2 := by
    calc y * z ≤ M * M := Nat.mul_le_mul hy hz
      _ = M ^ 2 := (pow_two M).symm
  refine ⟨le_trans ha (Nat.le_add_right _ _), by omega, ?_⟩
  have hcast : ((y * z : ℕ) : ℝ) ≤ ((M ^ 2 : ℕ) : ℝ) := by exact_mod_cast hyz
  simpa using hcast

/-- Taylor's formula to order `n` at the point `a`, in the Lagrange form, with the remainder
bounded by the one derivative bound the hypothesis class states. The endpoint `x = a` is the
degenerate case and both sides are zero there. -/
private theorem leafW_taylor_bound {c1 : ℝ} {n N P : ℕ} {f : ℝ → ℝ} {a x : ℝ}
    (_hP : 0 < P) (hn : 2 ≤ n)
    (hU : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1) f U)
    (hDer : ∀ y ∈ Set.Icc (N : ℝ) (N + P),
      |iteratedDeriv (n + 1) f y / ((n + 1).factorial : ℝ)|
        ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))))
    (haN : (N : ℝ) ≤ a) (hxP : x ≤ (N : ℝ) + P) (hax : a ≤ x) :
    |f x - taylorWithinEval f n (Set.uIcc a x) a x|
      ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (x - a) ^ (n + 1) := by
  obtain ⟨U, hUo, hIU, hC⟩ := hU
  have hsub : Set.uIcc a x ⊆ Set.Icc (N : ℝ) (N + P) := by
    intro t ht
    have ht' : t ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using ht
    exact ⟨le_trans haN ht'.1, le_trans ht'.2 hxP⟩
  have hsubU : Set.uIcc a x ⊆ U := fun t ht => hIU (hsub ht)
  have hCs : ContDiffOn ℝ (n + 1) f (Set.uIcc a x) := hC.mono hsubU
  have hn1 : 0 < n + 1 := by omega
  rcases eq_or_lt_of_le hax with h | h
  · rw [← h]
    rw [taylorWithinEval_self, sub_self, abs_zero]
    rw [sub_self, zero_pow (by omega : n + 1 ≠ 0), mul_zero]
  · obtain ⟨ξ, hξ, hEq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (n := n) (x := x) (x₀ := a) h.ne hCs
    have hξI : ξ ∈ Set.Icc (N : ℝ) (N + P) := by
      have hξ' : ξ ∈ Set.Ioo a x := by simpa [Set.uIoo_of_le hax] using hξ
      exact ⟨le_trans haN (le_of_lt hξ'.1), le_trans (le_of_lt hξ'.2) hxP⟩
    have hxa : (0 : ℝ) ≤ x - a := by linarith
    have hfac : iteratedDeriv (n + 1) f ξ * (x - a) ^ (n + 1) / ((n + 1).factorial : ℝ)
        = (iteratedDeriv (n + 1) f ξ / ((n + 1).factorial : ℝ)) * (x - a) ^ (n + 1) := by
      ring
    rw [hEq, hfac, abs_mul, abs_of_nonneg (pow_nonneg hxa _)]
    exact mul_le_mul_of_nonneg_right (hDer ξ hξI) (pow_nonneg hxa _)

/-! ### One term of the difference -/

/-- A single term of `W(a)` differs from its Taylor replacement by at most `2π P^{-1/n²}`: the
phase difference is `≤ P^{-c1(n+1)} (yz)^{n+1}`, the size of `yz` is at most `M`, and `M` was
chosen so that `M^{2(n+1)} ≤ P^{c1(n+1) - 1/n²}`. -/
private theorem leafW_term_bound {c1 : ℝ} {n N P : ℕ} {f : ℝ → ℝ} {a y z : ℕ}
    (hP : 0 < P) (hn : 2 ≤ n)
    (hU : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1) f U)
    (hDer : ∀ x ∈ Set.Icc (N : ℝ) (N + P),
      |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)|
        ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))))
    (hy : y ≤ karP2 c1 n P) (hz : z ≤ karP2 c1 n P) (ha : N ≤ a)
    (haP : a + karP2 c1 n P ^ 2 ≤ N + P) :
    ‖eC (f ((a + y * z : ℕ) : ℝ)) -
      eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
        iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
      ≤ 2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  obtain ⟨U, hUo, hIU, hC⟩ := hU
  obtain ⟨hNa, haP', hyz2⟩ := leafW_index_mem hy hz ha haP
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hnn : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  set x : ℝ := ((a + y * z : ℕ) : ℝ) with hxdef
  have haN : (N : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hxa : (a : ℝ) ≤ x := by
    have h2 : (a : ℝ) ≤ ((a + y * z : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right a (y * z)
    simpa [hxdef] using h2
  have hxP : x ≤ (N : ℝ) + P := by
    have h2 : ((a + y * z : ℕ) : ℝ) ≤ ((N + P : ℕ) : ℝ) := by exact_mod_cast haP'
    push_cast at h2
    simpa [hxdef] using h2
  have haNP : (a : ℝ) ≤ (N : ℝ) + P := by
    have h1 : ((a + y * z : ℕ) : ℝ) ≤ ((N + P : ℕ) : ℝ) := by exact_mod_cast haP'
    have h2 : ((a : ℕ) : ℝ) ≤ ((a + y * z : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right a (y * z)
    push_cast at h1
    push_cast at h2
    linarith
  have haU : (a : ℝ) ∈ U := hIU ⟨haN, haNP⟩
  have hxa_eq : x - (a : ℝ) = ((y * z : ℕ) : ℝ) := by
    simp only [hxdef]
    push_cast
    ring
  have hpow : (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (x - (a : ℝ)) ^ (n + 1)
      ≤ (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    rw [hxa_eq]
    have h1 : (((y * z : ℕ) : ℝ)) ^ (n + 1) ≤ ((karP2 c1 n P : ℝ)) ^ (2 * (n + 1)) := by
      refine (pow_le_pow_left₀ (by positivity) hyz2 (n + 1)).trans (le_of_eq ?_)
      rw [pow_mul]
    have h2 : ((karP2 c1 n P : ℝ)) ^ (2 * (n + 1))
        ≤ (P : ℝ) ^ (c1 * ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ) ^ 2) := leafW_karP2_pow_le hP hn
    calc (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (((y * z : ℕ) : ℝ)) ^ (n + 1)
        ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) *
            (P : ℝ) ^ (c1 * ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hPr.le _)
      _ = (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
          rw [← Real.rpow_add hPr]
          congr 1
          ring
  have hec : ‖eC (f x) - eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j)‖
      ≤ 2 * Real.pi * |f x - (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
        iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j)| :=
    leafW_eC_sub_le _ _
  have hgoal : ‖eC (f x) - eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j)‖
      ≤ 2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    rcases lt_or_eq_of_le hxa with hlt | heq
    · have hEq : taylorWithinEval f n (Set.uIcc (a : ℝ) x) (a : ℝ) x
          = f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j :=
        leafW_taylor_eq_explicit hUo hC haU hlt
      have hTay := leafW_taylor_bound (c1 := c1) (n := n) (N := N) (P := P)
        (f := f) (a := (a : ℝ)) (x := x) hP hn ⟨U, hUo, hIU, hC⟩ hDer haN hxP hxa
      rw [hEq] at hTay
      have hval : |f x - (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j)| ≤
          (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := hTay.trans hpow
      exact hec.trans (mul_le_mul_of_nonneg_left hval (by positivity))
    · have hyz0 : ((y * z : ℕ) : ℝ) = 0 := by
        rw [← hxa_eq, heq, sub_self]
      have hsum0 : ∑ j ∈ Finset.Icc 1 n,
          iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (x - (a : ℝ)) ^ j = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [hxa_eq, hyz0, zero_pow (by omega : j ≠ 0), mul_zero]
      rw [hsum0, add_zero, heq, sub_self, norm_zero]
      positivity
  rw [← hxa_eq]
  exact hgoal

/-- LEAF. Taylor's formula to order `n` at the point `a`, p. 245, the step that produces the phase
of the sum the mean value theorem is applied to. For the one derivative bound that the hypothesis
class states on `[N, N+P]`, every point `a + yz` with `y, z ≤ M` lies in that interval and the
Lagrange remainder gives `P^{-1/n²}` per term, so the whole difference of the two sums is at most a
constant times `(M+1)² P^{-1/n²}`. The Taylor polynomial is written out at `a`, so the term `yz = 0`
agrees in the two sums and the `n = 2` case is the usual second order formula. -/
theorem leaf_karW_taylor_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ (c1 : ℝ) (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ),
      0 < P → 2 ≤ n →
      (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1) f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (N + P),
        |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)|
          ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ)))) →
      N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
      ‖karW f (karP2 c1 n P) a -
        ∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
          eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
            iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
        ≤ C * ((karP2 c1 n P : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    refine ⟨2 * Real.pi, by positivity, ?_⟩
    intro c1 N P n f T a hP hn hU hDer ha haP
    set M := karP2 c1 n P with hM
    have hsub : karW f M a -
        ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
          eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
            iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))
        = ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
            (eC (f ((a + y * z : ℕ) : ℝ)) -
              eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
                iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))) := by
      simp only [karW]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by rw [← Finset.sum_sub_distrib]
    rw [hsub]
    set c : ℝ := 2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) with hc
    have hc0 : 0 ≤ c := by
      rw [hc]
      have : (0 : ℝ) < (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hP) _
      positivity
    have hinner : ∀ y ∈ Finset.range (M + 1),
        ‖∑ z ∈ Finset.range (M + 1),
            (eC (f ((a + y * z : ℕ) : ℝ)) -
              eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
                iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j)))‖
          ≤ ((M : ℝ) + 1) * c := by
      intro y hy
      rw [Finset.mem_range] at hy
      refine (norm_sum_le _ _).trans ?_
      have hyM : y ≤ karP2 c1 n P := by rw [← hM]; omega
      calc ∑ z ∈ Finset.range (M + 1),
            ‖eC (f ((a + y * z : ℕ) : ℝ)) -
              eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
                iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ ∑ _z ∈ Finset.range (M + 1), c := by
            refine Finset.sum_le_sum ?_
            intro z hz
            rw [Finset.mem_range] at hz
            have hzM : z ≤ karP2 c1 n P := by rw [← hM]; omega
            have := leafW_term_bound (c1 := c1) (n := n) (N := N) (P := P) (f := f)
              (a := a) (y := y) (z := z) hP hn hU hDer hyM hzM ha haP
            simpa [hc] using this
        _ = ((M : ℝ) + 1) * c := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hinner).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hc]
    push_cast
    have heq : ((M : ℝ) + 1) * (((M : ℝ) + 1) * (2 * Real.pi * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2))))
        = 2 * Real.pi * ((M : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by ring
    rw [heq]


/-! ### Second leaf: the analytic core -/

/-- LEAF. The Taylor polynomial sum of the first leaf, call it `S(a)`, is small, p. 245-248: the
mean value theorem bounds the number of solutions of the resulting system, the spacing bound bounds
the sums over the coefficient denominators, and Holder's inequality raises the whole to the power
`2k` that makes the mean value theorem applicable. The output is `‖S(a)‖ ≤ B (M+1)² P^{-e}` with
`e = ρ c0²/(32 n² (4 + L²)²)`, `ρ ≤ min(c1/3, c3, c4)` and `L = log(8/(ρ c0²))`: the two integers of
that argument are bounded by `l ≤ n L` and `k ≤ n²(4 + L²)`, and `s_1 + ... + s_r ≥ c0² n²/4`. The
exponent is deliberately weaker than the one the argument produces, so the whole choice of `l` sits
inside this leaf and the assembly needs no such choice. -/
theorem leaf_karW_taylor_sum_bound (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ B ρ cc : ℝ, 0 < B ∧ 0 < ρ ∧ ρ ≤ c1 / 3 ∧ ρ ≤ c3 ∧ ρ ≤ c4 ∧ 0 < cc ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ B * ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + (Real.log (8 / (ρ * c0 ^ 2))) ^ 2) ^ 2))) := by
  sorry

/-! ### The assembly -/

/-- The split of `leaf_W_bound`: the statement of that theorem, from the two leaves above and no
other input. Both leaves conclude an estimate with the same `M = karP2 c1 n P` and the same Taylor
polynomial sum, so the assembly only has to add the two bounds and compare the two exponents; the
exponents are compared at `γ = ρ c0²/(64(4+L²)²)`, which is `1/1024` of the size of the allowed
exponent at the smallest allowed parameters and stays positive because the denominator is a square
plus `4`. -/
theorem leaf_W_bound_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by
  intro c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  obtain ⟨C, hCpos, hC⟩ := leaf_karW_taylor_reduction
  obtain ⟨B, ρ, cc, hBpos, hρpos, hρc1, hρc3, hρc4, hcc, hBb⟩ :=
    leaf_karW_taylor_sum_bound h1 h3 h4 c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  set L := Real.log (8 / (ρ * c0 ^ 2)) with hL
  set γ := ρ * c0 ^ 2 / (64 * (4 + L ^ 2) ^ 2) with hγdef
  have hLpos : (0 : ℝ) < 4 + L ^ 2 := by positivity
  have hnum : (0 : ℝ) < ρ * c0 ^ 2 := mul_pos hρpos (pow_pos h0 2)
  have hγpos : 0 < γ := by
    rw [hγdef]
    exact div_pos hnum (by positivity)
  have hγ1 : γ ≤ 1 := by
    rw [hγdef, div_le_one (by positivity)]
    have hlt : ρ * c0 ^ 2 < 1 := by nlinarith
    have hsq : (16 : ℝ) ≤ (4 + L ^ 2) ^ 2 := by nlinarith [sq_nonneg L]
    nlinarith
  refine ⟨B + C, γ, cc, by linarith, hγpos, hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH a ha haP
  set M := karP2 c1 n P with hM
  set K := ((M : ℝ) + 1) ^ 2 with hK
  set S : ℂ := ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
    eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j)) with hS
  have hHall := hH
  obtain ⟨hU, hDer, -, -, -⟩ := hHall
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hTay : ‖karW f M a - S‖ ≤ C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    have := hC c1 N P n f T a hP hn hU hDer ha haP
    simpa [hM, hK, hS] using this
  have hAna : ‖S‖ ≤ B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have := hBb N P n f T a hP hn hpred hbig hH ha haP
    simpa [hM, hK, hS, hL] using this
  have hle1 : (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have := div_le_div_of_nonneg_right hγ1 hnpos.le
    linarith
  have hexp : γ / (n : ℝ) ^ 2 ≤ ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2) := by
    rw [hγdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnum, hLpos, hnpos, mul_pos hnum (mul_pos hLpos hnpos)]
  have hle2 : (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    linarith
  have hmain : ‖karW f M a‖ ≤
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have hsplit : karW f M a = (karW f M a - S) + S := by ring
    calc ‖karW f M a‖ = ‖(karW f M a - S) + S‖ := congrArg (fun z : ℂ => ‖z‖) hsplit
      _ ≤ ‖karW f M a - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hTay hAna
  have hcomp :
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    have hA := mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ C * K)
    have hB' := mul_le_mul_of_nonneg_left hle2 (by positivity : (0 : ℝ) ≤ B * K)
    have hring : (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2))
        = C * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) +
          B * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by ring
    rw [hring]
    linarith
  linarith [hmain, hcomp]

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

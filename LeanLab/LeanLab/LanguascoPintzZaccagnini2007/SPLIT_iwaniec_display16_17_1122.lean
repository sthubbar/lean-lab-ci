import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A further split of the two HARD leaves `iwaniec_display16_1122` and `iwaniec_display17_1122` of
`SPLIT_iwaniec_no_zero_open_strip481_steps`, along the two lines of page 103 of
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104, that derive
displays (16) and (17), read on the page image of `papers/Iwaniec1974.pdf`.

Each display comes from three inputs:
* Lemma 9, page 102: `|L(s, χ)| < M` in the circle about `s₀ = 1 + 5θ + iγ`, and the same for
  `χ²` about `s₁ = 1 + 5θ + 2iγ` with `2M`, as page 103 uses it;
* the lower bound at the centre, page 103: `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / 5θ`;
* Lemma 10, page 102: the Landau type lower bound for `Re F'/F (s₀)`.

The assemblies below prove the exact statements of the two parent leaves from these four
leaves. The geometry, that the zero `ρ` lies in the circle of radius `η/2` about `s₀` because
`12θ < η`, that every zero of `L` has real part below one, and the algebra turning
`4 / (η/2)` into `8 / η`, is proved here.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Helper: If F is holomorphic on B(s₀, r), F(s₀) ≠ 0, and |F(z)| ≤ B |F(s₀)| on B(s₀, r),
then B ≥ 1. -/
lemma iwaniec_lemma10_B_ge_one {F : ℂ → ℂ} {s₀ : ℂ} {r B : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0)
    (hB : ∀ s ∈ Metric.ball s₀ r, ‖F s‖ ≤ B * ‖F s₀‖) : 1 ≤ B := by
  have h₁ : s₀ ∈ Metric.ball s₀ r := by
    rw [Metric.mem_ball]
    simp [hr.le, dist_self]
  have h₂ : ‖F s₀‖ ≤ B * ‖F s₀‖ := hB s₀ h₁
  have h₃ : 0 < ‖F s₀‖ := by
    exact norm_pos_iff.mpr hF0
  have h₄ : 1 ≤ B := by
    by_contra h
    have h₅ : B < 1 := by linarith
    have h₆ : B * ‖F s₀‖ < 1 * ‖F s₀‖ := by
      nlinarith
    have h₇ : 1 * ‖F s₀‖ = ‖F s₀‖ := by ring
    linarith
  exact h₄

/-- Helper: Each term in the sum is nonnegative because ρ.re ≤ s₀.re. -/
lemma iwaniec_lemma10_sum_nonneg {s₀ : ℂ} {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, ρ.re ≤ s₀.re) :
    ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≥ 0 := by
  have h₁ : ∀ ρ ∈ Z, (1 / (s₀ - ρ)).re ≥ 0 := by
    intro ρ hρ
    have h₂ : ρ.re ≤ s₀.re := hZ ρ hρ
    have h₃ : (1 / (s₀ - ρ)).re = (s₀.re - ρ.re) / Complex.normSq (s₀ - ρ) := by
      simp [Complex.ext_iff, Complex.normSq, Complex.div_re, Complex.div_im, Complex.normSq_apply]
      <;> field_simp [Complex.normSq, Complex.ext_iff, sub_mul, mul_sub, Complex.normSq_apply]
      <;> ring_nf
      <;> simp_all [Complex.ext_iff, Complex.normSq, Complex.normSq_apply]
      <;> field_simp [Complex.normSq, Complex.ext_iff, sub_mul, mul_sub, Complex.normSq_apply]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    rw [h₃]
    have h₄ : 0 ≤ s₀.re - ρ.re := by linarith
    have h₅ : 0 < Complex.normSq (s₀ - ρ) := by
      have h₅₁ : s₀ - ρ ≠ 0 := by
        intro h
        have h₅₂ : s₀ = ρ := by
          rw [sub_eq_zero] at h
          exact h
        have h₅₃ : s₀.re = ρ.re := by rw [h₅₂]
        have h₅₄ : ρ.re ≤ s₀.re := hZ ρ (by simp_all [Finset.mem_singleton])
        have h₅₅ : s₀.re ≤ ρ.re := by linarith
        simp_all [Complex.ext_iff]
        <;>
        (try { contradiction }) <;>
        (try { linarith })
      exact Complex.normSq_pos_iff.mpr h₅₁
    exact div_nonneg h₄ (by linarith)
  exact Finset.sum_nonneg fun ρ hρ => h₁ ρ hρ

/-- Helper: The set of zeros of F in the closed ball of radius r/2 is finite. -/
lemma iwaniec_lemma10_finite_zeros {F : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0) :
    Set.Finite {z : ℂ | z ∈ Metric.ball s₀ (r / 2) ∧ F z = 0} := by
  have h₁ : {z : ℂ | z ∈ Metric.ball s₀ (r / 2) ∧ F z = 0} ⊆ {z : ℂ | z ∈ Metric.closedBall s₀ (r / 2) ∧ F z = 0} := by
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩
  have h₂ : Set.Finite {z : ℂ | z ∈ Metric.closedBall s₀ (r / 2) ∧ F z = 0} := by
    have h₃ : IsCompact (Metric.closedBall s₀ (r / 2)) := isCompact_closedBall
    have h₄ : ContinuousOn F (Metric.closedBall s₀ (r / 2)) := by
      have h₅ : ContinuousOn F (Metric.ball s₀ r) := hF.continuousOn
      have h₆ : Metric.closedBall s₀ (r / 2) ⊆ Metric.ball s₀ r := by
        intro z hz
        rw [Metric.mem_closedBall, Metric.mem_ball] at hz ⊢
        have h₇ : dist z s₀ ≤ r / 2 := hz
        have h₈ : r / 2 < r := by linarith
        linarith
      exact ContinuousOn.mono h₅ h₆
    have h₅ : Set.Finite {z : ℂ | z ∈ Metric.closedBall s₀ (r / 2) ∧ F z = 0} := by
      -- Use the fact that the zeros of a non-constant holomorphic function are isolated
      have h₆ : {z : ℂ | z ∈ Metric.closedBall s₀ (r / 2) ∧ F z = 0} = (Metric.closedBall s₀ (r / 2)) ∩ {z : ℂ | F z = 0} := by
        ext z
        simp [Set.mem_inter_iff]
        <;> aesop
      rw [h₆]
      have h₇ : IsClosed {z : ℂ | F z = 0} := by
        have h₈ : Continuous F := by
          have h₉ : ContinuousOn F (Metric.ball s₀ r) := hF.continuousOn
          have h₁₀ : ContinuousOn F (Set.univ : Set ℂ) := by
            -- F is differentiable on the ball, but we need it to be continuous everywhere
            -- Actually, we only know F is differentiable on the ball, not necessarily everywhere
            -- But we can use the fact that the zero set is closed in the subspace topology
            sorry
          sorry
        exact isClosed_eq h₈ continuous_const
      have h₈ : IsCompact (Metric.closedBall s₀ (r / 2)) := isCompact_closedBall
      have h₉ : IsCompact ((Metric.closedBall s₀ (r / 2)) ∩ {z : ℂ | F z = 0}) := by
        apply IsCompact.inter h₈ h₇
      -- A compact discrete set is finite
      have h₁₀ : Set.Finite ((Metric.closedBall s₀ (r / 2)) ∩ {z : ℂ | F z = 0}) := by
        sorry
      exact h₁₀
    exact h₅
  exact Set.Finite.subset h₂ h₁

/-- Helper: Construct the Blaschke product for the full set of zeros. -/
lemma iwaniec_lemma10_blaschke_full {F : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.ball s₀ (r / 2) ∧ F ρ = 0) :
    DifferentiableOn ℂ (fun z => F z * ∏ ρ ∈ Z, (s₀ - ρ) / (z - ρ)) (Metric.ball s₀ r) := by sorry

/-- Helper: The logarithmic derivative of the Blaschke product. -/
lemma iwaniec_lemma10_logDeriv_blaschke {s₀ : ℂ} {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, ρ ≠ s₀) :
    (∑ ρ ∈ Z, (1 / (s₀ - ρ)).re) = (∑ ρ ∈ Z, (1 / (s₀ - ρ))).re := by
  simp [Finset.sum_congr rfl, Complex.ext_iff, Finset.sum_const, nsmul_eq_mul]
  <;>
  simp_all [Complex.ext_iff, Finset.sum_const, nsmul_eq_mul]
  <;>
  ring_nf
  <;>
  norm_num
  <;>
  simp_all [Complex.ext_iff, Finset.sum_const, nsmul_eq_mul]
  <;>
  linarith

/-- Helper: Zero-free Borel-Caratheodory lemma giving Re(logDeriv H s₀) ≥ -(4/r) log B. -/
lemma iwaniec_lemma10_zero_free_bound {H : ℂ → ℂ} {s₀ : ℂ} {r B : ℝ} (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (Metric.ball s₀ (r / 2))) (hH0 : H s₀ ≠ 0)
    (hB : ∀ z ∈ Metric.ball s₀ (r / 2), ‖H z‖ ≤ B * ‖H s₀‖)
    (hZ : ∀ z ∈ Metric.ball s₀ (r / 2), H z ≠ 0) :
    -(4 / r) * Real.log B ≤ (logDeriv H s₀).re := by sorry

/-- LEAF: Iwaniec 1974 page 102, Lemma 10.
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 10, a
consequence of the maximum principle: if `F` is regular in `|s - s₀| < r` and there
`|F(s)| ≤ B |F(s₀)|`, then `Re F'/F (s₀) ≥ -(4/r) log B + Σ_ρ Re 1/(s₀ - ρ)`, the sum over the
zeros in `|s - s₀| < r/2`. Stated here for any finite set `Z` of distinct zeros in that circle,
which is weaker than the printed sum since every omitted term `Re 1/(s₀ - ρ)` is nonnegative
under the hypothesis that the zeros in the circle have real part at most `re s₀`. -/
theorem iwaniec_lemma10_1122 (F : ℂ → ℂ) (s₀ : ℂ) (r B : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0)
    (hB : ∀ s ∈ Metric.ball s₀ r, ‖F s‖ ≤ B * ‖F s₀‖)
    (hzeros : ∀ z ∈ Metric.ball s₀ (r / 2), F z = 0 → z.re ≤ s₀.re)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.ball s₀ (r / 2) ∧ F ρ = 0) :
    -(4 / r) * Real.log B + ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≤ (logDeriv F s₀).re := by
  have hB1 : 1 ≤ B := iwaniec_lemma10_B_ge_one hr hF hF0 hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  -- Step 1: Each term in the sum over Z is nonnegative
  have h_sum_nonneg : ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≥ 0 := by
    have h₁ : ∀ ρ ∈ Z, ρ.re ≤ s₀.re := by
      intro ρ hρ
      have h₂ : ρ ∈ Metric.ball s₀ (r / 2) := (hZ ρ hρ).1
      have h₃ : F ρ = 0 := (hZ ρ hρ).2
      exact hzeros ρ h₂ h₃
    exact iwaniec_lemma10_sum_nonneg h₁
  -- Step 2: The zero-free bound gives -(4/r) log B ≤ Re(logDeriv H s₀) for the Blaschke product
  -- with the full set of zeros. Since Z is a subset, the sum over Z is smaller.
  have h_main : -(4 / r) * Real.log B + ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≤ (logDeriv F s₀).re := by sorry
  exact h_main

/-- LEAF: Iwaniec 1974 page 103, the bound at the centre used for displays (16) and (17).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the line before
display (16): `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`, from the Euler product, with
`σ₀ = 1 + 5θ`. Stated for every character and `1 < σ ≤ 6/5`; on that range
`ζ(σ) / ζ(2σ) ≤ 1 / (σ - 1)`. -/
theorem iwaniec_centre_lower1122 (q : ℕ) (hq : 1 ≤ q) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    σ - 1 ≤ ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  sorry

/-- LEAF: Iwaniec 1974 page 102, Lemma 9, as page 103 applies it before display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 9, from
Theorem 1 of page 97: for a nonprincipal `χ` modulo `q ≥ 3`, `|L(s, χ)| < M` where
`Re s > 1 - η`. Page 103 uses it in the circle `|s - s₀| < η`, `s₀ = 1 + 5θ + iγ`, with `l`, `η`,
`M` taken at the height `γ`; see the QUESTION in the notes on this choice of height. -/
theorem iwaniec_lemma9_circle16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η) :
    ‖Lfun481 χ s‖ ≤ M := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, Lemma 9 as applied before display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the sentence
before display (17): for a nonprincipal `ψ`, here `χ²`, `L(s, ψ)` satisfies
`|L(s, ψ)| ≤ 2M` in the circle `|s - s₁| < η/2`, `s₁ = 1 + 5θ + 2iγ`, with `l`, `η`, `M` taken at
the height `γ`. From Lemma 9 of page 102; see the QUESTION in the notes on the factor `2`. -/
theorem iwaniec_lemma9_circle17_1122 (q : ℕ) (hq : 3 ≤ q) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (η / 2)) :
    ‖Lfun481 ψ s‖ ≤ 2 * M := by
  sorry

/-- The size facts of page 102 for the parameters: `0 < θ ≤ 1/25`, `0 < η` and `12 θ < η`,
the last because `θ = η / (400 log M)` and `log M ≥ 100`. -/
theorem iwaniec_params1122 (q : ℕ) (hq : 3 ≤ q) (γ l η θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    0 < θ ∧ θ ≤ 1 / 25 ∧ 0 < η ∧ 12 * θ < η := by
  have hq' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ |γ| := abs_nonneg _
  have hbase : (9 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 < 9 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hl2 : 2 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hL1 : 1 ≤ Real.log (2 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  set L := Real.log (2 * l) with hL
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hlogd : 0 ≤ Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
  set D := Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) with hD
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hsplit : (l * L) ^ (3 / 4 : ℝ) = l ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ) :=
    Real.mul_rpow hl0 hL0
  have hlpow : l ^ (1 / 2 : ℝ) ≤ l ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsqrt : Real.sqrt l = l ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow l
  have hLpow : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlhalf : 1 ≤ l ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hl34 : 1 ≤ l ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 1 ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit]; exact one_le_mul_of_one_le_of_one_le hl34 hLpow
  have hden : 1 ≤ D + (l * L) ^ (3 / 4 : ℝ) := by linarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθle : θ ≤ 1 / 25 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set E := l ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) with hE
  have hEpos : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le hlhalf hLpow
  have hηE : η = 1 / E := by rw [hη, hsqrt, hE]; exact (one_div _).symm
  have hηpos : 0 < η := by rw [hηE]; positivity
  have hEle : E ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit, hE]
    exact mul_le_mul_of_nonneg_right hlpow (by linarith)
  refine ⟨hθpos, hθle, hηpos, ?_⟩
  rw [hθ, hηE, mul_one_div, div_lt_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- `Lfun481` agrees with Mathlib's `LFunction` for a positive modulus. -/
theorem iwaniec_Lfun_eq1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q) :
    Lfun481 ψ = (haveI : NeZero q := ⟨hq⟩; DirichletCharacter.LFunction ψ) := by
  funext s
  simp only [Lfun481, dif_neg hq]

/-- For a nonprincipal character the zeros of `Lfun481` have real part below one, and the
function is differentiable everywhere. -/
theorem iwaniec_Lfun_facts1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) :
    Differentiable ℂ (Lfun481 ψ) ∧ ∀ z : ℂ, Lfun481 ψ z = 0 → z.re < 1 := by
  haveI : NeZero q := ⟨hq⟩
  rw [iwaniec_Lfun_eq1122 hq ψ]
  refine ⟨DirichletCharacter.differentiable_LFunction hψ, ?_⟩
  intro z hz
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp h) hz

/-- A character with a nonreal value is nonprincipal. -/
theorem iwaniec_ne_one_of_nonreal1122 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) : χ ≠ 1 := by
  rintro rfl
  obtain ⟨a, ha⟩ := hnonreal
  apply ha
  by_cases hu : IsUnit a
  · simp [MulChar.one_apply hu]
  · simp [MulChar.map_nonunit _ hu]

/-- Display (16) of page 103, the exact statement of `iwaniec_display16_1122`, from Lemma 9 in
the circle about `s₀`, the bound at the centre, and Lemma 10 with the zero `ρ = s`. -/
theorem iwaniec_display16_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ) (l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|s.im| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (hzero : Lfun481 χ s = 0) (hreg : 1 - θ < s.re) (hlt : s.re < 1) :
    -(4 / η) * Real.log (M / (5 * θ)) + 1 / (1 + 5 * θ - s.re) ≤
      (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, h12⟩ := iwaniec_params1122 q hq s.im l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hχ := iwaniec_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 χ hχ
  set s₀ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I with hs₀
  have hc := iwaniec_centre_lower1122 q (by omega) χ (1 + 5 * θ) s.im (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 χ s₀‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 χ s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₀ η, ‖Lfun481 χ z‖ ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle16_1122 q hq χ hχ s.im l η M θ hl hη hM hθ z hz
    have h2 : M ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' hMnn
    linarith
  have hdiffS : s₀ - s = (((1 + 5 * θ - s.re : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [hs₀]
  have hsball : s ∈ Metric.ball s₀ (η / 2) := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, hdiffS, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₀ (η / 2), Lfun481 χ z = 0 → z.re ≤ s₀.re := by
    intro z _ hz
    have := hre z hz
    have : s₀.re = 1 + 5 * θ := by simp [hs₀]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 χ) s₀ η (M / (5 * θ)) hηpos
    hdiff.differentiableOn hF0 hB hzeros {s} (by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact ⟨hsball, hzero⟩)
  rw [Finset.sum_singleton, hdiffS] at key
  have hre1 : (1 / (((1 + 5 * θ - s.re : ℝ)) : ℂ)).re = 1 / (1 + 5 * θ - s.re) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre1] at key
  exact key

/-- Display (17) of page 103, the exact statement of `iwaniec_display17_1122`, from Lemma 9 in
the circle about `s₁` for `χ²`, the bound at the centre, and Lemma 10 with no zero. -/
theorem iwaniec_display17_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    -(8 / η) * Real.log (2 * M / (5 * θ)) ≤
      (logDeriv (Lfun481 (χ ^ 2)) (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, _⟩ := iwaniec_params1122 q hq γ l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hψ := iwaniec_sq_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 (χ ^ 2) hψ
  set s₁ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I with hs₁
  have hc := iwaniec_centre_lower1122 q (by omega) (χ ^ 2) (1 + 5 * θ) (2 * γ) (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 (χ ^ 2) s₁‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 (χ ^ 2) s₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₁ (η / 2),
      ‖Lfun481 (χ ^ 2) z‖ ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle17_1122 q hq (χ ^ 2) hψ γ l η M θ hl hη hM hθ z hz
    have h2 : 2 * M ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' (by linarith)
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₁ (η / 2 / 2), Lfun481 (χ ^ 2) z = 0 → z.re ≤ s₁.re := by
    intro z _ hz
    have := hre z hz
    have : s₁.re = 1 + 5 * θ := by simp [hs₁]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 (χ ^ 2)) s₁ (η / 2) (2 * M / (5 * θ))
    (by linarith) hdiff.differentiableOn hF0 hB hzeros ∅ (by simp)
  rw [Finset.sum_empty, add_zero] at key
  have h48 : 4 / (η / 2) = 8 / η := by field_simp; ring
  rw [h48] at key
  exact key

end

end LeanLab.LPZ2007

import LeanLab.ExceptionalSet.UpJ200.Display10Effective

/-!
# Split of the two leaves of `Display10Effective`

Burst burst-20261122, Claude cloud session S112. AI wrote the Lean code. Binary Goldbach is open.

* `leaf_L1_lower_proved`, the exact twin of `Display10Effective.leaf_L1_lower`, PROVED from the
  two class number formula leaves `leaf_cnf_odd` and `leaf_cnf_even`, Davenport chapter 6, using
  only `h ≥ 1`, `w ≤ 6` and `u, v ≥ 1`.
* `leaf_Lderiv_bound_proved`, the exact twin of `Display10Effective.leaf_Lderiv_bound`, PROVED
  from the partial summation tail leaf `leaf_Lderiv_tail` and the head bound `leaf_Lderiv_head`,
  Davenport chapter 14.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Display10Leaves

open Real

lemma two_le_of_ne_one {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r} (hχ : χ ≠ 1) :
    2 ≤ r := by
  have hr0 : r ≠ 0 := NeZero.ne r
  have hr1 : r ≠ 1 := by
    intro heq
    subst r
    exact hχ (DirichletCharacter.level_one χ)
  omega

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 6, Dirichlet's class number formula for
an imaginary quadratic field, class HARD. For a real primitive odd character `χ` modulo `r`,
`L(1, χ) = 2π h / (w √r)` with class number `h ≥ 1` and `w ∈ {2, 4, 6}` the number of roots of
unity. -/
theorem leaf_cnf_odd : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = -1 →
    ∃ (h w : ℕ), 1 ≤ h ∧ w ∈ ({2, 4, 6} : Finset ℕ) ∧
      ‖χ.LFunction 1‖ = 2 * π * h / (w * Real.sqrt r) := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 6, Dirichlet's class number formula for
a real quadratic field, class HARD. For a real primitive even nonprincipal character `χ` modulo
`r`, `L(1, χ) = h log ε / √r` with class number `h ≥ 1` and `ε = (v + u √r)/2`, where `v, u` are
positive integers with `v² - r u² = ±4`. -/
theorem leaf_cnf_even : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = 1 →
    ∃ (h u v : ℕ), 1 ≤ h ∧ 1 ≤ u ∧ 1 ≤ v ∧
      ((v : ℤ) ^ 2 - r * u ^ 2 = 4 ∨ (v : ℤ) ^ 2 - r * u ^ 2 = -4) ∧
      ‖χ.LFunction 1‖ = h * Real.log ((v + u * Real.sqrt r) / 2) / Real.sqrt r := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14, partial summation for the tail
`∑_{n ≥ r} χ(n) log n n^{-σ}` of `-L'(σ, χ)`, using `|∑_{n ≤ x} χ(n)| ≤ r`, for
`1 - 1/log r ≤ σ ≤ 1`, class MEDIUM. Stated as: `L'(σ, χ)` plus the head sum over `n < r` is
`≪ log r`. Here `L'` is the complex derivative of Mathlib's continued `LFunction`. -/
theorem leaf_Lderiv_tail : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 →
      ‖deriv χ.LFunction (σ : ℂ) + ∑ n ∈ Finset.range r,
          χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤ C * Real.log r := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14, the head bound
`|∑_{n < r} χ(n) log n n^{-σ}| ≤ e ∑_{n < r} log n / n ≪ log² r` for `1 - 1/log r ≤ σ ≤ 1`,
since `n^{1-σ} ≤ r^{1/log r} = e`, class EASY. PROVED here. -/
theorem leaf_Lderiv_head : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 →
      ‖∑ n ∈ Finset.range r, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤
        C * Real.log r ^ 2 := by
  refine ⟨3 * Real.exp 1, by positivity, ?_⟩
  intro r hr χ hχ σ hσ1 hσ2
  have : NeZero r := hr
  have hr2 := two_le_of_ne_one hχ
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  set L := Real.log (r : ℝ) with hLdef
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hrR
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have h1σ : 1 - σ ≤ 1 / L := by linarith
  have hterm : ∀ n ∈ Finset.range r,
      ‖χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤ Real.exp 1 * L * (n : ℝ)⁻¹ := by
    intro n hn
    have hnr : n < r := Finset.mem_range.mp hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have hn0 : (0 : ℝ) < n := by linarith
    have hnrR : (n : ℝ) ≤ r := by exact_mod_cast hnr.le
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlognL : Real.log n ≤ L := Real.log_le_log hn0 hnrR
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
    have hχn : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hlogc : ‖(Real.log n : ℂ)‖ = Real.log n := by
      rw [Complex.norm_real, Real.norm_of_nonneg hlogn0]
    rw [hlogc]
    have hre : (-(σ : ℂ)).re = -σ := by simp
    rw [hre]
    have hpow : (n : ℝ) ^ (-σ) ≤ Real.exp 1 * (n : ℝ)⁻¹ := by
      rw [Real.rpow_def_of_pos hn0, ← Real.exp_log hn0, ← Real.exp_neg, ← Real.exp_add,
        Real.exp_log hn0]
      apply Real.exp_le_exp.mpr
      have : (1 - σ) * Real.log n ≤ 1 := by
        rcases le_or_gt σ 1 with _ | _
        · calc (1 - σ) * Real.log n ≤ (1 / L) * L := by
                apply mul_le_mul h1σ hlognL hlogn0 (by positivity)
            _ = 1 := by field_simp
        · linarith
      nlinarith
    have hp0 : 0 ≤ (n : ℝ) ^ (-σ) := by positivity
    calc ‖χ n‖ * (Real.log n * (n : ℝ) ^ (-σ)) ≤ 1 * (Real.log n * (n : ℝ) ^ (-σ)) := by
          apply mul_le_mul_of_nonneg_right hχn (by positivity)
      _ ≤ L * (Real.exp 1 * (n : ℝ)⁻¹) := by
          rw [one_mul]; exact mul_le_mul hlognL hpow hp0 hL0.le
      _ = Real.exp 1 * L * (n : ℝ)⁻¹ := by ring
  have hharm : ∑ n ∈ Finset.range r, (n : ℝ)⁻¹ ≤ 1 + L := by
    have h1 : ∑ n ∈ Finset.range r, (n : ℝ)⁻¹ ≤ ∑ n ∈ Finset.range (r + 1), (n : ℝ)⁻¹ := by
      rw [Finset.sum_range_succ]
      have : (0 : ℝ) ≤ ((r : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    have h2 : ∑ n ∈ Finset.range (r + 1), (n : ℝ)⁻¹ = (harmonic r : ℝ) := by
      rw [Finset.sum_range_succ']
      simp [harmonic]
    have := harmonic_le_one_add_log r
    linarith
  calc ‖∑ n ∈ Finset.range r, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖
      ≤ ∑ n ∈ Finset.range r, ‖χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range r, Real.exp 1 * L * (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = Real.exp 1 * L * ∑ n ∈ Finset.range r, (n : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * L * (1 + L) := by
        apply mul_le_mul_of_nonneg_left hharm (by positivity)
    _ ≤ 3 * Real.exp 1 * L ^ 2 := by
        have he : 0 < Real.exp 1 := Real.exp_pos 1
        have : 1 + L ≤ 3 * L := by linarith
        nlinarith [mul_pos he hL0]

/-- Twin of `Display10Effective.leaf_Lderiv_bound`, PROVED from the head and tail leaves. -/
theorem leaf_Lderiv_bound_proved :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Display10Effective.leaf_Lderiv_bound := by
  obtain ⟨C1, hC1, h1⟩ := leaf_Lderiv_tail
  obtain ⟨C2, hC2, h2⟩ := leaf_Lderiv_head
  refine ⟨2 * C1 + C2, by positivity, ?_⟩
  intro r hr χ hp hreal hχ σ hσ1 hσ2
  have : NeZero r := hr
  have hr2 := two_le_of_ne_one hχ
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hL2 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hrR
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set S := ∑ n ∈ Finset.range r, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))
  have e1 := h1 r hr χ hp hreal hχ σ hσ1 hσ2
  have e2 := h2 r hr χ hχ σ hσ1 hσ2
  have htri : ‖deriv χ.LFunction (σ : ℂ)‖ ≤ ‖deriv χ.LFunction (σ : ℂ) + S‖ + ‖S‖ := by
    have := norm_sub_le (deriv χ.LFunction (σ : ℂ) + S) S
    simpa using this
  have hLL : Real.log r ≤ 2 * Real.log r ^ 2 := by nlinarith
  nlinarith

lemma chi_neg_one {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (h : χ ^ 2 = 1) :
    χ (-1) = 1 ∨ χ (-1) = -1 := by
  have : χ (-1) ^ 2 = 1 := by
    have := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (-1)) h
    have hu : IsUnit (-1 : ZMod r) := isUnit_one.neg
    simpa [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] using this
  exact sq_eq_one_iff.mp this

/-- Twin of `Display10Effective.leaf_L1_lower`, PROVED from the two class number formula
leaves with `c = 1/6`. -/
theorem leaf_L1_lower_proved :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Display10Effective.leaf_L1_lower := by
  refine ⟨1 / 6, by norm_num, ?_⟩
  intro r hr χ hp hreal hχ
  have : NeZero r := hr
  have hr2 := two_le_of_ne_one hχ
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hs2 : Real.sqrt 2 ≤ Real.sqrt r := Real.sqrt_le_sqrt hrR
  have hsq2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt r := by linarith
  rcases chi_neg_one χ hreal with hev | hodd
  · obtain ⟨h, u, v, hh, hu, hv, -, heq⟩ := leaf_cnf_even r hr χ hp hreal hχ hev
    rw [heq]
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have hε : (1.2 : ℝ) ≤ (v + u * Real.sqrt r) / 2 := by nlinarith
    have hlog : (1 / 6 : ℝ) ≤ Real.log ((v + u * Real.sqrt r) / 2) := by
      have := Real.one_sub_inv_le_log_of_pos (x := (v + u * Real.sqrt r) / 2) (by linarith)
      have : (1 : ℝ) / ((v + u * Real.sqrt r) / 2) ≤ 1 / 1.2 :=
        one_div_le_one_div_of_le (by norm_num) hε
      rw [inv_eq_one_div] at *
      linarith
    rw [div_le_div_iff_of_pos_right hs0]
    nlinarith
  · obtain ⟨h, w, hh, hw, heq⟩ := leaf_cnf_odd r hr χ hp hreal hχ hodd
    rw [heq]
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hw6 : (w : ℝ) ≤ 6 ∧ (2 : ℝ) ≤ w := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> norm_num
    have hpi := Real.pi_gt_three
    rw [div_le_div_iff₀ hs0 (by nlinarith)]
    have a1 : 0 ≤ (π - 3) * Real.sqrt r := by nlinarith
    have a2 : 0 ≤ ((h : ℝ) - 1) * Real.sqrt r := by nlinarith
    have a3 : 0 ≤ (6 - (w : ℝ)) * Real.sqrt r := by nlinarith
    have a4 : 0 ≤ (π - 3) * (((h : ℝ) - 1) * Real.sqrt r) := by nlinarith
    nlinarith

end LeanLab.ExceptionalSet.UpJ200.Display10Leaves

#print axioms LeanLab.ExceptionalSet.UpJ200.Display10Leaves.leaf_L1_lower_proved
#print axioms LeanLab.ExceptionalSet.UpJ200.Display10Leaves.leaf_Lderiv_bound_proved
#print axioms LeanLab.ExceptionalSet.UpJ200.Display10Leaves.leaf_Lderiv_head

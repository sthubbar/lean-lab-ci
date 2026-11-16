/-
Split of `leaf_section4Block_mean_value_negative_small` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value.

The sealed leaf asks for the mean value of display 4.1 for the concrete tapered block of
pages 26 and 27, at the negative height and over the small exponent region, the block
running over the whole interval `(x / 2, 2 * x]`. This split cuts that block into its two
halves and separates the endpoint ordering of the integral, which the leaf needs before a
monotone comparison of two integrals is legitimate at all.

`leaf_section4Block_lower_block_mean_value` is the half `(x / 2, x]`,
`leaf_section4Block_upper_block_mean_value` is the half `(x, 2 * x]`, and
`leaf_section4Block_endpoint_order` supplies a threshold beyond which the lower endpoint of
the integral lies at or below the upper one. Each leaf is strictly easier than the sealed
leaf: the two block lemmas sum fewer terms, and the ordering lemma is an elementary
estimate about the two endpoints with no arithmetic input at all. The assembly adds the two
halves by the disjoint union of the index sets and the triangle inequality for the norm,
then compares constants.

Every leaf is OPEN. The family that vanishes identically meets every hypothesis and every
conclusion, so no leaf is vacuous. The hypothesis `h4` and the bound `hB` are carried
unchanged from the sealed statement; they play no role in the estimate, and the same is
true there.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF 1 of 3. The mean value step taken over the lower half of the block only. The
integral of display 4.1 at the negative height over the small exponent region is bounded
as in the sealed leaf, but the sum runs over the indices in `(x / 2, x]` instead of the
whole block `(x / 2, 2 * x]`, so fewer terms are summed and the same conclusion is asked of
a smaller object. The height exponent stays `Thm4.half (-t)` and the region hypothesis
stays `max m n ≤ 0.46`. One inequality on a norm integral, and it is met by the family that
vanishes identically, so it is not vacuous. -/
theorem leaf_section4Block_lower_block_mean_value
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 3. The same step over the upper half of the block. The sum runs over the
indices in `(x, 2 * x]`, the complement of the range of leaf 1 inside the sealed block, so
this half is not implied by leaf 1 and is a separate integral. The height exponent and the
region hypothesis are unchanged. One inequality on a norm integral, met by the family that
vanishes identically, so it is not vacuous. -/
theorem leaf_section4Block_upper_block_mean_value
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 3 of 3. The endpoint ordering of the integral in display 4.1. Past a threshold the
lower endpoint `exp (log x ^ (1/3))` lies at or below the upper endpoint
`x ^ (0.45 - 2 * ε / 3)`, which is what makes the interval nonempty; only then does a
pointwise comparison of two integrands imply a comparison of the two integrals. One
elementary inequality in `x`, with no arithmetic input, and it is expected to hold for
every positive `ε` below one tenth, so it is not vacuous. -/
theorem leaf_section4Block_endpoint_order (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (0.45 - 2 * ε / 3) := by
  sorry

/-- The block sum is continuous in the height, so every interval integral of its norm
exists. The coefficient, the character value and the index are fixed; the only dependence on
`t` is through `k ^ (1/2 + it)`, an exponential of a real-linear function of `t` at the
indices `k ≥ 1` that occur here. -/
private theorem continuous_block_sum (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) :
    Continuous fun t : ℝ =>
      ‖∑ k ∈ s, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
        (k : ℂ) ^ Thm4.half (-t)‖ := by
  have hhalf : Continuous Thm4.half := by
    unfold Thm4.half
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hsum : Continuous fun t : ℝ =>
      ∑ k ∈ s, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
        (k : ℂ) ^ Thm4.half (-t) := by
    refine continuous_finsetSum s ?_
    intro k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      have hk1 : k ≠ 0 := by
        have := hs k hk
        omega
      exact_mod_cast hk1
    have harg : Continuous fun t : ℝ => Thm4.half (-t) := hhalf.comp continuous_neg
    have hpow : Continuous fun t : ℝ => (k : ℂ) ^ Thm4.half (-t) :=
      harg.const_cpow (Or.inl hk0)
    have hne : ∀ t : ℝ, (k : ℂ) ^ Thm4.half (-t) ≠ 0 := by
      intro t
      rw [Complex.cpow_def_of_ne_zero hk0]
      exact Complex.exp_ne_zero _
    exact Continuous.div continuous_const hpow hne
  exact continuous_norm.comp hsum

/-- The assembly step for one block and one sign of the height. Given the two half-block
mean values, the mean value over the union of the halves follows: the index sets are
disjoint and their union is the whole block, so the norm of the full sum is at most the sum
of the two half norms at every height; the interval integral of that sum is the sum of the
two integrals because the integrands are continuous in the height; and the two constants are
added in absolute value, so each is dominated by the one constant of the conclusion. The
endpoint ordering is what makes the monotone comparison of the two integrals legitimate. -/
private theorem block_mean_value_of_two_halves (ε m n : ℝ) (a b : ℝ → ℕ → ℝ)
    {x A C₁ C₂ : ℝ} (hx1 : 1 ≤ x) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hord : Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (0.45 - 2 * ε / 3))
    (h₁ : (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) ≤ C₁ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A))
    (h₂ : (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) ≤ C₂ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :
    (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) ≤ (|C₁| + |C₂|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  have hP : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hcL : Continuous (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) :=
    continuous_block_sum ε m n a b x χ (Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊) (by
      intro k hk
      have h := (Finset.mem_Ioc.mp hk).1
      omega)
  have hcU : Continuous (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) :=
    continuous_block_sum ε m n a b x χ (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊) (by
      intro k hk
      have h := (Finset.mem_Ioc.mp hk).1
      omega)
  have hcF : Continuous (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) :=
    continuous_block_sum ε m n a b x χ (Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊) (by
      intro k hk
      have h := (Finset.mem_Ioc.mp hk).1
      omega)
  have hkey : ∀ t : ℝ,
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ ≤ ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ + ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ := by
    intro t
    have h₁' : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    have h₂' : ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_mono (by linarith)
    rw [← Finset.Ioc_union_Ioc_eq_Ioc h₁' h₂',
      Finset.sum_union (s₁ := Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊) (s₂ := Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊)
        (Finset.Ioc_disjoint_Ioc_of_le (le_refl ⌊x⌋₊))]
    exact norm_add_le _ _
  have hC : C₁ + C₂ ≤ |C₁| + |C₂| := by
    have h1 := le_abs_self C₁
    have h2 := le_abs_self C₂
    linarith
  have hmono : (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) ≤
      (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), (‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ + ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)) :=
    intervalIntegral.integral_mono_on hord (hcF.intervalIntegrable _ _)
      ((hcL.add hcU).intervalIntegrable _ _) (fun t _ => hkey t)
  have hadd : (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), (‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ + ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)) =
      (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) + (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) :=
    intervalIntegral.integral_add (hcL.intervalIntegrable _ _) (hcU.intervalIntegrable _ _)
  calc (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)
      ≤ (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), (‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ + ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)) := hmono
    _ = (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) + (∫ t in Real.exp (Real.log x ^ (1 / 3 : ℝ))..x ^ (0.45 - 2 * ε / 3), ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) := hadd
    _ ≤ C₁ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) + C₂ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := add_le_add h₁ h₂
    _ = (C₁ + C₂) * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by ring
    _ ≤ (|C₁| + |C₂|) * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hC hP
    _ = (|C₁| + |C₂|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved from the
three leaves above and never from the sealed leaf. The endpoints of the integral are compared
by the ordering leaf, the two half blocks are recombined by the block lemma, and the
threshold is the minimum of the three leaves and one tenth, which is what the ordering leaf
needs. -/
theorem leaf_section4Block_mean_value_negative_small_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η₁, hη₁, H₁⟩ := leaf_section4Block_lower_block_mean_value h4 B hB
  obtain ⟨η₂, hη₂, H₂⟩ := leaf_section4Block_upper_block_mean_value h4 B hB
  refine ⟨min (min η₁ η₂) (1 / 10), lt_min (lt_min hη₁ hη₂) (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hmax a b ha hb A hA
  have hεη₁ : ε < η₁ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεη₂ : ε < η₂ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε10 : ε ≤ 1 / 10 := (hεη.trans_le (min_le_right _ _)).le
  obtain ⟨X₀, hX₀, hX₀'⟩ := leaf_section4Block_endpoint_order ε hε hε10
  obtain ⟨C₁, X₁, h₁⟩ := H₁ ε hε hεη₁ m n hm0 hn0 hmax a b ha hb A hA
  obtain ⟨C₂, X₂, h₂⟩ := H₂ ε hε hεη₂ m n hm0 hn0 hmax a b ha hb A hA
  refine ⟨|C₁| + |C₂|, max (max X₁ X₂) X₀, ?_⟩
  intro x hx q hq hlog χ
  have hx₁ : X₁ ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hx₂ : X₂ ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hx₀ : X₀ ≤ x := (le_max_right _ _).trans hx
  exact block_mean_value_of_two_halves ε m n a b (hX₀.trans hx₀) χ (hX₀' x hx₀)
    (h₁ x hx₁ q hq hlog χ) (h₂ x hx₂ q hq hlog χ)

end LeanLab.BHP1997.Decomp528a

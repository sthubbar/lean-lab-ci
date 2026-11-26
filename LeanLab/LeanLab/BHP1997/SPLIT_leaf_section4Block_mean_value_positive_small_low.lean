/-
Split of `leaf_section4Block_mean_value_positive_small_low` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small, burst-20261122 S84 feed1122.

The sealed leaf bounds the integral in `t` of the norm of the block Dirichlet polynomial over
the lower height range, from `exp (log x ^ (1/3))` up to `x ^ (1/4)`. P0069 obtains display 4.1
for the block of display 4.7 from Theorem 4 on page 12 through Lemma 10, see pages 26 and 27,
and Theorem 4 bounds a sum of the norm over a well spaced set of heights, page 11, not an
integral. This split follows that route in two leaves:
- a MEDIUM leaf, the discretization: the integral of a continuous nonnegative function over an
  interval is at most the sum of its values over two well spaced finite subsets of the interval,
  one point of maximum on each unit subinterval, even and odd subintervals taken apart;
- a HARD leaf, the well spaced mean value: the sum of the norm of the block polynomial over any
  well spaced finite set of heights in the lower range is at most `C x^{1/2} (log x)^{-A}`, which
  is the shape of the conclusion of Theorem 4 applied through Lemma 10.
The assembly `leaf_section4Block_mean_value_positive_small_low_split` repeats the sealed
statement binder for binder and is proved from the two leaves with no further sorry, with the
constant doubled. The sealed statement keeps its own sorry by the folder convention.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF: the passage from the integral in display 4.1 to well spaced sums, P0069 page 11,
well spaced sets before Theorem 4, and page 27, display 4.1 from Theorem 4 via Lemma 10.
For continuous nonnegative `f` and any `a`, `b`, the integral from `a` to `b` is at most the
sum of `f` over two finite well spaced subsets of `[a, b]`. Proof idea: unit subintervals, a
maximum point on each, even and odd indices apart; empty sets when `b < a`.
Class: MEDIUM -/
theorem leaf_section4Block_integral_le_two_wellspaced_sums (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (a b : ℝ) :
    ∃ S₁ S₂ : Finset ℝ,
      (∀ t ∈ S₁, a ≤ t ∧ t ≤ b) ∧ (∀ t ∈ S₂, a ≤ t ∧ t ≤ b) ∧
      (∀ s ∈ S₁, ∀ t ∈ S₁, s ≠ t → 1 ≤ |s - t|) ∧
      (∀ s ∈ S₂, ∀ t ∈ S₂, s ≠ t → 1 ≤ |s - t|) ∧
      (∫ t in a..b, f t) ≤ ∑ t ∈ S₁, f t + ∑ t ∈ S₂, f t := by
  by_cases hab : a ≤ b
  · let N := ⌈b - a⌉₊
    let h : ℕ → ℝ := fun k => min (a + k) b
    have hmono (k : ℕ) : h k ≤ h (k + 1) := by
      dsimp [h]
      apply min_le_min_right
      push_cast
      linarith
    have hex (k : ℕ) :
        ∃ t ∈ Set.Icc (h k) (h (k + 1)), IsMaxOn f (Set.Icc (h k) (h (k + 1))) t :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hmono k)) hf.continuousOn
    choose t ht htmax using hex
    have hhk (k : ℕ) (hk : k < N) : h k = a + k := by
      have hlt : (k : ℝ) < b - a := (Nat.lt_ceil).1 hk
      exact min_eq_left (by linarith)
    have hh1 (k : ℕ) : h (k + 1) ≤ a + k + 1 := by
      exact (min_le_left _ _).trans (by push_cast; linarith)
    have ht_lo (k : ℕ) (hk : k < N) : a + k ≤ t k := by
      simpa only [hhk k hk] using (ht k).1
    have ht_hi (k : ℕ) : t k ≤ a + k + 1 := (ht k).2.trans (hh1 k)
    have ht_b (k : ℕ) : t k ≤ b := (ht k).2.trans (min_le_right _ _)
    have ht_a (k : ℕ) (hk : k < N) : a ≤ t k :=
      (le_add_of_nonneg_right (Nat.cast_nonneg k)).trans (ht_lo k hk)
    have hsep (j k : ℕ) (hj : j < N) (hk : k < N)
        (hpar : j % 2 = k % 2) (hne : j ≠ k) : 1 ≤ |t j - t k| := by
      rcases (show j + 2 ≤ k ∨ k + 2 ≤ j by omega) with h2 | h2
      · have : (j : ℝ) + 2 ≤ k := by exact_mod_cast h2
        have := ht_lo k hk
        have := ht_hi j
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have : (k : ℝ) + 2 ≤ j := by exact_mod_cast h2
        have := ht_lo j hj
        have := ht_hi k
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hpart (s : Finset ℕ) (hs : s ⊆ Finset.range N)
        (hp : ∀ j ∈ s, ∀ k ∈ s, j % 2 = k % 2) :
        (∀ v ∈ s.image t, a ≤ v ∧ v ≤ b) ∧
        (∀ u ∈ s.image t, ∀ v ∈ s.image t, u ≠ v → 1 ≤ |u - v|) ∧
        ∑ v ∈ s.image t, f v = ∑ k ∈ s, f (t k) := by
      have hinj : Set.InjOn t s := by
        intro j hj k hk heq
        by_contra hne
        have := hsep j k (Finset.mem_range.1 (hs hj)) (Finset.mem_range.1 (hs hk))
          (hp j hj k hk) hne
        rw [heq, sub_self, abs_zero] at this
        linarith
      refine ⟨?_, ?_, Finset.sum_image hinj⟩
      · intro v hv
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
        exact ⟨ht_a k (Finset.mem_range.1 (hs hk)), ht_b k⟩
      · intro u hu v hv huv
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hv
        exact hsep j k (Finset.mem_range.1 (hs hj)) (Finset.mem_range.1 (hs hk))
          (hp j hj k hk) (fun heq => huv (congrArg t heq))
    have hpiece (k : ℕ) (hk : k < N) :
        (∫ u in h k..h (k + 1), f u) ≤ f (t k) := by
      calc
        _ ≤ ∫ u in h k..h (k + 1), f (t k) :=
          intervalIntegral.integral_mono_on (hmono k) (hf.intervalIntegrable _ _)
            intervalIntegrable_const (fun u hu => htmax k hu)
        _ = (h (k + 1) - h k) * f (t k) := by simp
        _ ≤ 1 * f (t k) := by
          apply mul_le_mul_of_nonneg_right _ (hf0 _)
          rw [hhk k hk]
          have := hh1 k
          linarith
        _ = f (t k) := one_mul _
    have hsum : (∫ u in a..b, f u) =
        ∑ k ∈ Finset.range N, ∫ u in h k..h (k + 1), f u := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => hf.intervalIntegrable _ _)]
      congr 1
      · dsimp [h]
        simp [hab]
      · dsimp [h]
        exact (min_eq_right (by have := Nat.le_ceil (b - a); linarith)).symm
    let s₁ := (Finset.range N).filter (fun k => k % 2 = 0)
    let s₂ := (Finset.range N).filter (fun k => ¬ k % 2 = 0)
    have hp₁ := hpart s₁ (Finset.filter_subset _ _) (by
      intro j hj k hk
      simp only [s₁, Finset.mem_filter] at hj hk
      omega)
    have hp₂ := hpart s₂ (Finset.filter_subset _ _) (by
      intro j hj k hk
      simp only [s₂, Finset.mem_filter] at hj hk
      omega)
    refine ⟨s₁.image t, s₂.image t, hp₁.1, hp₂.1, hp₁.2.1, hp₂.2.1, ?_⟩
    rw [hp₁.2.2, hp₂.2.2, hsum, Finset.sum_filter_add_sum_filter_not]
    exact Finset.sum_le_sum (fun k hk => hpiece k (Finset.mem_range.1 hk))
  · refine ⟨∅, ∅, by simp, by simp, by simp, by simp, ?_⟩
    simp only [Finset.sum_empty, add_zero]
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg (le_of_not_ge hab)
      (fun t _ => hf0 t))

/-- LEAF: the well spaced mean value for the block over the lower height range, P0069 page 12,
Theorem 4, as applied on pages 26 and 27 through Lemma 10 to the factorization of the block of
display 4.7 into the polynomials `M_1 N L` with `d` in dyadic ranges, under the grouping
`max m n ≤ 0.46` of the sealed statement. For every finite set `S` of heights in
`[exp (log x ^ (1/3)), x ^ (1/4)]` whose distinct points are at distance at least one, the sum
over `S` of the norm of the block polynomial at `1/2 + i t` twisted by `χ` is at most
`C x^{1/2} (log x)^{-A}`, uniformly in `S`, `q ≤ (log x)^A` and `χ`. Non-vacuous: the vanishing
family meets it, and a set `S` of about `x^{1/4}` points makes the trivial bound fail.
Class: HARD -/
theorem leaf_section4Block_wellspaced_positive_small_low
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ S : Finset ℝ,
            (∀ t ∈ S, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ t ∧ t ≤ x ^ (1 / 4 : ℝ)) →
            (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
            ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- The height exponent written with a real half. -/
lemma s84a3_half_eq (t : ℝ) : Thm4.half t = ((1 / 2 : ℝ) : ℂ) + ↑t * Complex.I := by
  simp only [Thm4.half]
  push_cast
  ring

lemma s84a3_half_ne_zero (t : ℝ) : Thm4.half t ≠ 0 := by
  rw [s84a3_half_eq]
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre

/-- The norm of the twisted block polynomial is continuous in the height `t`. -/
lemma s84a3_block_norm_continuous (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ =>
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half t‖) := by
  refine Continuous.norm ?_
  refine continuous_finsetSum _ (fun k hk => ?_)
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le ⌊x / 2⌋₊) (Finset.mem_Ioc.mp hk).1
  have hkC : (k : ℂ) ≠ 0 := by
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    exact_mod_cast hkne
  have hden : Continuous (fun t : ℝ => (k : ℂ) ^ Thm4.half t) := by
    have hfun : (fun t : ℝ => (k : ℂ) ^ Thm4.half t) =
        fun t : ℝ => (k : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + ↑t * Complex.I) := by
      funext t
      rw [s84a3_half_eq]
    rw [hfun]
    exact (continuous_const_cpow' hkC).comp (by fun_prop)
  exact Continuous.div continuous_const hden
    (fun t => (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (s84a3_half_ne_zero t)).mpr hkC)

/-- The assembly, with nothing open beyond the two leaves above: the sealed statement
`leaf_section4Block_mean_value_positive_small_low`, binder for binder, with constant `2 C`. -/
theorem leaf_section4Block_mean_value_positive_small_low_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (1 / 4 : ℝ)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η, hη, H⟩ := leaf_section4Block_wellspaced_positive_small_low h4 B hB
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  obtain ⟨C, X, hC⟩ := H ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  refine ⟨C + C, X, ?_⟩
  intro x hx q hq hlog χ
  obtain ⟨S₁, S₂, hS₁, hS₂, hw₁, hw₂, hint⟩ :=
    leaf_section4Block_integral_le_two_wellspaced_sums _
      (s84a3_block_norm_continuous ε m n a b x q χ) (fun t => norm_nonneg _)
      (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (1 / 4 : ℝ))
  calc _ ≤ _ := hint
    _ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) + C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add (hC x hx q hq hlog χ S₁ hS₁ hw₁) (hC x hx q hq hlog χ S₂ hS₂ hw₂)
    _ = (C + C) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Decomp528a

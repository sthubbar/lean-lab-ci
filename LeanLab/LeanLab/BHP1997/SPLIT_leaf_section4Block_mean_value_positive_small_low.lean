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
  rcases le_or_gt b a with hba | hab
  · refine ⟨∅, ∅, by simp, by simp, by simp, by simp, ?_⟩
    simp only [Finset.sum_empty, add_zero]
    rw [intervalIntegral.integral_symm]
    have : 0 ≤ ∫ t in b..a, f t := intervalIntegral.integral_nonneg hba (fun t _ => hf0 t)
    linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈b - a⌉₊ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ i, g i = min (a + i) b := ⟨_, fun _ => rfl⟩
  have hgmono : ∀ i, g i ≤ g (i + 1) := by
    intro i
    rw [hg, hg]
    push_cast
    exact min_le_min_right _ (by linarith)
  have hgstep : ∀ i, g (i + 1) - g i ≤ 1 := by
    intro i
    rw [hg, hg]
    push_cast
    simp only [min_def]
    split_ifs <;> linarith
  have hex : ∀ i, ∃ t ∈ Set.Icc (g i) (g (i + 1)), IsMaxOn f (Set.Icc (g i) (g (i + 1))) t :=
    fun i => isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (hgmono i)) hf.continuousOn
  choose p hpmem hpmax using hex
  have hga : ∀ i, a ≤ g i := by
    intro i
    rw [hg]
    exact le_min (le_add_of_nonneg_right (Nat.cast_nonneg i)) hab.le
  have hgb : ∀ i, g i ≤ b := fun i => by rw [hg]; exact min_le_right _ _
  have hpab : ∀ i, a ≤ p i ∧ p i ≤ b :=
    fun i => ⟨(hga i).trans (hpmem i).1, (hpmem i).2.trans (hgb _)⟩
  have hgN : ∀ j, j < N → g j = a + j := by
    intro j hj
    have : (j : ℝ) < b - a := Nat.lt_ceil.mp (hN ▸ hj)
    rw [hg]
    exact min_eq_left (by linarith)
  have hsep : ∀ i j, i < j → j < N → (j : ℝ) - i - 1 ≤ p j - p i := by
    intro i j _ hjN
    have h1 := (hpmem j).1
    have h2 := (hpmem i).2
    rw [hgN j hjN] at h1
    have h3 : g (i + 1) ≤ a + ((i + 1 : ℕ) : ℝ) := by rw [hg]; exact min_le_left _ _
    push_cast at h3
    linarith
  have hspace : ∀ r : ℕ, ∀ i ∈ (Finset.range N).filter (fun i => i % 2 = r),
      ∀ j ∈ (Finset.range N).filter (fun i => i % 2 = r), i ≠ j → 1 ≤ |p i - p j| := by
    intro r i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · have h2 : i + 2 ≤ j := by omega
      have := hsep i j h hj.1
      have h2' : ((i : ℝ) + 2 ≤ j) := by exact_mod_cast h2
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    · have h2 : j + 2 ≤ i := by omega
      have := hsep j i h hi.1
      have h2' : ((j : ℝ) + 2 ≤ i) := by exact_mod_cast h2
      exact le_trans (by linarith) (le_abs_self _)
  have hinj : ∀ r, Set.InjOn p ((Finset.range N).filter (fun i => i % 2 = r)) := by
    intro r i hi j hj hpij
    by_contra hne
    have := hspace r i hi j hj hne
    rw [hpij, sub_self, abs_zero] at this
    linarith
  have hmemab : ∀ r, ∀ t ∈ ((Finset.range N).filter (fun i => i % 2 = r)).image p,
      a ≤ t ∧ t ≤ b := by
    intro r t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hpab i
  have hsp : ∀ r, ∀ s ∈ ((Finset.range N).filter (fun i => i % 2 = r)).image p,
      ∀ t ∈ ((Finset.range N).filter (fun i => i % 2 = r)).image p, s ≠ t → 1 ≤ |s - t| := by
    intro r s hs t ht hst
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact hspace r i hi j hj (fun h => hst (h ▸ rfl))
  refine ⟨((Finset.range N).filter (fun i => i % 2 = 0)).image p,
    ((Finset.range N).filter (fun i => i % 2 = 1)).image p,
    hmemab 0, hmemab 1, hsp 0, hsp 1, ?_⟩
  rw [Finset.sum_image (hinj 0), Finset.sum_image (hinj 1)]
  have hsplit : ∑ i ∈ Finset.range N, f (p i) =
      ∑ i ∈ (Finset.range N).filter (fun i => i % 2 = 0), f (p i) +
      ∑ i ∈ (Finset.range N).filter (fun i => i % 2 = 1), f (p i) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun i => i % 2 = 0)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hsplit]
  have hg0 : g 0 = a := by rw [hg]; simp [hab.le]
  have hgNN : g N = b := by
    rw [hg]
    have := Nat.le_ceil (b - a)
    rw [← hN] at this
    exact min_eq_right (by linarith)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (a := g) (n := N)
    (fun i _ => hf.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  rw [hg0, hgNN] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  calc ∫ t in g i..g (i + 1), f t ≤ ∫ _ in g i..g (i + 1), f (p i) :=
        intervalIntegral.integral_mono_on (hgmono i) (hf.intervalIntegrable _ _)
          intervalIntegrable_const (fun t ht => hpmax i ht)
    _ = (g (i + 1) - g i) * f (p i) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 1 * f (p i) := mul_le_mul_of_nonneg_right (hgstep i) (hf0 _)
    _ = f (p i) := one_mul _

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

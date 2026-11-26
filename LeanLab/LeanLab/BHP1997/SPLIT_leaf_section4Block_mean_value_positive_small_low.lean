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
  rcases lt_or_ge b a with hba | hab
  · refine ⟨∅, ∅, by simp, by simp, by simp, by simp, ?_⟩
    rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hba.le (fun t _ => hf0 t)
    simp only [Finset.sum_empty, add_zero]
    linarith
  set e : ℕ → ℝ := fun k => min (a + k) b with he
  have hmono : ∀ k, e k ≤ e (k + 1) := by
    intro k; simp only [he]; push_cast
    exact min_le_min_right _ (by linarith)
  have hex : ∀ k, ∃ t ∈ Set.Icc (e k) (e (k + 1)),
      ∀ s ∈ Set.Icc (e k) (e (k + 1)), f s ≤ f t := by
    intro k
    obtain ⟨t, ht, hmax⟩ := (isCompact_Icc (a := e k) (b := e (k+1))).exists_isMaxOn
      (Set.nonempty_Icc.2 (hmono k)) hf.continuousOn
    exact ⟨t, ht, fun s hs => hmax hs⟩
  choose t ht htmax using hex
  set n : ℕ := ⌈b - a⌉₊ with hn
  have hlt : ∀ k, k < n → (k : ℝ) < b - a := fun k hk => Nat.lt_ceil.1 hk
  have he_k : ∀ k, k < n → e k = a + k := by
    intro k hk; simp only [he]; exact min_eq_left (by linarith [hlt k hk])
  have ht_lo : ∀ k, k < n → a + k ≤ t k := by
    intro k hk; rw [← he_k k hk]; exact (ht k).1
  have ht_hi : ∀ k, t k ≤ a + k + 1 := by
    intro k; have := (ht k).2; simp only [he] at this; push_cast at this
    linarith [min_le_left (a + ((k:ℝ) + 1)) b]
  have ht_b : ∀ k, t k ≤ b := by
    intro k; have := (ht k).2; simp only [he] at this
    linarith [min_le_right (a + ((k+1 : ℕ):ℝ)) b]
  have hsep : ∀ k, k < n → ∀ k', k' < n → k % 2 = k' % 2 → k < k' →
      1 ≤ |t k - t k'| := by
    intro k hk k' hk' hpar hkk'
    have h2 : k + 2 ≤ k' := by omega
    have h2' : (k : ℝ) + 2 ≤ k' := by exact_mod_cast h2
    have := ht_lo k' hk'; have := ht_hi k
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have hsep' : ∀ k, k < n → ∀ k', k' < n → k % 2 = k' % 2 → k ≠ k' →
      1 ≤ |t k - t k'| := by
    intro k hk k' hk' hpar hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hsep k hk k' hk' hpar h
    · rw [abs_sub_comm]; exact hsep k' hk' k hk hpar.symm h
  have hinj : ∀ k, k < n → ∀ k', k' < n → k % 2 = k' % 2 → t k = t k' → k = k' := by
    intro k hk k' hk' hpar heq
    by_contra hne
    have := hsep' k hk k' hk' hpar hne
    rw [heq, sub_self, abs_zero] at this; linarith
  set E := (Finset.range n).filter (fun k => k % 2 = 0)
  set O := (Finset.range n).filter (fun k => ¬ k % 2 = 0)
  have hmemSet : ∀ (P : ℕ → Prop) [DecidablePred P], ∀ s ∈ ((Finset.range n).filter P).image t,
      a ≤ s ∧ s ≤ b := by
    intro P _ s hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hs
    have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
    exact ⟨by have := ht_lo k hk'; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith, ht_b k⟩
  -- integral bound
  have hint : (∫ s in a..b, f s) ≤ ∑ k ∈ Finset.range n, f (t k) := by
    have he0 : e 0 = a := by simp [he, hab]
    have hen : e n = b := by
      simp only [he]; exact min_eq_right (by linarith [Nat.le_ceil (b - a)])
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (a := e) (n := n)
      (μ := MeasureTheory.volume)
      (fun k _ => hf.intervalIntegrable _ _)
    rw [he0, hen] at hsum
    rw [← hsum]
    apply Finset.sum_le_sum
    intro k _
    calc (∫ s in e k..e (k+1), f s) ≤ ∫ s in e k..e (k+1), f (t k) :=
          intervalIntegral.integral_mono_on (hmono k) (hf.intervalIntegrable _ _)
            intervalIntegrable_const (fun s hs => htmax k s hs)
      _ = (e (k+1) - e k) * f (t k) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 1 * f (t k) := by
          apply mul_le_mul_of_nonneg_right _ (hf0 _)
          simp only [he]; push_cast
          rcases le_total (a + k) b with h | h
          · rw [min_eq_left h]; linarith [min_le_left (a + ((k:ℝ) + 1)) b]
          · rw [min_eq_right h, min_eq_right (by linarith)]; linarith
      _ = f (t k) := one_mul _
  refine ⟨E.image t, O.image t, hmemSet _, hmemSet _, ?_, ?_, ?_⟩
  · intro s hs s' hs' hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hs'
    simp only [E, Finset.mem_filter, Finset.mem_range] at hk hk'
    exact hsep' k hk.1 k' hk'.1 (by omega) (fun h => hne (h ▸ rfl))
  · intro s hs s' hs' hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hs'
    simp only [O, Finset.mem_filter, Finset.mem_range] at hk hk'
    exact hsep' k hk.1 k' hk'.1 (by omega) (fun h => hne (h ▸ rfl))
  · rw [Finset.sum_image, Finset.sum_image]
    · have := Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k % 2 = 0)
        (fun k => f (t k))
      rw [this]; exact hint
    · intro k hk k' hk' heq
      simp only [O, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk hk'
      exact hinj k hk.1 k' hk'.1 (by omega) heq
    · intro k hk k' hk' heq
      simp only [E, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk hk'
      exact hinj k hk.1 k' hk'.1 (by omega) heq

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

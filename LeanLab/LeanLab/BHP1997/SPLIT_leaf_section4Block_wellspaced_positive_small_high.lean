/-
Split of `leaf_section4Block_wellspaced_positive_small_high` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small_high.
burst-20261124 S5, bundle E, unit S5-13.

The parent is the well spaced mean value for the concrete tapered block of P0069 pages 26 and
27, at the positive height, over heights from x^(1/4) to x^(0.45 - 2 eps/3), in the repaired
region max m n at most 0.46. The proof of display 3.9 on P0069 page 12 opens with "by a
simple dyadic argument we may suppose" that all heights lie in one shell `[T/2, T]`, and
Lemma 10 on page 23 is stated for such shells, display 3.37. This split makes that dyadic
reduction explicit:

* LEAF `leaf_section4Block_wellspaced_positive_small_high_shell`, Class HARD, the one open leaf:
  the parent bound for well spaced sets that also lie in one dyadic shell `[T/2, T]`, from
  Lemma 10 under 3.39 after the page 27 decomposition into `M1 N L` over dyadic `D`.
* Glue, PROVED: the shell count `leaf_section4Block_mean_value_negative_large_upper_t_dyadic`
  of the sibling split, reused, and the logarithm count below.
* Assembly `leaf_section4Block_wellspaced_positive_small_high_split`: the parent statement,
  binder for binder, with no sorry. The shell leaf is used at `A + 1`, the extra logarithm
  pays for at most `4 log x` shells, and the constant becomes `4 |C|`.

The parent keeps its own sorry, as this file imports it; folder convention.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small_high

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF: Lemma 10 for this block over one dyadic shell of well spaced heights in the lower
range. P0069 page 23 Lemma 10 with the shells of display 3.37, under 3.39 in the repaired
form max m n at most 0.46, see Lemma11_12.lemma12_339_ok; page 12 display 3.9 and the
dyadic argument after it; page 27, the block as `M1 N L` summed over dyadic `D`. For every
`T` and every finite one separated set `S` of heights in `[x ^ (1/4), x ^ (0.45 - 2 ε / 3)]`
and in `[T/2, T]`, the sum over `S` of the block polynomial norms at `1/2 + i t` is
`O (x^(1/2) (log x)^(-A))`, with the parent threshold, region, coefficient and modulus
hypotheses. Smaller than the parent: one shell only. Not vacuous: met by the zero family.
Class: HARD -/
theorem leaf_section4Block_wellspaced_positive_small_high_shell
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ T : ℝ, ∀ S : Finset ℝ,
            (∀ t ∈ S, x ^ (1 / 4 : ℝ) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3) ∧ T / 2 ≤ t ∧ t ≤ T) →
            (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
            ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Glue, PROVED from the dyadic glue of the sibling split. Shell bounds at exponent `A + 1`
give the bound at exponent `A` for a set of heights in `[lo, hi]` with `1 ≤ lo` and
`1 ≤ hi ≤ x`: the number of shells is at most `logb 2 hi + 2 ≤ 4 log x`. P0069 page 12, the
dyadic argument. -/
private theorem wellspaced_positive_small_high_shells_to_set (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t)
    (x lo hi C A : ℝ) (hlog1 : 1 ≤ Real.log x) (hlo1 : 1 ≤ lo)
    (hhi1 : 1 ≤ hi) (hhix : hi ≤ x) (S : Finset ℝ) (hS : ∀ t ∈ S, lo ≤ t ∧ t ≤ hi)
    (hshell : ∀ T : ℝ, ∀ S' ⊆ S, (∀ t ∈ S', T / 2 ≤ t ∧ t ≤ T) →
      ∑ t ∈ S', g t ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1))) :
    ∑ t ∈ S, g t ≤ 4 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  have hlogpos : 0 < Real.log x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hP : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)) :=
    mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlogpos.le _)
  have hK : ∀ T : ℝ, ∀ S' ⊆ S, (∀ t ∈ S', T / 2 ≤ t ∧ t ≤ T) →
      ∑ t ∈ S', g t ≤ |C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1))) := by
    intro T S' hS' hT
    refine (hshell T S' hS' hT).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hP
  have hd := leaf_section4Block_mean_value_negative_large_upper_t_dyadic g hg hi
    (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) hhi1 S
    (fun t ht => ⟨hlo1.trans (hS t ht).1, (hS t ht).2⟩) hK
  have hlb : 0 ≤ Real.logb 2 hi := Real.logb_nonneg (by norm_num) hhi1
  have hlb2 : Real.logb 2 hi ≤ 2 * Real.log x := by
    unfold Real.logb
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlh : Real.log hi ≤ Real.log x := Real.log_le_log (by linarith) hhix
    have hlh0 : 0 ≤ Real.log hi := Real.log_nonneg hhi1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hrp : Real.log x * Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) := by
    rw [show -A = 1 + (-(A + 1)) by ring, Real.rpow_add hlogpos, Real.rpow_one]
  calc ∑ t ∈ S, g t ≤ (Real.logb 2 hi + 2) *
        (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) := hd
    _ ≤ (4 * Real.log x) * (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (abs_nonneg _) hP)
    _ = 4 * |C| * x ^ (1 / 2 : ℝ) * (Real.log x * Real.log x ^ (-(A + 1))) := by ring
    _ = 4 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by rw [hrp]

/-- The assembly, with no sorry. The parent statement binder for binder, from the shell leaf
and the glue, never from the parent. The threshold is capped at one half, so that the upper end of the range is at least one and at most x once x is at least e; the constant of the conclusion is `4 |C|`. -/
theorem leaf_section4Block_wellspaced_positive_small_high_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ S : Finset ℝ,
            (∀ t ∈ S, x ^ (1 / 4 : ℝ) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3)) →
            (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
            ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η, hη, H⟩ := leaf_section4Block_wellspaced_positive_small_high_shell h4 B hB
  refine ⟨min η (1 / 2), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  have hεη' : ε < η := hεη.trans_le (min_le_left _ _)
  have hε2 : ε < 1 / 2 := hεη.trans_le (min_le_right _ _)
  obtain ⟨C, X, hC⟩ := H ε hε hεη' m n hm0 hn0 hmn a b ha hb (A + 1) (by linarith)
  refine ⟨4 * |C|, max X (Real.exp 1), ?_⟩
  intro x hx q hq hlog χ S hS hsp
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hq' : (q : ℝ) ≤ Real.log x ^ (A + 1) :=
    hlog.trans (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))
  have he0 : (0 : ℝ) ≤ (0.45 - 2 * ε / 3) := by linarith
  have he1 : (0.45 - 2 * ε / 3) ≤ 1 := by linarith
  have hhi1 : 1 ≤ x ^ (0.45 - 2 * ε / 3) := Real.one_le_rpow hx1 he0
  have hhix : x ^ (0.45 - 2 * ε / 3) ≤ x :=
    (Real.rpow_le_rpow_of_exponent_le hx1 he1).trans_eq (Real.rpow_one x)
  have hlo1 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  exact wellspaced_positive_small_high_shells_to_set
    (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖)
    (fun t => norm_nonneg _) x (x ^ (1 / 4 : ℝ)) (x ^ (0.45 - 2 * ε / 3)) C A hlog1 hlo1 hhi1 hhix S hS
    (fun T S' hS' hT => hC x hxX q hq hq' χ T S'
      (fun t ht => ⟨(hS t (hS' ht)).1, (hS t (hS' ht)).2, (hT t ht).1, (hT t ht).2⟩)
      (fun t ht u hu htu => hsp t (hS' ht) u (hS' hu) htu))

end LeanLab.BHP1997.Decomp528a

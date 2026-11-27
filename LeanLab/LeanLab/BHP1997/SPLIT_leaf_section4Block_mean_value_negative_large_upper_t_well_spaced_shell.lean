/-
Split of `leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_negative_large_upper_t. CLOUD S5 burst-20261124.

The parent is the bound 3.9 of P0069 page 12 for the tapered block of pages 26 and 27 over
one dyadic shell of one separated heights, in the region of display 4.8. Page 27 proves
it by writing the truncated Mobius coefficient of page 26 as a sum over `d ~ D`, applying
Lemma 10 to each product `M1(s) N(s) L(s)` and then summing "over D = γ 2^(-j) for
j = 0, 1, ...". This file proves the sum over D and leaves one leaf, Lemma 10 for one piece:

* Definition `upperTDyadicPiece`, for a reviewer: the block with `d` restricted to the
  range `γ 2^(-j-1) < d ≤ γ 2^(-j)`, written as `⌊logb 2 (γ / d)⌋₊ = j`.
* Glue, PROVED: the dyadic decomposition of the truncated coefficient, linearity of the
  convolution 4.7, the block as the sum of its pieces, the triangle inequality over pieces,
  and the count of at most `2 log x` pieces.
* LEAF `leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_dyadic_piece`, HARD:
  the shell bound for one piece, uniformly in `j`.
* Assembly `leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_split`: the parent
  statement verbatim, from the leaf at `A + 1`, with no sorry.

The parent keeps its sorry, as this file imports it. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_negative_large_upper_t

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- Page 27 of P0069, the piece of the block of display 4.7 whose Mobius variable `d`
lies in one dyadic range `d ~ D`, `D = γ 2^(-j)`, `γ = x^(ε/12)`, the `w` of the paper being
`exp ((log x)^(9/10))` as in `section4Block`. For `1 ≤ d ≤ γ` the condition
`⌊logb 2 (γ / d)⌋₊ = j` says exactly `γ 2^(-j-1) < d ≤ γ 2^(-j)`. Its Dirichlet polynomial is
the product `M1(s) N(s) L(s)` displayed on page 27, with the taper of `section4Block`. -/
noncomputable def upperTDyadicPiece (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) (j : ℕ) :
    ℝ → ℕ → ℝ :=
  tapered (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
    (fun l => ∑ d ∈ (l.divisors.filter (fun d : ℕ =>
        d ∣ Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ))) ∧
          (d : ℝ) ≤ x ^ (ε / 12))).filter
        (fun d : ℕ => ⌊Real.logb 2 (x ^ (ε / 12) / d)⌋₊ = j),
      (ArithmeticFunction.moebius d : ℝ)) k)

/-- Glue, PROVED. Page 27, "sum over `D = γ 2^(-j)` for `j = 0, 1, ...`": the truncated
Mobius coefficient of page 26 splits over the dyadic ranges of `d`, finitely many since
`d ≥ 1`. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_rough_dyadic
    (l : ℕ) (z γ : ℝ) (J : ℕ) (hJ : Real.logb 2 γ < J) :
    truncatedRough l z γ = ∑ j ∈ Finset.range J,
      ∑ d ∈ (l.divisors.filter (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ)).filter
        (fun d : ℕ => ⌊Real.logb 2 (γ / d)⌋₊ = j), (ArithmeticFunction.moebius d : ℝ) := by
  unfold truncatedRough
  rw [Finset.sum_fiberwise_of_maps_to]
  intro d hd
  obtain ⟨hdl, _, hdγ⟩ := Finset.mem_filter.mp hd
  have hd1 : (1 : ℝ) ≤ d := by
    have := Nat.pos_of_mem_divisors hdl
    exact_mod_cast this
  apply Finset.mem_range.mpr
  have hγ : 0 < γ := by linarith
  have h1 : Real.logb 2 (γ / d) ≤ Real.logb 2 γ :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos hγ (by linarith))
      (div_le_self hγ.le hd1)
  have h0 : 0 ≤ Real.logb 2 (γ / d) :=
    Real.logb_nonneg (by norm_num) ((one_le_div (by linarith)).mpr hdγ)
  have := Nat.floor_le h0
  have h2 : (⌊Real.logb 2 (γ / d)⌋₊ : ℝ) < J := by linarith
  exact_mod_cast h2

/-- Glue, PROVED. The convolution of display 4.7 is linear in its last factor. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_conv_sum
    (M N : ℝ) (a b : ℕ → ℝ) (ι : Finset ℕ) (r : ℕ → ℕ → ℝ) (k : ℕ) :
    finiteConvolution M N a b (fun l => ∑ j ∈ ι, r j l) k =
      ∑ j ∈ ι, finiteConvolution M N a b (r j) k := by
  unfold finiteConvolution
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp [Finset.mul_sum]

/-- Glue, PROVED. Page 27: the block is the sum of its dyadic pieces in `d`. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_block_eq
    (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) (J : ℕ)
    (hJ : Real.logb 2 (x ^ (ε / 12)) < J) (k : ℕ) :
    section4Block ε m n a b x k =
      ∑ j ∈ Finset.range J, upperTDyadicPiece ε m n a b j x k := by
  simp only [section4Block, auxiliaryConvolution, upperTDyadicPiece, tapered]
  rw [← Finset.mul_sum]
  congr 1
  rw [show (fun l => truncatedRough l (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12))) =
      fun l => ∑ j ∈ Finset.range J,
        ∑ d ∈ (l.divisors.filter (fun d : ℕ =>
          d ∣ Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ))) ∧
            (d : ℝ) ≤ x ^ (ε / 12))).filter
          (fun d : ℕ => ⌊Real.logb 2 (x ^ (ε / 12) / d)⌋₊ = j),
        (ArithmeticFunction.moebius d : ℝ) from
      funext fun l => leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_rough_dyadic
        l _ _ J hJ]
  exact leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_conv_sum _ _ _ _ _ _ _

/-- Glue, PROVED. The shell sum of a polynomial whose coefficients are a sum of `J` pieces
is at most `J` times a uniform bound for the shell sums of the pieces. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_pieces_sum
    (S : Finset ℝ) (I : Finset ℕ) (J : ℕ) (c : ℕ → ℕ → ℝ) (w : ℝ → ℕ → ℂ) (K : ℝ)
    (hK : ∀ j, ∑ t ∈ S, ‖∑ k ∈ I, (c j k : ℂ) * w t k‖ ≤ K) :
    ∑ t ∈ S, ‖∑ k ∈ I, ((∑ j ∈ Finset.range J, c j k : ℝ) : ℂ) * w t k‖ ≤ J * K := by
  calc ∑ t ∈ S, ‖∑ k ∈ I, ((∑ j ∈ Finset.range J, c j k : ℝ) : ℂ) * w t k‖
      = ∑ t ∈ S, ‖∑ j ∈ Finset.range J, ∑ k ∈ I, (c j k : ℂ) * w t k‖ := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        congr 1
        push_cast
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ S, ∑ j ∈ Finset.range J, ‖∑ k ∈ I, (c j k : ℂ) * w t k‖ :=
        Finset.sum_le_sum (fun t _ => norm_sum_le _ _)
    _ = ∑ j ∈ Finset.range J, ∑ t ∈ S, ‖∑ k ∈ I, (c j k : ℂ) * w t k‖ := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range J, K := Finset.sum_le_sum (fun j _ => hK j)
    _ = J * K := by simp

/-- LEAF: Lemma 10 applied to one dyadic piece `M1(s) N(s) L(s)` of the block, P0069 page 27,
"apply Lemma 10 and 11 to" the product with `M1` carrying `d ~ D`, `D = γ 2^(-j)`; "in each
case M1 has length MD ≤ M x^(ε/12) so (3.38) or (3.39) holds", here display 4.8 giving
the grouping 3.38, see `Lemma11_12.lemma12_338`; Lemma 10, page 23,
with 3.37, gives the bound 3.9 of page 12. For every `j`, every `T` and every finite one
separated set `S` of heights in the range and in `[T/2, T]`, the sum over `S` of the norms of
the piece polynomial over the whole block from x/2 to 2x at `1/2 - i t` is `O (x^(1/2) (log x)^(-A))`,
uniformly in `j`. Smaller than the parent shell leaf: one dyadic range of `d` only, the sum
over `D` being proved glue. Not vacuous: met by the zero family.
Class: HARD -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_dyadic_piece
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ j : ℕ, ∀ T : ℝ, ∀ S : Finset ℝ,
            (∀ t ∈ S, x ^ ((0.45 - 2 * ε / 3) / 2) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3) ∧ T / 2 ≤ t ∧ t ≤ T) →
            (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) →
            (∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (upperTDyadicPiece ε m n a b j x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Glue, PROVED. The number of dyadic ranges: with `γ = x^(ε/12)`, `0 < ε < 1` and
`log x ≥ 1`, `⌊logb 2 γ⌋₊ + 1 ≤ 2 log x`. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_count
    (ε x : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hx1 : 1 ≤ x) (hlog1 : 1 ≤ Real.log x) :
    ((⌊Real.logb 2 (x ^ (ε / 12))⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlb : Real.logb 2 (x ^ (ε / 12)) = ε / 12 * Real.log x / Real.log 2 := by
    rw [Real.logb, Real.log_rpow hx0]
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h0 : 0 ≤ Real.logb 2 (x ^ (ε / 12)) := by
    rw [hlb]; positivity
  have h1 : Real.logb 2 (x ^ (ε / 12)) ≤ Real.log x := by
    rw [hlb, div_le_iff₀ (by linarith)]
    nlinarith
  have := Nat.floor_le h0
  push_cast
  linarith

/-- The assembly, with no sorry. The shell leaf statement of the parent file, binder for
binder, from the dyadic piece leaf at `A + 1` and the glue above: the block is the sum of
at most `2 log x` pieces, page 27 "then sum over D". The threshold is capped at one and the
constant becomes `2 |C|`. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ T : ℝ, ∀ S : Finset ℝ,
            (∀ t ∈ S, x ^ ((0.45 - 2 * ε / 3) / 2) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3) ∧ T / 2 ≤ t ∧ t ≤ T) →
            (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) →
            (∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η, hη, H⟩ := leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_dyadic_piece h4 B hB
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  intro ε hε hεη m n hm0 hn0 hreg a b ha hb A hA
  have hεη' : ε < η := hεη.trans_le (min_le_left _ _)
  have hε1 : ε < 1 := hεη.trans_le (min_le_right _ _)
  obtain ⟨C, X, hC⟩ := H ε hε hεη' m n hm0 hn0 hreg a b ha hb (A + 1) (by linarith)
  refine ⟨2 * |C|, max X (Real.exp 1), ?_⟩
  intro x hx q hq hlog χ T S hS hsep
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hlogpos : 0 < Real.log x := by linarith
  have hq' : (q : ℝ) ≤ Real.log x ^ (A + 1) :=
    hlog.trans (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))
  set J := ⌊Real.logb 2 (x ^ (ε / 12))⌋₊ + 1 with hJdef
  have hJ : Real.logb 2 (x ^ (ε / 12)) < J := by
    rw [hJdef]; push_cast; exact Nat.lt_floor_add_one _
  have hP : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hlogpos.le _)
  have hsum := leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_pieces_sum S
    (Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊) J (fun j k => upperTDyadicPiece ε m n a b j x k)
    (fun t k => χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t))
    (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) (fun j => by
      refine le_trans ?_ ((hC x hxX q hq hq' χ j T S hS hsep).trans ?_)
      · apply le_of_eq
        refine Finset.sum_congr rfl (fun t _ => ?_)
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hP)
  have hcount := leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_count ε x hε hε1 hx1 hlog1
  have hrp : Real.log x * Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) := by
    rw [show -A = 1 + (-(A + 1)) by ring, Real.rpow_add hlogpos, Real.rpow_one]
  calc (∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half (-t)‖)
      = ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          ((∑ j ∈ Finset.range J, upperTDyadicPiece ε m n a b j x k : ℝ) : ℂ) *
            (χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t))‖ := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← leaf_section4Block_mean_value_negative_large_upper_t_well_spaced_shell_block_eq ε m n a b x J hJ k]
        ring
    _ ≤ J * (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) := hsum
    _ ≤ (2 * Real.log x) * (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) :=
        mul_le_mul_of_nonneg_right hcount (mul_nonneg (abs_nonneg _) hP)
    _ = 2 * |C| * x ^ (1 / 2 : ℝ) * (Real.log x * Real.log x ^ (-(A + 1))) := by ring
    _ = 2 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by rw [hrp]

end LeanLab.BHP1997.Decomp528a

import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.PrimeKernel264
import LeanLab.ExceptionalSet.MajorSupplyJ200
import LeanLab.ExceptionalSet.BoundarySupplyJ200
import LeanLab.ExceptionalSet.CoeffSupplyJ200
import LeanLab.ExceptionalSet.MajorLeafJ200
import LeanLab.ExceptionalSet.TailSupplyJ200
import LeanLab.ExceptionalSet.UpJ200.Decomp467a

/-!
Decomposition of Theorem 1 of P0082, Brüdern and Perelli 1998, repaired in unit U-1610.
Source: journal pages 357 display (6), 365 Lemma 8, 366 end of section 5.
The old leaves `leaf_dyadic_split`, `leaf_dyadic_sum` and `leaf_dyadic_sum_exp` were false and
`leaf_minor_bound`, `leaf_major_bound` were proved of two definitions equal to `0`; the old
`leaf_dyadic_bound` was Theorem 1 itself in dyadic form, so the old assembly was circular with the
sorry `BrudernPerelli1998.brudernPerelli`. Refutations are in `Audit1610`.
`leaf_dyadic_bound` is now an assembly from the major arc leaf, the minor arc leaf, the Fourier
identity leaf and the dissection leaf. Nothing here uses `brudernPerelli`.
-/

namespace LeanLab.ExceptionalSet.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun nu calE eC)

attribute [local instance] Classical.propDecidable

/-- Number of exceptions in the dyadic block `[M, 2M)`. Half open, so that the blocks at
`M = 2 ^ j` partition the positive integers, `n = 1` included. -/
noncomputable def Eγ_dyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The dyadic indices `2 ^ j ≤ N`, `j ≤ log₂ N`. -/
noncomputable def dyadicIdx (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 N + 1)).image (fun j => 2 ^ j)

/-- The window of section 5, p. 366: `n ≤ 2N` with `X/2 < ν_n ≤ X`, `X = F(N)`. -/
noncomputable def window (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

/-- The integral over the major arcs `𝔑` in (6) at `v = F(n)`, with `X = F(N)`, `P = X^{6δ}`,
`Δ = ℰ^{-1/8}`, `ℰ = exp(κ (log N)^{3-2γ})`, pp. 357 and 365. -/
noncomputable def majorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The integral over the minor arcs `𝔫 = ℝ \ 𝔑` in (6), same parameters. -/
noncomputable def minorInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
      * eC (-(α * F γ n))

/-- The `n` of the window where the major arc integral misses `c₀ X ℰ^{-1/10}`, Lemma 8 p. 365. -/
noncomputable def Eγ_major_block (γ δ κ c₀ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card

/-- The `n` of the window where the minor arc integral exceeds `X ℰ^{-1/3}`, p. 366. -/
noncomputable def Eγ_minor_block (γ δ κ : ℝ) (N : ℕ) : ℕ :=
  ((window γ N).filter (fun n =>
    F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖)).card

/-- The members of a set `Bad` of integers lying in the window of `N`. -/
noncomputable def blockCount (γ : ℝ) (Bad : ℕ → Prop) (N : ℕ) : ℕ :=
  ((window γ N).filter Bad).card

/-- The members of a set `Bad` of integers lying in the block `[M, 2M)`. -/
noncomputable def dyadicCount (Bad : ℕ → Prop) (M : ℕ) : ℕ :=
  ((Finset.Ico M (2 * M)).filter Bad).card

/-- LEAF page 354: Trivial bound on dyadic exceptions. -/
theorem leaf_dyadic_trivial (γ : ℝ) (M : ℕ) :
    Eγ_dyadic γ M ≤ M := by
  unfold Eγ_dyadic
  have h : (Finset.Ico M (2 * M)).card = M := by
    rw [Nat.card_Ico]
    omega
  calc (Finset.Ico M (2 * M)).filter (fun n => ¬ Solvable γ n) |>.card
    _ ≤ (Finset.Ico M (2 * M)).card := Finset.card_filter_le _ _
    _ = M := h

/-- LEAF page 357, display (6). For large `N` every `n` of the window with no solution is bad for
the major arcs or for the minor arcs: `majorInt + minorInt = r(F(n))`, the sum (5) of
`log p₁ log p₂ w(p₁ + p₂ - F(n))` over `P < p₁, p₂ ≤ X`, and `w` vanishes off `|x| < 1`, so
`r(F(n)) = 0` when `n` has no solution. Then `(majorInt).re ≤ ‖minorInt‖`, and
`ℰ^{-1/3} < c₀ ℰ^{-1/10}` for large `N`. -/
theorem leaf_dyadic_split (γ δ κ c₀ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ) (hκ : 0 < κ)
    (hc₀ : 0 < c₀) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      blockCount γ (fun n => ¬ Solvable γ n) N ≤
        Eγ_minor_block γ δ κ N + Eγ_major_block γ δ κ c₀ N := by
  obtain ⟨N₀, hN₀⟩ := PrimeKernel264.split_parameters_eventually γ δ κ c₀ h1 h2 hδ hκ hc₀
  refine ⟨N₀, fun N hN => ?_⟩
  rcases hN₀ N hN with ⟨hP, hΔ, hΔ1, hsave⟩
  have hX : 0 < F γ N := Real.exp_pos _
  have hsplit (n : ℕ) (hn : ¬ Solvable γ n) :
      (majorInt γ δ κ N n).re ≤ ‖minorInt γ δ κ N n‖ := by
    simpa only [majorInt, minorInt] using
      PrimeKernel264.nonsolution_split
        (PrimeKernel264.measurableSet_majorArcs (F γ N ^ (6 * δ)) (F γ N))
        (γ := γ) hΔ hΔ1 hP n hn
  have hthreshold : F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) <
      c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    calc
      _ < F γ N * (c₀ * calE γ κ N ^ (-(1 / 10 : ℝ))) :=
        mul_lt_mul_of_pos_left hsave hX
      _ = _ := by ring
  let L := (window γ N).filter (fun n =>
    F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖)
  let R := (window γ N).filter (fun n =>
    (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  unfold blockCount Eγ_minor_block Eγ_major_block
  suffices hcard : ((window γ N).filter (fun n => ¬ Solvable γ n)).card ≤ L.card + R.card by
    convert hcard using 1 <;> congr 2
  calc
    _ ≤ (L ∪ R).card := by
      apply Finset.card_le_card
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnW, hnno⟩
      by_cases hm : F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖minorInt γ δ κ N n‖
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hnW, hm⟩))
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_filter.mpr
        exact ⟨hnW, lt_of_le_of_lt ((hsplit n hnno).trans (le_of_not_gt hm)) hthreshold⟩
    _ ≤ L.card + R.card := Finset.card_union_le _ _


/-! ### Split of `leaf_minor_bound`, P0082 pages 365 to 366, displays 24 to 27

AI wrote the Lean code. Goldbach is open. The split mirrors `Decomp371b.minor_bound_assembly`,
which cannot be imported here because `Decomp371b` imports this file. -/

/-- The integral over the truncated minor arcs `𝔫 ∩ [-P, P]` of P0082 page 365 display 24, with
the same `P = X^{6δ}`, `X = F(N)` and `Δ = ℰ^{-1/8}` as `minorInt`. -/
noncomputable def minorTruncInt (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
      Set.Icc (-(F γ N ^ (6 * δ))) (F γ N ^ (6 * δ)),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n))

/-- SPLIT of `leaf_minor_bound`, P0082 section 5, page 365 display 24: the part of the minor arc
integral with `|α| > P` is `O(X log X / (Δ P))`, by the decay `K(α) ≪ Δ^{-1} α^{-2}` of the kernel
and the trivial bound `|S| ≤ Σ log p`. For fixed `δ, κ > 0` this is eventually below half the
level `X ℰ^{-1/3}`, uniformly in `n`. The same statement for `Decomp371b.truncatedMinor` is
proved as `TailSupply385.leaf_tail_supplied`, outside this file's import cone. -/
theorem leaf_minor_tail (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ,
      ‖minorInt γ δ κ N n - minorTruncInt γ δ κ N n‖ ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  obtain ⟨N₀, hN₀⟩ := TailSupplyJ200.TailParameters.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨N₀, fun N hN n => ?_⟩
  obtain ⟨hX, hP, hd0, hd1, hb⟩ := hN₀ N hN
  have ht := TailSupplyJ200.PrimeTail.truncation_error_le
    (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(1 / 8 : ℝ)))
    (F γ n) (F γ N ^ (6 * δ)) hX hd0 hd1 hP
    (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ
  simpa only [minorInt, minorTruncInt, TailSupplyJ200.PrimeTail.integrand] using ht.trans hb

/-- P0082 pages 365 to 366, displays 25 to 27, CONDITIONAL ON the cited Karacuba Lemma 10,
P0082 pages 370 to 371: the second moment of `minorTruncInt` over the window is
`O(N X² ℰ^{-11/12})`. This is `Decomp467a.truncated_moment_of_karacuba` read through its upstream
copy `UpJ200.Decomp467a`, whose `truncatedMinor` and `window` are by definition `minorTruncInt`
and `window` of this file. -/
theorem minor_truncated_moment_of_karacuba (h10 : LeanLab.ExceptionalSet.U1539.Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖minorTruncInt γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) :=
  UpJ200.Decomp467a.truncated_moment_of_karacuba h10 γ h1 h2

/-- SPLIT of `leaf_minor_bound`, P0082 section 5, pages 365 to 366 displays 25 to 27: expanding
the square and summing over the window, Theorem 2 with `c = 1 - 3δ` bounds the far phase sums and
Gallagher's energy bound the near ones, so the second moment of the truncated minor integrals over
the window is `O(N X² (log X)² ℰ^{-1})`. Here only the weaker `ℰ^{-3/4}` is asked, after the
logarithms are absorbed into `ℰ^{1/4}`. -/
theorem leaf_minor_truncated_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖minorTruncInt γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
  -- The sum is the one of `Decomp467a.truncated_moment_of_karacuba`, through its upstream copy
  -- `UpJ200.Decomp467a`, with the cited Karacuba Lemma 10, P0082 pages 370 to 371, supplied by
  -- the existing sealed leaf `U1539.lemma10`. The exponent `-11/12` is then weakened to `-3/4`.
  obtain ⟨δ₀, hδ₀, hm⟩ := minor_truncated_moment_of_karacuba LeanLab.ExceptionalSet.U1539.lemma10
    γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, N₀, hm⟩ := hm κ hκ hκsmall
  refine ⟨B, hB, max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  exact (hm N ((le_max_right _ _).trans hN)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE (by norm_num)) (by positivity))

/-- SPLIT of `leaf_minor_bound`, the Chebyshev step of P0082 page 366 after display 27: if each
`f n` is within `T/2` of `g n` and `Σ ‖g n‖² ≤ A`, then at most `A / (T/2)²` indices have
`‖f n‖ > T`. Finite and elementary. -/
theorem minor_count_chebyshev (s : Finset ℕ) (f g : ℕ → ℂ)
    (T A : ℝ) (hT : 0 < T)
    (htail : ∀ n ∈ s, ‖f n - g n‖ ≤ T / 2)
    (hmoment : (∑ n ∈ s, ‖g n‖ ^ 2) ≤ A) :
    (((s.filter (fun n => T < ‖f n‖)).card : ℝ) * (T / 2) ^ 2) ≤ A := by
  let bad := s.filter (fun n => T < ‖f n‖)
  have hlarge : ∀ n ∈ bad, (T / 2) ^ 2 ≤ ‖g n‖ ^ 2 := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hnf⟩
    have hnorm : ‖f n‖ ≤ ‖f n - g n‖ + ‖g n‖ := norm_le_norm_sub_add _ _
    have hg : T / 2 ≤ ‖g n‖ := by linarith [htail n hns]
    exact pow_le_pow_left₀ (by positivity) hg 2
  calc
    _ ≤ ∑ n ∈ bad, ‖g n‖ ^ 2 := by
      simpa only [nsmul_eq_mul] using
        Finset.card_nsmul_le_sum bad (fun n => ‖g n‖ ^ 2) ((T / 2) ^ 2) hlarge
    _ ≤ ∑ n ∈ s, ‖g n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => sq_nonneg _)
    _ ≤ A := hmoment

/-- LEAF page 366, the variance bound of section 5, from Theorem 2 with `c = 1 - 3δ`, Vinogradov's
bound for `S` on `𝔫` and Chebyshev. The paper states the exceptions as `O(N ℰ^{-1/4})`; we ask only
for the weaker `O(N ℰ^{-1/12})`, which is all that the proof of Theorem 1 uses. -/
theorem leaf_minor_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hm⟩ := leaf_minor_truncated_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, Nm, hm⟩ := hm κ hκ hκsmall
  obtain ⟨Nt, ht⟩ := leaf_minor_tail γ h1 h2 δ κ hδ hκ
  refine ⟨4 * B, by positivity, max Nm Nt, fun N hN => ?_⟩
  have hNm : Nm ≤ N := (le_max_left _ _).trans hN
  have hNt : Nt ≤ N := (le_max_right _ _).trans hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hT : 0 < F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_pos hX (Real.rpow_pos_of_pos hE _)
  have hc := minor_count_chebyshev (window γ N)
    (minorInt γ δ κ N) (minorTruncInt γ δ κ N)
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)))
    (B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)))
    hT (fun n _ => ht N hNt n) (hm N hNm)
  change (Eγ_minor_block γ δ κ N : ℝ) *
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 ≤ _ at hc
  have hp : calE γ κ N ^ (-(3 / 4 : ℝ)) =
      calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hfactor : B * (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) =
      (4 * B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
        (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 := by
    rw [hp]
    ring
  rw [hfactor] at hc
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp hc

/-! ### Split of `leaf_major_bound`, P0082 pages 357 to 365

The proof of Lemma 8 on page 365 has three parts. First, display (8) on page 357, specialized as
display (23) on page 364, writes the major integral as `R₁(ν_n) + R₁(ν_n + 1)` whenever the
fractional part of `F(n)` stays `Δ = ℰ^{-1/8}` away from the integers. Second, Lemma 4 on page 358
bounds the `n` of the window whose fractional part is within `Δ` of an integer by `O(N Δ)`.
Third, Lemma 7 on page 362, with the odd second moment of displays (29) and (30) on pages 366
to 369, bounds the `n` where the adjacent coefficient sum is small. The three lemmas below are
those parts; AI wrote this Lean split. The first is proved downstream as
`Decomp404a.major_identity`, which this file cannot import because `Decomp404a` imports it. -/

/-- P0082 page 357 display (8) and page 364 display (23). When `Δ ≤ {F(n)} ≤ 1 - Δ`, both
trapezoid weights of the kernel equal one and the major integral is the sum of the two adjacent
coefficients `R₁(ν_n) + R₁(ν_n + 1)`. -/
theorem leaf_major_identity (γ δ κ : ℝ) (N n : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hleft : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ Int.fract (F γ n))
    (hright : Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ))) :
    majorInt γ δ κ N n =
      U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) := by
  unfold majorInt
  rw [MajorSupplyJ200.major_integral_formula _ _ _ _ hΔ hΔ1]
  have hw0 : KernelTransform264.weight (calE γ κ N ^ (-(1 / 8 : ℝ))) (Int.fract (F γ n)) = 1 := by
    apply KernelTransform264.weight_one hΔ hΔ1
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact hright
  have hw1 : KernelTransform264.weight (calE γ κ N ^ (-(1 / 8 : ℝ))) (Int.fract (F γ n) - 1) = 1 := by
    apply KernelTransform264.weight_one hΔ hΔ1
    rw [abs_of_nonpos (by linarith [Int.fract_lt_one (F γ n)] : Int.fract (F γ n) - 1 ≤ 0)]
    linarith
  rw [hw0, hw1]
  simp only [Complex.ofReal_one, one_mul, nu]

/-- P0082 page 358 Lemma 4, applied on page 364 after display (23). With `Δ = ℰ^{-1/8}`, at most
`B N Δ` members of the window have `{F(n)} < Δ` or `{F(n)} > 1 - Δ`, for every small `κ`. -/
theorem leaf_major_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  -- Burst 7: the simple variant of Lemma 4 that page 359 says suffices, proved in
  -- `BoundarySupplyJ200` by a Fejér square from Theorem 2 with `c = 1/2`. CONDITIONAL ON
  -- Theorem 2 only, supplied here by `U1539.theorem2_via_karacuba`, which rests on the CITED
  -- Lemma 10 of page 370, Karacuba's estimate.
  exact BoundarySupplyJ200.boundary_of_theorem2 U1539.theorem2_via_karacuba γ h1 h2

/-- P0082 page 362 Lemma 7, with the odd second moment of pages 366 to 369 displays (29) and
(30): the real part of `R₁(ν_n) + R₁(ν_n + 1)` is below `c₀ X ℰ^{-1/10}` for at most
`B N ℰ^{-1/12}` members of the window. -/
theorem leaf_major_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  -- Burst 7: the first sentence of the proof of Lemma 7 on page 362, from the even coefficient
  -- leaf and the odd moment leaf above. The proof copies `Decomp467b.coefficient_lower_from_inputs`.
  classical
  obtain ⟨δe, hδe, he⟩ := MajorLeafJ200.leaf_major_even_coefficient γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := MajorLeafJ200.leaf_major_odd_moment γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, Be, hc, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bo, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c / 2, Be + 16 * Bo / c ^ 2, by positivity, by positivity,
    max 2 (max Ne No), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNo : No ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  let f : ℕ → ℂ := fun n =>
    U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (CoeffSupplyJ200.evenAdjacent γ n)
  let g : ℕ → ℂ := fun n => U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (U1539.nuOdd γ n)
  let T := c / 2 * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  have hpair := CoeffSupplyJ200.bad_pair_count (window γ N) f g T
  have hrewrite (n : ℕ) : f n + g n =
      U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) :=
    CoeffSupplyJ200.adjacent_sum (U1539.R1 (F γ N ^ (6 * δ)) (F γ N)) γ n
  have htwo : 2 * T = c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    ring
  simp_rw [hrewrite, htwo] at hpair
  have hodd := CoeffSupplyJ200.odd_bad_count (window γ N) g c Bo (F γ N) (calE γ κ N) N
    hc hBo.le (Real.exp_pos _) hE (ho N hNo)
  have hpairR := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hpairR
  change _ ≤ _ at hodd
  have heN := he N hNe
  change (((window γ N).filter (fun n => (f n).re <
    c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤ _ at heN
  dsimp only [T] at hpairR
  refine hpairR.trans ((add_le_add heN hodd).trans ?_)
  ring_nf
  exact le_rfl

/-- LEAF page 365, Lemma 8, with one `κ` shared by the two arcs as in the paper, where `ℰ` is
fixed once for sections 4 to 7. `U1539.Lemma8` is the same bound with a private `κ`, too weak to
combine with `leaf_minor_bound`. -/
theorem leaf_major_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := leaf_major_coefficient_lower γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := leaf_major_fractional_boundary γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ :=
    hcoeff κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ :=
    hboundary κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c₀, Ba + Bb, hc₀, add_pos hBa hBb, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let A := (window γ N).filter (fun n : ℕ =>
    (U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := (window γ N).filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (window γ N).filter (fun n : ℕ =>
      (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hnmajor⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := leaf_major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hnW, by rwa [hid] at hnmajor⟩
  have hcard : (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ (A.card : ℝ) + B.card := by
    unfold Eγ_major_block
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc
    _ ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
      gcongr
    _ = _ := by ring


/-- ASSEMBLY of the three leaves above, p. 366: `r(F(n)) > 0` for all but `O(N ℰ^{-1/12})` values
of `n` with `X/2 < ν_n ≤ X`. -/
theorem block_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
        B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₁, hδ₁, hmin⟩ := leaf_minor_bound γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := leaf_major_bound γ h1 h2
  have hδ : 0 < min δ₁ δ₂ / 2 := half_pos (lt_min hδ₁ hδ₂)
  have hδ1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  have hδ2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  obtain ⟨κ₁, hκ₁, hmin⟩ := hmin _ hδ hδ1
  obtain ⟨κ₂, hκ₂, hmaj⟩ := hmaj _ hδ hδ2
  have hκ : 0 < min κ₁ κ₂ := lt_min hκ₁ hκ₂
  obtain ⟨B₁, hB₁, N₁, hmin⟩ := hmin _ hκ (min_le_left _ _)
  obtain ⟨c₀, B₂, hc₀, hB₂, N₂, hmaj⟩ := hmaj _ hκ (min_le_right _ _)
  obtain ⟨N₃, hsplit⟩ := leaf_dyadic_split γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ h1 h2 hδ hκ hc₀
  refine ⟨min κ₁ κ₂, B₁ + B₂, hκ, add_pos hB₁ hB₂, max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have h₁ := hmin N (le_trans (le_max_left _ _) hN)
  have h₂ := hmaj N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h₃ := hsplit N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have h₃' : (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
      Eγ_minor_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) N +
        Eγ_major_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ N := by exact_mod_cast h₃
  calc _ ≤ _ := h₃'
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

/-! ### Batch 1: monotonicity of `F` and the secant bound for `x ↦ x ^ γ` -/

private lemma one_sub_rpow_le_mul_one_sub {γ : ℝ} (h1 : 1 ≤ γ) {r : ℝ} (hr0 : 0 ≤ r) :
    1 - r ^ γ ≤ γ * (1 - r) := by
  have hb := one_add_mul_self_le_rpow_one_add (s := r - 1) (p := γ) (by linarith) h1
  rw [add_sub_cancel] at hb
  linarith

private lemma rpow_sub_le {γ : ℝ} (h1 : 1 ≤ γ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (a + d) ^ γ ≤ a ^ γ + γ * d * (a + d) ^ (γ - 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · simp
  set v := a + d with hvdef
  have hv : 0 < v := by rw [hvdef]; linarith
  have hrv : a / v * v = a := by field_simp
  have hr0 : 0 ≤ a / v := div_nonneg ha hv.le
  have hB : 1 - (a / v) ^ γ ≤ γ * (d / v) := by
    have h := one_sub_rpow_le_mul_one_sub h1 hr0
    have h1r : 1 - a / v = d / v := by field_simp; ring
    rw [h1r] at h
    exact h
  have hvp : 0 < v ^ γ := Real.rpow_pos_of_pos hv _
  have hmul := mul_le_mul_of_nonneg_left hB hvp.le
  have hkey : v ^ γ * (1 - (a / v) ^ γ) = v ^ γ - a ^ γ := by
    have h : a ^ γ = (a / v) ^ γ * v ^ γ := by rw [← Real.mul_rpow hr0 hv.le, hrv]
    rw [h]; ring
  have hvv : v ^ γ = v ^ (γ - 1) * v := by
    conv_lhs => rw [show γ = (γ - 1) + 1 by ring]
    rw [Real.rpow_add hv, Real.rpow_one]
  have hrhs : v ^ γ * (γ * (d / v)) = γ * d * v ^ (γ - 1) := by
    rw [hvv]; field_simp
  rw [hkey, hrhs] at hmul
  have hfin : a ^ γ + γ * d * (a + d) ^ (γ - 1) = a ^ γ + γ * d * v ^ (γ - 1) := by rw [hvdef]
  rw [hfin]
  linarith

/-! ### Batch 2: `2 ^ (1/8) ≤ 9/8` and the log increment bound -/

private lemma two_rpow_eighth_le : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 9 / 8 := by
  have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (p := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

private lemma log_le_log_add_div {n N K : ℕ} (hn : 1 ≤ n) (hNn : n ≤ N) (hNK : N ≤ n + K) :
    Real.log N ≤ Real.log n + (K : ℝ) / n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : Real.log N ≤ Real.log ((n : ℝ) + K) := by
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) ?_
    exact_mod_cast hNK
  have h2 : Real.log ((n : ℝ) + K) = Real.log n + Real.log (1 + (K : ℝ) / n) := by
    have h : (n : ℝ) + K = (n : ℝ) * (1 + (K : ℝ) / n) := by field_simp
    rw [h, Real.log_mul hn0.ne' (by positivity)]
  have h3 : Real.log (1 + (K : ℝ) / n) ≤ (K : ℝ) / n := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (K : ℝ) / n by positivity)
    linarith
  linarith

/-! ### Batch 3: membership in the window of `N` -/

private lemma mem_window_iff {γ : ℝ} {N n : ℕ} :
    n ∈ window γ N ↔ n ≤ 2 * N ∧ F γ N / 2 < (nu γ n : ℝ) ∧ (nu γ n : ℝ) ≤ F γ N := by
  unfold window
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private lemma log_eight_ge_one : (1 : ℝ) ≤ Real.log 8 := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have h := Real.log_two_gt_d9
  rw [hlog8]; linarith

private lemma rpow_one_sub_mul {x γ : ℝ} (hx : 0 < x) :
    x ^ (1 - γ) * x ^ (γ - 1) = 1 := by
  rw [← Real.rpow_add hx, show 1 - γ + (γ - 1) = 0 by ring, Real.rpow_zero]

/-- The width `log N - log n` that the window of `N` allows at a given `n`. -/
private noncomputable def dlt (γ : ℝ) (n : ℕ) : ℝ :=
  (Real.log 2 / (8 * γ)) * (Real.log (n : ℝ) + 1) ^ (1 - γ)

private lemma log_nat_add_one_pos (n : ℕ) : (0 : ℝ) < Real.log (n : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · exact Real.log_nonneg (by exact_mod_cast h0)
  linarith

private lemma dlt_nonneg {γ : ℝ} (hγ : 0 < γ) (n : ℕ) : 0 ≤ dlt γ n := by
  have h : (0 : ℝ) < (Real.log (n : ℝ) + 1) ^ (1 - γ) :=
    Real.rpow_pos_of_pos (log_nat_add_one_pos n) _
  have h2 : (0 : ℝ) < Real.log 2 / (8 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  exact mul_nonneg h2.le h.le

private lemma dlt_le_one {γ : ℝ} (hγ : 1 < γ) (n : ℕ) : dlt γ n ≤ 1 := by
  have hc : Real.log 2 / (8 * γ) ≤ 1 := by
    have h1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have h2 : (1 : ℝ) ≤ 8 * γ := by linarith
    rw [div_le_one (by linarith : (0 : ℝ) < 8 * γ)]
    linarith
  have hbase : (1 : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ Real.log (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · exact Real.log_nonneg (by exact_mod_cast h0)
    linarith
  have hpow : (Real.log (n : ℝ) + 1) ^ (1 - γ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase (by linarith : 1 - γ ≤ 0)
    rwa [Real.rpow_zero] at h
  calc dlt γ n = (Real.log 2 / (8 * γ)) * (Real.log (n : ℝ) + 1) ^ (1 - γ) := rfl
    _ ≤ 1 * 1 := by
      refine mul_le_mul hc hpow (Real.rpow_nonneg (by linarith) _) (by norm_num)
    _ = 1 := by norm_num

private lemma dlt_mul {γ : ℝ} (hγ : 1 < γ) (n : ℕ) :
    γ * dlt γ n * (Real.log (n : ℝ) + 1) ^ (γ - 1) = Real.log 2 / 8 := by
  have hx : (0 : ℝ) < Real.log (n : ℝ) + 1 := log_nat_add_one_pos n
  have hγ0 : (0 : ℝ) < γ := by linarith
  have h := rpow_one_sub_mul hx (γ := γ)
  have hc : γ * (Real.log 2 / (8 * γ)) = Real.log 2 / 8 := by field_simp
  rw [dlt]
  set A := (Real.log (n : ℝ) + 1) ^ (1 - γ) with hA
  set B := (Real.log (n : ℝ) + 1) ^ (γ - 1) with hB
  have hAB : A * B = 1 := h
  calc γ * (Real.log 2 / (8 * γ) * A) * B
      = (γ * (Real.log 2 / (8 * γ))) * (A * B) := by ring
    _ = (Real.log 2 / 8) * 1 := by rw [hc, hAB]
    _ = Real.log 2 / 8 := by ring

private lemma mem_window_of_log_le {γ : ℝ} (h1 : 1 < γ) {n N : ℕ} (hn : 8 ≤ n) (hNn : n ≤ N)
    (hlog : Real.log N ≤ Real.log n + dlt γ n) :
    n ∈ window γ N := by
  rw [mem_window_iff]
  set a := Real.log n with hadef
  have hγ0 : 0 < γ := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNn
    linarith
  have ha0 : 0 ≤ a := Real.log_nonneg hn1
  have ha1 : 1 ≤ a := by
    rw [hadef]
    have h : Real.log 8 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith [log_eight_ge_one]
  have hx : (0 : ℝ) < a + 1 := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hla : a ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hNn)
  have hd0 : 0 ≤ dlt γ n := dlt_nonneg hγ0 n
  have hd1 : dlt γ n ≤ 1 := dlt_le_one h1 n
  have hdle : dlt γ n = (Real.log 2 / (8 * γ)) * (a + 1) ^ (1 - γ) := by rw [dlt, hadef]
  have step1 : (Real.log N) ^ γ ≤ (a + dlt γ n) ^ γ := by
    refine Real.rpow_le_rpow hlogN0 ?_ hγ0.le
    rw [hadef]
    exact hlog
  have step2 : (a + dlt γ n) ^ γ ≤ a ^ γ + γ * dlt γ n * (a + 1) ^ (γ - 1) := by
    have hbase := rpow_sub_le h1.le ha0 hd0
    have hmono : (a + dlt γ n) ^ (γ - 1) ≤ (a + 1) ^ (γ - 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith : (0 : ℝ) ≤ γ - 1)
    have hgd : 0 ≤ γ * dlt γ n := mul_nonneg hγ0.le hd0
    nlinarith
  have step3 : γ * dlt γ n * (a + 1) ^ (γ - 1) = Real.log 2 / 8 := by
    rw [hdle]
    have := dlt_mul h1 n
    rw [dlt] at this
    linarith [this]
  have hub : (Real.log N) ^ γ ≤ a ^ γ + Real.log 2 / 8 :=
    step1.trans (step2.trans (by linarith [step3]))
  have hFn : F γ n = Real.exp (a ^ γ) := by rw [F, hadef]
  have hFN : F γ N = Real.exp ((Real.log N) ^ γ) := rfl
  have hbig : (2 : ℝ) < Real.exp (a ^ γ) * (7 / 8) := by
    have h1e : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hmono : Real.exp 1 ≤ Real.exp (a ^ γ) := by
      refine Real.exp_le_exp.mpr ?_
      have h : (1 : ℝ) ≤ a ^ γ := Real.one_le_rpow ha1 hγ0.le
      linarith
    nlinarith
  refine ⟨by omega, ?_, ?_⟩
  · -- `F γ N / 2 < ν_n`
    have hle : F γ N ≤ Real.exp (a ^ γ) * (9 / 8) := by
      rw [hFN]
      have hexp : Real.exp ((Real.log N) ^ γ) ≤
          Real.exp (a ^ γ) * Real.exp (Real.log 2 / 8) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (Real.log 2 / 8) = (2 : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      rw [h2] at hexp
      have h3 := two_rpow_eighth_le
      nlinarith
    have hfloor : Real.exp (a ^ γ) - 1 < (nu γ n : ℝ) := by
      rw [nu, hFn]
      exact Int.sub_one_lt_floor _
    nlinarith
  · -- `ν_n ≤ F γ N`
    have h1' : (nu γ n : ℝ) ≤ F γ n := by
      rw [nu]; exact Int.floor_le _
    have h2' : F γ n ≤ F γ N := by
      rw [hFn, hFN]
      exact Real.exp_le_exp.mpr (Real.rpow_le_rpow ha0 hla hγ0.le)
    linarith

/-! ### Batch 4: counting the windows that cover a dyadic block -/

/-- The stretch of `N` above `n` over which `n` stays in the window of `N`. -/
private noncomputable def step (γ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) * dlt γ n⌋₊

private lemma step_le {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    (step γ n : ℝ) ≤ (n : ℝ) * dlt γ n :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (dlt_nonneg hγ n))

private lemma step_lt_succ {γ : ℝ} (n : ℕ) : (n : ℝ) * dlt γ n < (step γ n : ℝ) + 1 :=
  Nat.lt_floor_add_one _

private lemma step_le_self {γ : ℝ} (hγ : 1 < γ) (n : ℕ) : step γ n ≤ n := by
  have h := step_le (by linarith) n
  have h1 : (n : ℝ) * dlt γ n ≤ (n : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (dlt_le_one hγ n) (Nat.cast_nonneg n)
  have h2 : (step γ n : ℝ) ≤ (n : ℝ) := by simpa using h.trans h1
  exact_mod_cast h2

private lemma mem_window_of_step {γ : ℝ} (h1 : 1 < γ) {n N : ℕ} (hn : 8 ≤ n)
    (hNn : n ≤ N) (hNK : N ≤ n + step γ n) : n ∈ window γ N := by
  refine mem_window_of_log_le h1 hn hNn ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1' : Real.log N ≤ Real.log n + (step γ n : ℝ) / n :=
    log_le_log_add_div (by omega) hNn hNK
  have h2 : (step γ n : ℝ) / n ≤ dlt γ n := by
    rw [div_le_iff₀ hn0]
    calc (step γ n : ℝ) ≤ (n : ℝ) * dlt γ n := step_le (by linarith) n
      _ = dlt γ n * n := by ring
  linarith

/-- The number of windows that must contain each member of `[M, 2M)`. -/
private noncomputable def mult (γ : ℝ) (M : ℕ) : ℕ :=
  ⌊(Real.log 2 / (16 * γ)) * (M : ℝ) * (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ)⌋₊

private lemma mult_le_cast {γ : ℝ} (hγ : 0 < γ) (M : ℕ) :
    (mult γ M : ℝ) ≤
      (Real.log 2 / (16 * γ)) * (M : ℝ) * (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) := by
  refine Nat.floor_le ?_
  have h1 : (0 : ℝ) < Real.log 2 / (16 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  have h2 : (0 : ℝ) < (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) :=
    Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
  exact mul_nonneg (mul_nonneg h1.le (Nat.cast_nonneg M)) h2.le

private lemma mult_le_step_succ {γ : ℝ} (h1 : 1 < γ) {M n : ℕ} (_hM : 8 ≤ M)
    (hnM : M ≤ n) (hn2M : n < 2 * M) : mult γ M ≤ step γ n + 1 := by
  have hγ0 : 0 < γ := by linarith
  set A := Real.log 2 / (16 * γ) with hA
  set L := Real.log ((2 * M : ℕ) : ℝ) + 1 with hL
  set X := Real.log (n : ℝ) + 1 with hX
  have hA0 : 0 ≤ A := by
    rw [hA]; exact (div_pos (Real.log_pos (by norm_num)) (by linarith)).le
  have hL0 : 0 < L := log_nat_add_one_pos _
  have hX0 : 0 < X := log_nat_add_one_pos _
  have hMn : (M : ℝ) ≤ 2 * (n : ℝ) := by
    have : M ≤ 2 * n := by omega
    exact_mod_cast this
  have hXL : X ≤ L := by
    have h1 : (n : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2 * M)
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) h1
    rw [hL, hX]; linarith
  have hpow : L ^ (1 - γ) ≤ X ^ (1 - γ) :=
    (Real.rpow_le_rpow_iff_of_neg hL0 hX0 (by linarith : 1 - γ < 0)).mpr hXL
  have hmain : (mult γ M : ℝ) ≤ (n : ℝ) * dlt γ n := by
    have h1 : (mult γ M : ℝ) ≤ A * (M : ℝ) * L ^ (1 - γ) := by
      rw [hA, hL]; exact mult_le_cast hγ0 M
    have h2 : A * (M : ℝ) * L ^ (1 - γ) ≤ A * (2 * (n : ℝ)) * X ^ (1 - γ) := by
      have hstep1 : A * (M : ℝ) * L ^ (1 - γ) ≤ A * (2 * (n : ℝ)) * L ^ (1 - γ) := by
        have := mul_le_mul_of_nonneg_left hMn hA0
        have hLp : (0 : ℝ) ≤ L ^ (1 - γ) := Real.rpow_nonneg hL0.le _
        nlinarith
      have hA2 : 0 ≤ A * (2 * (n : ℝ)) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      exact hstep1.trans (mul_le_mul_of_nonneg_left hpow hA2)
    have hd : (n : ℝ) * dlt γ n = 2 * (A * (n : ℝ) * X ^ (1 - γ)) := by
      rw [dlt, hA, hX]; ring
    calc (mult γ M : ℝ) ≤ A * (M : ℝ) * L ^ (1 - γ) := h1
      _ ≤ A * (2 * (n : ℝ)) * X ^ (1 - γ) := h2
      _ = (n : ℝ) * dlt γ n := by rw [hd]; ring
  have hfin : (mult γ M : ℝ) ≤ ((step γ n + 1 : ℕ) : ℝ) := by
    have := step_lt_succ (γ := γ) n
    push_cast
    linarith
  exact_mod_cast hfin

private lemma card_window_ge_mult {γ : ℝ} (h1 : 1 < γ) {M : ℕ} (hM : 8 ≤ M) {n : ℕ}
    (hn : M ≤ n) (hn2 : n < 2 * M) :
    mult γ M ≤ ((Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N)).card := by
  have hn8 : 8 ≤ n := le_trans hM hn
  have hsub : Finset.Ico n (n + step γ n + 1) ⊆
      (Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N) := by
    intro N hN
    simp only [Finset.mem_Ico] at hN
    obtain ⟨hN1, hN2⟩ := hN
    have h3 : N ≤ n + step γ n := by omega
    refine Finset.mem_filter.mpr ⟨?_, mem_window_of_step h1 hn8 hN1 h3⟩
    refine Finset.mem_Ico.mpr ⟨le_trans hn hN1, ?_⟩
    have hs : step γ n ≤ n := step_le_self h1 n
    omega
  have hcard : (Finset.Ico n (n + step γ n + 1)).card = step γ n + 1 := by
    rw [Nat.card_Ico]; omega
  calc mult γ M ≤ step γ n + 1 := mult_le_step_succ h1 hM hn hn2
    _ = (Finset.Ico n (n + step γ n + 1)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Double counting: every bad member of `[M, 2M)` lies in `mlt` windows `N ∈ [M, 4M]`, so the
dyadic count is at most the sum of the window counts divided by `mlt`. -/
private lemma card_mul_le_sum_blocks (γ : ℝ) (Bad : ℕ → Prop) (M mlt : ℕ)
    (hstep : ∀ n ∈ (Finset.Ico M (2 * M)).filter Bad,
      (mlt : ℝ) ≤ ((Finset.Ico M (4 * M + 1)).filter (fun N => n ∈ window γ N)).card) :
    (mlt : ℝ) * (((Finset.Ico M (2 * M)).filter Bad).card : ℝ) ≤
      ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) := by
  set S := (Finset.Ico M (2 * M)).filter Bad with hS
  set t := Finset.Ico M (4 * M + 1) with ht
  have h1 : (mlt : ℝ) * (S.card : ℝ) = ∑ _n ∈ S, (mlt : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h1]
  have hstep' : ∀ n ∈ S, (mlt : ℝ) ≤ ((t.filter (fun N => n ∈ window γ N)).card : ℝ) := by
    intro n hn
    rw [hS] at hn
    exact_mod_cast hstep n hn
  calc ∑ _n ∈ S, (mlt : ℝ)
      ≤ ∑ n ∈ S, ((t.filter (fun N => n ∈ window γ N)).card : ℝ) := Finset.sum_le_sum hstep'
    _ = ∑ n ∈ S, ∑ N ∈ t, (if n ∈ window γ N then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.card_filter]
        push_cast
        simp
    _ = ∑ N ∈ t, ∑ n ∈ S, (if n ∈ window γ N then (1 : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ N ∈ t, (blockCount γ Bad N : ℝ) := by
        refine Finset.sum_le_sum (fun N _ => ?_)
        have hbc : (blockCount γ Bad N : ℝ) = (((window γ N).filter Bad).card : ℝ) := rfl
        rw [hbc]
        have hsub : S.filter (fun n => n ∈ window γ N) ⊆ (window γ N).filter Bad := by
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          rw [hS] at hn
          simp only [Finset.mem_filter] at hn
          exact ⟨hn.2, hn.1.2⟩
        have hcard : ((S.filter (fun n => n ∈ window γ N)).card : ℝ) =
            ∑ n ∈ S, (if n ∈ window γ N then (1 : ℝ) else 0) := by
          rw [Finset.card_filter]
          push_cast
          simp
        rw [← hcard]
        exact_mod_cast Finset.card_le_card hsub

/-! ### Batch 5a: eventual bounds -/

/-- For `p > 0` and `ε > 0`, `log t ≤ ε * t ^ p` from some point on. -/
private lemma exists_log_le_mul_rpow {p : ℝ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → Real.log t ≤ ε * t ^ p := by
  set s := p / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsp : s + s = p := by rw [hs]; ring
  have hes : 0 < ε * s := mul_pos hε hs0
  refine ⟨max 2 ((1 / (ε * s)) ^ (1 / s)), ?_⟩
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hTt : (1 / (ε * s)) ^ (1 / s) ≤ t := le_trans (le_max_right _ _) ht
  have hbase : (0 : ℝ) < 1 / (ε * s) := by positivity
  have hts : 1 / (ε * s) ≤ t ^ s := by
    have h1 : ((1 / (ε * s)) ^ (1 / s)) ^ s = (1 / (ε * s)) ^ (1 : ℝ) := by
      rw [← Real.rpow_mul hbase.le]
      congr 1
      field_simp
    rw [Real.rpow_one] at h1
    rw [← h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hTt hs0.le
  have hts0 : (0 : ℝ) ≤ t ^ s := Real.rpow_nonneg ht0.le _
  have hone : (1 : ℝ) ≤ ε * s * t ^ s := by
    have h := mul_le_mul_of_nonneg_left hts hes.le
    have h' : ε * s * (1 / (ε * s)) = 1 := by field_simp
    rwa [h'] at h
  have hsq : t ^ s * t ^ s = t ^ p := by
    rw [← Real.rpow_add ht0, hsp]
  have hstep : t ^ s ≤ ε * s * t ^ p := by
    calc t ^ s = 1 * t ^ s := by ring
      _ ≤ (ε * s * t ^ s) * t ^ s := mul_le_mul_of_nonneg_right hone hts0
      _ = ε * s * (t ^ s * t ^ s) := by ring
      _ = ε * s * t ^ p := by rw [hsq]
  have hlog : Real.log t = (1 / s) * Real.log (t ^ s) := by
    rw [Real.log_rpow ht0]
    field_simp
  have hlog2 : Real.log (t ^ s) ≤ t ^ s := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 s)
    linarith
  calc Real.log t = (1 / s) * Real.log (t ^ s) := hlog
    _ ≤ (1 / s) * t ^ s := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ ≤ (1 / s) * (ε * s * t ^ p) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ε * t ^ p := by field_simp

/-- `κ / 24 * (log M) ^ p ≤ log M / 2` for large `M`, when `0 < p < 1`. -/
private lemma exists_calE_small {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {κ : ℝ} (hκ : 0 < κ) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → κ / 24 * Real.log M ^ p ≤ Real.log M / 2 := by
  set L₀ := (κ / 12) ^ (1 / (1 - p)) with hL₀
  have hL₀0 : 0 < L₀ := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun M hM => ?_⟩
  have hMe : Real.exp L₀ ≤ (M : ℝ) := by
    have h3 : (⌈Real.exp L₀⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
    have h2 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hL : L₀ ≤ Real.log M := by
    have h := Real.log_le_log (Real.exp_pos L₀) hMe
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log M := lt_of_lt_of_le hL₀0 hL
  have hpow : L₀ ^ (1 - p) ≤ (Real.log M) ^ (1 - p) :=
    Real.rpow_le_rpow hL₀0.le hL (by linarith : (0 : ℝ) ≤ 1 - p)
  have hL₀pow : L₀ ^ (1 - p) = κ / 12 := by
    rw [hL₀]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ κ / 12 by linarith)]
    rw [show (1 / (1 - p)) * (1 - p) = 1 by field_simp, Real.rpow_one]
  have hkey : κ / 12 ≤ (Real.log M) ^ (1 - p) := by rw [← hL₀pow]; exact hpow
  have hsplit : (Real.log M) ^ (1 - p) * (Real.log M) ^ p = Real.log M := by
    rw [← Real.rpow_add hLpos, show 1 - p + p = 1 by ring, Real.rpow_one]
  have hLp : 0 ≤ (Real.log M) ^ p := Real.rpow_nonneg hLpos.le _
  have hT := mul_le_mul_of_nonneg_right hkey hLp
  rw [hsplit] at hT
  calc κ / 24 * Real.log M ^ p = (κ / 12) * Real.log M ^ p / 2 := by ring
    _ ≤ (Real.log M) ^ (1 - p) * (Real.log M) ^ p / 2 := by linarith
    _ = Real.log M / 2 := by rw [hsplit]

private lemma log_twenty_one_ge_three : (3 : ℝ) ≤ Real.log 21 := by
  have hexp3 : Real.exp 3 < 21 := by
    have hsplit : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    rw [hsplit]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have h := Real.log_lt_log (Real.exp_pos 3) hexp3
  rw [Real.log_exp] at h
  linarith

/-- Absorption: `(log (2M) + 1) ^ (γ - 1) ≤ exp (κ/24 * (log M) ^ (3 - 2γ))` eventually. -/
private lemma eventually_absorb {γ κ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ M1 : ℕ, ∀ M : ℕ, M1 ≤ M →
      (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤
        Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) := by
  set p := 3 - 2 * γ with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hγ1 : 0 < γ - 1 := by linarith
  set ε := κ / (48 * (γ - 1)) with hεdef
  have hε : 0 < ε := div_pos hκ (by linarith)
  obtain ⟨T, hT⟩ := exists_log_le_mul_rpow hp hε
  refine ⟨max 21 (⌈Real.exp T⌉₊ + 1), fun M hM => ?_⟩
  have hM21 : 21 ≤ M := le_trans (le_max_left _ _) hM
  have hMe : Real.exp T ≤ (M : ℝ) := by
    have h3 : (⌈Real.exp T⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hM)
    have h2 : Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hL3 : 3 ≤ Real.log M :=
    le_trans log_twenty_one_ge_three
      (Real.log_le_log (by norm_num) (by exact_mod_cast hM21))
  have hLT : T ≤ Real.log M := by
    have h := Real.log_le_log (Real.exp_pos T) hMe
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log M := by linarith
  have h2Mpos : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by
    have : 0 < 2 * M := by omega
    exact_mod_cast this
  have hlog2M : Real.log ((2 * M : ℕ) : ℝ) = Real.log 2 + Real.log M := by
    rw [show ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) by push_cast; ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hX3 : Real.log ((2 * M : ℕ) : ℝ) + 1 ≤ 3 * Real.log M := by
    have hlog2 : Real.log 2 ≤ Real.log M :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ M))
    rw [hlog2M]; linarith
  have h2M1 : (0 : ℝ) ≤ Real.log ((2 * M : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * M))
  have hpow : (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤ (3 * Real.log M) ^ (γ - 1) :=
    Real.rpow_le_rpow (by linarith) hX3 hγ1.le
  have hexp3L : (3 * Real.log M) ^ (γ - 1) =
      Real.exp ((γ - 1) * Real.log (3 * Real.log M)) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 3 * Real.log M)]
    ring_nf
  have hlog3L : Real.log (3 * Real.log M) ≤ 2 * Real.log (Real.log M) := by
    have hmul : Real.log (3 * Real.log M) = Real.log 3 + Real.log (Real.log M) :=
      Real.log_mul (by norm_num) (by positivity)
    have h3L : Real.log 3 ≤ Real.log (Real.log M) := Real.log_le_log (by norm_num) (by linarith)
    rw [hmul]; linarith
  have hlogL : Real.log (Real.log M) ≤ ε * (Real.log M) ^ p := hT _ hLT
  have hε' : 2 * (γ - 1) * ε = κ / 24 := by
    rw [hεdef]; field_simp; ring
  have hLp : 0 ≤ (Real.log M) ^ p := Real.rpow_nonneg hLpos.le _
  have hfinal : (γ - 1) * Real.log (3 * Real.log M) ≤ κ / 24 * (Real.log M) ^ p := by
    have h := mul_le_mul_of_nonneg_left hlog3L hγ1.le
    have h' := mul_le_mul_of_nonneg_left hlogL (by positivity : (0 : ℝ) ≤ 2 * (γ - 1))
    nlinarith [h, h', hε', hLp]
  calc (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) ≤ (3 * Real.log M) ^ (γ - 1) := hpow
    _ = Real.exp ((γ - 1) * Real.log (3 * Real.log M)) := hexp3L
    _ ≤ Real.exp (κ / 24 * (Real.log M) ^ (3 - 2 * γ)) := Real.exp_le_exp.mpr hfinal

private lemma calE_rpow {γ κ : ℝ} {N : ℕ} :
    calE γ κ N ^ (-(1 / 12 : ℝ)) = Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) := by
  rw [calE, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The window counts summed over `[M, 4M]`, using `calE N ^ (-1/12) ≤ calE M ^ (-1/12)`. -/
private lemma sum_blockCount_le {γ κ B : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hB : 0 < B)
    {Bad : ℕ → Prop} {N₀ : ℕ}
    (h : ∀ N : ℕ, N₀ ≤ N → (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)))
    {M : ℕ} (hMN₀ : N₀ ≤ M) (hM1 : 1 ≤ M) :
    ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      16 * B * (M : ℝ) ^ 2 * Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := by
  set E := Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hp : 0 < 3 - 2 * γ := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hcard : (Finset.Ico M (4 * M + 1)).card = 3 * M + 1 := by
    rw [Nat.card_Ico]; omega
  have hterm : ∀ N ∈ Finset.Ico M (4 * M + 1),
      (blockCount γ Bad N : ℝ) ≤ B * (4 * (M : ℝ)) * E := by
    intro N hN
    obtain ⟨hNM, hN4⟩ := Finset.mem_Ico.mp hN
    have h1' : (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) :=
      h N (le_trans hMN₀ hNM)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 1 ≤ N := le_trans hM1 hNM
      exact_mod_cast this
    have hNM' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNM
    have hlogNM : Real.log M ≤ Real.log N := Real.log_le_log hM0 hNM'
    have hpowN : (Real.log M) ^ (3 - 2 * γ) ≤ (Real.log N) ^ (3 - 2 * γ) :=
      Real.rpow_le_rpow hlogM0 hlogNM hp.le
    have hexpN : Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) ≤ E := by
      rw [hEdef]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hpowN, hκ]
    have hcalN : calE γ κ N ^ (-(1 / 12 : ℝ)) = Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) :=
      calE_rpow
    rw [hcalN] at h1'
    have h4 : (N : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast (by omega : N ≤ 4 * M)
    have hBN : (0 : ℝ) ≤ B * N := by positivity
    have hstep1 : B * (N : ℝ) * Real.exp (-(κ / 12) * Real.log N ^ (3 - 2 * γ)) ≤ B * (N : ℝ) * E :=
      mul_le_mul_of_nonneg_left hexpN hBN
    have hstep2 : B * (N : ℝ) * E ≤ B * (4 * (M : ℝ)) * E := by
      have : B * (N : ℝ) ≤ B * (4 * (M : ℝ)) := mul_le_mul_of_nonneg_left h4 hB.le
      exact mul_le_mul_of_nonneg_right this hE.le
    linarith
  have hsum : ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      ∑ _N ∈ Finset.Ico M (4 * M + 1), (B * (4 * (M : ℝ)) * E) := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have h3 : ((3 * M + 1 : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by
    have : 3 * M + 1 ≤ 4 * M := by omega
    exact_mod_cast this
  have h4 : ((3 * M + 1 : ℕ) : ℝ) * (B * (4 * (M : ℝ)) * E) ≤
      (4 * (M : ℝ)) * (B * (4 * (M : ℝ)) * E) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : (4 * (M : ℝ)) * (B * (4 * (M : ℝ)) * E) =
      16 * B * (M : ℝ) ^ 2 * E := by ring
  linarith [hsum, h4, h5]

/-- LEAF page 366, "a routine dyadic dissection argument", last line of section 5. For any set
`Bad`: a block bound in the windows of `F` gives a saving on `[M, 2M)`. The block `[M, 2M)` meets
about `log₂ (F(2M)/F(M)) ≪ (log M)^γ` windows, each of size at most `B N ℰ^{-1/12}`, and that power
of `log M` is absorbed by the exponential. -/
theorem leaf_block_dissection (γ κ B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hB : 0 < B)
    (Bad : ℕ → Prop) (N₀ : ℕ)
    (h : ∀ N : ℕ, N₀ ≤ N → (blockCount γ Bad N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (dyadicCount Bad M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hA2 : 0 < Real.log 2 / (16 * γ) :=
    div_pos (Real.log_pos (by norm_num)) (by linarith)
  obtain ⟨M1, hM1⟩ := eventually_absorb h1 h2 hκ
  obtain ⟨M2, hM2⟩ := exists_calE_small (p := 3 - 2 * γ) hp hp1 hκ
  refine ⟨κ / 24, by linarith, 32 * B / (Real.log 2 / (16 * γ)), by positivity,
    max N₀ (max 8 (max M1 (max M2 5000))), ?_⟩
  intro M hM0
  have hMN₀ : N₀ ≤ M := le_trans (Nat.le_max_left _ _) hM0
  have hM8 : 8 ≤ M := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hM0
  have hMmid : max M1 (max M2 5000) ≤ M := by
    refine le_trans ?_ hM0
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hMM1 : M1 ≤ M := le_trans (Nat.le_max_left _ _) hMmid
  have hMM2 : M2 ≤ M := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hMmid)
  have hM5000 : 5000 ≤ M :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hMmid)
  have hM1' : 1 ≤ M := by omega
  have hMposN : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  -- the double count
  have hcount' : (mult γ M : ℝ) * (dyadicCount Bad M : ℝ) ≤
      ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) := by
    refine card_mul_le_sum_blocks γ Bad M (mult γ M) (fun n hn => ?_)
    obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnM, hn2M⟩ := Finset.mem_Ico.mp hnI
    exact_mod_cast card_window_ge_mult h1 hM8 hnM hn2M
  have hsum := sum_blockCount_le h1 h2 hκ hB h hMN₀ hM1'
  set k := (Real.log 2 / (16 * γ)) * (M : ℝ) *
    (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) with hkdef
  set Q := (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (γ - 1) with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]; exact Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
  have hinvQ : (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) = Q⁻¹ := by
    rw [hQdef, show (1 : ℝ) - γ = -(γ - 1) by ring,
      Real.rpow_neg (le_of_lt (log_nat_add_one_pos _))]
  have hkform : k = (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by rw [hkdef, hinvQ]
  have hkpos : 0 < k := by
    have h3 : 0 < (Real.log ((2 * M : ℕ) : ℝ) + 1) ^ (1 - γ) :=
      Real.rpow_pos_of_pos (log_nat_add_one_pos _) _
    rw [hkdef]; exact mul_pos (mul_pos hA2 hMposN) h3
  have hmult_le : (mult γ M : ℝ) ≤ k := by
    rw [hkdef]; exact mult_le_cast hγ0 M
  have hmult_lt : k < (mult γ M : ℝ) + 1 := by
    rw [hkdef]; exact Nat.lt_floor_add_one _
  -- `√M = exp (log M / 2)`
  have hQsqM : Real.sqrt (M : ℝ) = Real.exp (Real.log M / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hMposN]
    congr 1
    ring
  have hQle : Q ≤ Real.sqrt (M : ℝ) := by
    refine le_trans (hM1 M hMM1) ?_
    rw [hQsqM]
    exact Real.exp_le_exp.mpr (hM2 M hMM2)
  have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMposN
  have hMsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMposN.le
  have hsqrt70 : (70 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    have hsq : Real.sqrt ((70 : ℝ) ^ 2) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 4900 ≤ M))
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70)] at hsq
  have h70 : (2 : ℝ) ≤ (Real.log 2 / (16 * γ)) * 70 := by
    have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 16 * γ)]
    nlinarith
  have hk2 : 2 ≤ k := by
    rw [hkform]
    have hle : Real.sqrt (M : ℝ) ≤ (M : ℝ) / Q := by
      rw [le_div_iff₀ hQpos]
      calc Real.sqrt (M : ℝ) * Q ≤ Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) :=
            mul_le_mul_of_nonneg_left hQle hsqrtpos.le
        _ = (M : ℝ) := hMsq
    have h4 : (M : ℝ) / Q = (M : ℝ) * Q⁻¹ := by ring
    have hstep : (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ) ≤
        (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by
      calc (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ)
          ≤ (Real.log 2 / (16 * γ)) * ((M : ℝ) / Q) :=
            mul_le_mul_of_nonneg_left hle hA2.le
        _ = (Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹ := by
            rw [h4]; ring
    calc (2 : ℝ) ≤ (Real.log 2 / (16 * γ)) * 70 := h70
      _ ≤ (Real.log 2 / (16 * γ)) * Real.sqrt (M : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt70 hA2.le
      _ ≤ _ := hstep
  have hmultk : k / 2 ≤ (mult γ M : ℝ) := by linarith
  set E1 := Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) with hE1def
  have hDk : (dyadicCount Bad M : ℝ) * k ≤
      2 * (∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ)) := by
    have hD0 : (0 : ℝ) ≤ (dyadicCount Bad M : ℝ) := Nat.cast_nonneg _
    nlinarith [hcount', hmultk, hkpos, hD0]
  have hS16 : ∑ N ∈ Finset.Ico M (4 * M + 1), (blockCount γ Bad N : ℝ) ≤
      16 * B * (M : ℝ) ^ 2 * E1 := by
    rw [hE1def]; exact hsum
  have hD_le : (dyadicCount Bad M : ℝ) ≤ 32 * B * (M : ℝ) ^ 2 * E1 / k := by
    rw [le_div_iff₀ hkpos]
    nlinarith [hDk, hS16]
  refine hD_le.trans ?_
  have hscalar : E1 ≤ Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
    have hQle' : Q ≤ Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) := hM1 M hMM1
    have hone : (1 : ℝ) ≤ Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hQle' (le_of_lt (inv_pos.mpr hQpos))
      rwa [mul_inv_cancel₀ (ne_of_gt hQpos)] at h
    have hpos1 : (0 : ℝ) < Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := Real.exp_pos _
    have h := mul_le_mul_of_nonneg_left hone hpos1.le
    rw [mul_one] at h
    calc E1 = Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) := hE1def
      _ ≤ Real.exp (-(κ / 12) * Real.log M ^ (3 - 2 * γ)) *
            (Real.exp (κ / 24 * Real.log M ^ (3 - 2 * γ)) * Q⁻¹) := h
      _ = Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
  rw [div_le_iff₀ hkpos, hkform]
  have hM2nn : (0 : ℝ) ≤ 32 * B * (M : ℝ) ^ 2 := by positivity
  calc 32 * B * (M : ℝ) ^ 2 * E1
      ≤ 32 * B * (M : ℝ) ^ 2 *
          (Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) * Q⁻¹) :=
        mul_le_mul_of_nonneg_left hscalar hM2nn
    _ = 32 * B / (Real.log 2 / (16 * γ)) * (M : ℝ) *
          Real.exp (-(κ / 24) * Real.log M ^ (3 - 2 * γ)) *
          ((Real.log 2 / (16 * γ)) * (M : ℝ) * Q⁻¹) := by
        field_simp

/-- ASSEMBLY page 366 and 367. No longer Theorem 1 restated: it follows from `block_bound` and the
dissection leaf, and does not use `BrudernPerelli1998.brudernPerelli`. -/
theorem leaf_dyadic_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, hB, N₀, h⟩ := block_bound γ h1 h2
  obtain ⟨c, hc, C, hC, M0, hM⟩ :=
    leaf_block_dissection γ κ B h1 h2 hκ hB (fun n => ¬ Solvable γ n) N₀ h
  refine ⟨c, hc, C, hC, M0, fun M hM0 => ?_⟩
  have e : Eγ_dyadic γ M = dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold Eγ_dyadic dyadicCount
    congr!
  rw [e]
  exact hM M hM0

/-- PROVED. The total exceptions up to `N` are at most the sum over the dyadic blocks. -/
theorem leaf_dyadic_sum (γ : ℝ) (N : ℕ) :
    (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := by
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ Solvable γ n) ⊆
      (dyadicIdx N).biUnion (fun i => (Finset.Ico i (2 * i)).filter (fun n => ¬ Solvable γ n)) := by
    intro n hn
    obtain ⟨hn, hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    refine Finset.mem_biUnion.mpr ⟨2 ^ Nat.log 2 n, ?_, Finset.mem_filter.mpr ⟨?_, hb⟩⟩
    · refine Finset.mem_image.mpr ⟨Nat.log 2 n, ?_, rfl⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hnN))
    · refine Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [pow_succ] at this
      omega
  have hcard : Eγ γ N ≤ ∑ i ∈ dyadicIdx N, Eγ_dyadic γ i :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact_mod_cast hcard

/-- For `0 < p ≤ 1` and `0 ≤ y`, `y ^ p ≤ y + 1`. -/
private lemma rpow_le_self_add_one {y p : ℝ} (hy : 0 ≤ y) (hp : 0 < p) (hp1 : p ≤ 1) :
    y ^ p ≤ y + 1 := by
  by_cases h : y ≤ 1
  · have := Real.rpow_le_one hy h hp.le
    linarith
  · have hy1 : (1 : ℝ) < y := not_le.mp h
    have h' := Real.rpow_le_rpow_of_exponent_le hy1.le hp1
    rw [Real.rpow_one] at h'
    linarith

/-- PROVED, page 367. The sum of the exponential bound over the dyadic blocks: the sum runs over
`M = 2 ^ j ≤ N` and is geometric; over all `M ≤ N` it would be about `N²` times the exponential. -/
theorem leaf_dyadic_sum_exp (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ)) := by
  set p : ℝ := 3 - 2 * γ with hpdef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  set d : ℝ := min c (1 / 2) with hd
  have hd0 : 0 < d := lt_min hc (by norm_num)
  have hdc : d ≤ c := min_le_left _ _
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  refine ⟨d, hd0, C * Real.exp d * 4, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hN1
  set sN : ℝ := Real.exp (L / 2) with hsN
  have hsN0 : 0 < sN := Real.exp_pos _
  have hsN2 : sN ^ 2 = N := by
    rw [hsN, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (L / 2) = L := by push_cast; ring
    rw [this, hL, Real.exp_log hN0]
  set r : ℝ := Real.exp (Real.log 2 / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ^ 2 = 2 := by
    rw [hr, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (Real.log 2 / 2) = Real.log 2 := by push_cast; ring
    rw [this, Real.exp_log (by norm_num)]
  have hr43 : 4 / 3 ≤ r := by
    by_contra hlt
    have hlt' : r < 4 / 3 := not_le.mp hlt
    nlinarith
  have hgeom : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), r ^ j ≤ 4 * r ^ J := by
    intro J
    induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ r n]
      have hrn : 0 < r ^ n := pow_pos hr0 n
      nlinarith
  have hterm : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * Real.log ((2 ^ j : ℕ) : ℝ) ^ p) ≤
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := by
    intro j hj
    have hjN : 2 ^ j ≤ N := by
      have hj' : j ≤ Nat.log 2 N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 (by omega))
    have hM1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    set x : ℝ := Real.log ((2 ^ j : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := Real.log_nonneg hM1
    have hxL : x ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hjN)
    have hy0 : 0 ≤ L - x := by linarith
    have hsub : L ^ p ≤ x ^ p + (L - x) ^ p := by
      have := Real.rpow_add_le_add_rpow hx0 hy0 hp.le hp1.le
      rwa [add_sub_cancel] at this
    have hy1 : (L - x) ^ p ≤ (L - x) + 1 := rpow_le_self_add_one hy0 hp hp1.le
    have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx0 _
    have hyp : 0 ≤ (L - x) ^ p := Real.rpow_nonneg hy0 _
    have hkey : -c * x ^ p ≤ d + -d * L ^ p + (L - x) / 2 := by
      have e1 : d * L ^ p ≤ d * x ^ p + d * (L - x) ^ p := by nlinarith
      have e2 : d * x ^ p ≤ c * x ^ p := mul_le_mul_of_nonneg_right hdc hxp
      have e3 : d * (L - x) ^ p ≤ d * ((L - x) + 1) := mul_le_mul_of_nonneg_left hy1 hd0.le
      have e4 : d * (L - x) ≤ (1 / 2) * (L - x) := mul_le_mul_of_nonneg_right hd2 hy0
      nlinarith
    have hexp := Real.exp_le_exp.mpr hkey
    have hxval : ((2 ^ j : ℕ) : ℝ) = Real.exp x := by
      rw [hx, Real.exp_log (by linarith)]
    have hrj : r ^ j = Real.exp (x / 2) := by
      rw [hr, ← Real.exp_nat_mul, hx]
      congr 1
      push_cast
      rw [Real.log_pow]
      ring
    have hcomb : Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) =
        Real.exp d * Real.exp (-d * L ^ p) * sN * Real.exp (x / 2) := by
      rw [hsN]
      simp only [← Real.exp_add]
      congr 1
      ring
    rw [hrj]
    calc C * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c * x ^ p)
        = C * Real.exp x * Real.exp (-c * x ^ p) := by rw [← hxval]
      _ ≤ C * Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * (Real.exp x * Real.exp (d + -d * L ^ p + (L - x) / 2)) := by ring
      _ = _ := by rw [hcomb]; ring
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j)
      (Finset.range (Nat.log 2 N + 1) : Set ℕ) :=
    fun _ _ _ _ h => Nat.pow_right_injective (le_refl 2) h
  unfold dyadicIdx
  rw [Finset.sum_image hinj]
  have hA : 0 ≤ C * Real.exp d * Real.exp (-d * L ^ p) * sN := by positivity
  have hrJ : r ^ Nat.log 2 N ≤ sN := by
    have h2J : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have : (r ^ Nat.log 2 N) ^ 2 ≤ sN ^ 2 := by
      rw [hsN2, ← pow_mul, mul_comm, pow_mul, hr2]
      exact_mod_cast h2J
    exact (pow_le_pow_iff_left₀ (by positivity) hsN0.le (by norm_num)).mp this
  calc _ ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * r ^ j := Finset.sum_le_sum hterm
    _ = (C * Real.exp d * Real.exp (-d * L ^ p) * sN) *
        ∑ j ∈ Finset.range (Nat.log 2 N + 1), r ^ j := by rw [Finset.mul_sum]
    _ ≤ (C * Real.exp d * Real.exp (-d * L ^ p) * sN) * (4 * sN) :=
        mul_le_mul_of_nonneg_left ((hgeom _).trans (by linarith)) hA
    _ = C * Real.exp d * 4 * sN ^ 2 * Real.exp (-d * L ^ p) := by ring
    _ = _ := by rw [hsN2]

/-- For `N ≥ 2` and `0 < p < 1`, the factor `N * exp (-c * (log N) ^ p)` dominates the constant
`exp (-c) * 2 ^ (1 - c)` when `0 < c ≤ 1`. -/
private lemma le_mul_exp_neg_mul_log_rpow {c p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-c) * (2 : ℝ) ^ (1 - c) ≤
      (N : ℝ) * Real.exp (-c * Real.log N ^ p) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hstep : Real.log N ^ p ≤ Real.log N + 1 := rpow_le_self_add_one hlog hp hp1.le
  have hmul : c * Real.log N ^ p ≤ c * (Real.log N + 1) :=
    mul_le_mul_of_nonneg_left hstep hc.le
  have hexp_le : Real.exp (-c * Real.log N - c) ≤ Real.exp (-c * Real.log N ^ p) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (0 : ℝ) ≤ 1 - c := by linarith
  have hNpow : (2 : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c) :=
    Real.rpow_le_rpow (by norm_num) hN2 hpow
  have hmain : (N : ℝ) * Real.exp (-c * Real.log N) = (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * Real.exp (-c * Real.log N)
        = Real.exp (Real.log N) * Real.exp (-c * Real.log N) := by rw [Real.exp_log hNpos]
      _ = Real.exp (Real.log N + -c * Real.log N) := by rw [← Real.exp_add]
      _ = Real.exp (Real.log N * (1 - c)) := by
          congr 1
          ring
      _ = (N : ℝ) ^ (1 - c) := by rw [Real.rpow_def_of_pos hNpos]
  calc Real.exp (-c) * (2 : ℝ) ^ (1 - c)
      ≤ Real.exp (-c) * (N : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hNpow (Real.exp_pos _).le
    _ = Real.exp (-c) * ((N : ℝ) * Real.exp (-c * Real.log N)) := by rw [hmain]
    _ = (N : ℝ) * (Real.exp (-c) * Real.exp (-c * Real.log N)) := by ring
    _ = (N : ℝ) * Real.exp (-c * Real.log N - c) := by
        congr 1
        rw [← Real.exp_add]
        ring
    _ ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ p) :=
        mul_le_mul_of_nonneg_left hexp_le hNpos.le

/-- LEAF page 367: Given the exponential sum bound and dyadic sum bound, Theorem 1 holds. -/
theorem leaf_theorem1_from_sums (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    (∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ))) →
    (∀ M : ℕ, Eγ_dyadic γ M ≤ M) →
    (∀ N : ℕ, (Eγ γ N : ℝ) ≤ (∑ i ∈ dyadicIdx N, Eγ_dyadic γ i : ℝ)) →
    (∀ c C : ℝ, 0 < c → 0 < C → ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ dyadicIdx N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ) ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))) →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
  intro hA hB hC hD
  obtain ⟨c₀, hc₀, C₀, hC₀, M₀, hM₀⟩ := hA
  obtain ⟨c₁, hc₁, C₁, hC₁, hD₁⟩ := hD c₀ C₀ hc₀ hC₀
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  set c : ℝ := min c₁ (1 / 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact lt_min hc₁ (by norm_num)
  have hcc₁ : c ≤ c₁ := by
    rw [hcdef]; exact min_le_left _ _
  have hc1 : c ≤ 1 := by
    rw [hcdef]; have := min_le_right c₁ (1 / 2 : ℝ); linarith
  have hδ : 0 < Real.exp (-c) * (2 : ℝ) ^ (1 - c) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c, hc, (M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnonneg : (0 : ℝ) ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg hlogN _
  have hexp_le : Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) ≤
      Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsplit : (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ))
      = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (dyadicIdx N) (fun i => i < M₀)
      (fun i => (Eγ_dyadic γ i : ℝ))).symm
  have hpart1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ (M₀ : ℝ) ^ 2 := by
    have h1 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact_mod_cast hB i
    have h2 : (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ)) ≤ (M₀ : ℝ) ^ 2 := by
      have hcard : ((dyadicIdx N).filter (fun i => i < M₀)).card ≤ M₀ := by
        have hsub : (dyadicIdx N).filter (fun i => i < M₀) ⊆ Finset.range M₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
        calc _ ≤ (Finset.range M₀).card := Finset.card_le_card hsub
          _ = M₀ := Finset.card_range M₀
      have hcard' : (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) ≤ (M₀ : ℝ) := by
        exact_mod_cast hcard
      have hM₀nn : (0 : ℝ) ≤ (M₀ : ℝ) := by positivity
      calc (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (i : ℝ))
          ≤ ∑ _i ∈ (dyadicIdx N).filter (fun i => i < M₀), (M₀ : ℝ) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi' : i < M₀ := (Finset.mem_filter.mp hi).2
            exact_mod_cast hi'.le
        _ = (((dyadicIdx N).filter (fun i => i < M₀)).card : ℝ) * (M₀ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M₀ : ℝ) * (M₀ : ℝ) := by nlinarith
        _ = (M₀ : ℝ) ^ 2 := by ring
    linarith
  have hpart2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by
    have hle1 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiM : M₀ ≤ i := by
        have := (Finset.mem_filter.mp hi).2
        omega
      exact hM₀ i hiM
    have hle2 : (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))))
        ≤ ∑ i ∈ dyadicIdx N, (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro i _ _
      positivity
    linarith [hD₁ N hN]
  have hDbound : (M₀ : ℝ) ^ 2 ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
      * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by
    have hkey := le_mul_exp_neg_mul_log_rpow (c := c) (p := 3 - 2 * γ) hc hc1 hp hp1 hN
    calc (M₀ : ℝ) ^ 2
        = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) := by field_simp
      _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) :=
          mul_le_mul_of_nonneg_left hkey (div_nonneg (sq_nonneg _) hδ.le)
  have hC₁le : C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
      ≤ C₁ * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    have h1 : (0 : ℝ) ≤ C₁ * (N : ℝ) := by positivity
    calc C₁ * (N : ℝ) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
        = (C₁ * (N : ℝ)) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ (C₁ * (N : ℝ)) * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) :=
          mul_le_mul_of_nonneg_left hexp_le h1
  calc (Eγ γ N : ℝ)
      ≤ (∑ i ∈ dyadicIdx N, (Eγ_dyadic γ i : ℝ)) := hC N
    _ = (∑ i ∈ (dyadicIdx N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        + (∑ i ∈ (dyadicIdx N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) := hsplit
    _ ≤ (M₀ : ℝ) ^ 2 + C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by linarith
    _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁)
        * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by nlinarith
    _ = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁) * N
        * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by ring

/-- ASSEMBLY. Theorem 1 of Brudern and Perelli 1998 from leaves. -/
theorem brudernPerelli_assembly : Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (leaf_dyadic_bound γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.DecompJ200

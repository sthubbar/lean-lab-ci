/-
P0054 J. Pintz, "An approximate formula for Goldbach's problem with applications",
Riv. Mat. Univ. Parma 12 (2021), 181-199. Unit U-1581 decomposed, GEMINI task281.

AI-written Lean code, Gemini, 2026-10-28. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.Applications

namespace LeanLab.Pintz2021.DecompJ281

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Modified singular series and U cutoff, (2.11) and (2.12) -/

/-- `c'(χ₁,χ₂,q,m) = φ(q)^{-2} c_{χ₁\overline{χ₂}χ₀,q}(-m) τ(\overline{χ₁}χ₀,q) \overline{τ(\overline{χ₂}χ₀,q)}`. -/
def cCoefPrime (z w : ExcPair) (q : ℕ) (m : ℕ) : ℂ :=
  ((Nat.totient q : ℂ) ^ 2)⁻¹ * cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ)) *
    tau q (lift z q)⁻¹ * starRingEnd ℂ (tau q (lift w q)⁻¹)

/-- The partial sums of `𝔖'`: `∑_{q ≤ Q, [r₁, r₂] ∣ q} c'(χ₁,χ₂,q,m)`. -/
def singPartialPrime (z w : ExcPair) (m Q : ℕ) : ℂ :=
  ∑ q ∈ (Icc 1 Q).filter (fun q => Nat.lcm z.r w.r ∣ q), cCoefPrime z w q m

/-- `R₁'(m) = ∫_{𝔐} |S(α)|² e(-mα) dα`, using `differenceR1`. -/
def R1majPrime (ε X P : ℝ) (m : ℕ) : ℂ :=
  differenceR1 (S (X1 ε X) X) (Lemma1U1369.majorArcs P (X / P))ᶜ m

/-- The main term of (2.11), with the discrete difference kernel `I'(ϱᵢ,ϱⱼ,m)`:
`∑_{i,j ∈ E} A(ϱᵢ)A(ϱⱼ) 𝔖'(χᵢ,χⱼ,m) I'(ϱᵢ,ϱⱼ,m)`. -/
def mainTermPrime (E : Set ExcPair) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (ε X : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E), ∑ᶠ (w) (_ : w ∈ E),
    ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg' z w m *
      WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m true

/-- The cutoff function `U(χ₁, χ₂, m) = \max(r₁²/(r₁,r₂)², r₂²/(r₁,r₂)², r₁/(m,r₁), r₂/(m,r₂), \mathrm{cond}(χ₁\overline{χ₂}))`.
We evaluate the gcd for `m : ℕ`. -/
def UCutoff (z w : ExcPair) (m : ℕ) : ℝ :=
  max (max ((z.r : ℝ)^2 / (Nat.gcd z.r w.r : ℝ)^2) ((w.r : ℝ)^2 / (Nat.gcd z.r w.r : ℝ)^2))
    (max (max ((z.r : ℝ) / (Nat.gcd m z.r : ℝ)) ((w.r : ℝ) / (Nat.gcd m w.r : ℝ)))
      ((lift z (Nat.lcm z.r w.r) * (lift w (Nat.lcm z.r w.r))⁻¹).conductor : ℝ))


/-- The pre-2026-11-01 form of the truncated main term of (2.12), without the paper's
`[r₁, r₂] ≤ P` restriction; kept so LeafAudit168's refutations still build. -/
def mainTermTruncatedPrime_v1 (E : Set ExcPair) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (ε X U : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E ∧ |z.ρ.im| ≤ U), ∑ᶠ (w) (_ : w ∈ E ∧ |w.ρ.im| ≤ U),
    if UCutoff z w m ≤ U then
      ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg' z w m *
        WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m true
    else 0

/-- The truncated main term of (2.12).
DECISION 2026-11-01 architect PC 20261101T0240Z-32570 U-1591: adds the paper's [r₁, r₂] ≤ P restriction of display 2.22, matching Truncation168.retainedPairs; old form mainTermTruncatedPrime_v1. -/
def mainTermTruncatedPrime (E : Set ExcPair) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (ε X P U : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E ∧ |z.ρ.im| ≤ U), ∑ᶠ (w) (_ : w ∈ E ∧ |w.ρ.im| ≤ U),
    if (Nat.lcm z.r w.r : ℝ) ≤ P ∧ UCutoff z w m ≤ U then
      ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg' z w m *
        WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m true
    else 0

/-- LEAF P0054 page 8: for `1 ≤ P` the pole pair passes the `[r₁, r₂] ≤ P` restriction. -/
theorem pole_lcm_retained {P : ℝ} (hP : 1 ≤ P) :
    (Nat.lcm pole.r pole.r : ℝ) ≤ P := by
  simpa [pole] using hP

/-- LEAF P0054 page 8: The pole lies in the truncated subset if U is at least 0. -/
theorem pole_mem_truncated {H P X U : ℝ} (hU : 0 ≤ U) :
    pole ∈ excSet H (Real.sqrt X) P X ∧ |pole.ρ.im| ≤ U := by
  refine ⟨pole_mem_excSet H (Real.sqrt X) P X, ?_⟩
  simp [pole, hU]

/-- LEAF P0054 page 8: The pole is not truncated by any U at least 1. -/
theorem pole_not_truncated {m : ℕ} {U : ℝ} (hU : 1 ≤ U) :
    UCutoff pole pole m ≤ U := by
  have hc : (lift pole (Nat.lcm pole.r pole.r) *
      (lift pole (Nat.lcm pole.r pole.r))⁻¹).conductor = 1 := by
    rw [Audit168.lift_pole, inv_one, mul_one]
    change (1 : DirichletCharacter ℂ 1).conductor = 1
    exact DirichletCharacter.conductor_one
  simp only [UCutoff, hc]
  simpa [pole] using hU

/-- LEAF P0054 page 8: `cCoefPrime` for the pole is exactly `cCoef` for the pole, as the trivial character is real. -/
theorem cCoefPrime_pole (q m : ℕ) :
    cCoefPrime pole pole q m = cCoef pole pole q m := by
  have ht : tau q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    (Audit168.cRam_one q 1).trans (PrincipalSeriesTask99.gauss_principal q)
  simp only [cCoefPrime, cCoef, Audit168.lift_pole, inv_one, mul_one, ht, map_intCast]


/-- LEAF P0054 page 8 display 2.21: Theorem 1 display 2.21 is cited as a leaf.
DECISION 2026-10-31 architect PC 20261031T2333Z-383: convergence asked only at `0 < m`;
LeafAudit168.untruncated_leaf_false refuted the old clause at `m = 0`.
DECISION 2026-11-06 architect 20261106T0803Z-25677 U-1625: the conclusion now also gives `1 ≤ P`.
Source P0054 page 2 display 1.2 fixes `2 ≤ P ≤ √X` for every arc level, Pin1 display 1.8 fixes
`L^c ≤ P`, so the printed Theorem 1 supplies this bound. Without it the pole fails the lcm
restriction in `assembly_222`, as `DecompJ281Audit.leaf_truncation_error_false` shows.
Twin: for small positive epsilon, some level P at least 1 inside the interval from P0 X to the
minus epsilon up to P0 satisfies display 2.21. Instance: `Audit1625.leaf_221_range_instance`, for the U-1625 range.
DECISION 2026-11-08 architect 20261108T0450Z U-1634: the quantifier shape of
`State1581.Theorem1_220`, U-1634 form: `c, C, A ≥ 0, H₀` existential, then a fixed `H ≥ H₀`, then
`X₀`; range `X^ε L^A ≤ P₀ ≤ X^{4/9-ε}`; `H ≤ (log X)/2` dropped. Source Pin1 displays 1.8, 2.8 and
the remark after 2.12. The U-1625 form was false at `P₀ = 1`, `H = (log X)/2` by hand. `1 ≤ P` now
also follows from the range, as `P ≥ P₀X^{-ε} ≥ L^A ≥ 1` for `X ≥ 3`. Instance of the range:
`State1581.thm1Hyp_inhabited`.
DECISION 2026-11-08 architect arch20261108T1030Z PMT: second error term `X^{1-ε}`, the
`O_ε(X^{1-ε})` of display 2.21, P0054 page 188 Theorem 1, read from the page image; the former
`X^{1-ε₀}` with `ε < ε₀` is smaller for `X ≥ 1`, so it claimed more than the paper.
DECISION 2026-11-09 architect 20261109T0802Z-9291 U-1637: the conclusion also gives display 2.22
at the chosen `P`: for `m ∈ [X/4, X/2]` and `2 ≤ U ≤ √X` the full and truncated main terms differ
by at most `C 𝔖(m) X log U / √U`. P0054 page 188 Theorem 1 lists 2.22 among the properties of the
chosen `P`, and Pin1 arXiv 1804.05561v1 Theorem 1 page 9 states 2.12 the same way; its proof,
Pin1 pages 33 to 37 displays 10.5, 10.6, 10.12, 10.21 and 10.24, uses the gap condition 10.6 of
the chosen `P`, both to drop the zeros of 10.7 and to drop the moduli `q ≥ P`. So 2.22 is not
sourced at every `P` in `[P₀X^{-ε}, P₀]`, and the former universal `leaf_truncation_error` is now a
corollary of this leaf. -/
theorem leaf_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ, ∀ X P0 : ℝ,
      Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, 1 ≤ P ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          (∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε))) ∧
          ∀ m : ℕ, ∀ U : ℝ, X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U → U ≤ Real.sqrt X →
            ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
              mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
              C * (Sing m * X * Real.log U / Real.sqrt U) := by sorry


/-- LEAF P0054 page 8 display 2.22: The difference between the full and truncated main terms is
bounded by the additional error `O(𝔖(m) X log U / √U)`, inside Theorem 1's parameter range.
DECISION 2026-10-31 architect PC 20261031T2333Z-383: the old form quantified over every `Sg'`, `U`,
`X`, `H`, `P` and `m` with one constant, and LeafAudit168.unrestricted_tail_false refuted it at
`U = 0`. It now takes Theorem 1's range, `P ≤ P₀`, a finite `E`, `Sg'` the actual limits of the
series at positive frequencies, `m ∈ [X/4, X/2]` as in (2.21), and `U ≥ 2`; the constant may depend
on `ε`, matching the `O_ε` of Theorem 1.
DECISION 2026-11-01 U-1591: the truncated term now keeps only pairs with [r₁, r₂] ≤ P, as in the paper.
DECISION 2026-11-06 architect 20261106T0803Z-25677 U-1625: three hypotheses added, each a weakening
of the leaf, and all three are met in `assembly_222`. `1 ≤ P` and `P0 * X ^ (-ε) ≤ P` are the
source range, P0054 page 2 display 1.2 and page 8 Theorem 1; the former form admitted `P = 0`
and is refuted by `DecompJ281Audit.leaf_truncation_error_false`. `U ≤ √X`: at fixed `X` the old
form let `U` grow, where the right side tends to zero while pairs with `[r₁, r₂] > P` stay
dropped, so it forced their sum to vanish exactly, which the source never claims. Source
P0054 page 8 display 2.22 uses a bounded cutoff, and `assembly_222` uses `U = √X`.
Twin: for the level P at least 1 in the source interval and U from 2 to the square root of X, the
full and truncated main terms differ by at most C' Sing m X log U over the square root of U.
Instance: `Audit1625.leaf_truncation_range_instance`, for the U-1625 range.
DECISION 2026-11-08 architect 20261108T0450Z U-1634: carried to the U-1634 range. For every
exponent `A` there are `C' > 0` and `H₀`, then a fixed `H ≥ H₀` and `X₀`; `C'` precedes `H` as the
`O` of Pin1 display 2.12 carries no subscript. Taking every `A` is what `assembly_222` needs, it
receives `A` from `leaf_221`.
DECISION 2026-11-09 architect 20261109T0802Z-9291 U-1637: `P` is no longer universal. P0054
page 188 Theorem 1 and Pin1 page 9 Theorem 1 give display 2.22, Pin1 2.12, only at the chosen `P`
of Pin1 displays 10.5 and 10.6, and the proof of 2.12 uses 10.6. The bound is now a clause of
`leaf_221`, and this theorem is its projection, with `P`, `A` and the series `Sg'` existential as
there and one constant. No longer a leaf: PROVED from `leaf_221`, so CONDITIONAL on it. -/
theorem leaf_truncation_error :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ C' A H0 : ℝ, 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ, ∀ X P0 : ℝ,
      Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, 1 ≤ P ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
            Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) ∧
          ∀ m : ℕ, ∀ U : ℝ, X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U → U ≤ Real.sqrt X →
            ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
              mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
              C' * (Sing m * X * Real.log U / Real.sqrt U) := by
  obtain ⟨ε0, hε0, h⟩ := leaf_221
  refine ⟨ε0, hε0, fun ε hε hεlt => ?_⟩
  obtain ⟨c, C, A, H0, -, hA0, hA⟩ := h ε hε hεlt
  refine ⟨C, A, H0, hA0, fun H hH => ?_⟩
  obtain ⟨X0, hX⟩ := hA H hH
  refine ⟨X0, fun X P0 hHyp => ?_⟩
  obtain ⟨P, hP1, hPl, hPu, hFin, Sg', hSg, -, hT⟩ := hX X P0 hHyp
  exact ⟨P, hP1, hPl, hPu, hFin, Sg', hSg, hT⟩

/-- LEAF P0054 page 8 display 2.22: The combined error bound is derived from the main term bound and the truncation bound via triangle inequality.
DECISION 2026-10-31 architect PC 20261031T2333Z-383: takes `1 ≤ X`, so `log U ≥ 0`;
LeafAudit168.triangle_leaf_false refuted the old form at `X = -1`. Now PROVED. -/
theorem leaf_triangle_inequality {H X P U ε ε0 c C C' : ℝ} {m : ℕ} {Sg' : ExcPair → ExcPair → ℕ → ℂ}
    (h_bound1 : ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
      C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)))
    (h_bound2 : ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U))
    (hU : U = Real.sqrt X) (hX : 1 ≤ X) :
    ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      max C C' * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) + Sing m * X * Real.log U / (X ^ (1/4 : ℝ))) := by
  have hS := Applications.Sing_pos m
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hU1 : 1 ≤ U := by
    rw [hU, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hX
  have hsq : Real.sqrt U = X ^ (1 / 4 : ℝ) := by
    rw [hU, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]; norm_num
  rw [← hsq]
  have ha : 0 ≤ Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) :=
    add_nonneg (mul_nonneg (mul_nonneg hS.le hX0) (Real.exp_pos _).le) (Real.rpow_nonneg hX0 _)
  have hb : 0 ≤ Sing m * X * Real.log U / Real.sqrt U :=
    div_nonneg (mul_nonneg (mul_nonneg hS.le hX0) (Real.log_nonneg hU1)) (Real.sqrt_nonneg _)
  calc _ ≤ ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ +
        ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
          mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) +
        C' * (Sing m * X * Real.log U / Real.sqrt U) := add_le_add h_bound1 h_bound2
    _ ≤ max C C' * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) +
        max C C' * (Sing m * X * Real.log U / Real.sqrt U) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hb)
    _ = _ := by ring

/-- Assembly theorem for 2.22, proved from the leaves. Changed 2026-10-31 only in its convergence
clause, now `0 < m` as in leaf_221; the proof takes `X₀` at least 4 so that `U = √X ≥ 2`.
Statement unchanged by U-1625 2026-11-06; only the proof passes the new `1 ≤ P` of `leaf_221`
to the repaired `leaf_truncation_error`.
DECISION 2026-11-08 U-1634: the quantifier shape of `State1581.Theorem1_220`, U-1634 form.
DECISION 2026-11-08 architect arch20261108T1030Z PMT: error term `X^{1-ε}` as in `leaf_221`,
`State1581.Theorem1_220` and P0054 page 188.
DECISION 2026-11-09 architect 20261109T0802Z-9291 U-1637: statement unchanged; the proof takes
both bounds from the one chosen `P` of `leaf_221`, which now carries display 2.22. -/
theorem assembly_222 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c C A H0 : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ H : ℝ, H0 ≤ H → ∃ X0 : ℝ, ∀ X P0 : ℝ,
      Thm1Hyp ε A X0 X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, X / 4 ≤ m ∧ (m : ℝ) ≤ X / 2 →
            ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P (Real.sqrt X) m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε) + Sing m * X * Real.log (Real.sqrt X) / (X ^ (1/4 : ℝ))) := by
  obtain ⟨ε1, hε1, h1⟩ := leaf_221
  refine ⟨ε1, hε1, ?_⟩
  intro ε hε hεlt
  obtain ⟨c, C, A, H0, hc, hA0, hA⟩ := h1 ε hε hεlt
  refine ⟨c, max C C, A, H0, hc, hA0, ?_⟩
  intro H hH
  obtain ⟨X0, hAX⟩ := hA H hH
  refine ⟨max X0 4, ?_⟩
  intro X P0 hHyp
  obtain ⟨hX0, hX3, hlow, hP0X⟩ := hHyp
  have hXa : X0 ≤ X := le_trans (le_max_left _ _) hX0
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_right _ _) hX0
  have hHA : Thm1Hyp ε A X0 X P0 := ⟨hXa, hX3, hlow, hP0X⟩
  obtain ⟨P, -, hP1, hP2, hFin, Sg', hSg1, hSg2, hSg3⟩ := hAX X P0 hHA
  refine ⟨P, hP1, hP2, hFin, Sg', hSg1, ?_⟩
  intro m hm
  have hU2 : (2 : ℝ) ≤ Real.sqrt X := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX4
  have hb1 := hSg2 m (by linarith [hm.2])
  have hb2 := hSg3 m (Real.sqrt X) hm.1 hm.2 hU2 le_rfl
  exact leaf_triangle_inequality hb1 hb2 rfl (by linarith)

end
end LeanLab.Pintz2021.DecompJ281

#print axioms LeanLab.Pintz2021.DecompJ281.pole_not_truncated

#print axioms LeanLab.Pintz2021.DecompJ281.pole_lcm_retained

#print axioms LeanLab.Pintz2021.DecompJ281.cCoefPrime_pole

#print axioms LeanLab.Pintz2021.DecompJ281.leaf_triangle_inequality

#print axioms LeanLab.Pintz2021.DecompJ281.assembly_222

#print axioms LeanLab.Pintz2021.DecompJ281.leaf_truncation_error



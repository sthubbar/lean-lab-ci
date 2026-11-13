/-
Split of `mv_no_siegel150` of `LeanLab.BhowmikGrimmelt2026.Decomp150b` into four leaves.

`mv_no_siegel150` is the no-Siegel-zero half of Theorem 5.1: with no Siegel zero of level
`X ^ ϑ` the exceptional even numbers of the dyadic window `[X / 2, X]` satisfy
`|Edy X| ≤ C X ^ (1 - ϑ / 2)`. The route of Section 5 is: part one of Proposition 5.2 gives
the saving `exp (-c log N / log R)` on the sum over primitive characters of the interval
maxima; at the level `R = X ^ ϑ` that saving is the constant `exp (-(c / ϑ))` and the level
gain `N / R` is `X ^ (1 - ϑ)`; the minor arc second moment from Gallagher 1970 pays the
error of the major arc lower bound; and half of the exponent `ϑ` absorbs the fixed
logarithmic losses of that count.

The four leaves are one step each:

* LEAF 1: part one of Proposition 5.2, unpacked from `h52`. No count is asserted.
* LEAF 2: the range conditions of that proposition hold at `N = ⌈X⌉₊`, `R = X ^ ϑ` for large
  `X`, and the saving there is at most `exp (-(c / ϑ))`.
* LEAF 3: the circle-method count, from the saving of LEAF 2 and the Gallagher bound to
  `K exp (-(c / ϑ)) X ^ (1 - ϑ) (log X) ^ 8` exceptional evens. This is the large step.
* LEAF 4: `K X ^ (1 - ϑ) (log X) ^ 8 ≤ C X ^ (1 - ϑ / 2)` for large `X`, half of the power
  paying for the logarithm.

The assembly `mv_no_siegel150_split` has no sorry, uses none of `mv_siegel150`,
`theorem51_decomposed150` or `theorem51`, and carries its own exponent bookkeeping.
LEAF 4 is proved in this file; LEAVES 1 to 3 are OPEN. AI wrote the Lean code. Binary
Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150b

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerSaving)
open ArithmeticFunction

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000 in
/-- LEAF 1 of 4. Part one of Proposition 5.2, read off from `h52` alone: there are `c > 0`
and `C` such that, whenever the three range conditions of the proposition hold and there is
no Siegel zero of level `R`, the sum over primitive characters of the interval maxima is at
most `C * exp (-c log N / log R)`. Nothing is asserted about the exceptional set, and the
second conjunct of `Prop52`, the Siegel zero case, is dropped. -/
theorem leaf_prop52_part_one (h52 : Prop52) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R) := by
  obtain ⟨c, hc, C, hC⟩ := h52
  refine ⟨c, C, hc, ?_⟩
  intro N R h1 h2 h3 hns
  exact (hC N R h1 h2 h3).1 hns

/-- LEAF 2 of 4. The level `R = X ^ ϑ` is admissible and the saving of LEAF 1 there is the
constant `exp (-(c / ϑ))`. For every `ϑ` in `(0, 1/5)` all three range conditions hold once
`X` is large, and with `N = ⌈X⌉₊` one has `log ⌈X⌉₊ ≥ log X`, so the exponent
`-c log ⌈X⌉₊ / log (X ^ ϑ)` is at most `-(c / ϑ)` and the saving at most `exp (-(c / ϑ))`;
the bound is stated with `max C 0` so that the sign of `C` needs no hypothesis. Only the
character sum at this level is bounded; no count of exceptional even numbers. -/
theorem leaf_interval_max_saving_at_level (c C : ℝ) (hc : 0 < c)
    (hbound : ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R)) :
    ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 5 → ∃ X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (X ^ ϑ) r χ β) →
      primSum (X ^ ϑ) (fun _ _ χ => intervalMax ⌈X⌉₊ (X ^ ϑ)
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        max C 0 * Real.exp (-(c / ϑ)) := by
  intro ϑ hϑ hϑ5
  refine ⟨Real.exp (Real.exp 2 / ϑ ^ 2) + 2, ?_⟩
  intro X hX hX0 hns
  have hXpos : 0 < X := by linarith
  have hϑ2pos : (0 : ℝ) < ϑ ^ 2 := by positivity
  have hϑ2lt1 : ϑ ^ 2 < 1 := by nlinarith [hϑ, hϑ5]
  have hexp2ge : (2 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hlogX_big : Real.exp 2 / ϑ ^ 2 ≤ Real.log X := by
    have hle : Real.exp (Real.exp 2 / ϑ ^ 2) ≤ X := by linarith
    have h := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp] at h
  have hLge2 : (2 : ℝ) ≤ Real.log X := by
    have h1 : (2 : ℝ) ≤ Real.exp 2 / ϑ ^ 2 := by
      rw [le_div_iff₀ hϑ2pos]
      nlinarith
    linarith
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hNX : X ≤ ((⌈X⌉₊ : ℕ) : ℝ) := Nat.le_ceil X
  have hNXpos : (0 : ℝ) < ((⌈X⌉₊ : ℕ) : ℝ) := by linarith
  have hNle : ((⌈X⌉₊ : ℕ) : ℝ) ≤ 2 * X := by
    have h := Nat.ceil_lt_add_one hXpos.le
    linarith
  have hlogN_ge : Real.log X ≤ Real.log ((⌈X⌉₊ : ℕ) : ℝ) := Real.log_le_log hXpos hNX
  have hlogN_le : Real.log ((⌈X⌉₊ : ℕ) : ℝ) ≤ 2 * Real.log X := by
    have h1 := Real.log_le_log hNXpos hNle
    have h2 : Real.log (2 * X) = Real.log 2 + Real.log X :=
      Real.log_mul (by norm_num) hXpos.ne'
    have h3 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    linarith
  have hlogN1 : (1 : ℝ) ≤ Real.log ((⌈X⌉₊ : ℕ) : ℝ) := by linarith
  have hcond1 : (2 : ℝ) ≤ Real.exp (Real.sqrt (Real.log ⌈X⌉₊)) := by
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Real.log ((⌈X⌉₊ : ℕ) : ℝ)) := by
      have h := Real.sqrt_le_sqrt hlogN1
      simpa using h
    have h1 : Real.exp 1 ≤ Real.exp (Real.sqrt (Real.log ((⌈X⌉₊ : ℕ) : ℝ))) :=
      Real.exp_le_exp.mpr hsqrt1
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    linarith
  have hsqrt_le : Real.sqrt (Real.log ((⌈X⌉₊ : ℕ) : ℝ)) ≤ ϑ * Real.log X := by
    have h1 : Real.sqrt (Real.log ((⌈X⌉₊ : ℕ) : ℝ)) ≤ Real.sqrt (2 * Real.log X) :=
      Real.sqrt_le_sqrt hlogN_le
    have h2 : Real.sqrt (2 * Real.log X) ≤ ϑ * Real.log X := by
      rw [Real.sqrt_le_left (mul_pos hϑ hLpos).le]
      have hmul : Real.exp 2 ≤ ϑ ^ 2 * Real.log X := by
        have h := (div_le_iff₀ hϑ2pos).1 hlogX_big
        rwa [mul_comm] at h
      nlinarith [hmul, hexp2ge, hLpos, hϑ2pos]
    linarith
  have hcond2 : Real.exp (Real.sqrt (Real.log ⌈X⌉₊)) ≤ X ^ ϑ := by
    rw [Real.rpow_def_of_pos hXpos]
    refine Real.exp_le_exp.mpr ?_
    calc Real.sqrt (Real.log ⌈X⌉₊) ≤ ϑ * Real.log X := hsqrt_le
      _ = Real.log X * ϑ := by ring
  have hcond3 : X ^ ϑ ≤ ((⌈X⌉₊ : ℕ) : ℝ) := by
    have h1 : X ^ ϑ ≤ X := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X) (by linarith : ϑ ≤ 1)
      simpa using h
    exact h1.trans hNX
  have hb := hbound ⌈X⌉₊ (X ^ ϑ) hcond1 hcond2 hcond3 hns
  have hlogR : Real.log (X ^ ϑ) = ϑ * Real.log X := Real.log_rpow hXpos ϑ
  have hmono : Real.exp (-c * Real.log ⌈X⌉₊ / Real.log (X ^ ϑ)) ≤ Real.exp (-(c / ϑ)) := by
    apply Real.exp_le_exp.mpr
    rw [hlogR]
    have h1 : c / ϑ ≤ c * Real.log ((⌈X⌉₊ : ℕ) : ℝ) / (ϑ * Real.log X) := by
      have hcϑ : (0 : ℝ) < c / ϑ := div_pos hc hϑ
      have hAL : (1 : ℝ) ≤ Real.log ((⌈X⌉₊ : ℕ) : ℝ) / Real.log X := by
        rw [le_div_iff₀ hLpos]
        linarith
      have heq : c * Real.log ((⌈X⌉₊ : ℕ) : ℝ) / (ϑ * Real.log X)
          = (c / ϑ) * (Real.log ((⌈X⌉₊ : ℕ) : ℝ) / Real.log X) := by
        field_simp
      rw [heq]
      calc c / ϑ = (c / ϑ) * 1 := by ring
        _ ≤ (c / ϑ) * (Real.log ((⌈X⌉₊ : ℕ) : ℝ) / Real.log X) :=
            mul_le_mul_of_nonneg_left hAL hcϑ.le
    have harg : -c * Real.log ((⌈X⌉₊ : ℕ) : ℝ) / (ϑ * Real.log X)
        = -(c * Real.log ((⌈X⌉₊ : ℕ) : ℝ) / (ϑ * Real.log X)) := by
      rw [neg_mul, neg_div]
    rw [harg]
    exact neg_le_neg h1
  have hCs : C * Real.exp (-c * Real.log ⌈X⌉₊ / Real.log (X ^ ϑ))
      ≤ max C 0 * Real.exp (-(c / ϑ)) := by
    by_cases hC0 : C ≤ 0
    · have h1 : C * Real.exp (-c * Real.log ⌈X⌉₊ / Real.log (X ^ ϑ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
      have h2 : (0 : ℝ) ≤ max C 0 * Real.exp (-(c / ϑ)) :=
        mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
      linarith
    · have hCpos : 0 < C := lt_of_not_ge hC0
      rw [max_eq_left hCpos.le]
      exact mul_le_mul_of_nonneg_left hmono hCpos.le
  exact hb.trans hCs

/-- LEAF 3 of 4. The count of the circle method, and the large step of this split: given the
character sum bound of LEAF 2 at the level `X ^ ϑ` and the Gallagher second moment bound on
the minor arcs, the major arc lower bound for the number of representations leaves
at most `K exp (-(c / ϑ)) X ^ (1 - ϑ) (log X) ^ 8` even numbers of `[X / 2, X]` with no
representation as a sum of two primes. The power `1 - ϑ` is the level gain `N / R`; the eighth
power of the logarithm is one fixed loss of the major arc bookkeeping, to be paid for by half
of the exponent `ϑ` in the next leaf. No bound of the shape `X ^ (1 - ϑ / 2)` is asserted
here, and the constant may depend on both `c` and `C`. -/
theorem leaf_exceptional_count_from_saving (c C : ℝ) (hc : 0 < c)
    (hGallagher : GallagherStandard)
    (hsaving : ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 5 → ∃ Xh : ℝ, ∀ X : ℝ, 2 ≤ X → Xh ≤ X →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (X ^ ϑ) r χ β) →
      primSum (X ^ ϑ) (fun _ _ χ => intervalMax ⌈X⌉₊ (X ^ ϑ)
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-(c / ϑ))) :
    ∃ K X₀ : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 2 ≤ X → X₀ ≤ X → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 5 →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (X ^ ϑ) r χ β) →
      (Edy X : ℝ) ≤ K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by
  sorry

/-- LEAF 4 of 4. Half of the saving pays for the logarithm: for a fixed `k` and `ϑ > 0` the
quantity `K X ^ (1 - ϑ) (log X) ^ k` is at most `C' X ^ (1 - ϑ / 2)` once `X` is large,
because `(log X) ^ k` grows slower than `X ^ (ϑ / 2)`. Pure real analysis, no arithmetic
input; at `k = 0` it is the monotonicity of `X ↦ X ^ (1 - ϑ)` in the exponent, and at `X = 2`
the constant `C'` and the threshold `X₀` absorb everything. -/
theorem leaf_log_loss_absorbed (K ϑ : ℝ) (k : ℕ) (hK : 0 ≤ K) (hϑ : 0 < ϑ) :
    ∃ C' X₀ : ℝ, 0 ≤ C' ∧ ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
      K * X ^ (1 - ϑ) * (Real.log X) ^ k ≤ C' * X ^ (1 - ϑ / 2) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨K, 1, hK, ?_⟩
    intro X hX _
    simp only [pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hK
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h2k : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    set ε : ℝ := ϑ / (2 * (k : ℝ)) with hεdef
    have hε : 0 < ε := by
      rw [hεdef]
      exact div_pos hϑ h2k
    have hεk : ε * (k : ℝ) = ϑ / 2 := by
      rw [hεdef]
      field_simp
    refine ⟨K / ε ^ k, 1, div_nonneg hK (pow_pos hε k).le, ?_⟩
    intro X hX _
    have hXpos : 0 < X := by linarith
    have hlogbound : Real.log X ≤ X ^ ε / ε := Real.log_le_rpow_div hXpos.le hε
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hpowk : (Real.log X) ^ k ≤ (X ^ ε / ε) ^ k := pow_le_pow_left₀ hlog0 hlogbound k
    have hsplit : (X ^ ε / ε) ^ k = X ^ (ϑ / 2) / ε ^ k := by
      rw [div_pow, ← Real.rpow_natCast (X ^ ε) k, ← Real.rpow_mul hXpos.le ε (k : ℝ), hεk]
    have hKX : 0 ≤ K * X ^ (1 - ϑ) := mul_nonneg hK (Real.rpow_nonneg hXpos.le _)
    have h1 : K * X ^ (1 - ϑ) * (Real.log X) ^ k
        ≤ K * X ^ (1 - ϑ) * (X ^ (ϑ / 2) / ε ^ k) :=
      mul_le_mul_of_nonneg_left (hpowk.trans_eq hsplit) hKX
    have hcomm : X ^ (1 - ϑ) * X ^ (ϑ / 2) = X ^ (1 - ϑ / 2) := by
      rw [← Real.rpow_add hXpos, show 1 - ϑ + ϑ / 2 = 1 - ϑ / 2 by ring]
    have h2 : K * X ^ (1 - ϑ) * (X ^ (ϑ / 2) / ε ^ k)
        = K / ε ^ k * X ^ (1 - ϑ / 2) := by
      rw [← hcomm]
      ring
    exact h1.trans (le_of_eq h2)

/-- `mv_no_siegel150` of `LeanLab.BhowmikGrimmelt2026.Decomp150b`, assembled from the four
leaves: `ϑ₀ = 1 / 5`, the count of LEAF 3 with the factor `exp (-(c / ϑ)) ≤ 1` dropped, and
the absorption of LEAF 4 at `k = 8`. -/
theorem mv_no_siegel150_split (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  obtain ⟨c, C, hc, hbound⟩ := leaf_prop52_part_one h52
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro ϑ hϑ _ hϑ5
  obtain ⟨K, X₁, hK, hcount⟩ :=
    leaf_exceptional_count_from_saving c (max C 0) hc hGallagher
      (fun ϑ hϑ hϑ5 => leaf_interval_max_saving_at_level c C hc hbound ϑ hϑ hϑ5)
  obtain ⟨C', X₂, hC', habs⟩ := leaf_log_loss_absorbed K ϑ 8 hK hϑ
  refine ⟨C', max X₁ X₂, ?_⟩
  intro X hX hX0 hns
  have hX₁ : X₁ ≤ X := le_trans (le_max_left X₁ X₂) hX0
  have hX₂ : X₂ ≤ X := le_trans (le_max_right X₁ X₂) hX0
  have hcount' := hcount X hX hX₁ ϑ hϑ hϑ5 hns
  have hexp : Real.exp (-(c / ϑ)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hpos : 0 < c / ϑ := div_pos hc hϑ
    linarith
  have hstep : K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8
      ≤ K * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by
    have hXnn : (0 : ℝ) ≤ X := by linarith
    have hpow : (0 : ℝ) ≤ X ^ (1 - ϑ) := Real.rpow_nonneg hXnn _
    have hlog : (0 : ℝ) ≤ (Real.log X) ^ 8 := by positivity
    have hfac : (0 : ℝ) ≤ K * X ^ (1 - ϑ) * (Real.log X) ^ 8 :=
      mul_nonneg (mul_nonneg hK hpow) hlog
    have hrw : K * Real.exp (-(c / ϑ)) * X ^ (1 - ϑ) * (Real.log X) ^ 8
        = (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * Real.exp (-(c / ϑ)) := by ring
    rw [hrw]
    calc (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * Real.exp (-(c / ϑ))
        ≤ (K * X ^ (1 - ϑ) * (Real.log X) ^ 8) * 1 :=
          mul_le_mul_of_nonneg_left hexp hfac
      _ = K * X ^ (1 - ϑ) * (Real.log X) ^ 8 := by ring
  exact hcount'.trans (hstep.trans (habs X hX hX₂))

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

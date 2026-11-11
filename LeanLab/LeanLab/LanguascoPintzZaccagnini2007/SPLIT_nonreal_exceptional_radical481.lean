import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `nonreal_exceptional_radical481` of `Decomp481b`.

The target bounds the odd radical of the conductor of every zero of the box `zeroBox481 X H T P`
whose character takes a nonreal value from below by `c * Lg X ^ 2`, at bounded height `T`, in the
strip `1 - H / log X ≤ re < 1`, uniformly in the major arc parameter `P` in its admissible range.

The proof has three steps, and they are separate estimates.

The zero region. The hypothesis `hiw` forbids zeros of a nonreal primitive character in
`re > 1 - 1 / iwaniecDenom481 r t`. A zero of the box sits at `re ≥ 1 - H / log X`, so the two
inequalities can both hold only if `log X / H ≤ iwaniecDenom481 r t`. That is
`leaf_iwaniec_bound481`, and it is all the analytic input used.

The size of the denominator. A zero of the box has conductor `r ≤ P ≤ X ^ (41 / 100)` and
`|im| ≤ T`, so the argument of the denominator is at most a constant times `log X`, and the
denominator itself is at most `C * (log X) ^ (7 / 8)`, with a constant that depends on `T` only.
That is `leaf_denom_upper_bound481`.

The growth comparison. For fixed `C` and `H` the bound `log X / H ≤ C * (log X) ^ (7 / 8)` fails
for every large enough `X`, because the seventh-eighth power of `log X` is smaller than `log X`
by an unbounded factor. That is `leaf_log_growth_excludes481`.

Together the three leaves make a zero of the box with a nonreal character impossible once `X` is
large enough, so the conclusion holds for any positive constant, and in particular for one. The
threshold absorbs the small scales, where the box is not excluded.

`nonreal_exceptional_radical481_split` below is proved from the three leaves with no `sorry`,
does not use `nonreal_exceptional_radical481`, and keeps the statement of the target.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

private theorem lpz481_oddRad_pos (r : ℕ) : 0 < oddRad131 r := by
  rw [oddRad131]
  refine Finset.prod_pos ?_
  intro p hp
  have h2 : 2 < p := (Finset.mem_filter.mp hp).2
  omega

/-- The Iwaniec denominator is positive at conductor at least one. -/
private theorem lpz481_denom_pos {r : ℕ} {t : ℝ} (hr : 1 ≤ r) :
    0 < iwaniecDenom481 r t := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have habs : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hprod : (2 : ℝ) ≤ (r : ℝ) * (|t| + 2) := by
    have h := mul_le_mul hr1 habs (by norm_num : (0 : ℝ) ≤ 2) hr0
    simpa using h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((r : ℝ) * (|t| + 2)) := Real.log_pos (by linarith)
  have hLge : Real.log 2 ≤ Real.log ((r : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by norm_num) hprod
  have h2L : 0 < Real.log (2 * Real.log ((r : ℝ) * (|t| + 2))) := by
    apply Real.log_pos
    linarith
  have hterm : 0 ≤ (Real.log ((r : ℝ) * (|t| + 2)) *
      Real.log (2 * Real.log ((r : ℝ) * (|t| + 2)))) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (le_of_lt (mul_pos hLpos h2L)) _
  have hodd1 : (1 : ℝ) ≤ (oddRad131 r : ℝ) := by
    have h1 : 1 ≤ oddRad131 r := by have := lpz481_oddRad_pos r; omega
    exact_mod_cast h1
  have hodd : 0 < Real.log (2 * (oddRad131 r : ℝ)) := by
    apply Real.log_pos
    linarith
  have hrw : iwaniecDenom481 r t
      = 4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
          (Real.log ((r : ℝ) * (|t| + 2)) *
            Real.log (2 * Real.log ((r : ℝ) * (|t| + 2)))) ^ ((3 : ℝ) / 4)) := rfl
  rw [hrw]
  exact mul_pos (by norm_num) (by linarith)

/-- LEAF. The zero free region in the shape the box uses. From the hypothesis `hiw`, a zero of a
nonreal primitive character that lies in the box, whose real part is at least `1 - H / log X`,
cannot sit inside `re > 1 - 1 / iwaniecDenom481 r t`; hence the two radii are ordered, that is
`log X / H ≤ iwaniecDenom481 r t` for its height `t = im`. -/
theorem leaf_iwaniec_bound481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ X : ℕ, 2 ≤ X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
      (∃ a, (z.2.1 a).im ≠ 0) →
        Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im := by
  intro X hX P z hz him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  have hHpos : 0 < H := by linarith
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hD : 0 < iwaniecDenom481 z.1 z.2.2.im := lpz481_denom_pos h1
  have hnot : ¬ (1 - 1 / iwaniecDenom481 z.1 z.2.2.im < z.2.2.re) := by
    intro hlt
    exact (hiw z.1 h1 z.2.1 h3 him z.2.2 hlt) h4
  have hle : z.2.2.re ≤ 1 - 1 / iwaniecDenom481 z.1 z.2.2.im := not_lt.mp hnot
  have hstep : (1 : ℝ) / iwaniecDenom481 z.1 z.2.2.im ≤ H / Real.log X := by linarith
  have hmul : Real.log X ≤ H * iwaniecDenom481 z.1 z.2.2.im := by
    have h := (div_le_div_iff₀ hD hlogX).mp hstep
    linarith
  rw [div_le_iff₀ hHpos]
  linarith [mul_comm H (iwaniecDenom481 z.1 z.2.2.im)]


/-- LEAF. The size of the denominator. A zero of the box has conductor at most `P` and height at
most `T`, and an admissible `P` is at most `X ^ (41 / 100)`; therefore the logarithm
`log (r (|t| + 2))` in the denominator is at most a constant times `log X`, so the denominator is
at most `C * (log X) ^ (7 / 8)` once `X ≥ 2`, with one constant `C` that depends on `T` only. -/
theorem leaf_denom_upper_bound481 (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∀ P H : ℝ, AdmissibleP131 X P →
      ∀ z ∈ zeroBox481 X H T P,
        iwaniecDenom481 z.1 z.2.2.im ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := by
  sorry

private theorem lpz481_rpow_eighth_pow {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 8)) ^ 8 = x := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ 8 = (x ^ ((1 : ℝ) / 8)) ^ (8 : ℝ) :=
    (Real.rpow_natCast _ 8).symm
  rw [h1, ← Real.rpow_mul hx.le]
  norm_num

/-- Helper: `C * H < L ^ (1/8)` once `(C H) ^ 8 + 1 ≤ L`. -/
private theorem lpz481_ch_lt_eighth {C H L : ℝ} (hCH : 0 < C * H)
    (hL : (C * H) ^ 8 + 1 ≤ L) : C * H < L ^ ((1 : ℝ) / 8) := by
  have hLpos : 0 < L := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  have hDpos : 0 < L ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hLpos _
  have hD8 : (L ^ ((1 : ℝ) / 8)) ^ 8 = L := lpz481_rpow_eighth_pow hLpos
  have hlt : (C * H) ^ 8 < (L ^ ((1 : ℝ) / 8)) ^ 8 := by
    rw [hD8]
    nlinarith [pow_pos hCH 8]
  by_contra hcon
  push_neg at hcon
  have := pow_le_pow_left₀ (le_of_lt hDpos) hcon 8
  linarith

/-- LEAF. The growth comparison. For a fixed positive constant `C` and a fixed `H ≥ 1`, the
seventh-eighth power of `log X` falls below `log X / (C H)` once `X` is large, that is
`C * (log X) ^ (7 / 8) < log X / H` for every `X` at least the threshold. -/
theorem leaf_log_growth_excludes481 (C : ℝ) (hC : 0 < C) (H : ℝ) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := by
  have hHpos : 0 < H := by linarith
  have hCH : 0 < C * H := mul_pos hC hHpos
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((C * H) ^ 8 + 1))
  have hN1 : (0 : ℝ) < (N : ℝ) := by
    have hpos : (0 : ℝ) < Real.exp ((C * H) ^ 8 + 1) := Real.exp_pos _
    linarith
  refine ⟨N, fun X hX => ?_⟩
  have hL : (C * H) ^ 8 + 1 ≤ Real.log X := by
    have h1 : (C * H) ^ 8 + 1 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos ((C * H) ^ 8 + 1)) (le_of_lt hN)
      rwa [Real.log_exp] at h
    have h2 : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hN1 (by exact_mod_cast hX)
    linarith
  have hLpos : 0 < Real.log X := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  set D : ℝ := (Real.log X) ^ ((1 : ℝ) / 8) with hDdef
  have hDpos : 0 < D := Real.rpow_pos_of_pos hLpos _
  have hCHltD : C * H < D := lpz481_ch_lt_eighth hCH hL
  have hsplit : (Real.log X) ^ (7 / 8 : ℝ) = Real.log X / D := by
    have h78 : (7 : ℝ) / 8 = 1 - 1 / 8 := by norm_num
    rw [h78, Real.rpow_sub hLpos, Real.rpow_one, hDdef]
  have hkey : C * (Real.log X / D) = (C * Real.log X) / D := by ring
  rw [hsplit, hkey, div_lt_div_iff₀ hDpos hHpos]
  nlinarith [mul_pos hLpos (sub_pos.mpr hCHltD)]


/-- The split target: the statement of `nonreal_exceptional_radical481`, proved from the three
leaves by the contradictory pair of estimates, with constant one and the threshold of the growth
comparison. -/
theorem nonreal_exceptional_radical481_split (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨C, hC, hden⟩ := leaf_denom_upper_bound481 T hT
  obtain ⟨X₁, hX₁⟩ := leaf_log_growth_excludes481 C hC H hH
  refine ⟨1, one_pos, max X₁ 2, ?_⟩
  intro X hX P hP z hz him
  have h2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hle : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hlow : Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im :=
    leaf_iwaniec_bound481 hiw H T hH hT X h2 P z hz him
  have hup : iwaniecDenom481 z.1 z.2.2.im ≤ C * (Real.log X) ^ (7 / 8 : ℝ) :=
    hden X h2 P H hP z hz
  have hbig : C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := hX₁ X hle
  exfalso
  exact absurd (hlow.trans hup) (not_le.mpr hbig)

end

end LeanLab.LPZ2007

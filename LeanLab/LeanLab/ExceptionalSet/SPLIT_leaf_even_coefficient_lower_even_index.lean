import LeanLab.ExceptionalSet.SPLIT_leaf_even_coefficient_lower

/-!
Split of the even index parity piece `leaf_even_coefficient_lower_even_index` of
`SPLIT_leaf_even_coefficient_lower.lean`.

The piece counts, over the window indices whose floor value `ν_n` is even, those at which the
adjacent coefficient `R₁(ν_n)` has real part below `c₀ F(γ,N) ℰ^(-1/10)`, and asks that there be at
most `B N ℰ^(-1/12)` of them, for a positive `B`, uniformly over the admissible `δ` below a positive
cap and the positive `κ` below a positive cap, for all large `N`.

Two estimates carry the content, and both are strictly weaker than the counting statement.

* `leaf_even_index_real_part_upper`: on those indices the real part of the coefficient is at most
  the window height `F(γ,N)`. This is the pointwise major arc bound; it is what makes every deficit
  `F - re` below nonnegative.
* `leaf_even_index_deficit_sum`: the total deficit `∑ (F - re)` over those indices is at most
  `C N F ℰ^(-1/12)`. No single coefficient is controlled by this; it is a first moment of the
  deficit, and it says only that the coefficients on these indices average to within `O(ℰ^(-1/12))`
  relative distance of the window height.

Everything else is arithmetic and is proved here. Each counted index carries a deficit of more than
`F - λ` with `λ = c₀ F ℰ^(-1/10)`, and `λ ≤ F/2` once `c₀ = 1/2`, because `ℰ ≥ 1`; so each counted
index carries more than `F/2` of deficit, whence `(count) F/2 ≤ C N F ℰ^(-1/12)`, that is
`count ≤ 2C N ℰ^(-1/12)` after cancelling `F/2 > 0`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Adjacent446 (evenAdjacent)

/-- LEAF. Step one of the argument: on the even half of the floor window the real part of the
coefficient at `ν_n` never exceeds the window height `F(γ,N)`. Uniformly over the admissible `δ`
below a positive cap, the positive `κ` below a positive cap, and all `N ≥ 2`. This is the pointwise
major arc bound; it is what makes every deficit in the next leaf nonnegative. -/
theorem leaf_even_index_real_part_upper :
    ∃ δ₀ κ₀ : ℝ, 0 < δ₀ ∧ 0 < κ₀ ∧ ∀ γ : ℝ, 1 < γ → γ < 3 / 2 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ N : ℕ, 2 ≤ N →
        ∀ n : ℕ, n ∈ (window γ N).filter (fun n : ℕ => Even (nu γ n)) →
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re ≤ F γ N := by
  sorry

/-- LEAF. Step two of the argument: the total deficit of the real part from the window height over
the even half of the window is at most `C N F(γ,N) ℰ^(-1/12)`. This is the first moment estimate
with a power saving in `ℰ`: the coefficients on those indices average to within `O(ℰ^(-1/12))`
relative distance of `F(γ,N)`. It is strictly weaker than the counting bound, since it controls no
single coefficient. -/
theorem leaf_even_index_deficit_sum :
    ∃ δ₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < κ₀ ∧ 0 < C ∧ ∀ γ : ℝ, 1 < γ → γ < 3 / 2 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ N : ℕ, 2 ≤ N →
        ∑ n ∈ (window γ N).filter (fun n : ℕ => Even (nu γ n)),
            (F γ N - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re)
          ≤ C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- The counting step, proved: for a finite set `s` of indices inside `W`, a coefficient family `z`
whose real parts are at most `H` on `W`, and a level `lam ≤ H/2`, the indices of `s` whose real
part is below `lam` are at most `H/2`-th of the total deficit `∑ (H - re)`. -/
private theorem card_bad_mul_le_deficit {W s : Finset ℕ} {z : ℕ → ℂ} {H lam : ℝ}
    (hsub : s ⊆ W) (hdef : ∀ n ∈ W, (z n).re ≤ H) (hbad : ∀ n ∈ s, (z n).re < lam)
    (hlam : lam ≤ H / 2) :
    (s.card : ℝ) * (H / 2) ≤ ∑ n ∈ W, (H - (z n).re) := by
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hstep1 : (s.card : ℝ) * (H / 2) ≤ (s.card : ℝ) * (H - lam) :=
    mul_le_mul_of_nonneg_left (by linarith) hcard
  have hstep2 : (s.card : ℝ) * (H - lam) = ∑ _n ∈ s, (H - lam) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstep3 : ∑ _n ∈ s, (H - lam) ≤ ∑ n ∈ s, (H - (z n).re) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have h := hbad n hn
    linarith
  have hstep4 : ∑ n ∈ s, (H - (z n).re) ≤ ∑ n ∈ W, (H - (z n).re) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hnW _
    have h := hdef n hnW
    linarith
  linarith

/-- `ℰ = exp(κ (log N)^(3-2γ)) ≥ 1` for `N ≥ 2`, `κ > 0` and `γ < 3/2`, because the exponent is a
product of nonnegative factors. -/
private theorem one_le_calE (γ κ : ℝ) (N : ℕ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hN : 2 ≤ N) :
    1 ≤ calE γ κ N := by
  have htwo : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg htwo
  have hγ : (0 : ℝ) < 3 - 2 * γ := by linarith
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hlog _
  rw [calE]
  exact Real.one_le_exp (mul_nonneg hκ.le hpow)

/-- The level `c₀ F ℰ^(-1/10)` with `c₀ = 1/2` is at most `F/2`, since `ℰ ≥ 1` makes
`ℰ^(-1/10) ≤ 1`. -/
private theorem half_level_le_half (γ κ : ℝ) (N : ℕ) (h2 : γ < 3 / 2) (hκ : 0 < κ) (hN : 2 ≤ N) :
    (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ F γ N / 2 := by
  have hE1 : 1 ≤ calE γ κ N := one_le_calE γ κ N h2 hκ hN
  have hrpow : calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hE1 (by norm_num)
  have hF : 0 ≤ F γ N := (Real.exp_pos _).le
  calc (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
      = (1 / 2 * F γ N) * calE γ κ N ^ (-(1 / 10 : ℝ)) := by ring
    _ ≤ (1 / 2 * F γ N) * 1 := mul_le_mul_of_nonneg_left hrpow (by linarith)
    _ = F γ N / 2 := by ring

/-- Assembly. The even index coefficient count over the floor window follows from the two estimates:
the counted set is a subset of the even half of the window, every deficit there is nonnegative and
every counted index carries a deficit of more than `F/2`, so the count times `F/2` is at most the
total deficit, which is at most `C N F ℰ^(-1/12)`; cancelling `F/2 > 0` gives `2C N ℰ^(-1/12)`. -/
theorem leaf_even_coefficient_lower_even_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δu, κu, hu0, hu1, Hu⟩ := leaf_even_index_real_part_upper
  obtain ⟨δs, κs, C, hs0, hs1, hC, Hs⟩ := leaf_even_index_deficit_sum
  refine ⟨min δu δs, lt_min hu0 hs0, fun δ hδ hδlt => ?_⟩
  refine ⟨min κu κs, lt_min hu1 hs1, fun κ hκ hκlt => ?_⟩
  refine ⟨1 / 2, 2 * C, by norm_num, by linarith, 2, fun N hN => ?_⟩
  have hδu : δ < δu := hδlt.trans_le (min_le_left _ _)
  have hδs : δ < δs := hδlt.trans_le (min_le_right _ _)
  have hκu : κ ≤ κu := hκlt.trans (min_le_left _ _)
  have hκs : κ ≤ κs := hκlt.trans (min_le_right _ _)
  have hupper := Hu γ h1 h2 δ hδ hδu κ hκ hκu N hN
  have hsum := Hs γ h1 h2 δ hδ hδs κ hκ hκs N hN
  have hFpos : 0 < F γ N := Real.exp_pos _
  have hlam : (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ F γ N / 2 :=
    half_level_le_half γ κ N h2 hκ hN
  have key : (((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
        (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ)) * (F γ N / 2) ≤
      C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    refine (card_bad_mul_le_deficit
      (W := (window γ N).filter (fun n : ℕ => Even (nu γ n)))
      (s := ((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
          (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (z := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n))
      (H := F γ N) (lam := (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
      ?_ ?_ ?_ hlam).trans hsum
    · intro n hn
      exact (Finset.mem_filter.mp hn).1
    · intro n hn
      exact hupper n hn
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
  have hhalf : 0 < F γ N / 2 := by linarith
  have hrhs : C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) =
      ((2 * C) * (N : ℝ) * calE γ κ N ^ (-(1 / 12 : ℝ))) * (F γ N / 2) := by ring
  rw [hrhs] at key
  exact le_of_mul_le_mul_right key hhalf

end LeanLab.ExceptionalSet.Decomp446a

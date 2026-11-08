import LeanLab.ExceptionalSet.SPLIT_leaf_even_coefficient_lower

/-!
Split of the odd-index parity piece `leaf_even_coefficient_lower_odd_index` of
`SPLIT_leaf_even_coefficient_lower.lean`.

The piece counts, over the window indices with odd floor value `ν_n`, the adjacent integer `ν_n + 1`
whose coefficient real part falls below `c₀ F(γ,N) ℰ^(-1/10)`, and asks for at most
`B N ℰ^(-1/12)` such indices, for a positive `B` and all large `N`.

Two analytic inputs carry the content.

* `leaf_odd_index_real_part_upper`: the coefficient real part never exceeds `F` on those indices.
* `leaf_odd_index_deficit_sum`: the total deficit `∑ (F - re)` over those indices is at most
  `C N F ℰ^(-1/12)`.

Everything else is arithmetic, done here. Each deficit is nonnegative by the first input, so the sum
over the counted set is at most the sum over the whole odd sub-window; each counted index contributes
more than `F - λ` with `λ = c₀ F ℰ^(-1/10)`, and `λ ≤ F/2` once `c₀ ≤ 1/2`, which costs nothing
because `ℰ ≥ 1`: its exponent `κ (log N)^(3-2γ)` is nonnegative for `N ≥ 2`, `κ > 0` and `γ < 3/2`.
Hence `(count) · F/2 ≤ C N F ℰ^(-1/12)`, that is `count ≤ 2C N ℰ^(-1/12)`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Adjacent446 (evenAdjacent)

/-- LEAF. Step one of the argument: on the odd half of the floor window the real part of the
adjacent coefficient at `ν_n + 1` never exceeds the window height `F(γ,N)`. Uniformly over the
admissible `δ` below a positive cap and the positive `κ` below a positive cap, and over all
`N ≥ 2`. This is the pointwise major arc bound; it is what makes every deficit below nonnegative. -/
theorem leaf_odd_index_real_part_upper :
    ∃ δ₀ κ₀ : ℝ, 0 < δ₀ ∧ 0 < κ₀ ∧ ∀ γ : ℝ, 1 < γ → γ < 3 / 2 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ N : ℕ, 2 ≤ N →
        ∀ n : ℕ, n ∈ (window γ N).filter (fun n : ℕ => ¬ Even (nu γ n)) →
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re ≤ F γ N := by
  sorry

/-- LEAF. Step two of the argument: the total deficit of the real part from `F(γ,N)` over the odd
half of the window is at most `C N F(γ,N) ℰ^(-1/12)`. This is the first moment estimate with a
power saving in `ℰ`; it says the coefficients on those indices average to within
`O(ℰ^(-1/12))` relative distance of `F(γ,N)`, and it is strictly weaker than the counting bound
because no single coefficient is controlled. -/
theorem leaf_odd_index_deficit_sum :
    ∃ δ₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < κ₀ ∧ 0 < C ∧ ∀ γ : ℝ, 1 < γ → γ < 3 / 2 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ N : ℕ, 2 ≤ N →
        ∑ n ∈ (window γ N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            (F γ N - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re)
          ≤ C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- The counting step, proved: for a finite set `s` of indices inside `W`, a coefficient family `z`
whose real parts are at most `F₀` on `W`, and a level `lam ≤ F₀/2`, the indices of `s` whose real
part is below `lam` are at most `F₀/2`-th of the total deficit `∑ (F₀ - re)`. -/
private theorem card_bad_mul_le_deficit {W s : Finset ℕ} {z : ℕ → ℂ} {F₀ lam : ℝ}
    (hsub : s ⊆ W) (hdef : ∀ n ∈ W, (z n).re ≤ F₀) (hbad : ∀ n ∈ s, (z n).re < lam)
    (hlam : lam ≤ F₀ / 2) (_hF : 0 ≤ F₀) :
    (s.card : ℝ) * (F₀ / 2) ≤ ∑ n ∈ W, (F₀ - (z n).re) := by
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hstep1 : (s.card : ℝ) * (F₀ / 2) ≤ (s.card : ℝ) * (F₀ - lam) := by
    refine mul_le_mul_of_nonneg_left ?_ hcard
    linarith
  have hstep2 : (s.card : ℝ) * (F₀ - lam) = ∑ n ∈ s, (F₀ - lam) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstep3 : ∑ n ∈ s, (F₀ - lam) ≤ ∑ n ∈ s, (F₀ - (z n).re) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have h := hbad n hn
    linarith
  have hstep4 : ∑ n ∈ s, (F₀ - (z n).re) ≤ ∑ n ∈ W, (F₀ - (z n).re) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hnW _
    have h := hdef n hnW
    linarith
  linarith

/-- The level `c₀ F ℰ^(-1/10)` with `c₀ = 1/2` is at most `F/2`: `ℰ ≥ 1` because its exponent
`κ (log N)^(3-2γ)` is nonnegative. -/
private theorem half_mul_rpow_le_half (γ κ : ℝ) (N : ℕ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hκ : 0 < κ) (hN : 2 ≤ N) :
    (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ F γ N / 2 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hγ : (0 : ℝ) < 3 - 2 * γ := by linarith
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hlog _
  have harg : 0 ≤ κ * Real.log (N : ℝ) ^ (3 - 2 * γ) := mul_nonneg hκ.le hpow
  have hE1 : 1 ≤ calE γ κ N := by
    rw [calE]
    exact Real.one_le_exp harg
  have hrpow : calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hE1 (by norm_num)
  have hFpos : 0 < F γ N := Real.exp_pos _
  calc (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
      = (1 / 2 * F γ N) * calE γ κ N ^ (-(1 / 10 : ℝ)) := by ring
    _ ≤ (1 / 2 * F γ N) * 1 :=
        mul_le_mul_of_nonneg_left hrpow (by linarith)
    _ = F γ N / 2 := by ring

/-- Assembly. The odd-index coefficient count over the floor window follows from the two analytic
inputs: the counted set is a subset of the odd half of the window, every deficit is nonnegative and
every counted index carries a deficit of more than `F/2`, so the count times `F/2` is at most the
total deficit, which is at most `C N F ℰ^(-1/12)`; cancelling `F/2 > 0` gives `2C N ℰ^(-1/12)`. -/
theorem leaf_even_coefficient_lower_odd_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δu, κu, hu0, hu1, Hu⟩ := leaf_odd_index_real_part_upper
  obtain ⟨δs, κs, C, hs0, hs1, hC, Hs⟩ := leaf_odd_index_deficit_sum
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
  have hF : 0 ≤ F γ N := hFpos.le
  have hlam : (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ F γ N / 2 :=
    half_mul_rpow_le_half γ κ N h1 h2 hκ hN
  have key : ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) * (F γ N / 2) ≤
      C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    refine (card_bad_mul_le_deficit
      (W := (window γ N).filter (fun n : ℕ => ¬ Even (nu γ n)))
      (s := ((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
          (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (z := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1))
      (F₀ := F γ N) (lam := (1 / 2 : ℝ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
      (Finset.filter_subset _ _) hupper ?_ hlam hF).trans hsum
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hhalf : 0 < F γ N / 2 := by linarith
  have hrhs : C * N * F γ N * calE γ κ N ^ (-(1 / 12 : ℝ)) =
      ((2 * C) * (N : ℝ) * calE γ κ N ^ (-(1 / 12 : ℝ))) * (F γ N / 2) := by ring
  rw [hrhs] at key
  exact le_of_mul_le_mul_right key hhalf

end LeanLab.ExceptionalSet.Decomp446a

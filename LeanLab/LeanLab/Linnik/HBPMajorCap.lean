import LeanLab.ChenExplicit.TwinCNumeric

/-!
# Heath-Brown and Puchta 2002: the major arc constant cannot save a power of 2

T2 FRONTIER map, unit U-1265, PC run 20261020T1703Z-9112. AI wrote the Lean code. P0012.

HBP Section 6 takes `K` powers of 2 when `13.968 λ^{K-2} < C`, with `C = 2.7895` the Section 4
major arc constant from the divisors `d ≤ 5` of the singular series, `λ = 0.863665`
unconditionally, `λ = 0.722428` under GRH; `Numerics.lean` proves `K = 13` and `K = 7`.
Section 4 drops every `d > 5`. Keeping all of them, the major arc factor is twice the mean of
`∏_{p ∣ n, p > 2} (p - 1)/(p - 2)` over `n = N - Σ 2^{νᵢ}`, which in the limit of equidistributed `n`
is `2 ∏_{p > 2} (1 + 1/(p(p - 2))) = 2 / C₀`, `C₀ = twinC ≈ 0.66016`, so about `3.0296`.
Monte Carlo, Linnik/numerics/hbp_cap_U1265.py: `3.017` to `3.040` at `K = 12, 13` for five `N`.

This file proves the arithmetic that turns that model into a map:
* `cap_le`: `2 / C₀ ≤ 3.0770`, from `twinC_ge_065`;
* `k12_needs`: `K = 12` at `λ = 0.863665` needs `C > 3.2254`, above the cap;
* `grh_k6_needs`: `K = 6` at `λ = 0.722428` needs `C > 3.8046`, above the cap;
* `lam_needed_k12`: with `C ≤ 2/C₀`, `K = 12` needs `λ < 0.8597`, against HBP's `0.863665`;
* `vacuity_k13`: the criterion does hold at `K = 13` with `C = 2.7895`.

Plain math: no choice of truncation in Section 4 can lower `K` in either case; any gain in HBP's
framework must come from `λ` or from the minor arc constant `13.968`, as Pintz and Ruzsa did.
The cap `2 / C₀` is a MODEL, the limit of the mean singular series, not a proved upper bound at
finite `K`; only the arithmetic below is proved. KNOWN-LIKELY; the later literature, Pintz-Ruzsa
K = 8 and Johnston-Trudgian K = 7 unconditionally, moved by sharper λ and other arcs.
Binary Goldbach is OPEN; `K = 0` is binary Goldbach.
-/

namespace LeanLab.Linnik.HBPMajorCap

open LeanLab.ChenExplicit

/-- HBP's Section 6 criterion with major arc constant `C`. -/
def Crit (C lam : ℝ) (K : ℕ) : Prop := 13968 / 1000 * lam ^ (K - 2) < C

theorem cap_le : 2 / twinC ≤ (30770 / 10000 : ℝ) := by
  have h := twinC_ge_065
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem k12_needs {C : ℝ} (h : Crit C (863665 / 1000000) 12) : (32254 / 10000 : ℝ) < C := by
  unfold Crit at h
  norm_num at h ⊢
  linarith

theorem k12_fails_at_cap : ¬ Crit (2 / twinC) (863665 / 1000000) 12 := by
  intro h
  have := k12_needs h
  have := cap_le
  linarith

theorem grh_k6_needs {C : ℝ} (h : Crit C (722428 / 1000000) 6) : (38046 / 10000 : ℝ) < C := by
  unfold Crit at h
  norm_num at h ⊢
  linarith

theorem grh_k6_fails_at_cap : ¬ Crit (2 / twinC) (722428 / 1000000) 6 := by
  intro h
  have := grh_k6_needs h
  have := cap_le
  linarith

/-- With the full major arc constant at most `2 / C₀`, `K = 12` needs `λ < 0.8597`. -/
theorem lam_needed_k12 {lam : ℝ} (h0 : 0 ≤ lam) (h : Crit (2 / twinC) lam 12) :
    lam < 8597 / 10000 := by
  by_contra hge
  push_neg at hge
  unfold Crit at h
  norm_num at h
  have hp : (8597 / 10000 : ℝ) ^ 10 ≤ lam ^ 10 := pow_le_pow_left₀ (by norm_num) hge 10
  have hc := cap_le
  norm_num at hp
  nlinarith

theorem vacuity_k13 : Crit (27895 / 10000) (863665 / 1000000) 13 := by
  unfold Crit; norm_num

end LeanLab.Linnik.HBPMajorCap

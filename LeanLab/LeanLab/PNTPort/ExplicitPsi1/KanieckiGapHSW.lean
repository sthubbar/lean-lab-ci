import LeanLab.KanieckiGap.Lemma6Gap
import LeanLab.PNTPort.ExplicitPsi1.Schoenfeld61Large

/-!
# Kaniecki Lemma 6 without the Schoenfeld 1976 citation

I-5270, unit U-6708, CLOUD 20261020T1816Z-cloud48, T2, P0022. AI wrote the Lean code. Known
mathematics.

`gap_lt_hsw`, `lemma6_hsw`, `gap_lt'_hsw`, `lemma6'_hsw` are `gap_lt`, `lemma6` of Lemma6.lean
and `gap_lt'`, `lemma6'` of Lemma6Gap.lean with the cited `hS : LeanLab.DERZ1997.Schoenfeld61`
replaced by RH and the Hasanalizade-Shen-Wong counts `HSWN70`, `HSWHead14` and `Ordinates14`
for the true ordinates `gZ`; other hypotheses and conclusions are identical, the proofs are the
originals with `hS` taken from `schoenfeld61_large`, Schoenfeld61Large.lean. That theorem holds
only for `x ≥ 3.6 · 10^13`, and this is enough: the originals apply `hS` only in the analytic
case, at `p` and `nextPrime p - 1 ≥ p`, where `p > 7.263 · 10^13 / 2` for `gap_lt`, from
`nextPrime p ≤ 2p`, and `p > 4 · 10^18 - 1476` for `gap_lt'`.

CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14`, plus `YoungPotler` for `lemma6_hsw`
and `GapBound1476` for `lemma6'_hsw`. Binary Goldbach is OPEN.
-/

namespace LeanLab.KanieckiGap
open Real Chebyshev
open LeanLab.GoldbachGaps.Sumset (GapBound1476)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ schoenfeld61_large)
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.ChirreHagen2025.SmoothT2 (Ordinates14)

/-- `gap_lt` of Lemma6.lean with `Schoenfeld61` replaced by RH and the HSW counts. -/
theorem gap_lt_hsw (hRH : RiemannHypothesis) (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ)
    (h14z : Ordinates14 gZ) (hY : YoungPotler) {p x : ℕ}
    (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * π) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  rcases Nat.lt_or_ge (7263 * 10 ^ 10) (nextPrime p) with hbig | hsmall
  · -- the analytic case: p ≥ 3.6 · 10^13
    have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    have hp13 : 23 * 10 ^ 8 ≤ p := by omega
    have hp36 : (36 * 10 ^ 12 : ℝ) ≤ p := by exact_mod_cast (by omega : 36 * 10 ^ 12 ≤ p)
    have hS := schoenfeld61_large hRH hNz hHz h14z
    have hpR : (23 * 10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp13
    set q := nextPrime p with hq
    have hθ := theta_before_next p
    rw [← hq] at hθ
    have hcast : ((q - 1 : ℕ) : ℝ) = (p : ℝ) + (gapAt p : ℝ) - 1 := by
      unfold gapAt; rw [← hq]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hg1 : (1 : ℝ) ≤ gapAt p := by unfold gapAt; exact_mod_cast (by omega : 1 ≤ q - p)
    have hS1 := hS ((q - 1 : ℕ) : ℝ) (by rw [hcast]; linarith)
    have hS2 := hS (p : ℝ) hp36
    have hgp : (gapAt p : ℝ) ≤ p := by unfold gapAt; exact_mod_cast (by omega : q - p ≤ p)
    have hkey : (gapAt p : ℝ) - 1 < B p + B (p + gapAt p - 1) := by
      rw [hθ, hcast] at hS1
      have a1 := (abs_lt.mp hS1).1
      have a2 := (abs_lt.mp hS2).2
      unfold B; linarith
    refine (core hpR hg1 hgp hkey).trans_le ?_
    have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx
    have hLp := log_ge_21_5 hpR
    gcongr
  · -- the table case
    have h778 := hY p hp hsmall
    have : (gapAt p : ℝ) ≤ 778 := by exact_mod_cast h778
    have hsx : (47958 : ℝ) ≤ √(x : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hsx (pow_le_pow_left₀ (by norm_num) hLx 2) (by norm_num)
      (Real.sqrt_nonneg _)]

/-- **Kaniecki Lemma 6**, `lemma6` with `Schoenfeld61` replaced by RH and the HSW counts,
CONDITIONAL ON those and `YoungPotler`. -/
theorem lemma6_hsw (hRH : RiemannHypothesis) (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ)
    (h14z : Ordinates14 gZ) (hY : YoungPotler) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [if_neg hx7, hpeq]
  rw [hlam]
  refine (gap_lt_hsw hRH hNz hHz h14z hY hpmem.2 (by omega) hx).trans_le ?_
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  gcongr

/-- `gap_lt'` of Lemma6Gap.lean with `Schoenfeld61` replaced by RH and the HSW counts. -/
theorem gap_lt'_hsw (hRH : RiemannHypothesis) (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ)
    (h14z : Ordinates14 gZ) (hG : GapBound1476) {p x : ℕ}
    (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * π) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  rcases Nat.lt_or_ge (4 * 10 ^ 18) (p + 1476) with hbig | hsmall
  · have hp13 : 23 * 10 ^ 8 ≤ p := by omega
    have hp36 : (36 * 10 ^ 12 : ℝ) ≤ p := by exact_mod_cast (by omega : 36 * 10 ^ 12 ≤ p)
    have hS := schoenfeld61_large hRH hNz hHz h14z
    have hpR : (23 * 10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp13
    have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    set q := nextPrime p with hq
    have hθ := theta_before_next p
    rw [← hq] at hθ
    have hcast : ((q - 1 : ℕ) : ℝ) = (p : ℝ) + (gapAt p : ℝ) - 1 := by
      unfold gapAt; rw [← hq]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hg1 : (1 : ℝ) ≤ gapAt p := by unfold gapAt; exact_mod_cast (by omega : 1 ≤ q - p)
    have hS1 := hS ((q - 1 : ℕ) : ℝ) (by rw [hcast]; linarith)
    have hS2 := hS (p : ℝ) hp36
    have hgp : (gapAt p : ℝ) ≤ p := by unfold gapAt; exact_mod_cast (by omega : q - p ≤ p)
    have hkey : (gapAt p : ℝ) - 1 < B p + B (p + gapAt p - 1) := by
      rw [hθ, hcast] at hS1
      have a1 := (abs_lt.mp hS1).1
      have a2 := (abs_lt.mp hS2).2
      unfold B; linarith
    refine (core hpR hg1 hgp hkey).trans_le ?_
    have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx
    have hLp := log_ge_21_5 hpR
    gcongr
  · have h1476 := gapAt_le_1476 hG hp hsmall
    have : (gapAt p : ℝ) ≤ 1476 := by exact_mod_cast h1476
    have hsx : (47958 : ℝ) ≤ √(x : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    have k1 : (47958 : ℝ) * 21.5 ^ 2 ≤ √(x : ℝ) * Real.log x ^ 2 :=
      mul_le_mul hsx (pow_le_pow_left₀ (by norm_num) hLx 2) (by norm_num) (Real.sqrt_nonneg _)
    rw [lt_div_iff₀ (by positivity)]
    clear hsmall h1476 hq1 hq2 hx hxR hpx
    have k2 : (gapAt p : ℝ) * (4 * π) ≤ 1476 * (4 * π) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    have k3 : (1476 : ℝ) * (4 * π) < 47958 * 21.5 ^ 2 := by nlinarith
    linarith

/-- **Kaniecki Lemma 6**, `lemma6'` with `Schoenfeld61` replaced by RH and the HSW counts,
CONDITIONAL ON those and the 1476 table. -/
theorem lemma6'_hsw (hRH : RiemannHypothesis) (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ)
    (h14z : Ordinates14 gZ) (hG : GapBound1476) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [if_neg hx7, hpeq]
  rw [hlam]
  refine (gap_lt'_hsw hRH hNz hHz h14z hG hpmem.2 (by omega) hx).trans_le ?_
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  gcongr

end LeanLab.KanieckiGap

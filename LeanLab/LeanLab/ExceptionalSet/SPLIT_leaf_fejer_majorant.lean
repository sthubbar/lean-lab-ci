/-
Split of `leaf_fejer_majorant` in `ExceptionalSet/SPLIT_lemma4.lean` into smaller leaves.

The statement being split is the Fejér-kernel majorant for the indicator of an interval of
fractional parts: the number of `N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` differs from
`(z₁ - z₂)N/2` by at most `4N/(H+1)` plus the first `H` exponential sums at the frequencies `hα`,
each weighted by `4N/(h+1)`.

`leaf_fejer_majorant_split` below proves that statement from the leaves, with no `sorry` of its own
and without using the target theorem.  The leaves are, in the order the assembly uses them:

1. `leaf_vaaler_trig_majorant` - the per-point step, and the only step with analytic content: for
   every `H` and every interval `[z₂,z₁) ⊆ [0,1]` there is a trigonometric polynomial of degree `H`
   whose coefficients are bounded by `2/(h+1)` and which is within `2/(H+1)` of the indicator at
   every point, in both directions.
2. `leaf_dirichlet_lower` - a lower bound for the exponential sums over the window: among the first
   `N - N/2` frequencies one of the sums has modulus at least 1, so the weighted sum of the sums is
   not smaller than `1/(4N-2)`.  This is what absorbs the additive `1/2` of the window shift.

The assembly then does three things, all elementary: it sums the per-point bound over the window
and bounds the polynomial part by the exponential sums through the triangle inequality, it shifts
the comparison from `N/2` to the exact window length `N - N/2` (off by at most `1/2`), and it
carries out the resulting bookkeeping of constants.

The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma4

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. The per-point majorant: for every `H` and every interval `[z₂,z₁) ⊆ [0,1]` there is a
trigonometric polynomial `θ ↦ ∑ h ∈ Icc 1 H, (c h * e(hθ)).re` of degree `H` whose coefficients
satisfy `‖c h‖ ≤ 2/(h+1)` and which differs from the indicator of the interval by at most
`2/(H+1)` at every real point, in absolute value.  Nothing here mentions `N`, `α`, `γ` or a count:
it is one inequality, about one point. -/
theorem leaf_vaaler_trig_majorant (H : ℕ) (z₁ z₂ : ℝ) (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁)
    (hz₁ : z₁ ≤ 1) :
    ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
        - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1) := by
  sorry

/-- LEAF. The lower bound for the sums over the window: for `N ≥ 1` and every frequency cutoff
`H ≥ N - N/2` the weighted sum of the moduli of the exponential sums, with weights `1/(h+1)`, is at
least `1/(4N-2)`.  Its proof is the second moment `∑_{h ≤ N-N/2} ‖S h‖² ≥ N - N/2` (the kernel of
two distinct points is at least `-1`), so one frequency `h ≤ N - N/2 ≤ N` has `‖S h‖ ≥ 1`. -/
theorem leaf_dirichlet_lower (α γ : ℝ) (N H : ℕ) (hN : 1 ≤ N) (hH : N - N / 2 ≤ H) :
    1 ≤ (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  sorry

/-! ### Bookkeeping, proved -/

/-- The window `N/2 < n ≤ N` has `N - N/2` elements, which is `N/2` up to `1/2`. -/
private lemma card_window_shift (N : ℕ) :
    |((Finset.Ioc (N / 2) N).card : ℝ) - (N : ℝ) / 2| ≤ 1 / 2 := by
  rw [Nat.card_Ioc]
  have hdm : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
  have hsub : N - N / 2 = N / 2 + N % 2 := by omega
  have hN : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
    have h : ((2 * (N / 2) + N % 2 : ℕ) : ℝ) = (N : ℝ) := by rw [hdm]
    push_cast at h ⊢
    linarith
  have hmod0 : ((N % 2 : ℕ) : ℝ) = 0 ∨ ((N % 2 : ℕ) : ℝ) = 1 := by
    have h2 : N % 2 = 0 ∨ N % 2 = 1 := by omega
    rcases h2 with h | h <;> rw [h] <;> norm_num
  rw [hsub]
  push_cast
  rw [abs_le]
  rcases hmod0 with h | h
  · rw [h] at hN
    norm_num at hN
    constructor <;> linarith
  · rw [h] at hN
    norm_num at hN
    constructor <;> linarith

/-- The polynomial part of the majorant, summed over a finite set of points, is bounded by the
exponential sums: `∑_n ∑_h (c h e(h x n)).re = ∑_h (c h ∑_n e(h x n)).re`, and each term of the
last sum is at most `‖c h‖ ‖∑_n e(h x n)‖`. -/
private lemma abs_sum_re_le (s : Finset ℕ) (H : ℕ) (c : ℕ → ℂ) (e : ℕ → ℕ → ℝ)
    (hbnd : ∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) :
    |∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re| ≤
      2 * ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ s, eC (e h n)‖ / ((h : ℝ) + 1) := by
  classical
  have hswap : ∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re
      = ∑ h ∈ Finset.Icc 1 H, (c h * ∑ n ∈ s, eC (e h n)).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    calc ∑ n ∈ s, (c h * eC (e h n)).re
        = ∑ n ∈ s, Complex.reCLM (c h * eC (e h n)) := by
            exact Finset.sum_congr rfl fun n _ => (Complex.reCLM_apply _).symm
      _ = Complex.reCLM (∑ n ∈ s, c h * eC (e h n)) :=
          (map_sum Complex.reCLM (fun n => c h * eC (e h n)) s).symm
      _ = Complex.reCLM (c h * ∑ n ∈ s, eC (e h n)) := by rw [Finset.mul_sum]
      _ = (c h * ∑ n ∈ s, eC (e h n)).re := Complex.reCLM_apply _
  have hterm : ∀ h ∈ Finset.Icc 1 H, |(c h * ∑ n ∈ s, eC (e h n)).re|
      ≤ 2 / ((h : ℝ) + 1) * ‖∑ n ∈ s, eC (e h n)‖ := by
    intro h hh
    calc |(c h * ∑ n ∈ s, eC (e h n)).re|
        ≤ ‖c h * ∑ n ∈ s, eC (e h n)‖ := Complex.abs_re_le_norm _
      _ = ‖c h‖ * ‖∑ n ∈ s, eC (e h n)‖ := norm_mul _ _
      _ ≤ 2 / ((h : ℝ) + 1) * ‖∑ n ∈ s, eC (e h n)‖ :=
          mul_le_mul_of_nonneg_right (hbnd h hh) (norm_nonneg _)
  rw [hswap]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [Finset.mul_sum]
  exact le_of_eq (Finset.sum_congr rfl fun h _ => by ring)

/-- Summing a per-point bound over the window: if at every point the indicator of the interval
differs from `b` plus the polynomial by at most `2/(H+1)`, then the count over the window differs
from `b` times its length by at most `2/(H+1)` times its length, plus the polynomial's total. -/
private lemma count_deviation (s : Finset ℕ) (H : ℕ) (b z₁ z₂ : ℝ) (x : ℕ → ℝ)
    (e : ℕ → ℕ → ℝ) (c : ℕ → ℂ) (he : ∀ h n, e h n = h * x n)
    (hpt : ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - b
      - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1)) :
    |((s.filter (fun n : ℕ => z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁)).card : ℝ)
        - b * (s.card : ℝ) - ∑ n ∈ s, ∑ h ∈ Finset.Icc 1 H, (c h * eC (e h n)).re|
      ≤ 2 / ((H : ℝ) + 1) * (s.card : ℝ) := by
  classical
  simp only [he]
  have hcard : ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁)).card : ℝ)
      = ∑ n ∈ s, (if z₂ ≤ Int.fract (x n) ∧ Int.fract (x n) < z₁ then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hbc : b * (s.card : ℝ) = ∑ n ∈ s, b := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcard, hbc]
  simp only [← Finset.sum_sub_distrib]
  have hsum : (∑ n ∈ s, 2 / ((H : ℝ) + 1)) = 2 / ((H : ℝ) + 1) * (s.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hsum]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => hpt (x n))

/-- The bookkeeping of the constants: the deviation of the count from `b N/2` is the deviation from
`b M`, the polynomial total, and the window shift, and these three fit inside `4N/(H+1) + 4N S`
once the shift is at most `1/2` and `1 ≤ 2N/(H+1) + (4N-2) S`. -/
private lemma arith_core (A b T S M N H' : ℝ) (hH' : 1 ≤ H') (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hMN : M ≤ N) (h1 : |A - b * M - T| ≤ 2 / H' * M) (h2 : |T| ≤ 2 * S)
    (h3 : |M - N / 2| ≤ 1 / 2) (h5 : 1 ≤ 2 * N / H' + (4 * N - 2) * S) :
    |A - b * N / 2| ≤ 4 * N / H' + 4 * N * S := by
  have hH'pos : (0 : ℝ) < H' := by linarith
  have hshift : b * M - b * N / 2 = b * (M - N / 2) := by ring
  have habs : |b * M - b * N / 2| = b * |M - N / 2| := by
    rw [hshift, abs_mul, abs_of_nonneg hb0]
  have hsplit : A - b * N / 2 = (A - b * M - T) + T + (b * M - b * N / 2) := by ring
  have h1a : |A - b * M - T| ≤ 2 * M / H' := by
    have he : 2 / H' * M = 2 * M / H' := by ring
    linarith
  have hMshift : 2 * M / H' ≤ 2 * N / H' := by
    refine div_le_div_of_nonneg_right ?_ hH'pos.le
    linarith
  have hb2 : b * (1 / 2) ≤ 1 / 2 := by linarith
  have hfour : 4 * N / H' = 2 * (2 * N / H') := by ring
  have h5a : (1 : ℝ) ≤ 2 * N / H' + (4 * N * S - 2 * S) := by
    have hprod : (4 * N - 2) * S = 4 * N * S - 2 * S := by ring
    rw [hprod] at h5
    linarith
  calc |A - b * N / 2|
      = |(A - b * M - T) + T + (b * M - b * N / 2)| := by rw [hsplit]
    _ ≤ |A - b * M - T| + |T| + |b * M - b * N / 2| := by
        have hA1 := abs_add_le ((A - b * M - T) + T) (b * M - b * N / 2)
        have hA2 := abs_add_le (A - b * M - T) T
        linarith
    _ = |A - b * M - T| + |T| + b * |M - N / 2| := by rw [habs]
    _ ≤ 2 * M / H' + 2 * S + b * (1 / 2) := by
        have hb' : b * |M - N / 2| ≤ b * (1 / 2) := mul_le_mul_of_nonneg_left h3 hb0
        linarith
    _ ≤ 2 * N / H' + 2 * S + 1 / 2 := by linarith
    _ ≤ 2 * N / H' + 2 * S + 1 := by linarith
    _ ≤ 4 * N / H' + 4 * N * S := by linarith

/-! ### Assembly -/

theorem leaf_fejer_majorant_split (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) - (z₁ - z₂) * N / 2| ≤ 4 * N / ((H : ℝ) + 1) + 4 * N * ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp
  have hb0 : (0 : ℝ) ≤ z₁ - z₂ := by linarith
  have hb1 : z₁ - z₂ ≤ 1 := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMN : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    have h : (Finset.Ioc (N / 2) N).card ≤ N := by
      rw [Nat.card_Ioc]
      omega
    exact_mod_cast h
  obtain ⟨c, hcb, hcp⟩ := leaf_vaaler_trig_majorant H z₁ z₂ hz₂ hz1 hz₁
  have hT := abs_sum_re_le (Finset.Ioc (N / 2) N) H c
    (fun h n => h * α * F γ n) hcb
  have hA := count_deviation (Finset.Ioc (N / 2) N) H (z₁ - z₂) z₁ z₂
    (fun n => α * F γ n) (fun h n => h * α * F γ n) c
    (fun h n => by ring) hcp
  have hwin := card_window_shift N
  have habs : (1 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1)
      + (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
    by_cases hc : (H : ℝ) + 1 ≤ 2 * (N : ℝ)
    · have hq : (1 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < (H : ℝ) + 1)]
        linarith
      have hsum0 : (0 : ℝ) ≤ ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
        apply Finset.sum_nonneg
        intro h _
        positivity
      have hcoef0 : (0 : ℝ) ≤ 4 * (N : ℝ) - 2 := by linarith
      have : (0 : ℝ) ≤ (4 * (N : ℝ) - 2) * ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) :=
        mul_nonneg hcoef0 hsum0
      linarith
    · have hbig : 2 * (N : ℝ) < (H : ℝ) + 1 := by linarith
      have hHge : N - N / 2 ≤ H := by
        have h2 : ((2 * N : ℕ) : ℝ) < ((H + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
        have h3 : 2 * N < H + 1 := by exact_mod_cast h2
        omega
      have hd := leaf_dirichlet_lower α γ N H hN hHge
      have hq : (0 : ℝ) ≤ 2 * (N : ℝ) / ((H : ℝ) + 1) := by positivity
      linarith
  exact arith_core _ (z₁ - z₂)
    (∑ n ∈ Finset.Ioc (N / 2) N, ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * α * F γ n)).re)
    (∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1))
    ((Finset.Ioc (N / 2) N).card : ℝ) (N : ℝ) ((H : ℝ) + 1)
    (by linarith) hb0 hb1 hMN hA hT hwin habs

end LeanLab.ExceptionalSet.U1539

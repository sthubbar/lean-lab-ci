import Mathlib
import LeanLab.Linnik.Decomp1532b
import LeanLab.Linnik.U7204Display4

/-!
# Gallagher 1975 p. 138: the nonzero frequency remainder over the major arcs

Unit U-1532, FREE-nv-minimax task28, 2026-11-01.

This file splits the sealed leaf `Decomp1532c.major_arc_remainder_bound` into the part that is
elementary and the part that is an external analytic input.

* `card_pairs`: the number of exponent tuple pairs is `L^(2k)`, p. 134 display (3).
* `major_arc_frequency_remainder`: LEAF. Gallagher 1975 p. 127 Theorem 3, with Lemmas 8, 9 and 10
  of pp. 136-137 and the exceptional conductor bound of p. 127. The major arc Fourier coefficient
  of `‖Sg N α‖^2` at a nonzero frequency `n` with `|n| ≤ 2 * 2^L` equals `Jn N n * 𝔖(n)` up to
  `(N / log^2 N) (C exp(-c/θ) + δ)`, uniformly in `n`, for all large `N`. This is the external
  input of Gallagher 1970, Invent. Math. 11 pp. 329-339, and Montgomery and Vaughan 1975,
  Acta Arith. 27 pp. 353-370.
* `remainder_of_frequency_remainder`: the aggregation over the `L^(2k)` tuple differences, that is
  the step from Theorem 3, p. 127, to the error term before display (5) on p. 138.

AI wrote the Lean code. Known mathematics. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.Linnik.Decomp1532cFrequency

open Finset MeasureTheory Filter
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg)

/-- Gallagher 1975 p.134 display (3). The number of exponent tuple pairs is `L^(2k)`. -/
theorem card_pairs (k L : ℕ) :
    (LeanLab.Linnik.Decomp1532a.pairs k L).card = L ^ (2 * k) := by
  calc (LeanLab.Linnik.Decomp1532a.pairs k L).card =
      (Fintype.card (Fin k → Fin L)) * (Fintype.card (Fin k → Fin L)) := by
        simp [LeanLab.Linnik.Decomp1532a.pairs, Fintype.card_prod]
    _ = L ^ k * L ^ k := by simp [Fintype.card_fun, Fintype.card_fin]
    _ = L ^ (2 * k) := by rw [← pow_add]; congr 1; omega

/-- LEAF. Gallagher 1975 p.127 Theorem 3, with Lemmas 8, 9 and 10 of pp.136 to 137 and the
exceptional conductor bound of p.127. For each fixed `k ≥ 2` and each `0 < θ ≤ θ₀`, and for all
large `N`, the major arc Fourier coefficient of `‖Sg N α‖^2` at every nonzero frequency `n` with
`|n| ≤ 2 * 2^L` equals `Jn N n * 𝔖(n)` up to `(N / log^2 N) (C exp(-c/θ) + δ)`, uniformly in `n`.
Here `L = Nat.log 2 N` and `𝔖` is the singular series of p. 130. This is the external analytic
input of Gallagher 1970, Inventiones 11 pp.329 to 339, and Montgomery and Vaughan 1975, Acta
Arithmetica 27 pp.353 to 370. -/
theorem major_arc_frequency_remainder : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N),
          LeanLab.Linnik.Decomp1532a.dif x ≠ 0 →
          |(∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e
                  ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
            LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
              (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re|
            ≤ (N : ℝ) / Real.log N ^ 2 * (C * Real.exp (-c / θ) + δ) := by
  sorry

/-- Gallagher 1975 p.138. The error before display (5) follows from Theorem 3, p.127, by the
triangle inequality over the `L^(2k)` tuple differences. -/
theorem remainder_of_frequency_remainder
    (h : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N),
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 →
            |(∫ α in majorArcs N ((N : ℝ) ^ θ),
                ‖Sg N α‖ ^ 2 *
                  (LeanLab.PNTPort.LargeSieve.e
                    ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re|
              ≤ (N : ℝ) / Real.log N ^ 2 * (C * Real.exp (-c / θ) + δ)) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
        ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
          |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
              LeanLab.Linnik.Decomp1532a.dif x ≠ 0, ∫ α in majorArcs N ((N : ℝ) ^ θ),
                ‖Sg N α‖ ^ 2 *
                  (LeanLab.PNTPort.LargeSieve.e
                    ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
            (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
              LeanLab.Linnik.Decomp1532a.dif x ≠ 0,
                LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                  (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
            (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
              (C * Real.exp (-c / θ) + δ) := by
  classical
  obtain ⟨c, C, θ₀, hc, hθ₀, hmain⟩ := h
  refine ⟨c, |C|, θ₀, hc, hθ₀, ?_⟩
  intro θ hθ hθmax k hk δ hδ
  obtain ⟨N₀, hN₀⟩ := hmain θ hθ hθmax k hk δ hδ
  refine ⟨max 8 N₀, fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let L : ℕ := Nat.log 2 N
  let s : Finset (LeanLab.Linnik.Decomp1532a.pairs k L) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0)
  let A : ℝ := |C| * Real.exp (-c / θ) + δ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA0 : C * Real.exp (-c / θ) + δ ≤ A := by
    dsimp [A]
    have he : 0 < Real.exp (-c / θ) := Real.exp_pos _
    have hc' := mul_le_mul_of_nonneg_left (le_abs_self C) he.le
    linarith
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
  have htri : |(∑ x in s, ∫ α in majorArcs N ((N : ℝ) ^ θ),
                  ‖Sg N α‖ ^ 2 *
                    (LeanLab.PNTPort.LargeSieve.e
                      ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
                (∑ x in s, LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                    (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)|
      ≤ ∑ x in s, |(∫ α in majorArcs N ((N : ℝ) ^ θ),
                  ‖Sg N α‖ ^ 2 *
                    (LeanLab.PNTPort.LargeSieve.e
                      ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
                LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                    (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum : ∑ x in s, |(∫ α in majorArcs N ((N : ℝ) ^ θ),
                  ‖Sg N α‖ ^ 2 *
                    (LeanLab.PNTPort.LargeSieve.e
                      ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
                LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                    (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)|
      ≤ ∑ x in s, (N : ℝ) / Real.log N ^ 2 * A := by
    apply Finset.sum_le_sum
    intro x hx
    have hx' := hN₀ N hN0 x (Finset.mem_filter.mp hx).2
    have h2 : (N : ℝ) / Real.log N ^ 2 * (C * Real.exp (-c / θ) + δ)
        ≤ (N : ℝ) / Real.log N ^ 2 * A := by
      have := mul_le_mul_of_nonneg_left hA0 hscale
      linarith
    linarith
  have hcard : s.card ≤ L ^ (2 * k) := by
    have hsub : s ⊆ Finset.univ := by
      simp [s]
    calc s.card ≤ (LeanLab.Linnik.Decomp1532a.pairs k L).card := Finset.card_le_card hsub
      _ = L ^ (2 * k) := card_pairs k L
  have hsum2 : ∑ x in s, (N : ℝ) / Real.log N ^ 2 * A
      ≤ (N : ℝ) / Real.log N ^ 2 * A * (L : ℝ) ^ (2 * k) := by
    calc (∑ x in s, (N : ℝ) / Real.log N ^ 2 * A)
        = s.card * ((N : ℝ) / Real.log N ^ 2 * A) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hfinal : (N : ℝ) / Real.log N ^ 2 * A * (L : ℝ) ^ (2 * k)
      ≤ (2 * N * (L : ℝ) ^ (2 * k) / Real.log N ^ 2) * A := by
    have hP : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
    have hQ : 0 ≤ (L : ℝ) ^ (2 * k) := by positivity
    have hstep := mul_le_mul_of_nonneg_left
      (show (N : ℝ) / Real.log N ^ 2 ≤ 2 * ((N : ℝ) / Real.log N ^ 2) by linarith)
      (mul_nonneg hA hQ)
    calc (N : ℝ) / Real.log N ^ 2 * A * (L : ℝ) ^ (2 * k)
        ≤ 2 * ((N : ℝ) / Real.log N ^ 2) * A * (L : ℝ) ^ (2 * k) := by linarith
      _ = (2 * N * (L : ℝ) ^ (2 * k) / Real.log N ^ 2) * A := by ring
  calc |(∑ x in s, ∫ α in majorArcs N ((N : ℝ) ^ θ),
            ‖Sg N α‖ ^ 2 *
              (LeanLab.PNTPort.LargeSieve.e
                ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x in s, LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
              (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)|
      ≤ ∑ x in s, |(∫ α in majorArcs N ((N : ℝ) ^ θ),
            ‖Sg N α‖ ^ 2 *
              (LeanLab.PNTPort.LargeSieve.e
                ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
              (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| := htri
    _ ≤ ∑ x in s, (N : ℝ) / Real.log N ^ 2 * A := hsum
    _ ≤ (N : ℝ) / Real.log N ^ 2 * A * (L : ℝ) ^ (2 * k) := hsum2
    _ ≤ (2 * N * (L : ℝ) ^ (2 * k) / Real.log N ^ 2) * A := hfinal
    _ = (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) *
          (|C| * Real.exp (-c / θ) + δ) := by dsimp [L, A]; ring

end LeanLab.Linnik.Decomp1532cFrequency

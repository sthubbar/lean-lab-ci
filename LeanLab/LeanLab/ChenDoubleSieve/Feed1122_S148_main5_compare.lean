import LeanLab.ChenDoubleSieve.Feed1122_S148_PiCompare
import LeanLab.ChenDoubleSieve.Decomp348c

/-!
Wu 2004 page 39, equation 10.5: the replacement of pi of N by N over log N in the
Upsilon 5 main term, the statement of the LEAF `main5_compare` in
Feed1122_Decomp348c_main5_lower.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The prime pair sum converges to the F5 double integral by the proved
`lowerSum5_tendsto` of Decomp348c, so it is bounded on large even N, and the
generic comparison of Feed1122_S148_PiCompare applies.
This file imports Decomp348c, which imports the leaf file, so the proof lives here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S148
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- A sequence converging along a filter is eventually bounded in absolute value. -/
theorem eventually_abs_le_of_tendsto {l : Filter ℕ} {S : ℕ → ℝ} {L : ℝ}
    (hS : Tendsto S l (𝓝 L)) : ∀ᶠ N in l, |S N| ≤ |L| + 1 := by
  filter_upwards [hS (Metric.ball_mem_nhds L one_pos)] with N hN
  rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hN
  have := abs_sub_abs_le_abs_sub (S N) L
  linarith

/-- Wu 2004 page 39, the statement of the LEAF `main5_compare`: replacing pi of N
by N over log N in the Upsilon 5 main term costs at most eta Theta N. -/
theorem main5_compare_proved (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |(N : ℝ) / log N * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))
          - (Nat.primeCounting N : ℝ) * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))| ≤ η * Θ N := by
  intro η hη B hB
  exact compare_of_bounded (lowerSum5 f B) _
    (eventually_abs_le_of_tendsto (lowerSum5_tendsto F f h B hB)) η hη

end LeanLab.ChenDoubleSieve.Feed1122.S148

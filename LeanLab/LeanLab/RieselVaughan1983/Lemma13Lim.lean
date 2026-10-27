/-
P0032 Riesel-Vaughan 1983, Lemma 13 for the value of the series (8.10) itself, not its partial sums.
Unit U-1250, PC run 20261020T1503Z-30533. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

`Phi` is the limit value of (8.16); `lemma13_limit`: Re Φ_k ≥ ½ C (16/15 S_k² − 2S_k(N_k − S_k log 5)
/(15(−2.9024 + log N_k))), page 64, CONDITIONAL ON `Eq818`, (8.18).
-/
import LeanLab.RieselVaughan1983.Lemma13Red

open Finset Real ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Lemma13Lim

open LeanLab.RieselVaughan1983.Delta LeanLab.RieselVaughan1983.Eq816
  LeanLab.RieselVaughan1983.Lemma13Red LeanLab.RieselVaughan1983.Xi

/-- Φ_k, the value of (8.10) by (8.16). -/
def Phi (y : ℝ) (k : ℕ) (w : ℝ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊w⌋₊, ((((1 / 2) * LeanLab.RieselVaughan1983.Ctw * ((μ q : ℤ) : ℝ) *
    LeanLab.RieselVaughan1983.Lemma13Max.fq q : ℝ)) : ℂ) * Pq y k q

/-- **Lemma 13**, page 64, for Φ_k itself, CONDITIONAL ON (8.18). -/
theorem lemma13_limit (h818 : Eq818) {x : ℝ} (hx : 0 < x) (hL : 350 < Real.log (x / 202))
    {k : ℕ} (hk : k ∈ Icc 1 200) :
    1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-(29024 / 10000) + Real.log (Nk (x / 202) k)))) ≤
      (Phi (x / 202) k (wk (x / 202) k)).re := by
  have hw0 : 0 ≤ wk (x / 202) k := by unfold wk; positivity
  have hre := (Complex.continuous_re.tendsto _).comp (eq816 (x / 202) k hw0)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨D0, hD0⟩ := lemma13_of_818 h818 x hx hL k hk (ε / 2) (by linarith)
  have hge : _ - ε / 2 ≤ (Phi (x / 202) k (wk (x / 202) k)).re :=
    ge_of_tendsto hre (eventually_atTop.mpr ⟨D0, fun D hD => hD0 D hD⟩)
  linarith

end LeanLab.RieselVaughan1983.Lemma13Lim

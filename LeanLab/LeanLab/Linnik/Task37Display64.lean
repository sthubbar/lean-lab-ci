/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 21, Lemma 7.1 display 64.
The reflection bound follows unconditionally from Parseval and the PNT first moments.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37FirstMoments

namespace LeanLab.Linnik.Task37Display64
open Set Real Finset Filter Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U1434Lemma21
open LeanLab.Linnik.Task37Lemma71
open LeanLab.Linnik.Task37Lemma71Integral
open LeanLab.Linnik.Task37FirstMoments

/-- The little o lower bound in display 64, with every positive error δ. -/
def Lemma71 (κ a b c τ : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop, Even N →
    (2 * (N : ℝ) * (Lfun N : ℝ) ^ 6 * (1 - c + τ * (1 - a - b)) ^ 2 -
        Joint a b c τ (N1f κ N) N (Lfun N)) / (2 * τ * Lfun N) ≤
      r5pp (N1f κ N) N (Lfun N) + δ * (N * (Lfun N : ℝ) ^ 5)

lemma normalization_arith {n l τ δ A m J r : ℝ} (hn : 0 < n) (hl : 0 < l) (hτ : 0 < τ)
    (hsq : (A ^ 2 - τ * δ) * (n * l ^ 3) ^ 2 ≤ m ^ 2)
    (hfin : ((2 / n) * m ^ 2 - J) / (2 * τ * l) ≤ r) :
    (2 * n * l ^ 6 * A ^ 2 - J) / (2 * τ * l) ≤ r + δ * (n * l ^ 5) := by
  have hden : 0 < 2 * τ * l := by positivity
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 / n)
  have he : (2 / n) * ((A ^ 2 - τ * δ) * (n * l ^ 3) ^ 2) =
      2 * n * l ^ 6 * A ^ 2 - δ * (n * l ^ 5) * (2 * τ * l) := by
    field_simp
  rw [he] at hm
  have hf := (div_le_iff₀ hden).mp hfin
  rw [div_le_iff₀ hden]
  nlinarith

/-- Lemma 7.1 with the exact denominator and exponent of display 64. -/
theorem display64 {κ a b c τ : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (hc : 0 ≤ c) (hc1 : c < 1) (hτ : 0 < τ) : Lemma71 κ a b c τ := by
  intro δ hδ
  let A : ℝ := 1 - c + τ * (1 - a - b)
  have hA : 0 < A := by
    have hp : 0 < τ * (1 - a - b) := mul_pos hτ (by linarith)
    dsimp [A]
    linarith
  have hlim : Tendsto (combined a b c τ κ) atTop (𝓝 A) := combined_tendsto hκ a b c τ
  have he1 : ∀ᶠ N : ℕ in atTop, 0 < combined a b c τ κ N :=
    hlim.eventually (lt_mem_nhds hA)
  have he2 : ∀ᶠ N : ℕ in atTop, A ^ 2 - τ * δ < (combined a b c τ κ N) ^ 2 :=
    (hlim.pow 2).eventually (lt_mem_nhds (by nlinarith [mul_pos hτ hδ]))
  filter_upwards [he1, he2, eventually_Lfun_ge_one, eventually_ge_atTop 1]
    with N hz hsq0 hL hN hEven
  have hNp : 0 < N := by omega
  have hLp : 0 < Lfun N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hLr : (0 : ℝ) < Lfun N := by exact_mod_cast hLp
  let g : ℕ → ℝ := fun n => max (f2 c (N1f κ N) N (Lfun N) n) 0
  let h : ℕ → ℝ := fun n => max (ff a b (N1f κ N) N (Lfun N) n) 0
  let m : ℝ := (Lfun N : ℝ) * ∑ n ∈ UN N, g n + τ * ∑ n ∈ UN N, h n
  let M : ℝ := (N : ℝ) * (Lfun N : ℝ) ^ 3
  have hM : 0 < M := by dsimp [M]; positivity
  have hg : ∑ n ∈ UN N, f2 c (N1f κ N) N (Lfun N) n ≤ ∑ n ∈ UN N, g n :=
    sum_le_sum fun n _ => le_max_left _ _
  have hh : ∑ n ∈ UN N, ff a b (N1f κ N) N (Lfun N) n ≤ ∑ n ∈ UN N, h n :=
    sum_le_sum fun n _ => le_max_left _ _
  have hm : combined a b c τ κ N * M ≤ m := by
    rw [combined_eq a b c τ κ hNp hLp, div_mul_cancel₀ _ hM.ne']
    exact add_le_add (mul_le_mul_of_nonneg_left hg hLr.le) (mul_le_mul_of_nonneg_left hh hτ.le)
  have hs1 := pow_le_pow_left₀ (mul_nonneg hz.le hM.le) hm 2
  have hs2 := mul_le_mul_of_nonneg_right hsq0.le (sq_nonneg M)
  have hsq : (A ^ 2 - τ * δ) * ((N : ℝ) * (Lfun N : ℝ) ^ 3) ^ 2 ≤ m ^ 2 := by
    change (A ^ 2 - τ * δ) * M ^ 2 ≤ m ^ 2
    nlinarith
  have hfin := lemma71_integral_finite ha hb hc hτ (N1f κ N) N (Lfun N) hEven hNp hLp
  change ((2 / N) * m ^ 2 - Joint a b c τ (N1f κ N) N (Lfun N)) /
    (2 * τ * Lfun N) ≤ r5pp (N1f κ N) N (Lfun N) at hfin
  exact normalization_arith hNr hLr hτ hsq hfin

/-- The coefficients used in the paper's five power application satisfy the hypotheses. -/
theorem display64_instance : Lemma71 (1 / 2) (1 / 4) (1 / 16) (1 / 8) 2 :=
  display64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end LeanLab.Linnik.Task37Display64

#print axioms LeanLab.Linnik.Task37Display64.normalization_arith
#print axioms LeanLab.Linnik.Task37Display64.display64
#print axioms LeanLab.Linnik.Task37Display64.display64_instance

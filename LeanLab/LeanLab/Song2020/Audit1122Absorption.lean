/-
AI wrote the Lean code. CLAUDE S60 ROUTE BURST burst-20261122, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, Section 4, printed page 9, the line
"By Lemma 3.3, Lemma 3.4 and Lemma 3.5, we have".

QUESTION Q139c made precise. Feed the displayed bounds into the displayed Cauchy step:
the Lemma 4 bound C₄ n^(21/31 - 14γ/31 + ε) y^(23/31) for max |f - g| and the Lemma 5 bounds
C₅ n^(1-γ) y and C₅ y for the two mean squares. The resulting error term is NOT
O(y² / log⁴ n) on the printed window n^((52-45γ)/8) < y ≤ n/3, for any ε > 0 and any
positive constants: at y = 2 n^((52-45γ)/8) it equals a constant times n^ε y².
So the printed deduction needs a window margin; Repair591Margin proves the margin version.
This is a statement about the printed proof step, not a claim that Theorem 1 is false.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Audit139

namespace LeanLab.Song2020.Audit1122Absorption

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- PROVED. Page 9, exponent bookkeeping at y = 2 n^θ, θ = (52 - 45γ)/8: the Lemma 4 scale
times the Lemma 5 scale of f equals 2^(-8/31) n^ε y². -/
theorem scale_identity (γ ε : ℝ) (n : ℝ) (hn : 0 < n) :
    n ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * n ^ songExponent γ) ^ ((23 : ℝ) / 31) *
        (n ^ (1 - γ) * (2 * n ^ songExponent γ)) =
      (2 : ℝ) ^ (-(8 : ℝ) / 31) * n ^ ε * (2 * n ^ songExponent γ) ^ 2 := by
  have hP : 0 < n ^ songExponent γ := Real.rpow_pos_of_pos hn _
  have h2P : 0 < 2 * n ^ songExponent γ := by positivity
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow h2P,
    Real.log_rpow hn, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos, Real.log_pow,
    Real.log_mul two_ne_zero hP.ne']
  simp only [Real.log_rpow hn]
  unfold songExponent
  push_cast
  ring

/-- PROVED, FALSE result about the printed step. For 44/45 < γ < 1, every ε > 0 and all
positive constants C₄, C₅, the product of the displayed Lemma 4 bound and the displayed
Lemma 5 bounds, as in the Cauchy step on page 9, is not O(y² / log⁴ n) on the printed window. -/
theorem printed_absorption_false (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1)
    (ε : ℝ) (hε : 0 < ε) (C₄ C₅ : ℝ) (hC₄ : 0 < C₄) (hC₅ : 0 < C₅) :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        2 * (C₄ * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31))) *
            (C₅ * ((n : ℝ) ^ (1 - γ) * y) + C₅ * y) ≤
          C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  rintro ⟨C, N₀, h⟩
  have hθ1 : songExponent γ < 1 := (songExponent_mem hγ hγ1).2
  have hpowlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - songExponent γ))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - songExponent γ)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpowlim.eventually_gt_atTop 6)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * C₄ * C₅ * (2 : ℝ) ^ (-(8 : ℝ) / 31) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨n, hnN, hlt⟩ :=
    Audit139.positive_power_not_log_saving139 ε hε (C / K) (max N₀ (max N2 2))
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (n : ℝ) ^ songExponent γ := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hn0 _
  have hPn : P * (n : ℝ) ^ (1 - songExponent γ) = n := by
    rw [hP, ← Real.rpow_add hn0]
    simp
  have hwin : 2 * P ≤ (n : ℝ) / 3 := by
    have hbig := hN2 n (by omega)
    nlinarith [mul_lt_mul_of_pos_left hbig hP0]
  have hy := h n (by omega) (2 * P) (by rw [← hP]; linarith) hwin
  have hid := scale_identity γ ε n hn0
  rw [← hP] at hid
  have hL : 0 < Real.log (n : ℝ) ^ 4 := pow_pos (Real.log_pos hn1) 4
  have hX : 0 ≤ (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31) := by
    positivity
  have hdrop : 2 * (C₄ * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31))) *
        (C₅ * ((n : ℝ) ^ (1 - γ) * (2 * P))) ≤
      2 * (C₄ * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31))) *
        (C₅ * ((n : ℝ) ^ (1 - γ) * (2 * P)) + C₅ * (2 * P)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have heq : 2 * (C₄ * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31))) *
        (C₅ * ((n : ℝ) ^ (1 - γ) * (2 * P))) = K * (n : ℝ) ^ ε * (2 * P) ^ 2 := by
    rw [hK, show 2 * (C₄ * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31))) *
        (C₅ * ((n : ℝ) ^ (1 - γ) * (2 * P))) = 2 * C₄ * C₅ *
        ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * (2 * P) ^ ((23 : ℝ) / 31) *
          ((n : ℝ) ^ (1 - γ) * (2 * P))) by ring, hid]
    ring
  have hmain : K * (n : ℝ) ^ ε * (2 * P) ^ 2 ≤
      (C / Real.log (n : ℝ) ^ 4) * (2 * P) ^ 2 := by
    have := (heq ▸ hdrop).trans hy
    calc K * (n : ℝ) ^ ε * (2 * P) ^ 2 ≤ C * ((2 * P) ^ 2 / Real.log (n : ℝ) ^ 4) := this
      _ = _ := by ring
  have h4 : K * (n : ℝ) ^ ε ≤ C / Real.log (n : ℝ) ^ 4 :=
    le_of_mul_le_mul_right hmain (by positivity)
  have h5 : (n : ℝ) ^ ε ≤ C / K / Real.log (n : ℝ) ^ 4 := by
    rw [show C / K / Real.log (n : ℝ) ^ 4 = (C / Real.log (n : ℝ) ^ 4) / K by ring,
      le_div_iff₀ hK0]
    linarith
  linarith

end

end LeanLab.Song2020.Audit1122Absorption

#print axioms LeanLab.Song2020.Audit1122Absorption.scale_identity
#print axioms LeanLab.Song2020.Audit1122Absorption.printed_absorption_false

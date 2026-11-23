/-
P0088, Kumchev and Liu 2007, page 10, Lemma 3.3: the Perron error for one pair m, k, the
first analytic step toward the LEAF `Lemma33Perron1122.lemma33_overlap`. Uses the PROVED
truncated Perron kernel of DERZ1997 Perron136. Standard lemma, not new.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DERZ1997.Perron136
import LeanLab.KumchevLiu2007.Lemma33PerronGap1122

namespace LeanLab.KumchevLiu2007.Lemma33PerronErr1122

open LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Perron136
open LeanLab.KumchevLiu2007.Lemma33Perron1122 LeanLab.KumchevLiu2007.Lemma33PerronGap1122

/-- Perron error for one pair, PROVED: for M ≤ m and 1 ≤ k < 2K, the truncated Perron
integral at y = k/(m+1/2) differs from the indicator of m < k by at most
(2K/M)^c 4K/(pi T). -/
theorem perron_err (m k M K : ℕ) (c T : ℝ) (hM : 1 ≤ M) (hm : M ≤ m) (hk1 : 1 ≤ k)
    (hk : k < 2 * K) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI ((k : ℝ) / ((m : ℝ) + 1 / 2)) c T - (if m < k then 1 else 0)‖ ≤
      (2 * K / M : ℝ) ^ c * (4 * K) / (Real.pi * T) := by
  have hy := y_pos m k hk1
  have hg := log_gap m k K hk1 hk
  have hK : (0 : ℝ) < 4 * K := by
    have : 0 < K := by omega
    have : (0 : ℝ) < K := by exact_mod_cast this
    linarith
  have hy1 : (k : ℝ) / ((m : ℝ) + 1 / 2) ≠ 1 := by
    intro h
    rw [h, Real.log_one, abs_zero] at hg
    have : (0 : ℝ) < 1 / (4 * K) := by positivity
    linarith
  have h := perron_remainder_bound hy hy1 hc hT
  have hind : (if 1 < (k : ℝ) / ((m : ℝ) + 1 / 2) then (1 : ℂ) else 0) =
      (if m < k then 1 else 0) := by
    by_cases hmk : m < k
    · rw [if_pos ((one_lt_y_iff m k).mpr hmk), if_pos hmk]
    · rw [if_neg (fun h' => hmk ((one_lt_y_iff m k).mp h')), if_neg hmk]
  rw [hind] at h
  exact h.trans (rem_le m k M K c T hM hm hk1 hk hc.le hT)

end LeanLab.KumchevLiu2007.Lemma33PerronErr1122

#print axioms LeanLab.KumchevLiu2007.Lemma33PerronErr1122.perron_err

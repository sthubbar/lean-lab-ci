/-
P0088, Kumchev and Liu 2007, page 10, Lemma 3.3: real-variable pieces of the Perron error
sum for the LEAF `Lemma33Perron1122.lemma33_overlap`. With y = k/(m+1/2): y > 0, y > 1 iff
m < k, and the remainder bound of DERZ1997 Perron136 is at most (2K/M)^c 4K/(pi T).
Standard lemma, not new.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Lemma33Perron1122

namespace LeanLab.KumchevLiu2007.Lemma33PerronGap1122

open LeanLab.KumchevLiu2007.Lemma33Perron1122

/-- y = k/(m+1/2) is positive, PROVED. -/
theorem y_pos (m k : ℕ) (hk : 1 ≤ k) : 0 < (k : ℝ) / ((m : ℝ) + 1 / 2) := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  positivity

/-- y > 1 exactly when m < k, PROVED. -/
theorem one_lt_y_iff (m k : ℕ) : 1 < (k : ℝ) / ((m : ℝ) + 1 / 2) ↔ m < k := by
  have h0 : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  rw [one_lt_div h0]
  constructor
  · intro h
    have : (m : ℝ) < k := by linarith
    exact_mod_cast this
  · intro h
    have : (m : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith


/-- The Perron remainder y^c/(pi T |log y|) is at most (2K/M)^c 4K/(pi T) for M ≤ m and
1 ≤ k < 2K, PROVED, using log_gap. -/
theorem rem_le (m k M K : ℕ) (c T : ℝ) (hM : 1 ≤ M) (hm : M ≤ m) (hk1 : 1 ≤ k)
    (hk : k < 2 * K) (hc : 0 ≤ c) (hT : 0 < T) :
    ((k : ℝ) / ((m : ℝ) + 1 / 2)) ^ c / (Real.pi * T * |Real.log ((k : ℝ) / ((m : ℝ) + 1 / 2))|)
      ≤ (2 * K / M : ℝ) ^ c * (4 * K) / (Real.pi * T) := by
  have hy := y_pos m k hk1
  have hg := log_gap m k K hk1 hk
  have hK : (0 : ℝ) < K := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmR : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (k : ℝ) + 1 ≤ 2 * K := by
    have : k + 1 ≤ 2 * K := hk
    exact_mod_cast this
  have hyle : (k : ℝ) / ((m : ℝ) + 1 / 2) ≤ 2 * K / M := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpow : ((k : ℝ) / ((m : ℝ) + 1 / 2)) ^ c ≤ (2 * K / M : ℝ) ^ c :=
    Real.rpow_le_rpow hy.le hyle hc
  have hL : 0 < |Real.log ((k : ℝ) / ((m : ℝ) + 1 / 2))| :=
    lt_of_lt_of_le (by positivity) hg
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp0 : 0 ≤ ((k : ℝ) / ((m : ℝ) + 1 / 2)) ^ c := Real.rpow_nonneg hy.le c
  have h4 : 1 ≤ 4 * (K : ℝ) * |Real.log ((k : ℝ) / ((m : ℝ) + 1 / 2))| := by
    rw [div_le_iff₀ (by positivity)] at hg
    linarith
  have hPT : 0 < Real.pi * T := by positivity
  calc ((k : ℝ) / ((m : ℝ) + 1 / 2)) ^ c * (Real.pi * T)
      ≤ (2 * K / M : ℝ) ^ c * (Real.pi * T) := mul_le_mul_of_nonneg_right hpow hPT.le
    _ ≤ (2 * K / M : ℝ) ^ c * (Real.pi * T) *
          (4 * (K : ℝ) * |Real.log ((k : ℝ) / ((m : ℝ) + 1 / 2))|) :=
        le_mul_of_one_le_right (by positivity) h4
    _ = (2 * K / M : ℝ) ^ c * (4 * K) *
          (Real.pi * T * |Real.log ((k : ℝ) / ((m : ℝ) + 1 / 2))|) := by ring

end LeanLab.KumchevLiu2007.Lemma33PerronGap1122

#print axioms LeanLab.KumchevLiu2007.Lemma33PerronGap1122.y_pos
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronGap1122.one_lt_y_iff
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronGap1122.rem_le

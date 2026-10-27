/-
AI-written Lean code, Claude, 2026-10-20, PC run 20261020T2203Z-17931, unit U-1291, track T2.
P0009 BJS 2022, the u₀ = 10⁸ line at log log X₂ = 32.16, tied together in one place.

The cloud's chen_3216, AssemblyT3216.lean of U-6718, runs Section 9 with Lemma 18's
ε = εU = 1.91·10⁻⁷ of Section9U8.lean, the value Lemma 18 gives at u₀ = 10⁸, and at α = 10⁻⁵, but
nothing in that file imports Lemma18U8 or states the u₀ range conditions of Theorems 44, 50, 51; they
were checked numerically only. This file adds, PROVED:

* `epsU_eq`: Section9U8.εU is exactly the 191/10⁹ of Lemma18U8.lemma18_1e8.
* `u0cond_44_50_1e8`: the u₀ condition of Theorems 44 and 50 in logs, p. 42 and p. 51,
  `α L − 10 log lx₁ − 2.5 log L ≥ u₀ (1 + 9·10⁻⁷ / log u₀)` at u₀ = 10⁸, α = 10⁻⁵, for every
  `L = log N ≥ 9·10¹³` and `1 ≤ lx₁ ≤ L`; model ratio of the two sides 9.27 at log log N = 32.16.
* `u0cond_51_1e8`: Theorem 51's condition `10 log 3 + α L − 10 log L ≥ u₀ (1 + 9·10⁻⁷ / log u₀)`, p. 56.
* `ranges_1e8`: (140) `8α + 160 log L / L < 1`, `α < 1/24`, `α < 1/6`, `L/4 ≤ (1/2 − α) L − 20 log L`,
  Lemma 18's `log z = L/8 > 4000`, and Theorem 6's `εU ≤ 1/74`.
* `chen_3216_u0`: under Lemma 17 (48), (49) and the corrected Theorems 44, 50, 51 at t = 32.16,
  BJS Theorem 3 holds at exp(exp 32.16), Lemma 18 (53) holds at u₀ = 10⁸ with the very ε that
  Section9U8 uses, and the range conditions above hold for every N > exp(exp 32.16).
  CONDITIONAL ON Lemma 17 (48), (49) and Thm44At, Thm50At, Thm51At, as named hypotheses.

HONEST NOTE, per the U-1285 VERIFY: BJS prove Theorems 44, 50, 51 only at u₀ = 10⁹, ε = 1.452·10⁻⁷.
Their use here at u₀ = 10⁸, ε = 1.91·10⁻⁷ is a lab re-derivation, BJS's proofs rerun at a new u₀,
checked by reading only. So this line rests on more than the 32.716 line, which used the printed u₀.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT3216
import LeanLab.ChenExplicit.Lemma18U8

open Real

noncomputable section

namespace LeanLab.ChenExplicit.At3216U0

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.Lemma18General

/-- Section9U8's ε is the ε of Lemma18U8. -/
theorem epsU_eq : Section9U8.εU = 191 / 10 ^ 9 := rfl

/-- `log 10⁸ ≥ 1`. -/
lemma log1e8_ge1 : (1 : ℝ) ≤ log 100000000 := by
  have := Lemma18U8.log1e8_ge; linarith

/-- `log L ≤ 33 + L / 10¹⁴` for `L > 0`. -/
lemma log_le_lin_gen (L c : ℝ) (hL : 0 < L) (hc0 : 0 < c) : log L ≤ log c + L / c - 1 := by
  have h1 : log (L / c) ≤ L / c - 1 := log_le_sub_one_of_pos (div_pos hL hc0)
  have h2 : log (L / c) = log L - log c := log_div hL.ne' hc0.ne'
  rw [h2] at h1; linarith

lemma log1e14_le : log ((10 : ℝ) ^ 14) ≤ 33 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have e : exp (33 : ℝ) = exp 1 ^ 33 := by rw [← exp_nat_mul]; norm_num
  have he := exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 33 ≤ exp 1 ^ 33 := pow_le_pow_left₀ (by norm_num) he.le 33
  have : (10 : ℝ) ^ 14 ≤ 2.7182818283 ^ 33 := by norm_num
  rw [e]; linarith

lemma log_le_lin14 (L : ℝ) (hL : 0 < L) : log L ≤ 33 + L / 10 ^ 14 := by
  have h := log_le_lin_gen L ((10 : ℝ) ^ 14) hL (by positivity)
  have h3 := log1e14_le
  generalize log ((10 : ℝ) ^ 14) = a at h h3
  linarith

/-- The right side of the u₀ condition at u₀ = 10⁸ is at most 10⁸ + 90. -/
lemma rhs_le : (100000000 : ℝ) * (1 + 9e-7 / log 100000000) ≤ 100000000 + 90 := by
  have h6 : 9e-7 / log (100000000 : ℝ) ≤ 9e-7 := div_le_self (by norm_num) log1e8_ge1
  nlinarith

/-- **Theorems 44 and 50, the u₀ condition at u₀ = 10⁸, α = 10⁻⁵**, every `L ≥ 9·10¹³`,
`1 ≤ lx₁ ≤ L`. -/
theorem u0cond_44_50_1e8 (L lx1 : ℝ) (hL : 9 * 10 ^ 13 ≤ L) (hx1 : 1 ≤ lx1) (hx1L : lx1 ≤ L) :
    100000000 * (1 + 9e-7 / log 100000000) ≤ α * L - 10 * log lx1 - 2.5 * log L := by
  have hL0 : 0 < L := by linarith
  have h1 : log lx1 ≤ log L := log_le_log (by linarith) hx1L
  have h2 := log_le_lin14 L hL0
  have hm := rhs_le
  simp only [α]
  nlinarith

/-- **Theorem 51's condition at u₀ = 10⁸, α₃ = 10⁻⁵**: `log 3¹⁰ + α L − 10 log L ≥ u₀(1 + 9·10⁻⁷/log u₀)`. -/
theorem u0cond_51_1e8 (L : ℝ) (hL : 9 * 10 ^ 13 ≤ L) :
    100000000 * (1 + 9e-7 / log 100000000) ≤ 10 * log 3 + α * L - 10 * log L := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  have h3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  have hm := rhs_le
  simp only [α]
  nlinarith

/-- **The other ranges at `L ≥ 9·10¹³`**, α = 10⁻⁵, ε = εU. -/
theorem ranges_1e8 (L : ℝ) (hL : 9 * 10 ^ 13 ≤ L) :
    8 * α + 160 * log L / L < 1 ∧ α < 1 / 24 ∧ α < 1 / 6 ∧
      L / 4 ≤ (1 / 2 - α) * L - 20 * log L ∧ 4000 < L / 8 ∧ Section9U8.εU ≤ 1 / 74 := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  refine ⟨?_, by norm_num, by norm_num, ?_, by linarith, by norm_num⟩
  · have hlog : log L ≤ L / 1000 := by nlinarith
    have : 160 * log L / L ≤ 160 / 1000 := by
      rw [div_le_iff₀ hL0]; nlinarith
    simp only [α]; linarith
  · simp only [α]; nlinarith

/-- **Chen at exp(exp 32.16) on the u₀ = 10⁸ line, with its Lemma 18 instance and range
conditions**, CONDITIONAL ON Lemma 17 (48), (49) and the corrected Theorems 44, 50, 51. -/
theorem chen_3216_u0 (M : ℝ) (h48 : Lemma17Lower M) (h49 : Lemma17Upper M)
    (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3216 / 100) (AT3216.cA3216 caseA w))
    (hQ : Thm50At (3216 / 100) (AT3216.cQ3216 caseA))
    (hB : Thm51At (3216 / 100) AT3216.cB3216) :
    BJS3At (3216 / 100) ∧
    (∀ u z : ℝ, 100000000 ≤ u → u < z → exp 4000 < z →
      ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ < (1 + Section9U8.εU) * (log z / log u)) ∧
    (∀ N : ℕ, exp (exp (3216 / 100)) < (N : ℝ) →
      (∀ lx1 : ℝ, 1 ≤ lx1 → lx1 ≤ Real.log N →
        100000000 * (1 + 9e-7 / log 100000000) ≤ α * Real.log N - 10 * log lx1 - 2.5 * log (Real.log N)) ∧
      100000000 * (1 + 9e-7 / log 100000000) ≤ 10 * log 3 + α * Real.log N - 10 * log (Real.log N)) := by
  refine ⟨AT3216.chen_3216 caseA w hw hA hQ hB, ?_, ?_⟩
  · intro u z hu huz hz
    rw [epsU_eq]; exact Lemma18U8.lemma18_1e8 M h48 h49 u z hu huz hz
  · intro N hN
    have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
    have hL : AT3216.LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
    have h9 : (9 : ℝ) * 10 ^ 13 ≤ Real.log N := le_trans AT3216.LX_ge hL
    exact ⟨fun lx1 h1 h2 => u0cond_44_50_1e8 _ lx1 h9 h1 h2, u0cond_51_1e8 _ h9⟩

end LeanLab.ChenExplicit.At3216U0

#print axioms LeanLab.ChenExplicit.At3216U0.u0cond_44_50_1e8
#print axioms LeanLab.ChenExplicit.At3216U0.u0cond_51_1e8
#print axioms LeanLab.ChenExplicit.At3216U0.ranges_1e8
#print axioms LeanLab.ChenExplicit.At3216U0.chen_3216_u0

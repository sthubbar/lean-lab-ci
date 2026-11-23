/-
REPAIR audit 2026-11-22, unit P1122-0148, burst-20261122 S43.
Kumchev and Liu 2007, P0088, arXiv 0801.0130.

Audits the header claim of Prep1121KLRoughBulk.lean, theorem
rough_block_bulk_of_block_leaves: in the block range
X^(7/18 + eps) P^(-4) at most H at most Y P^(-4), with Y = windowY X eps =
X^(7/12 + eps/2) and P = (log X)^B, the hypotheses of Lemma 3.4 of page 11,
x^(1/2) at most y at most x and 2 at most z at most y x^(-1/2) L^(-2B), still hold
when applied as on page 15 after display 52 with x = Y, y = H, z = z1 = Y^(1/6 + eps/2).

Verdict: CONFIRMED for every eps in (0, 7/18]. The exact exponent identity is
(7/12 + eps/2)(2/3 + eps/2) + eps (3/8 - eps/4) = 7/18 + eps, and the margin
eps (3/8 - eps/4) is at least 5 eps / 18 for eps at most 7/18, which absorbs P^6.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLRoughBulk

namespace LeanLab.KumchevLiu2007.Margin1122KLBlockCutoff

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. P0088 page 15 after display 52, cutoff of Lemma 3.4 page 11: the exact
exponent identity behind z1 Y^(1/2) versus the block lower end,
(7/12 + eps/2)(2/3 + eps/2) + eps (3/8 - eps/4) = 7/18 + eps. -/
theorem block_cutoff_exponent_gap (ε : ℝ) :
    (7 / 12 + ε / 2) * (2 / 3 + ε / 2) + ε * (3 / 8 - ε / 4) = 7 / 18 + ε := by
  ring

/-- PROVED. P0088 page 15 after display 52: for 0 < eps at most 7/18 the margin
eps (3/8 - eps/4) in block_cutoff_exponent_gap is at least 5 eps / 18. -/
theorem block_cutoff_margin_ge (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    5 * ε / 18 ≤ ε * (3 / 8 - ε / 4) := by
  nlinarith

/-- PROVED. P0088 page 11 Lemma 3.4 hypotheses x^(1/2) ≤ y ≤ x and
2 ≤ z ≤ y x^(-1/2) L^(-2B), as applied on page 15 after display 52 with x = Y,
y = H, z = z1 = Y^(1/6 + eps/2), in the block range of Prep1121KLRough. The forms
proved, sqrt Y ≤ H, 4 H ≤ Y and z1 sqrt Y P^2 ≤ H, imply the hypotheses for both
x = Y/4 and x = Y/2, which cover the lab window [Y/4, Y], since log x ≤ log X. -/
theorem block_lemma34_conditions (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      Real.sqrt (windowY X ε) ≤ H ∧ 4 * H ≤ windowY X ε ∧
      2 ≤ windowY X ε ^ (1 / 6 + ε / 2) ∧
      windowY X ε ^ (1 / 6 + ε / 2) * Real.sqrt (windowY X ε) *
        (Real.log X ^ B) ^ (2 : ℕ) ≤ H := by
  set a : ℝ := 7 / 12 + ε / 2 with ha
  set c : ℝ := 1 / 6 + ε / 2 with hc
  have hac : 0 < a * c := by positivity
  -- log power below X^(7/72)
  have h1 := (isLittleO_log_rpow_rpow_atTop (4 * B)
    (by norm_num : (0 : ℝ) < 7 / 72)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X1, k1⟩ := Filter.eventually_atTop.mp h1
  -- log power below X^(5 eps / 18)
  have h2 := (isLittleO_log_rpow_rpow_atTop (6 * B)
    (by positivity : (0 : ℝ) < 5 * ε / 18)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X2, k2⟩ := Filter.eventually_atTop.mp h2
  -- P^4 at least 4
  have h3 := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 4 * B)).comp
    Real.tendsto_log_atTop).eventually (Filter.eventually_ge_atTop (4 : ℝ))
  obtain ⟨X3, k3⟩ := Filter.eventually_atTop.mp h3
  -- z1 at least 2
  have h4 := (tendsto_rpow_atTop hac).eventually (Filter.eventually_ge_atTop (2 : ℝ))
  obtain ⟨X4, k4⟩ := Filter.eventually_atTop.mp h4
  refine ⟨max 2 (max X1 (max X2 (max X3 X4))), le_max_left _ _, ?_⟩
  intro X H hX hlo hhi
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXa : X1 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXb : X2 ≤ X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hXc : X3 ≤ X := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hX
  have hXd : X4 ≤ X := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  set P : ℝ := Real.log X ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hL B
  have hPn : ∀ n : ℕ, Real.log X ^ ((n : ℝ) * B) = P ^ n := by
    intro n
    rw [show (n : ℝ) * B = B * (n : ℝ) by ring, Real.rpow_mul hL.le, Real.rpow_natCast]
  have hzp : (P) ^ (-4 : ℤ) = (P ^ (4 : ℕ))⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  rw [hzp] at hlo hhi
  have hP4 : 0 < P ^ (4 : ℕ) := pow_pos hP 4
  -- the three log power facts at X
  have e1 : P ^ (4 : ℕ) ≤ X ^ (7 / 72 : ℝ) := by
    have h := k1 X hXa
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL _), abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at h
    have := hPn 4
    push_cast at this
    rw [this] at h
    exact h
  have e2 : P ^ (6 : ℕ) ≤ X ^ (5 * ε / 18) := by
    have h := k2 X hXb
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL _), abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at h
    have := hPn 6
    push_cast at this
    rw [this] at h
    exact h
  have e3 : 4 ≤ P ^ (4 : ℕ) := by
    have h : 4 ≤ Real.log X ^ (4 * B) := k3 X hXc
    have := hPn 4
    push_cast at this
    rw [this] at h
    exact h
  have e4 : 2 ≤ X ^ (a * c) := k4 X hXd
  have hY : windowY X ε = X ^ a := rfl
  have hsq : Real.sqrt (windowY X ε) = X ^ (a / 2) := by
    rw [hY, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    ring_nf
  have hz1 : windowY X ε ^ c = X ^ (a * c) := by
    rw [hY, ← Real.rpow_mul hX0.le]
  rw [hsq, hz1]
  rw [hY] at hhi
  refine ⟨?_, ?_, e4, ?_⟩
  · -- sqrt Y ≤ H
    have hsplit : X ^ (7 / 18 + ε) = X ^ (a / 2) * X ^ (7 / 72 + 3 * ε / 4) := by
      rw [← Real.rpow_add hX0]
      congr 1
      rw [ha]
      ring
    have hmono : X ^ (7 / 72 : ℝ) ≤ X ^ (7 / 72 + 3 * ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hpos : 0 < X ^ (a / 2) := Real.rpow_pos_of_pos hX0 _
    have key : X ^ (a / 2) * P ^ (4 : ℕ) ≤ X ^ (7 / 18 + ε) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left (e1.trans hmono) hpos.le
    calc X ^ (a / 2) = X ^ (a / 2) * P ^ (4 : ℕ) * (P ^ (4 : ℕ))⁻¹ := by
          field_simp
      _ ≤ X ^ (7 / 18 + ε) * (P ^ (4 : ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_right key (inv_pos.mpr hP4).le
      _ ≤ H := hlo
  · -- 4 H ≤ Y
    have hYp : 0 < X ^ a := Real.rpow_pos_of_pos hX0 _
    have hinv : (P ^ (4 : ℕ))⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hP4 (by norm_num)]
      norm_num
      linarith
    have : X ^ a * (P ^ (4 : ℕ))⁻¹ ≤ X ^ a * (1 / 4) :=
      mul_le_mul_of_nonneg_left hinv hYp.le
    linarith
  · -- z1 sqrt Y P^2 ≤ H
    have hgap := block_cutoff_exponent_gap ε
    have hmarg := block_cutoff_margin_ge ε hε hε'
    have hsplit : X ^ (7 / 18 + ε) =
        X ^ (a * c) * X ^ (a / 2) * X ^ (ε * (3 / 8 - ε / 4)) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      congr 1
      rw [ha, hc]
      linarith
    have hmono : X ^ (5 * ε / 18) ≤ X ^ (ε * (3 / 8 - ε / 4)) :=
      Real.rpow_le_rpow_of_exponent_le hX1 hmarg
    have hpos : 0 < X ^ (a * c) * X ^ (a / 2) :=
      mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.rpow_pos_of_pos hX0 _)
    have key : X ^ (a * c) * X ^ (a / 2) * P ^ (6 : ℕ) ≤ X ^ (7 / 18 + ε) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left (e2.trans hmono) hpos.le
    calc X ^ (a * c) * X ^ (a / 2) * P ^ (2 : ℕ)
        = X ^ (a * c) * X ^ (a / 2) * P ^ (6 : ℕ) * (P ^ (4 : ℕ))⁻¹ := by
          field_simp
      _ ≤ X ^ (7 / 18 + ε) * (P ^ (4 : ℕ))⁻¹ :=
          mul_le_mul_of_nonneg_right key (inv_pos.mpr hP4).le
      _ ≤ H := hlo

end LeanLab.KumchevLiu2007.Margin1122KLBlockCutoff

#print axioms LeanLab.KumchevLiu2007.Margin1122KLBlockCutoff.block_cutoff_exponent_gap
#print axioms LeanLab.KumchevLiu2007.Margin1122KLBlockCutoff.block_cutoff_margin_ge
#print axioms LeanLab.KumchevLiu2007.Margin1122KLBlockCutoff.block_lemma34_conditions

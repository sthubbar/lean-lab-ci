/-
The unweighted first Buchstab sum in P0088 page 15 display 52.
The explicit quadratic energy estimate is absorbed into the minor arc budget.
Source P0088 page 11 Lemma 3.4, with rough weight one.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.QuadraticEnergy674
import LeanLab.KumchevLiu2007.InteriorHalvesAux

namespace LeanLab.KumchevLiu2007.Task674
open Real Complex MeasureTheory Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The four terms in the unweighted quadratic energy bound cost at most
64 times H squared over T under their four elementary budget inequalities. -/
theorem quadratic_budget_le (H R q J T : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hT : 0 < T)
    (hRT : R * T ≤ H) (hTq : T ≤ q) (hJR : J * T ≤ 2 * R)
    (hqJ : q * J * T ≤ 2 * H) :
    18 * H * R + 32 * H ^ 2 / q + 4 * H ^ 2 * J / R + 2 * H * q * J ≤
      64 * H ^ 2 / T := by
  have h1 : 18 * H * R ≤ 18 * H ^ 2 / T := by
    apply (le_div_iff₀ hT).mpr
    calc
      18 * H * R * T = 18 * H * (R * T) := by ring
      _ ≤ 18 * H * H := mul_le_mul_of_nonneg_left hRT (by positivity)
      _ = _ := by ring
  have h2 : 32 * H ^ 2 / q ≤ 32 * H ^ 2 / T :=
    div_le_div_of_nonneg_left (by positivity) hT hTq
  have hratio : J / R ≤ 2 / T := (div_le_div_iff₀ hR hT).mpr hJR
  have h3 : 4 * H ^ 2 * J / R ≤ 8 * H ^ 2 / T := by
    have h := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * H ^ 2)
    convert h using 1 <;> ring
  have h4 : 2 * H * q * J ≤ 4 * H ^ 2 / T := by
    apply (le_div_iff₀ hT).mpr
    calc
      2 * H * q * J * T = 2 * H * (q * J * T) := by ring
      _ ≤ 2 * H * (2 * H) := mul_le_mul_of_nonneg_left hqJ (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤ H ^ 2 / T := by positivity
  have hsum := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  calc
    _ ≤ 18 * H ^ 2 / T + 32 * H ^ 2 / T + 8 * H ^ 2 / T + 4 * H ^ 2 / T := hsum
    _ = 62 * (H ^ 2 / T) := by ring
    _ ≤ 64 * (H ^ 2 / T) := mul_le_mul_of_nonneg_right (by norm_num) hnonneg
    _ = 64 * H ^ 2 / T := by ring

/-- P0088 page 11 Lemma 3.4 with rough weight one, on any ordered
subinterval of the square window. The fixed frequency estimate is proved
by Weyl differencing and the lab Vinogradov count, with no cited input. -/
theorem unweighted_first_sum (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ windowY X ε →
        (∫ t in a..b,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨T1, ht1⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 7 / 72)).bound
      (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T2, ht2⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 7 / 24)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨A + 2, by linarith, ?_⟩
  intro B hB ε hε
  refine ⟨64, max 3 (max T1 T2), by norm_num, by linarith [le_max_left (3 : ℝ) (max T1 T2)], ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose a b ha hab hb
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX3
  have hL : 0 < Real.log X := by linarith
  have hT : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL _
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have hB0 : 0 ≤ B := by linarith
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB0
  have hT1 : 1 ≤ Real.log X ^ A := Real.one_le_rpow hL1 hA.le
  have hY : 1 ≤ windowY X ε := Real.one_le_rpow hX1 (by linarith : 0 ≤ 7 / 12 + ε / 2)
  have hR : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hR0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr (by linarith)
  have hAbs1 : Real.log X ^ A ≤ X ^ (7 / 72 : ℝ) := by
    have h := ht1 X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
    simpa only [Real.norm_eq_abs, abs_of_pos hT,
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 72 : ℝ)), one_mul] using h
  have hAbs2 : Real.log X ^ (A + 1) ≤ X ^ (7 / 24 : ℝ) := by
    have h := ht2 X (((le_max_right _ _).trans (le_max_right _ _)).trans hX)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (A + 1)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 24 : ℝ)), one_mul] using h
  have hRT : Real.sqrt (windowY X ε) * Real.log X ^ A ≤ H := by
    calc
      _ ≤ Real.sqrt (windowY X ε) * X ^ (7 / 72 : ℝ) :=
        mul_le_mul_of_nonneg_left hAbs1 hR0.le
      _ = X ^ (7 / 24 + ε / 4 + 7 / 72) := by rw [hR, ← Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ ≤ H := hlow
  have hroot : Real.sqrt (windowY X ε) ≤ H :=
    (le_mul_of_one_le_right hR0.le hT1).trans hRT
  have hH0 : 0 ≤ H := hR0.le.trans hroot
  have hHpos : 0 < H := hR0.trans_le hroot
  have hqpos : (0 : ℝ) < q := hP.trans hqP
  have hqn : 1 ≤ q := by exact_mod_cast (show 0 < q by exact_mod_cast hqpos)
  have hHX : H ≤ X := hhigh.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (by linarith : 1 - ε ≤ (1 : ℝ)))
  have hqX : (q : ℝ) ≤ X := hqQ.trans ((div_le_self hH0 hP1).trans hHX)
  have hlogq : Real.log (q : ℝ) ≤ Real.log X := Real.log_le_log hqpos hqX
  have hJ : 1 + Real.log (q : ℝ) ≤ 2 * Real.log X := by linarith
  have hTq : Real.log X ^ A ≤ (q : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : A ≤ B)).trans hqP.le
  have hTL : Real.log X ^ A * Real.log X ≤ Real.log X ^ B := by
    calc
      Real.log X ^ A * Real.log X = Real.log X ^ (A + 1) := by
        rw [Real.rpow_add hL, Real.rpow_one]
      _ ≤ Real.log X ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hJR : (1 + Real.log (q : ℝ)) * Real.log X ^ A ≤ 2 * Real.sqrt (windowY X ε) := by
    calc
      _ ≤ (2 * Real.log X) * Real.log X ^ A := mul_le_mul_of_nonneg_right hJ hT.le
      _ = 2 * Real.log X ^ (A + 1) := by rw [Real.rpow_add hL, Real.rpow_one]; ring
      _ ≤ 2 * X ^ (7 / 24 : ℝ) := by gcongr
      _ ≤ 2 * Real.sqrt (windowY X ε) := by
        rw [hR]
        gcongr
        linarith
  have hqPJ : (q : ℝ) * Real.log X ^ B ≤ H := (le_div_iff₀ hP).mp hqQ
  have hqJ : (q : ℝ) * (1 + Real.log (q : ℝ)) * Real.log X ^ A ≤ 2 * H := by
    calc
      _ ≤ (q : ℝ) * (2 * Real.log X) * Real.log X ^ A := by gcongr
      _ = 2 * (q : ℝ) * (Real.log X ^ A * Real.log X) := by ring
      _ ≤ 2 * (q : ℝ) * Real.log X ^ B := by gcongr
      _ ≤ 2 * H := by nlinarith
  have happ : |α - (v : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 :=
    (Eq33RouteD.display41_of_minor (by omega : 0 < q) hqQ hclose).le
  exact (unweighted_square_energy_bound (windowY X ε) H α a b hY hroot ha hab hb
    hqn hcop happ).trans (quadratic_budget_le H (Real.sqrt (windowY X ε)) q
      (1 + Real.log q) (Real.log X ^ A) hH0 hR0 hT hRT hTq hJR hqJ)

end LeanLab.KumchevLiu2007.Task674

#print axioms LeanLab.KumchevLiu2007.Task674.quadratic_budget_le
#print axioms LeanLab.KumchevLiu2007.Task674.unweighted_first_sum

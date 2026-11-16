import LeanLab.ChenDoubleSieve.Task587SharpTail
import LeanLab.ChenDoubleSieve.Task587PolynomialTools
import LeanLab.ChenDoubleSieve.Task587Kernel
import LeanLab.ChenDoubleSieve.Task562Boxes

/-!
Generic reciprocal polynomial certificates for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- A centered interval gives a reciprocal polynomial with its exact relative radius.
Wu 2004 page 26, derived cell certificate. -/
theorem reciprocal_cell_upper (N : ℕ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) :
    1 / x ≤ reciprocalUpper N ((a + b) / 2) ((b - a) / (b + a)) x := by
  have hc : 0 < (a + b) / 2 := by linarith
  have hd : 0 < b + a := by linarith
  have hab0 : a + b ≠ 0 := by linarith
  have hr : (b - a) / (b + a) < 1 := (div_lt_one hd).mpr (by linarith)
  have hdist : |(a + b) / 2 - x| ≤ (b - a) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hz : |1 - x / ((a + b) / 2)| ≤ (b - a) / (b + a) := by
    calc
      |1 - x / ((a + b) / 2)| = |(a + b) / 2 - x| / ((a + b) / 2) := by
        rw [show 1 - x / ((a + b) / 2) = ((a + b) / 2 - x) / ((a + b) / 2) by
          field_simp [hab0] <;> ring, abs_div, abs_of_pos hc]
      _ ≤ ((b - a) / 2) / ((a + b) / 2) := div_le_div_of_nonneg_right hdist hc.le
      _ = (b - a) / (b + a) := by field_simp [hab0, hd.ne'] <;> ring
  exact reciprocal_le_upper N hc hr hz

/-- A reciprocal polynomial for a rational box, with its designated repeated coordinate.
Wu 2004 page 26, derived finite polynomial data. -/
def cellPoly {d : ℕ} (N : ℕ) (k : Fin d) (lo hi : Fin d → ℚ) (x : Fin d → ℝ) : ℝ :=
  (∏ j, reciprocalUpper N (((lo j + hi j) / 2 : ℚ) : ℝ)
    (((hi j - lo j) / (hi j + lo j) : ℚ) : ℝ) (x j)) *
  reciprocalUpper N (((lo k + hi k) / 2 : ℚ) : ℝ)
    (((hi k - lo k) / (hi k + lo k) : ℚ) : ℝ) (x k)

/-- The box polynomial dominates its reciprocal kernel on the ordered domain.
Wu 2004 page 26, derived pointwise certificate. -/
theorem reciprocal_le_cellPoly {d : ℕ} (N : ℕ) (k : Fin d) (lo hi : Fin d → ℚ)
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j) {x : Fin d → ℝ}
    (hx : x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) :
    1 / ((∏ j, x j) * x k) ≤ cellPoly N k lo hi x := by
  have hp (j : Fin d) : 0 < x j := by
    have h : (0 : ℝ) < lo j := by exact_mod_cast hlo j
    exact h.trans_le (hx.2 j).1
  have h (j : Fin d) : 1 / x j ≤ reciprocalUpper N (((lo j + hi j) / 2 : ℚ) : ℝ)
      (((hi j - lo j) / (hi j + lo j) : ℚ) : ℝ) (x j) := by
    push_cast
    exact reciprocal_cell_upper N (by exact_mod_cast hlo j) (by exact_mod_cast hle j) (hx.2 j)
  have hprod := prod_le_prod₀ (s := (univ : Finset (Fin d)))
    (fun j _ => (one_div_pos.mpr (hp j)).le) (fun j _ => h j)
  calc
    1 / ((∏ j, x j) * x k) = (∏ j, 1 / x j) * (1 / x k) := by simp [mul_comm]
    _ ≤ cellPoly N k lo hi x := mul_le_mul hprod (h k) (one_div_pos.mpr (hp k)).le
      (prod_nonneg fun j _ => (one_div_pos.mpr (hp j)).le.trans (h j))

/-- The rational box polynomial is integrable on the ordered compact domain.
Wu 2004 page 26, derived polynomial integrability. -/
theorem cellPoly_integrable {d : ℕ} (N : ℕ) (k : Fin d) (lo hi : Fin d → ℚ) :
    IntegrableOn (cellPoly N k lo hi)
      (domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold cellPoly reciprocalUpper
  fun_prop

/-- The sharper Buchstab cap bounds every three or four dimensional tail from phi seven halves.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
theorem cell_tail_integral {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ} (hn : n ≤ 2)
    (N : ℕ) (lo hi : Fin (n + 2) → ℚ) {φ : ℝ} (hφ : (7 / 2 : ℝ) ≤ φ)
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j)
    (hhi : ∀ j, hi j ≤ (5 / 11 : ℚ)) :
    buchstabIntegral ω n (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ ≤
      (5618 / 10000 : ℝ) * ∫ x in domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
        cellPoly N ⟨n, by omega⟩ lo hi x := by
  have hl (j : Fin (n + 2)) : (0 : ℝ) < lo j := by exact_mod_cast hlo j
  have hh (j : Fin (n + 2)) : (hi j : ℝ) ≤ (5 / 11 : ℝ) := by
    have h : (hi j : ℝ) ≤ ((5 / 11 : ℚ) : ℝ) := by exact_mod_cast hhi j
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have harg (x : Fin (n + 2) → ℝ)
      (hx : x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) :
      (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩ := by
    apply Task562.argument_ge_of_box ⟨n, by omega⟩ (lo := fun j => (lo j : ℝ))
      (hi := fun _ => (5 / 11 : ℝ)) (P := 7 / 2) (by norm_num)
      ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2.trans (hh j)⟩
      ((hl _).trans_le (hx.2 _).1) hφ
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
    push_cast
    nlinarith
  have hf := kernel_integrable_above_one hω _ _ φ hl
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 7 / 2).trans (harg x hx))
  have hm := setIntegral_mono_on hf ((cellPoly_integrable N ⟨n, by omega⟩ lo hi).const_mul (5618 / 10000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hl j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (buchstab_le_5618 hω (harg x hx)) hd.le
      calc
        _ ≤ (5618 / 10000 : ℝ) / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = (5618 / 10000 : ℝ) * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_le_cellPoly N _ lo hi hlo hle hx) (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

/-- Rational candidate moments for two separated ordered pairs.
Wu 2004 page 26, D2,18. The integral bridge is a separate obligation. -/
def listMomentPair (ts : List (ℚ × (Fin 4 → ℕ))) (a b c : ℚ) : ℚ :=
  (ts.map fun t => t.1 *
    ((b - a) ^ (t.2 0 + t.2 1 + 2) / Task562.momentDenom 2 ![t.2 0, t.2 1]) *
    ((c - b) ^ (t.2 2 + t.2 3 + 2) / Task562.momentDenom 2 ![t.2 2, t.2 3])).sum

end LeanLab.ChenDoubleSieve.Task587

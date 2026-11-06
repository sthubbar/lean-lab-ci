/-
MMS https://arxiv.org/abs/1610.02017v2, page 3, condition 2.
Baker, Harman and Pintz 1997, reference 2, pages 3, 4 and 41.
Separate prime distribution from the elementary interval normalization.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp361b

namespace LeanLab.Ternary.MMS.Task379
open Finset Filter Topology

/-- LEAF. Endpoint prime distribution with a reserved density margin.
BHP page 4, proof of Theorem 3 part I, using Theorem 2 item i on page 3
and the lower density above 0.9953 on page 41.
The character expansion supplies the totient denominator used by MMS page 3.
Only the lower estimate is retained, with coefficient 0.995 and log squared moduli.
Closed intervals include the open lower endpoint count in BHP. -/
theorem bhp_endpoint_lower (σ : ℝ) (hσ : 11 / 20 < σ) (hσ1 : σ < 1) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y → ∀ h : ℝ,
      y ^ σ ≤ h → h ≤ y / Real.log y → ∀ d c : ℕ,
      1 ≤ d → (d : ℝ) ≤ Real.log y ^ (2 : ℕ) → Nat.Coprime c d →
      0.995 * h / (d.totient * Real.log y) ≤
        ∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), ρ n := by sorry

/-- The printed endpoint coefficient alone loses density when the endpoint increases.
Derived diagnostic for MMS page 3 and BHP page 4. It explains the reserved margin. -/
theorem endpoint_coefficient_loss {x b : ℝ} (hx : 1 < x) (hxb : x < b) :
    0.99 / Real.log b < 0.99 / Real.log x := by
  exact div_lt_div_of_pos_left (by norm_num) (Real.log_pos hx)
    (Real.log_lt_log (by linarith) hxb)

/-- The real budgets needed to normalize the endpoint grow beyond every fixed bound.
Derived step for MMS page 3 and BHP page 4. Mathlib logarithmic growth is used directly. -/
theorem eventual_normalization_budget (θ σ Y : ℝ) (hσθ : σ < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      4 ≤ x ∧ Y ≤ x / 2 ∧ 8 ≤ Real.log x ∧
      200 * Real.log 2 ≤ Real.log x ∧
      (2 : ℝ) ^ σ ≤ x ^ ((θ - σ) / 2) ∧
      16 * Real.log x ≤ x ^ (1 - θ) := by
  have hpow := (tendsto_rpow_atTop (by linarith : 0 < (θ - σ) / 2)).eventually_ge_atTop
    ((2 : ℝ) ^ σ)
  have hlog := (isLittleO_log_rpow_atTop (by linarith : 0 < 1 - θ)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (max 4 (2 * Y)),
    Real.tendsto_log_atTop.eventually_ge_atTop 8,
    Real.tendsto_log_atTop.eventually_ge_atTop (200 * Real.log 2), hpow, hlog]
    with x hx hl8 hl200 hp hl
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hxY : 2 * Y ≤ x := (le_max_right _ _).trans hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ Real.log x),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] at hl
  exact ⟨hx4, by linarith, hl8, hl200, hp, by linarith⟩

/-- LEAF. The MMS intervals eventually satisfy the endpoint conditions.
Derived real variable step in MMS page 3 below Theorem 2.1, applying BHP
page 4 with endpoint b and length b minus a. This statement has no prime input.
The spare exponent and the density margin are fixed before x. -/
theorem interval_normalization (θ σ Y : ℝ) (hσ : 0 < σ) (hσθ : σ < θ)
    (hθ1 : θ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ a b : ℝ, x - x ^ θ / 3 ≤ a → b ≤ x + x ^ θ →
      x ^ (θ - ε) ≤ b - a →
        Y ≤ b ∧ 1 < b ∧ 0 < Real.log x ∧ b ^ σ ≤ b - a ∧
        b - a ≤ b / Real.log b ∧ Real.log x ≤ Real.log b ^ (2 : ℕ) ∧
        0.99 * Real.log b ≤ 0.995 * Real.log x := by
  let ε : ℝ := (θ - σ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  obtain ⟨X, hX⟩ := eventual_normalization_budget θ σ Y hσθ hθ1
  refine ⟨ε, hε, hε1, X, ?_⟩
  intro x hx a b ha hb hlen
  obtain ⟨hx4, hxY, hl8, hl200, hgap, hsmall⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxp : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hxx : x ^ θ ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hθ1.le
  have hlen0 : 0 < b - a := (Real.rpow_pos_of_pos hx0 _).trans_le hlen
  have hbx : x / 2 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hb1 : 1 < b := by linarith
  have hb2 : b ≤ 2 * x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll := Real.log_le_log (by linarith : 0 < x / 2) hbx
  rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hll
  have hlu := Real.log_le_log hb0 hb2
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hlu
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hloghalf : Real.log x / 2 ≤ Real.log b := by linarith
  have hmod : Real.log x ≤ Real.log b ^ (2 : ℕ) := by
    have hsq := mul_self_le_mul_self (by linarith : 0 ≤ Real.log x / 2) hloghalf
    have hprod := mul_nonneg (by linarith : 0 ≤ Real.log x)
      (by linarith : 0 ≤ Real.log x - 4)
    nlinarith only [hsq, hprod]
  have hlogs : 0.99 * Real.log b ≤ 0.995 * Real.log x := by linarith
  have hlenupper : b - a ≤ 4 * x ^ θ / 3 := by linarith
  have hprod : x ^ θ * x ^ (1 - θ) = x := by
    rw [← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hbudget := mul_le_mul_of_nonneg_left hsmall hxp.le
  rw [hprod] at hbudget
  have hlengthlog : (b - a) * Real.log b ≤ x / 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hlenupper hlb.le
    have h₂ := mul_le_mul_of_nonneg_left
      (show Real.log b ≤ 2 * Real.log x by linarith) (by positivity : 0 ≤ 4 * x ^ θ / 3)
    nlinarith only [h₁, h₂, hbudget, hx0]
  have hupper : b - a ≤ b / Real.log b :=
    (le_div_iff₀ hlb).mpr (hlengthlog.trans hbx)
  have hpσ : b ^ σ ≤ (2 * x) ^ σ := Real.rpow_le_rpow hb0.le hb2 hσ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le] at hpσ
  have hgap' : (2 : ℝ) ^ σ * x ^ σ ≤ x ^ (θ - ε) := by
    calc
      _ ≤ x ^ ((θ - σ) / 2) * x ^ σ :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hx0.le _)
      _ = x ^ (θ - ε) := by
        rw [← Real.rpow_add hx0]
        congr 1
        dsimp [ε]
        ring
  exact ⟨hxY.trans hbx, hb1, by linarith, hpσ.trans (hgap'.trans hlen),
    hupper, hmod, hlogs⟩

/-- The exact short progression input follows from endpoint distribution
and the elementary normalization. MMS page 3, condition 2 and the paragraph below it.
CONDITIONAL ON bhp_endpoint_lower and interval_normalization. -/
theorem short_progression_input_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Hyp2 θ ε x 0.99 := by
  let σ : ℝ := (θ + 11 / 20) / 2
  have hσ : 11 / 20 < σ := by dsimp [σ]; linarith
  have hσθ : σ < θ := by dsimp [σ]; linarith
  obtain ⟨Y, hY, hB⟩ := bhp_endpoint_lower σ hσ (hσθ.trans hθ1)
  obtain ⟨ε, he, he1, X, hX⟩ := interval_normalization θ σ Y (by linarith) hσθ hθ1
  refine ⟨ε, he, he1, X, ?_⟩
  intro x hx a b ha hb hlen d c hd hdlog hcd
  obtain ⟨hYb, hb1, hlx, hlow, hupp, hmod, hlogs⟩ := hX x hx a b ha hb hlen
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have ht : 0 < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
  have hlen0 : 0 ≤ b - a := (Real.rpow_nonneg (by linarith : 0 ≤ b) σ).trans hlow
  have hbound := hB b hYb (b - a) hlow hupp d c hd (hdlog.trans hmod) hcd
  have hab : b - (b - a) = a := by ring
  rw [hab] at hbound
  apply le_trans _ hbound
  apply (div_le_div_iff₀ (mul_pos ht hlx) (mul_pos ht hlb)).mpr
  have hm := mul_nonneg (mul_nonneg ht.le hlen0) (sub_nonneg.mpr hlogs)
  nlinarith only [hm]

end LeanLab.Ternary.MMS.Task379

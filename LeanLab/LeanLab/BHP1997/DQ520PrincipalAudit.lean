/-
P0069 pages 43, 51 and 52. Audit of the principal character in displays 5.19 and 5.20.
The lab coefficient has rough support. Its principal polynomial is independent of the
modulus in the permitted range. This does not prove either analytic subleaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLowerExceptional520Split

namespace LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open Classical Complex DecompC165b DecompC165d LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- Page 52 display 5.19, its principal square error is integrable even before its bound. -/
theorem sub_519_principal_integrable (ω : ℝ → ℝ) (ε x : ℝ) (hx : 1 ≤ x) (q : ℕ) :
    IntervalIntegrable (fun y =>
      ‖(∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
        (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
          perronW ω ε x q y (perronZ0 x)‖ ^ 2) volume
      (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  simpa [Thm2.delta, perronW, lowerG, perronT0] using
    DQLeaf518Split.leaf_lemma29_integrable (lowerShortWeight ω ε) ε x hx q
      (1 : DirichletCharacter ℂ q) (perronZ0 x) (perronZ0_pos x).le

/-- Page 51 display 5.17, the lab error scale eventually absorbs integer rounding. -/
theorem sub_517_rounding_absorbed {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ x ^ (11 / 20 + ε) * ((perronT0 x ^ 5)⁻¹ + perronZ0 x ^ 2) := by
  have hα : 0 < (11 / 20 + ε) / 4 := by linarith
  filter_upwards [eventually_T0_le_power521 hα,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hT hx
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 < perronT0 x := by unfold perronT0; positivity
  have hpow : perronT0 x ^ 4 ≤ x ^ (11 / 20 + ε) := by
    calc
      _ ≤ (x ^ ((11 / 20 + ε) / 4)) ^ 4 :=
        pow_le_pow_left₀ hT0.le hT 4
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        congr 1
        ring
  have hz : perronZ0 x ^ 2 = 1 / perronT0 x ^ 4 := by
    simp only [perronZ0, div_pow, one_pow, ← pow_mul]
  have hmain : 1 ≤ x ^ (11 / 20 + ε) * perronZ0 x ^ 2 := by
    rw [hz, ← div_eq_mul_one_div, le_div_iff₀ (pow_pos hT0 4), one_mul]
    exact hpow
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (inv_nonneg.mpr (pow_nonneg hT0.le 5)))
    (Real.rpow_nonneg hx0 _))

/-- Pages 50 to 52, the rough support makes the principal character act as one on b0. -/
theorem lowerShortWeight_mul_principal_eq (ω : ℝ → ℝ)
    {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x)
    {q m : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x)
    (hm : m ∈ rightInterval ε x) :
    (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) =
      (lowerShortWeight ω ε x m : ℂ) := by
  by_cases h0 : rawLower ε x m = 0
  · simp [lowerShortWeight, h0]
  obtain ⟨hQZ, hQY⟩ := sieveQ_lt_rough hε hε8 hx
  obtain ⟨_, hZ1⟩ := scaleZ_rpow_ge hε hε8 hx
  have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  unfold rightInterval at hm
  have hmY : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hm).1
  have hYm : x ^ (11 / 20 + ε) < (m : ℝ) := by
    have := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
    have : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmY
    linarith
  have hqm : q < m := by exact_mod_cast (show (q : ℝ) < m by linarith)
  have hqZ : (q : ℝ) < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) := by linarith
  have hu : IsUnit (m : ZMod q) :=
    (ZMod.isUnit_iff_coprime m q).mpr (rawLower_coprime hZ1 hq hqm hqZ h0)
  rw [MulChar.one_apply hu, mul_one]

/-- Pages 43 and 52, the principal polynomial at any permitted modulus equals that at one. -/
theorem lowerG_principal_eq_mod_one (ω : ℝ → ℝ)
    {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x)
    {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x) (s : ℂ) :
    lowerG ω ε x (1 : DirichletCharacter ℂ q) s =
      lowerG ω ε x (1 : DirichletCharacter ℂ 1) s := by
  unfold lowerG
  apply Finset.sum_congr rfl
  intro m hm
  rw [lowerShortWeight_mul_principal_eq ω hε hε8 hx hq hqQ hm,
    lowerShortWeight_mul_principal_eq ω hε hε8 hx (le_refl 1) (hq.trans hqQ) hm]

/-- Page 52, W for the principal character is independent of the permitted modulus. -/
theorem perronW_eq_mod_one (ω : ℝ → ℝ)
    {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x)
    {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x) (y z : ℝ) :
    perronW ω ε x q y z = perronW ω ε x 1 y z := by
  unfold perronW
  simp_rw [lowerG_principal_eq_mod_one ω hε hε8 hx hq hqQ]

/-- Page 52 display 5.19, the principal window sum equals the untwisted window sum. -/
theorem window_principal_eq_untwisted (ω : ℝ → ℝ)
    {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x)
    {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x) (y z : ℝ) :
    (∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) =
      ∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (lowerShortWeight ω ε x m : ℂ) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact lowerShortWeight_mul_principal_eq ω hε hε8 hx hq hqQ (Finset.mem_filter.mp hm).1

end LeanLab.BHP1997.DQLowerExceptionalMeanSquare

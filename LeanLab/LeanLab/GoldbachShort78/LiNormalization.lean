import LeanLab.GoldbachShort78.LiCounts
import LeanLab.GoldbachShort78.Growth

/-!
AI wrote the Lean code, Codex task57. Binary Goldbach is OPEN.
Runbo Li, arXiv:2407.05651v6, Theorem 1.1, printed p. 2.
https://arxiv.org/abs/2407.05651
The source uses intervals with n-dependent length and a positive epsilon.
-/

namespace LeanLab.GoldbachShort78

/-- The integers z in [Y, 2Y] whose closed interval of length z^a has no prime. -/
noncomputable def powerBadSet (a : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc Y (2 * Y)).filter fun z =>
    ∀ p : ℕ, z ≤ p → (p : ℝ) ≤ z + (z : ℝ) ^ a → ¬p.Prime

/-- A cited exceptional-count consequence of Li Theorem 1.1, p. 2.
The log power three follows by choosing a larger allowed log power.
Monotonicity extends the sufficiently small positive epsilon range to every positive epsilon. -/
def LiPrintedExceptionalCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C y₀ : ℝ, 0 < C ∧ ∀ Y : ℕ, y₀ ≤ Y →
    ((powerBadSet (1 / 21.5 + η) Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3

/-- Positive exponent slack absorbs the dyadic factor and the implied constant. -/
theorem almostAllCount_of_power_exceptions {a b C y₀ : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (_hC : 0 < C)
    (hin : ∀ Y : ℕ, y₀ ≤ Y → ((powerBadSet a Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3) :
    ∃ X : ℝ, AlmostAllCount b X := by
  classical
  have hgrowth : ∀ᶠ y : ℝ in Filter.atTop, (2 : ℝ) ^ a ≤ y ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop ((2 : ℝ) ^ a)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hgrowth
  have hlog : ∀ᶠ y : ℝ in Filter.atTop, max C 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop (max C 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max y₀ (max A (max B 2)), ?_⟩
  intro Y hY H hH
  have hY0 : y₀ ≤ (Y : ℝ) := by grind
  have hYA : A ≤ (Y : ℝ) := by grind
  have hYB : B ≤ (Y : ℝ) := by grind
  have hY2 : (2 : ℝ) ≤ Y := by grind
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := by have := hB Y hYB; grind
  have hCle : C ≤ Real.log Y := le_trans (le_max_left _ _) (hB Y hYB)
  have hsub : badSet Y H ⊆ powerBadSet a Y := by
    intro z hz
    obtain ⟨hzmem, hfree⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzY, hz2Y⟩ := Finset.mem_Icc.mp hzmem
    have hz2 : (z : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast hz2Y
    have hlength : (z : ℝ) ^ a ≤ H := by
      calc
        (z : ℝ) ^ a ≤ (2 * (Y : ℝ)) ^ a :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hz2 ha
        _ = (2 : ℝ) ^ a * (Y : ℝ) ^ a := Real.mul_rpow (by norm_num) hYpos.le
        _ ≤ (Y : ℝ) ^ (b - a) * (Y : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (hA Y hYA) (by positivity)
        _ = (Y : ℝ) ^ b := by rw [← Real.rpow_add hYpos]; congr 1; ring
        _ ≤ H := hH
    apply Finset.mem_filter.mpr
    refine ⟨hzmem, ?_⟩
    intro p hzp hpupper hpprime
    have hpH : p ≤ z + H := by
      have hpr : (p : ℝ) ≤ (z : ℝ) + H := by linarith
      exact_mod_cast hpr
    exact hfree p (Finset.mem_Icc.mpr ⟨hzp, hpH⟩) hpprime
  have hcard : ((badSet Y H).card : ℝ) ≤ (powerBadSet a Y).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    ((badSet Y H).card : ℝ) ≤ (powerBadSet a Y).card := hcard
    _ ≤ C * Y / Real.log Y ^ 3 := hin Y hY0
    _ ≤ (Y : ℝ) / Real.log Y ^ 2 := by
      apply (div_le_div_iff₀ (pow_pos hlogY 3) (pow_pos hlogY 2)).mpr
      have hm := mul_le_mul_of_nonneg_right hCle
        (show 0 ≤ (Y : ℝ) * Real.log Y ^ 2 by positivity)
      nlinarith

/-- The dyadic Li input is derived with positive epsilon, never with epsilon zero. -/
theorem liAlmostAllCountEps_of_printed (hin : LiPrintedExceptionalCount) {ε : ℝ}
    (hε : 0 < ε) : ∃ y₀ : ℝ, LiAlmostAllCountEps ε y₀ := by
  obtain ⟨C, y₀, hC, hbound⟩ := hin (ε / 2) (by linarith)
  exact almostAllCount_of_power_exceptions
    (by positivity : (0 : ℝ) ≤ 1 / 21.5 + ε / 2)
    (by linarith : (1 : ℝ) / 21.5 + ε / 2 < 1 / 21.5 + ε) hC hbound

/-- Primes in all intervals imply the dyadic almost-all count at every larger exponent. -/
theorem almostAllCount_of_primesAll {a b T : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hP : PrimesAll a T) : ∃ X : ℝ, AlmostAllCount b X := by
  classical
  have hbound : ∀ Y : ℕ, max T 2 ≤ (Y : ℝ) →
      ((powerBadSet a Y).card : ℝ) ≤ (1 : ℝ) * Y / Real.log Y ^ 3 := by
    intro Y hY
    have hYT : T ≤ (Y : ℝ) := le_trans (le_max_left _ _) hY
    have hY2 : (2 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
    have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
    have hempty : powerBadSet a Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzmem, hfree⟩ := Finset.mem_filter.mp hz
      have hzY : (Y : ℝ) ≤ z := by exact_mod_cast (Finset.mem_Icc.mp hzmem).1
      obtain ⟨p, hp, hzp, hpu⟩ := hP z (le_trans hYT hzY)
      have hzpNat : z ≤ p := by exact_mod_cast hzp.le
      exact hfree p hzpNat hpu hp
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  exact almostAllCount_of_power_exceptions ha hab (by norm_num : (0 : ℝ) < 1) hbound

end LeanLab.GoldbachShort78

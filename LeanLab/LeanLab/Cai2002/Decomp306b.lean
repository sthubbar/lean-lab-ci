/-
Cai 2002 Lemma 1, page 598. BJS equation 8, page 5.
Global construction of the linear sieve differential functions.
Source: https://arxiv.org/abs/2207.09452
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ChenExplicit.LinearSieve

open Set Filter intervalIntegral
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- Integral stages for the scaled upper and lower functions in equation 8, page 5.
Clamping below two extends each stage continuously to the whole real line. -/
def sieveStage306 : ℕ → ℝ → ℝ × ℝ
  | 0, _ => (2 * Real.exp Real.eulerMascheroniConstant, 0)
  | n + 1, s =>
      (2 * Real.exp Real.eulerMascheroniConstant +
        ∫ t in (2 : ℝ)..max s 2, (sieveStage306 n (t - 1)).2 / max (t - 1) 1,
        ∫ t in (2 : ℝ)..max s 2, (sieveStage306 n (t - 1)).1 / max (t - 1) 1)

/-- Every integral stage is continuous. Derived construction for page 5 equation 8. -/
theorem sieveStage_continuous306 (n : ℕ) : Continuous (sieveStage306 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hk (j : ℝ × ℝ → ℝ) (hj : Continuous j) :
        Continuous (fun t : ℝ => j (sieveStage306 n (t - 1)) / max (t - 1) 1) := by
      apply Continuous.div
      · exact (hj.comp ih).comp (continuous_id.sub continuous_const)
      · exact (continuous_id.sub continuous_const).max continuous_const
      · intro t
        have := le_max_right (t - 1) (1 : ℝ)
        linarith
    have hp (h : ℝ → ℝ) (hc : Continuous h) :
        Continuous (fun s : ℝ => ∫ t in (2 : ℝ)..max s 2, h t) := by
      have hh : Continuous (fun s : ℝ => ∫ t in (2 : ℝ)..s, h t) :=
        continuous_iff_continuousAt.mpr (fun s =>
          (hc.integral_hasStrictDerivAt 2 s).hasDerivAt.continuousAt)
      exact hh.comp (continuous_id.max continuous_const)
    exact (continuous_const.add (hp _ (hk Prod.snd continuous_snd))).prodMk
      (hp _ (hk Prod.fst continuous_fst))

/-- Every stage has the required initial data below two. Equation 8, page 5. -/
theorem sieveStage_initial306 (n : ℕ) (s : ℝ) (hs : s ≤ 2) :
    sieveStage306 n s = (2 * Real.exp Real.eulerMascheroniConstant, 0) := by
  cases n <;> simp [sieveStage306, max_eq_right hs]

/-- Adjacent integral stages agree through the next completed unit interval.
Derived method of steps for equation 8, page 5. -/
theorem sieveStage_stable306 (n : ℕ) (s : ℝ) (hs : s ≤ (n : ℝ) + 2) :
    sieveStage306 (n + 1) s = sieveStage306 n s := by
  induction n generalizing s with
  | zero =>
    have hs2 : s ≤ 2 := by simpa using hs
    rw [sieveStage_initial306 _ s hs2, sieveStage_initial306 _ s hs2]
  | succ n ih =>
    by_cases hs2 : s ≤ 2
    · rw [sieveStage_initial306 _ s hs2, sieveStage_initial306 _ s hs2]
    have h2s : 2 ≤ s := le_of_not_ge hs2
    have hi : ∀ t ∈ uIcc (2 : ℝ) (max s 2),
        sieveStage306 (n + 1) (t - 1) = sieveStage306 n (t - 1) := by
      intro t ht
      rw [max_eq_left h2s, uIcc_of_le h2s] at ht
      apply ih
      push_cast at hs
      linarith [ht.2]
    apply Prod.ext
    · change (2 * Real.exp Real.eulerMascheroniConstant +
        ∫ t in (2 : ℝ)..max s 2, (sieveStage306 (n + 1) (t - 1)).2 / max (t - 1) 1) =
        (2 * Real.exp Real.eulerMascheroniConstant +
        ∫ t in (2 : ℝ)..max s 2, (sieveStage306 n (t - 1)).2 / max (t - 1) 1)
      congr 1
      apply integral_congr
      intro t ht
      dsimp only
      rw [hi t ht]
    · change (∫ t in (2 : ℝ)..max s 2,
        (sieveStage306 (n + 1) (t - 1)).1 / max (t - 1) 1) =
        ∫ t in (2 : ℝ)..max s 2, (sieveStage306 n (t - 1)).1 / max (t - 1) 1
      apply integral_congr
      intro t ht
      dsimp only
      rw [hi t ht]

/-- Later stages preserve every completed interval. Equation 8, page 5. -/
theorem sieveStage_later306 (n m : ℕ) (hnm : n ≤ m) (s : ℝ)
    (hs : s ≤ (n : ℝ) + 2) : sieveStage306 m s = sieveStage306 n s := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hnr : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact (sieveStage_stable306 m s (by linarith)).trans ih

/-- Two stages agree wherever both have completed the method of steps.
Equation 8, page 5. -/
theorem sieveStage_agree306 (n m : ℕ) (s : ℝ)
    (hn : s ≤ (n : ℝ) + 2) (hm : s ≤ (m : ℝ) + 2) :
    sieveStage306 n s = sieveStage306 m s := by
  rcases le_total n m with h | h
  · exact (sieveStage_later306 n m h s hn).symm
  · exact sieveStage_later306 m n h s hm

/-- The globally defined scaled pair for equation 8, page 5.
The ceiling selects a stage that has already stabilized at s. -/
def sieveScaled306 (s : ℝ) : ℝ × ℝ := sieveStage306 ⌈s⌉₊ s

/-- The scaled pair agrees with any sufficiently advanced finite stage.
Equation 8, page 5. -/
theorem sieveScaled_eq_stage306 (n : ℕ) (s : ℝ) (hs : s ≤ (n : ℝ) + 2) :
    sieveScaled306 s = sieveStage306 n s := by
  exact sieveStage_agree306 _ _ s (by linarith [Nat.le_ceil s]) hs

/-- The stabilized pair is continuous on the whole real line.
Equation 8, page 5. -/
theorem sieveScaled_continuous306 : Continuous sieveScaled306 := by
  apply continuous_iff_continuousAt.mpr
  intro s
  let n : ℕ := ⌈s⌉₊ + 1
  have hs : s < (n : ℝ) + 2 := by dsimp [n]; push_cast; linarith [Nat.le_ceil s]
  apply (sieveStage_continuous306 n).continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hs] with t ht
  exact sieveScaled_eq_stage306 n t ht.le

/-- The stabilized pair satisfies both delay equations above two.
Equation 8, page 5. -/
theorem sieveScaled_deriv306 (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => (sieveScaled306 t).1)
      ((sieveScaled306 (s - 1)).2 / (s - 1)) s ∧
    HasDerivAt (fun t => (sieveScaled306 t).2)
      ((sieveScaled306 (s - 1)).1 / (s - 1)) s := by
  let n : ℕ := ⌈s⌉₊ + 1
  have hsn : s < (n : ℝ) + 2 := by dsimp [n]; push_cast; linarith [Nat.le_ceil s]
  have hk (j : ℝ × ℝ → ℝ) (hj : Continuous j) :
      Continuous (fun t : ℝ => j (sieveStage306 n (t - 1)) / max (t - 1) 1) := by
    apply Continuous.div
    · exact (hj.comp (sieveStage_continuous306 n)).comp (continuous_id.sub continuous_const)
    · exact (continuous_id.sub continuous_const).max continuous_const
    · intro t
      have := le_max_right (t - 1) (1 : ℝ)
      linarith
  have heq : ∀ᶠ t : ℝ in 𝓝 s,
      sieveScaled306 t =
        (2 * Real.exp Real.eulerMascheroniConstant +
          ∫ u in (2 : ℝ)..t, (sieveStage306 n (u - 1)).2 / max (u - 1) 1,
          ∫ u in (2 : ℝ)..t, (sieveStage306 n (u - 1)).1 / max (u - 1) 1) := by
    filter_upwards [eventually_gt_nhds hs, eventually_lt_nhds hsn] with t ht2 htn
    rw [sieveScaled_eq_stage306 (n + 1) t (by push_cast; linarith)]
    change (2 * Real.exp Real.eulerMascheroniConstant +
        ∫ u in (2 : ℝ)..max t 2, (sieveStage306 n (u - 1)).2 / max (u - 1) 1,
        ∫ u in (2 : ℝ)..max t 2, (sieveStage306 n (u - 1)).1 / max (u - 1) 1) = _
    rw [max_eq_left ht2.le]
  have hprev : sieveStage306 n (s - 1) = sieveScaled306 (s - 1) :=
    (sieveScaled_eq_stage306 n (s - 1) (by linarith)).symm
  have hu := ((hk Prod.snd continuous_snd).integral_hasStrictDerivAt 2 s).hasDerivAt.const_add
    (2 * Real.exp Real.eulerMascheroniConstant)
  have hl := ((hk Prod.fst continuous_fst).integral_hasStrictDerivAt 2 s).hasDerivAt
  rw [hprev, max_eq_left (by linarith : 1 ≤ s - 1)] at hu hl
  constructor
  · apply hu.congr_of_eventuallyEq
    filter_upwards [heq] with t ht
    exact congrArg Prod.fst ht
  · apply hl.congr_of_eventuallyEq
    filter_upwards [heq] with t ht
    exact congrArg Prod.snd ht

/-- The global upper linear sieve function. Cai page 598 and BJS page 5 equation 8. -/
def sieveUpper306 (s : ℝ) : ℝ := (sieveScaled306 s).1 / s

/-- The global lower linear sieve function. Cai page 598 and BJS page 5 equation 8. -/
def sieveLower306 (s : ℝ) : ℝ := (sieveScaled306 s).2 / s

/-- The constructed global functions satisfy the complete initial differential system.
Cai Lemma 1 page 598 and BJS equation 8 page 5. No sieve theorem is assumed. -/
theorem sieveFns306 :
    LeanLab.ChenExplicit.IsLinearSieveFns sieveUpper306 sieveLower306 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hs2
    have hi : sieveScaled306 s = (2 * Real.exp Real.eulerMascheroniConstant, 0) := by
      rw [sieveScaled_eq_stage306 0 s (by simpa using hs2)]
      rfl
    simp [sieveUpper306, sieveLower306, hi]
  · exact sieveScaled_continuous306.fst.continuousOn.div continuousOn_id
      (fun s hs => ne_of_gt hs)
  · exact sieveScaled_continuous306.snd.continuousOn.div continuousOn_id
      (fun s hs => ne_of_gt hs)
  · intro s hs
    obtain ⟨hu, hl⟩ := sieveScaled_deriv306 s hs
    constructor
    · apply hu.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show 0 < s by linarith)] with t ht
      dsimp [sieveUpper306]
      field_simp
    · apply hl.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds (show 0 < s by linarith)] with t ht
      dsimp [sieveLower306]
      field_simp

/-- The scaled upper function stays above its initial constant and the scaled lower
function stays nonnegative at every finite stage. Equation 8, page 5. -/
theorem sieveStage_bounds306 (n : ℕ) (s : ℝ) :
    2 * Real.exp Real.eulerMascheroniConstant ≤ (sieveStage306 n s).1 ∧
      0 ≤ (sieveStage306 n s).2 := by
  induction n generalizing s with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have hden (t : ℝ) : 0 ≤ max (t - 1) 1 :=
      zero_le_one.trans (le_max_right _ _)
    constructor
    · change _ ≤ _ + ∫ t in (2 : ℝ)..max s 2,
        (sieveStage306 n (t - 1)).2 / max (t - 1) 1
      apply le_add_of_nonneg_right
      apply integral_nonneg (le_max_right _ _)
      intro t _
      exact div_nonneg (ih (t - 1)).2 (hden t)
    · change 0 ≤ ∫ t in (2 : ℝ)..max s 2,
        (sieveStage306 n (t - 1)).1 / max (t - 1) 1
      apply integral_nonneg (le_max_right _ _)
      intro t _
      exact div_nonneg ((show 0 ≤ 2 * Real.exp Real.eulerMascheroniConstant by positivity).trans
        (ih (t - 1)).1) (hden t)

/-- The constructed upper function is positive on the positive half line.
Cai Lemma 1 page 598 and BJS equation 8 page 5. -/
theorem sieveUpper_pos306 (s : ℝ) (hs : 0 < s) : 0 < sieveUpper306 s := by
  apply div_pos _ hs
  exact (show 0 < 2 * Real.exp Real.eulerMascheroniConstant by positivity).trans_le
    (sieveStage_bounds306 ⌈s⌉₊ s).1

/-- The constructed lower function is nonnegative on the positive half line.
Cai Lemma 1 page 598 and BJS equation 8 page 5. -/
theorem sieveLower_nonneg306 (s : ℝ) (hs : 0 < s) : 0 ≤ sieveLower306 s := by
  exact div_nonneg (sieveStage_bounds306 ⌈s⌉₊ s).2 hs.le

#print axioms sieveStage_bounds306
#print axioms sieveUpper_pos306
#print axioms sieveLower_nonneg306

example : sieveUpper306 2 = Real.exp Real.eulerMascheroniConstant := by
  have h := (sieveFns306.1 2 (by norm_num) le_rfl).1
  convert h using 1 <;> ring

example : sieveLower306 2 = 0 := (sieveFns306.1 2 (by norm_num) le_rfl).2

#print axioms sieveFns306

#print axioms sieveScaled_deriv306

#print axioms sieveStage_later306
#print axioms sieveStage_agree306
#print axioms sieveScaled_eq_stage306
#print axioms sieveScaled_continuous306

#print axioms sieveStage_initial306
#print axioms sieveStage_stable306

#print axioms sieveStage_continuous306
/-- The explicit sieve error function is continuous above three.
BJS page 5 equation 7. -/
theorem continuousAt_hSieve306 (s : ℝ) (hs : 3 < s) :
    ContinuousAt LeanLab.ChenExplicit.hSieve s := by
  have hc : ContinuousAt (fun t : ℝ => 3 * t⁻¹ * Real.exp (-t)) s := by
    apply ContinuousAt.mul
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (3 : ℝ)) s).mul
        ((continuousAt_id : ContinuousAt (fun t : ℝ => t) s).inv₀ (by dsimp; linarith))
    · exact (Real.continuous_exp.comp continuous_neg).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  rw [LeanLab.ChenExplicit.hSieve, ite_eq_right (by linarith : ¬ t ≤ 2), ite_eq_right (by linarith : ¬ t ≤ 3)]
#print axioms continuousAt_hSieve306

end LeanLab.Cai2002

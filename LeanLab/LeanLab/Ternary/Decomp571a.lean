/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
Finite Buchstab recursion on the domain used by the displayed integral.
Eight steps suffice on arguments at most nine.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379c

namespace LeanLab.Ternary.MMS.Task571
open MeasureTheory

/-- Finite unrolling of the Buchstab integral equation.
MMS page 11 bottom display and page 12 reference to section 1.4 of Harman.
On arguments from one to n plus two, stage n agrees with Buchstab's function. -/
noncomputable def buchstabStage : ℕ → ℝ → ℝ
  | 0, u => 1 / u
  | n + 1, u => if u ≤ 2 then 1 / u else
      (1 + ∫ t in (1 : ℝ)..(u - 1), buchstabStage n t) / u

/-- The finite Buchstab model used only on arguments from one to seven.
MMS page 11 bottom display. Values outside this domain are not used. -/
noncomputable def buchstabModel (u : ℝ) : ℝ := buchstabStage 8 u

/-- A local copy of the notebook envelope permits an independent supply file.
MMS page 12 footnote 3. The formula is identical to the sealed envelope. -/
noncomputable def referenceEnvelope (u : ℝ) : ℝ :=
  if u ≤ 2 then 1 / u else
    if u ≤ 3 then (1 + Real.log (u - 1)) / u else (1 + Real.log 2) / 3

/-- The ordered triple integral with an arbitrary real profile.
MMS page 11 bottom Buchstab display. -/
noncomputable def profileIntegral (w : ℝ → ℝ) : ℝ :=
  ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
    ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ),
      w ((1 - a - b - c) / a) / (a ^ 2 * b * c)

/-- Each finite stage is nonnegative on arguments at least one.
Derived sign check for MMS page 11 Buchstab coefficient. -/
theorem buchstabStage_nonneg (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ buchstabStage n u := by
  induction n generalizing u with
  | zero => simp only [buchstabStage]; positivity
  | succ n ih =>
    simp only [buchstabStage]
    split_ifs with h
    · positivity
    · have hi : 0 ≤ ∫ t in (1 : ℝ)..(u - 1), buchstabStage n t :=
        intervalIntegral.integral_nonneg (by linarith) (fun t ht => ih ht.1)
      positivity

/-- Every finite stage has the initial reciprocal formula.
MMS page 12 and the initial Buchstab formula used in the notebook. -/
theorem buchstabStage_initial (n : ℕ) {u : ℝ} (hu : u ≤ 2) :
    buchstabStage n u = 1 / u := by
  cases n <;> simp [buchstabStage, hu]

/-- Every positive stage has the logarithmic formula between two and three.
MMS page 12 footnote 3 and the notebook middle branch. -/
theorem buchstabStage_middle (n : ℕ) {u : ℝ} (hu : 2 ≤ u) (hu3 : u ≤ 3) :
    buchstabStage (n + 1) u = (1 + Real.log (u - 1)) / u := by
  by_cases h : u ≤ 2
  · have he : u = 2 := le_antisymm h hu
    subst u
    norm_num [buchstabStage]
  · rw [buchstabStage, if_neg h]
    have hi : (∫ t in (1 : ℝ)..(u - 1), buchstabStage n t) =
        ∫ t in (1 : ℝ)..(u - 1), 1 / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
      exact buchstabStage_initial n (by linarith [ht.2])
    rw [hi, integral_one_div_of_pos (by norm_num) (by linarith)]
    simp

/-- Later unrollings stabilize on each earlier stage's valid domain.
Derived finite form of the Buchstab integral equation for MMS page 11. -/
theorem buchstabStage_stable (n m : ℕ) (hnm : n ≤ m) {u : ℝ}
    (hu : 1 ≤ u) (hun : u ≤ (n : ℝ) + 2) :
    buchstabStage m u = buchstabStage n u := by
  induction n generalizing m u with
  | zero =>
    rw [buchstabStage_initial m (by simpa using hun), buchstabStage]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [buchstabStage]
      split_ifs with ht
      · rfl
      · congr 2
        apply intervalIntegral.integral_congr
        intro t ht'
        rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht'
        apply ih m (by omega) ht'.1
        push_cast at hun
        linarith [ht'.2]

/-- The finite model satisfies the Buchstab integral equation on its used domain.
MMS page 11 bottom display and the definition of omega in the cited section 1.4. -/
theorem buchstabModel_recursion {u : ℝ} (hu : 2 < u) (hu10 : u ≤ 10) :
    buchstabModel u = (1 + ∫ t in (1 : ℝ)..(u - 1), buchstabModel t) / u := by
  change buchstabStage (7 + 1) u = _
  rw [buchstabStage, if_neg (not_le.mpr hu)]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
  exact (buchstabStage_stable 7 8 (by norm_num) ht.1 (by norm_num; linarith [ht.2])).symm

/-- Any function with the Buchstab initial formula and recursion agrees with each valid stage.
Derived finite uniqueness check for MMS page 11 bottom Buchstab display. -/
theorem buchstabStage_eq_of_recursion (w : ℝ → ℝ) (n : ℕ)
    (hinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hrec : ∀ u : ℝ, 2 < u → u ≤ (n : ℝ) + 2 →
      w u = (1 + ∫ t in (1 : ℝ)..(u - 1), w t) / u)
    {u : ℝ} (hu : 1 ≤ u) (hun : u ≤ (n : ℝ) + 2) :
    buchstabStage n u = w u := by
  induction n generalizing u with
  | zero => exact (hinit u hu (by simpa using hun)).symm
  | succ n ih =>
    by_cases ht : u ≤ 2
    · rw [buchstabStage_initial (n + 1) ht, hinit u hu ht]
    · rw [buchstabStage, if_neg ht, hrec u (lt_of_not_ge ht) hun]
      congr 2
      apply intervalIntegral.integral_congr
      intro t ht'
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht'
      apply ih (fun v hv hvn => hrec v hv (by push_cast; linarith)) ht'.1
      push_cast at hun
      linarith [ht'.2]

/-- The finite model is strictly positive at four.
Derived positivity of the first coefficient in MMS page 11 bottom display. -/
theorem buchstabModel_four_pos : 0 < buchstabModel 4 := by
  change 0 < buchstabStage (7 + 1) 4
  rw [buchstabStage, if_neg (by norm_num : ¬ (4 : ℝ) ≤ 2)]
  have hi : 0 ≤ ∫ t in (1 : ℝ)..(4 - 1), buchstabStage 7 t :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => buchstabStage_nonneg 7 ht.1)
  positivity

/-- LEAF. Recovery obligation.  Clamping below one gives a continuous extension of each finite stage.
Derived regularity check for the Buchstab integral on MMS page 11. -/
theorem buchstabStage_continuous_clamp (n : ℕ) :
    Continuous (fun u : ℝ => buchstabStage n (max 1 u)) := by
  induction n with
  | zero =>
    have hzero : (fun u : ℝ => buchstabStage 0 (max 1 u)) = fun u : ℝ => 1 / max 1 u := by
      funext u
      simp only [buchstabStage]
    rw [hzero]
    exact continuous_const.div (continuous_const.max continuous_id)
      (fun u => (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) u)).ne')
  | succ n ih =>
    let F : ℝ → ℝ := fun u =>
      (1 + ∫ t in (1 : ℝ)..(max 1 u - 1), buchstabStage n (max 1 t)) / (max 1 u)
    have hker : Continuous (fun p : ℝ × ℝ => buchstabStage n (max 1 p.2)) :=
      ih.comp continuous_snd
    have hint : Continuous (fun u : ℝ =>
        ∫ t in (1 : ℝ)..(max 1 u - 1), buchstabStage n (max 1 t)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := volume) (a₀ := 1) (f := fun _ : ℝ => fun t : ℝ => buchstabStage n (max 1 t))
        hker (by fun_prop)
    have hF : Continuous F := by
      dsimp only [F]
      exact (continuous_const.add hint).div (by fun_prop)
        (fun u => (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) u)).ne')
    have hpoint : (fun u : ℝ => buchstabStage (n + 1) (max 1 u))
        = fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u := by
      funext u
      by_cases hu : u ≤ 2
      · rw [if_pos hu]
        exact buchstabStage_initial (n + 1) (max_le (by norm_num) hu)
      · have hu2 : 2 < u := lt_of_not_ge hu
        have hmax : max 1 u = u := max_eq_right (by linarith : (1 : ℝ) ≤ u)
        rw [if_neg hu]
        dsimp only [F]
        rw [hmax]
        rw [buchstabStage, if_neg (not_le.mpr hu2)]
        have hi : (∫ t in (1 : ℝ)..(u - 1), buchstabStage n t)
            = ∫ t in (1 : ℝ)..(u - 1), buchstabStage n (max 1 t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
          show buchstabStage n t = buchstabStage n (max 1 t)
          rw [max_eq_right ht.1]
        rw [hi]
    rw [hpoint]
    have hEqK : Set.EqOn (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u)
        (fun u : ℝ => 1 / max 1 u) (Set.Iic 2) := by
      intro u hu
      rw [Set.mem_Iic] at hu
      show (if u ≤ 2 then 1 / max 1 u else F u) = 1 / max 1 u
      rw [if_pos hu]
    have hEqF : Set.EqOn (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u) F (Set.Ici 2) := by
      intro u hu
      rw [Set.mem_Ici] at hu
      show (if u ≤ 2 then 1 / max 1 u else F u) = F u
      rcases eq_or_lt_of_le hu with h | h
      · rw [← h]
        rw [if_pos le_rfl]
        dsimp only [F]
        rw [show max 1 (2 : ℝ) = 2 by norm_num]
        rw [show (2 : ℝ) - 1 = 1 by norm_num]
        simp
      · rw [if_neg (not_le.mpr h)]
    have hK : Continuous (fun u : ℝ => 1 / max 1 u) :=
      continuous_const.div (continuous_const.max continuous_id)
        (fun u => (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) u)).ne')
    have h1 : ContinuousOn (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u) (Set.Iic 2) :=
      hK.continuousOn.congr hEqK
    have h2 : ContinuousOn (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u) (Set.Ici 2) :=
      hF.continuousOn.congr hEqF
    have hall : ContinuousOn (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else F u) Set.univ := by
      rw [← Set.Iic_union_Ici (a := (2 : ℝ))]
      exact ContinuousOn.union_of_isClosed h1 h2 isClosed_Iic isClosed_Ici
    exact continuousOn_univ.mp hall

/-- LEAF. Recovery obligation.  A continuous extension of the notebook envelope below its domain.
Derived regularity check for MMS page 12 footnote 3. -/
theorem referenceEnvelope_continuous_clamp :
    Continuous (fun u : ℝ => referenceEnvelope (max 1 u)) := by
  let K : ℝ → ℝ := fun u => 1 / max 1 u
  let M : ℝ → ℝ := fun u => (1 + Real.log (max 1 (u - 1))) / max 1 u
  let C : ℝ := (1 + Real.log 2) / 3
  let G : ℝ → ℝ := fun u => if u ≤ 2 then K u else if u ≤ 3 then M u else C
  have hpos : ∀ u : ℝ, 0 < max 1 u :=
    fun u => lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) u)
  have hlog : Continuous fun u : ℝ => Real.log (max 1 (u - 1)) :=
    Continuous.log (by fun_prop : Continuous fun u : ℝ => max 1 (u - 1))
      (fun u => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (u - 1))))
  have hK : Continuous K := by
    dsimp only [K]
    exact continuous_const.div (continuous_const.max continuous_id) (fun u => (hpos u).ne')
  have hM : Continuous M := by
    dsimp only [M]
    exact (continuous_const.add hlog).div (by fun_prop) (fun u => (hpos u).ne')
  have hG : (fun u : ℝ => referenceEnvelope (max 1 u)) = G := by
    funext u
    show referenceEnvelope (max 1 u) = (if u ≤ 2 then K u else if u ≤ 3 then M u else C)
    by_cases hu : u ≤ 2
    · have hm : max 1 u ≤ 2 := max_le (by norm_num) hu
      rw [if_pos hu]
      dsimp only [K]
      simp only [referenceEnvelope, if_pos hm]
    · have hu2 : 2 < u := lt_of_not_ge hu
      have hmax : max 1 u = u := max_eq_right (by linarith : (1 : ℝ) ≤ u)
      by_cases hu3 : u ≤ 3
      · rw [if_neg hu, if_pos hu3]
        dsimp only [M]
        rw [hmax, max_eq_right (by linarith : (1 : ℝ) ≤ u - 1)]
        simp only [referenceEnvelope, if_neg (not_le.mpr hu2), if_pos hu3]
      · have hu3' : 3 < u := lt_of_not_ge hu3
        rw [if_neg hu, if_neg hu3]
        dsimp only [C]
        rw [hmax]
        simp only [referenceEnvelope, if_neg (not_le.mpr hu2), if_neg (not_le.mpr hu3')]
  rw [hG]
  have hEqK : Set.EqOn G K (Set.Iic 2) := by
    intro u hu
    rw [Set.mem_Iic] at hu
    show (if u ≤ 2 then K u else if u ≤ 3 then M u else C) = K u
    rw [if_pos hu]
  have hEqM : Set.EqOn G M (Set.Icc 2 3) := by
    intro u hu
    rw [Set.mem_Icc] at hu
    show (if u ≤ 2 then K u else if u ≤ 3 then M u else C) = M u
    by_cases h2 : u = 2
    · rw [h2, if_pos le_rfl]
      dsimp only [K, M]
      rw [show max 1 (2 : ℝ) = 2 by norm_num,
        show max 1 ((2 : ℝ) - 1) = 1 by norm_num, Real.log_one]
      norm_num
    · have hle : ¬ u ≤ 2 := by
        intro h
        exact h2 (le_antisymm h hu.1)
      rw [if_neg hle, if_pos hu.2]
  have hEqC : Set.EqOn G (fun _ : ℝ => C) (Set.Ici 3) := by
    intro u hu
    rw [Set.mem_Ici] at hu
    show (if u ≤ 2 then K u else if u ≤ 3 then M u else C) = C
    by_cases h3 : u = 3
    · rw [h3, if_neg (by norm_num : ¬ (3 : ℝ) ≤ 2), if_pos le_rfl]
      dsimp only [M, C]
      rw [show max 1 (3 : ℝ) = 3 by norm_num,
        show max 1 ((3 : ℝ) - 1) = 2 by norm_num]
    · have hle : ¬ u ≤ 3 := by
        intro h
        exact h3 (le_antisymm h hu)
      rw [if_neg (by linarith : ¬ u ≤ 2), if_neg hle]
  have h1 : ContinuousOn G (Set.Iic 2) := hK.continuousOn.congr hEqK
  have h2 : ContinuousOn G (Set.Icc 2 3) := hM.continuousOn.congr hEqM
  have h3 : ContinuousOn G (Set.Ici 3) := continuousOn_const.congr hEqC
  have hall : ContinuousOn G (((Set.Iic (2 : ℝ)) ∪ (Set.Icc 2 3)) ∪ (Set.Ici 3)) :=
    ContinuousOn.union_of_isClosed
      (ContinuousOn.union_of_isClosed h1 h2 isClosed_Iic isClosed_Icc) h3
      (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  have hun : ((Set.Iic (2 : ℝ) ∪ Set.Icc 2 3) ∪ Set.Ici 3) = Set.univ := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, Set.mem_univ, iff_true]
    rcases le_or_gt u 2 with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt u 3 with h3 | h3
      · exact Or.inl (Or.inr ⟨le_of_lt h, h3⟩)
      · exact Or.inr (le_of_lt h3)
  rw [hun] at hall
  exact continuousOn_univ.mp hall

/-- LEAF. Recovery obligation.  Continuous clamped extensions are integrable on intervals above one.
Derived regularity step for MMS page 11 Buchstab integral equation. -/
theorem clamped_intervalIntegrable {w : ℝ → ℝ}
    (hw : Continuous (fun u : ℝ => w (max 1 u))) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable w volume a b := by
  apply (hw.intervalIntegrable a b).congr
  intro t ht
  rw [Set.uIoc_of_le hab] at ht
  dsimp only
  rw [max_eq_right (ha.trans ht.1.le)]

/-- Three rational pointwise bounds for the initial logarithmic branch.
Derived elementary estimates for the notebook envelope on MMS page 12. -/
theorem referenceEnvelope_middle_budgets :
    (∀ u : ℝ, 2 ≤ u → u ≤ 9 / 4 → referenceEnvelope u ≤ (0.55 : ℝ)) ∧
    (∀ u : ℝ, 2 ≤ u → u ≤ 5 / 2 → referenceEnvelope u ≤ (0.563 : ℝ)) ∧
    (∀ u : ℝ, 5 / 2 ≤ u → u ≤ 3 → referenceEnvelope u ≤ (0.57 : ℝ)) := by
  have formula (u : ℝ) (hu : 2 ≤ u) (hu3 : u ≤ 3) :
      referenceEnvelope u = (1 + Real.log (u - 1)) / u := by
    by_cases ht : u ≤ 2
    · have he : u = 2 := le_antisymm ht hu
      subst u
      norm_num [referenceEnvelope]
    · simp [referenceEnvelope, ht, hu3]
  have tangent (u r : ℝ) (hu : 2 ≤ u) (hr : 0 < r) :
      Real.log (u - 1) ≤ Real.log r + (u - 1) / r - 1 := by
    have hz : 0 < u - 1 := by linarith
    have ht := Real.log_le_sub_one_of_pos (div_pos hz hr)
    rw [Real.log_div hz.ne' hr.ne'] at ht
    linarith
  have h54 : Real.log (5 / 4 : ℝ) ≤ (0.224 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    linarith [Real.log_five_lt_d9, Real.log_two_gt_d9]
  have h32 : Real.log (3 / 2 : ℝ) ≤ (0.406 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have h95 : Real.log (9 / 5 : ℝ) ≤ (0.588 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    linarith [Real.log_three_lt_d9, Real.log_five_gt_d9]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu hu9
    rw [formula u hu (by linarith)]
    apply (div_le_iff₀ (by linarith : 0 < u)).mpr
    have ht := tangent u (5 / 4) hu (by norm_num)
    norm_num at ht
    nlinarith
  · intro u hu hu5
    rw [formula u hu (by linarith)]
    apply (div_le_iff₀ (by linarith : 0 < u)).mpr
    have ht := tangent u (3 / 2) hu (by norm_num)
    norm_num at ht
    nlinarith
  · intro u hu hu3
    rw [formula u (by linarith) hu3]
    apply (div_le_iff₀ (by linarith : 0 < u)).mpr
    have ht := tangent u (9 / 5) (by linarith) (by norm_num)
    norm_num at ht
    nlinarith

/-- The running integral of the middle branch is at most 0.564 times its length.
Derived elementary enclosure for the Buchstab comparison on MMS page 12.
Only rational pointwise bounds and exact constant integrals are used. -/
theorem referenceEnvelope_middle_integral {v : ℝ} (hv : 2 ≤ v) (hv3 : v ≤ 3) :
    (∫ t in (2 : ℝ)..v, referenceEnvelope t) ≤ (0.564 : ℝ) * (v - 2) := by
  obtain ⟨h55, h563, h57⟩ := referenceEnvelope_middle_budgets
  have hi {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :=
    clamped_intervalIntegrable referenceEnvelope_continuous_clamp ha hab
  have bound {a b K : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
      (hB : ∀ t ∈ Set.Icc a b, referenceEnvelope t ≤ K) :
      (∫ t in a..b, referenceEnvelope t) ≤ K * (b - a) := by
    have h := intervalIntegral.integral_mono_on hab (hi ha hab)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a b) hB
    simpa [mul_comm] using h
  by_cases hv5 : v ≤ 5 / 2
  · have h := bound (by norm_num : (1 : ℝ) ≤ 2) hv
      (fun t ht => h563 t ht.1 (ht.2.trans hv5))
    nlinarith
  · have hv5' : (5 / 2 : ℝ) ≤ v := le_of_not_ge hv5
    have h1 := bound (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 9 / 4) (fun t ht => h55 t ht.1 ht.2)
    have h2 := bound (by norm_num : (1 : ℝ) ≤ 9 / 4)
      (by norm_num : (9 / 4 : ℝ) ≤ 5 / 2)
      (fun t ht => h563 t (by linarith [ht.1]) ht.2)
    have h3 := bound (by norm_num : (1 : ℝ) ≤ 5 / 2) hv5'
      (fun t ht => h57 t ht.1 (ht.2.trans hv3))
    have hs1 := intervalIntegral.integral_add_adjacent_intervals
      (hi (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 9 / 4))
      (hi (by norm_num : (1 : ℝ) ≤ 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 5 / 2))
    have hs2 := intervalIntegral.integral_add_adjacent_intervals
      (hi (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 5 / 2))
      (hi (by norm_num : (1 : ℝ) ≤ 5 / 2) hv5')
    linarith

/-- The notebook envelope is a supersolution of the Buchstab integral equation.
Derived comparison from the initial formulas and the tail constant in MMS page 12.
No numerical triple integral is used. -/
theorem referenceEnvelope_primitive_bound {v : ℝ} (hv : 2 ≤ v) :
    1 + (∫ t in (1 : ℝ)..v, referenceEnvelope t) ≤
      ((1 + Real.log 2) / 3) * (v + 1) := by
  let C : ℝ := (1 + Real.log 2) / 3
  have hC : (0.564 : ℝ) ≤ C := by
    dsimp [C]
    linarith [Real.log_two_gt_d9]
  have hi {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :=
    clamped_intervalIntegrable referenceEnvelope_continuous_clamp ha hab
  have h12 : (∫ t in (1 : ℝ)..2, referenceEnvelope t) = Real.log 2 := by
    calc
      _ = ∫ t in (1 : ℝ)..2, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        simp [referenceEnvelope, ht.2]
      _ = Real.log 2 := by rw [integral_one_div_of_pos (by norm_num) (by norm_num)]; simp
  have split := intervalIntegral.integral_add_adjacent_intervals
    (hi (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2))
    (hi (by norm_num : (1 : ℝ) ≤ 2) hv)
  rw [h12] at split
  by_cases hv3 : v ≤ 3
  · have hm := referenceEnvelope_middle_integral hv hv3
    have hh := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ v - 2)
    dsimp [C] at hh
    linarith
  · have hv3' : (3 : ℝ) ≤ v := le_of_not_ge hv3
    have hm := referenceEnvelope_middle_integral (by norm_num : (2 : ℝ) ≤ 3) le_rfl
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hi (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3))
      (hi (by norm_num : (1 : ℝ) ≤ 3) hv3')
    have ht : (∫ t in (3 : ℝ)..v, referenceEnvelope t) = C * (v - 3) := by
      calc
        _ = ∫ t in (3 : ℝ)..v, C := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hv3'] at ht
          by_cases h3 : t ≤ 3
          · have he : t = 3 := le_antisymm h3 ht.1
            subst t
            norm_num [referenceEnvelope, C]
          · simp [referenceEnvelope, show ¬ t ≤ 2 by linarith [ht.1], h3, C]
        _ = C * (v - 3) := by simp [mul_comm]
    rw [ht] at hs
    dsimp [C] at hC hs
    linarith

/-- Every finite Buchstab stage lies under the notebook envelope above one.
Derived comparison from the initial formulas and the supersolution inequality.
MMS page 12 first paragraph and footnote 3. -/
theorem buchstabStage_le_referenceEnvelope (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    buchstabStage n u ≤ referenceEnvelope u := by
  induction n generalizing u with
  | zero =>
    change 1 / u ≤ referenceEnvelope u
    unfold referenceEnvelope
    split_ifs with h2 h3
    · exact le_rfl
    · have hl := Real.log_nonneg (by linarith : 1 ≤ u - 1)
      apply (div_le_div_iff_of_pos_right (by linarith : 0 < u)).mpr
      linarith
    · have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have hu0 : 0 < u := by linarith
      apply (div_le_iff₀ hu0).mpr
      nlinarith
  | succ n ih =>
    by_cases h2 : u ≤ 2
    · rw [buchstabStage_initial (n + 1) h2]
      simp [referenceEnvelope, h2]
    by_cases h3 : u ≤ 3
    · rw [buchstabStage_middle n (by linarith) h3]
      simp [referenceEnvelope, h2, h3]
    have hu3 : 3 < u := lt_of_not_ge h3
    rw [buchstabStage, if_neg h2]
    have hs := referenceEnvelope_primitive_bound (v := u - 1) (by linarith)
    have hmono := intervalIntegral.integral_mono_on
      (by linarith : (1 : ℝ) ≤ u - 1)
      (clamped_intervalIntegrable (buchstabStage_continuous_clamp n) le_rfl (by linarith))
      (clamped_intervalIntegrable referenceEnvelope_continuous_clamp le_rfl (by linarith))
      (fun t ht => ih ht.1)
    simp only [referenceEnvelope, if_neg h2, if_neg h3]
    apply (div_le_iff₀ (by linarith : 0 < u)).mpr
    linarith

/-- LEAF. The finite Buchstab model is bounded by omega three on the required tail.
MMS page 12 first paragraph, citing Harman equation 1.4.16.
Only the compact range three to seven is needed by the page 11 display.
This statement contains no prime sum and no mean asymptotic. -/
theorem buchstabModel_tail {u : ℝ} (hu : 3 ≤ u) (hu7 : u ≤ 7) :
    buchstabModel u ≤ (1 + Real.log 2) / 3 := by
  change buchstabStage 8 u ≤ (1 + Real.log 2) / 3
  have hstage := buchstabStage_le_referenceEnvelope 8 (by linarith : (1 : ℝ) ≤ u)
  have hre : referenceEnvelope u ≤ (1 + Real.log 2) / 3 := by
    rcases eq_or_lt_of_le hu with h | h
    · rw [← h]
      have h1 : (3 : ℝ) - 1 = 2 := by norm_num
      simp only [referenceEnvelope, h1, if_neg (by norm_num : ¬ (3 : ℝ) ≤ 2), if_pos le_rfl]
      exact le_rfl
    · simp only [referenceEnvelope, if_neg (by linarith : ¬ u ≤ 2), if_neg (not_le.mpr h)]
      exact le_rfl
  linarith

/-- The initial formulas and the tail bound give the pointwise notebook envelope.
MMS page 12 first paragraph and footnote 3. CONDITIONAL ON buchstabModel_tail. -/
theorem buchstabModel_le_envelope {u : ℝ} (hu : 1 ≤ u) (hu7 : u ≤ 7) :
    buchstabModel u ≤ referenceEnvelope u := by
  unfold referenceEnvelope
  split_ifs with htwo hthree
  · exact (buchstabStage_initial 8 htwo).le
  · exact (buchstabStage_middle 7 (by linarith) hthree).le
  · exact buchstabModel_tail (by linarith) hu7

/-- Every argument in the ordered integration region lies between one and seven.
Derived domain check for MMS page 11 bottom display. -/
theorem profile_argument_bounds {a b c : ℝ}
    (ha : (1 / 10 : ℝ) ≤ a) (ha4 : a ≤ 1 / 4)
    (hab : a ≤ b) (hb4 : b ≤ 1 / 4) (hbc : b ≤ c) (hc4 : c ≤ 1 / 4) :
    1 ≤ (1 - a - b - c) / a ∧ (1 - a - b - c) / a ≤ 7 := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply (le_div_iff₀ ha0).mpr
    linarith
  · apply (div_le_iff₀ ha0).mpr
    linarith

/-- A nonnegative profile gives a nonnegative ordered integral.
Derived sign check for MMS page 11 bottom display. -/
theorem profileIntegral_nonneg {w : ℝ → ℝ}
    (hw : ∀ u : ℝ, 1 ≤ u → u ≤ 7 → 0 ≤ w u) : 0 ≤ profileIntegral w := by
  unfold profileIntegral
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro a ha
  apply intervalIntegral.integral_nonneg ha.2
  intro b hb
  apply intervalIntegral.integral_nonneg hb.2
  intro c hc
  have hu := profile_argument_bounds ha.1 ha.2 hb.1 hb.2 hc.1 hc.2
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := ha0.trans_le hb.1
  have hc0 : 0 < c := hb0.trans_le hc.1
  exact div_nonneg (hw _ hu.1 hu.2) (by positivity)

/-- The paper coefficient is positive without any numerical integration.
MMS page 11 bottom display and page 12 definition of alpha plus. -/
theorem buchstab_coefficient_pos :
    0 < 4 * buchstabModel 4 + profileIntegral buchstabModel := by
  have hi := profileIntegral_nonneg (w := buchstabModel)
    (fun u hu _ => buchstabStage_nonneg 8 hu)
  have hp := buchstabModel_four_pos
  positivity

/-- LEAF. Recovery obligation.  Integrating a globally continuous parameter kernel between continuous endpoints
preserves continuity. Derived regularity step for MMS page 11 bottom display. -/
theorem continuous_integral_bounds {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f : X → ℝ → ℝ) (hf : Continuous f.uncurry)
    (lo hi : X → ℝ) (hlo : Continuous lo) (hhi : Continuous hi) :
    Continuous (fun x => ∫ t in lo x..hi x, f x t) := by
  have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hhi
  have hl := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hlo
  apply (hh.sub hl).congr
  intro x
  have hx : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hx.intervalIntegrable (μ := volume) 0 (lo x)) (hx.intervalIntegrable (μ := volume) (lo x) (hi x))
  dsimp only [Pi.sub_apply]
  linarith

/-- Clipping integration coordinates gives a globally continuous kernel.
Derived compact domain verification for MMS page 11 bottom display. -/
noncomputable def extendedKernel (w : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  let A := max (1 / 10 : ℝ) (min (1 / 4 : ℝ) a)
  let B := max (1 / 10 : ℝ) (min (1 / 4 : ℝ) b)
  let C := max (1 / 10 : ℝ) (min (1 / 4 : ℝ) c)
  w (max 1 ((1 - A - B - C) / A)) / (A ^ 2 * B * C)

/-- The extended kernel is continuous when the profile has a continuous clamped extension.
Derived regularity step for MMS page 11 bottom display. -/
theorem extendedKernel_continuous {w : ℝ → ℝ}
    (hw : Continuous (fun u : ℝ => w (max 1 u))) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => extendedKernel w p.1.1 p.1.2 p.2) := by
  have ha : Continuous (fun p : (ℝ × ℝ) × ℝ => max (1 / 10 : ℝ) (min (1 / 4 : ℝ) p.1.1)) := by fun_prop
  have hb : Continuous (fun p : (ℝ × ℝ) × ℝ => max (1 / 10 : ℝ) (min (1 / 4 : ℝ) p.1.2)) := by fun_prop
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => max (1 / 10 : ℝ) (min (1 / 4 : ℝ) p.2)) := by fun_prop
  have hpos (t : ℝ) : 0 < max (1 / 10 : ℝ) (min (1 / 4 : ℝ) t) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact (hw.comp (((continuous_const.sub ha).sub hb).sub hc |>.div ha
    (fun p => (hpos _).ne'))).div ((ha.pow 2).mul hb |>.mul hc)
      (fun p => by have := hpos p.1.1; have := hpos p.1.2; have := hpos p.2; positivity)

/-- LEAF. Recovery obligation.  The extended kernel equals the original kernel throughout the ordered region.
Derived domain verification for MMS page 11 bottom display. -/
theorem extendedKernel_eq {w : ℝ → ℝ} {a b c : ℝ}
    (ha : (1 / 10 : ℝ) ≤ a) (ha4 : a ≤ 1 / 4)
    (hab : a ≤ b) (hb4 : b ≤ 1 / 4) (hbc : b ≤ c) (hc4 : c ≤ 1 / 4) :
    extendedKernel w a b c = w ((1 - a - b - c) / a) / (a ^ 2 * b * c) := by
  have hb : (1 / 10 : ℝ) ≤ b := ha.trans hab
  have hc : (1 / 10 : ℝ) ≤ c := hb.trans hbc
  have hu := profile_argument_bounds ha ha4 hab hb4 hbc hc4
  dsimp only [extendedKernel]
  rw [min_eq_right ha4, min_eq_right hb4, min_eq_right hc4,
    max_eq_right ha, max_eq_right hb, max_eq_right hc, max_eq_right hu.1]

/-- LEAF. Recovery obligation.  The ordered integral is monotone for profiles with continuous clamped extensions.
Derived comparison step for MMS page 12 footnote 3. -/
theorem profileIntegral_mono {v w : ℝ → ℝ}
    (hv : Continuous (fun u : ℝ => v (max 1 u)))
    (hw : Continuous (fun u : ℝ => w (max 1 u)))
    (hvw : ∀ u : ℝ, 1 ≤ u → u ≤ 7 → v u ≤ w u) :
    profileIntegral v ≤ profileIntegral w := by
  have hEv : Continuous (fun p : (ℝ × ℝ) × ℝ => extendedKernel v p.1.1 p.1.2 p.2) :=
    extendedKernel_continuous hv
  have hEw : Continuous (fun p : (ℝ × ℝ) × ℝ => extendedKernel w p.1.1 p.1.2 p.2) :=
    extendedKernel_continuous hw
  have hrewrite : ∀ g : ℝ → ℝ, Continuous (fun u : ℝ => g (max 1 u)) →
      profileIntegral g = ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
        ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), extendedKernel g a b c := by
    intro g _
    unfold profileIntegral
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4)] at ha
    apply intervalIntegral.integral_congr
    intro b hb
    rw [Set.uIcc_of_le ha.2] at hb
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hb.2] at hc
    exact (extendedKernel_eq ha.1 ha.2 hb.1 hb.2 hc.1 hc.2).symm
  have hinner : ∀ (a b : ℝ), (1 / 10 : ℝ) ≤ a → a ≤ 1 / 4 → a ≤ b → b ≤ 1 / 4 →
      (∫ c in b..(1 / 4 : ℝ), extendedKernel v a b c) ≤
        ∫ c in b..(1 / 4 : ℝ), extendedKernel w a b c := by
    intro a b ha ha4 hab hb4
    have hcv : Continuous fun c : ℝ => extendedKernel v a b c :=
      hEv.comp (by fun_prop : Continuous (fun c : ℝ => ((a, b), c)))
    have hcw : Continuous fun c : ℝ => extendedKernel w a b c :=
      hEw.comp (by fun_prop : Continuous (fun c : ℝ => ((a, b), c)))
    refine intervalIntegral.integral_mono_on hb4 (hcv.intervalIntegrable _ _)
      (hcw.intervalIntegrable _ _) ?_
    intro c hc
    rw [Set.mem_Icc] at hc
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hc0 : 0 < c := by linarith
    have hu := profile_argument_bounds ha ha4 hab hb4 hc.1 hc.2
    rw [extendedKernel_eq ha ha4 hab hb4 hc.1 hc.2,
      extendedKernel_eq ha ha4 hab hb4 hc.1 hc.2]
    gcongr
    exact hvw _ hu.1 hu.2
  have hdouble : ∀ g : ℝ → ℝ, Continuous (fun u : ℝ => g (max 1 u)) →
      Continuous (fun p : ℝ × ℝ => ∫ c in p.2..(1 / 4 : ℝ), extendedKernel g p.1 p.2 c) := by
    intro g hg
    exact continuous_integral_bounds (X := ℝ × ℝ)
      (f := fun p c => extendedKernel g p.1 p.2 c)
      (extendedKernel_continuous hg) (fun p => p.2) (fun _ => (1 / 4 : ℝ)) continuous_snd continuous_const
  have hbcont : ∀ g : ℝ → ℝ, Continuous (fun u : ℝ => g (max 1 u)) → ∀ a : ℝ,
      Continuous fun b : ℝ => ∫ c in b..(1 / 4 : ℝ), extendedKernel g a b c := by
    intro g hg a
    exact continuous_integral_bounds (X := ℝ)
      (f := fun b c => extendedKernel g a b c)
      ((extendedKernel_continuous hg).comp
        (by fun_prop : Continuous (fun q : ℝ × ℝ => ((a, q.1), q.2))))
      (fun b => b) (fun _ => (1 / 4 : ℝ)) continuous_id continuous_const
  have hacont : ∀ g : ℝ → ℝ, Continuous (fun u : ℝ => g (max 1 u)) →
      Continuous fun a : ℝ =>
        ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), extendedKernel g a b c := by
    intro g hg
    exact continuous_integral_bounds (X := ℝ)
      (f := fun a b => ∫ c in b..(1 / 4 : ℝ), extendedKernel g a b c)
      (hdouble g hg)
      (fun a => a) (fun _ => (1 / 4 : ℝ)) continuous_id continuous_const
  have hmid : ∀ a : ℝ, (1 / 10 : ℝ) ≤ a → a ≤ 1 / 4 →
      (∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), extendedKernel v a b c) ≤
        ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), extendedKernel w a b c := by
    intro a ha ha4
    refine intervalIntegral.integral_mono_on ha4 ((hbcont v hv a).intervalIntegrable _ _)
      ((hbcont w hw a).intervalIntegrable _ _) ?_
    intro b hb
    rw [Set.mem_Icc] at hb
    exact hinner a b ha ha4 hb.1 hb.2
  rw [hrewrite v hv, hrewrite w hw]
  exact intervalIntegral.integral_mono_on (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4)
    ((hacont v hv).intervalIntegrable _ _) ((hacont w hw).intervalIntegrable _ _)
    (fun a ha => by
      rw [Set.mem_Icc] at ha
      exact hmid a ha.1 ha.2)

/-- LEAF. Recovery obligation.  The paper coefficient is bounded by the exact notebook envelope without numerics.
MMS page 12 first paragraph and footnote 3. CONDITIONAL ON buchstabModel_tail. -/
theorem buchstab_coefficient_le :
    4 * buchstabModel 4 + profileIntegral buchstabModel ≤
      4 * referenceEnvelope 4 + profileIntegral referenceEnvelope := by
  have hp := buchstabModel_le_envelope (u := 4) (by norm_num) (by norm_num)
  have hi := profileIntegral_mono (buchstabStage_continuous_clamp 8)
    referenceEnvelope_continuous_clamp (fun u hu hu7 => buchstabModel_le_envelope hu hu7)
  change profileIntegral buchstabModel ≤ profileIntegral referenceEnvelope at hi
  linarith

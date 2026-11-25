/-
PREP 2026-11-21, KL-cited-p2 deepening pass. Cuts four open leaves of
Prep1121KLMajorArc.lean, the major arc block of Task628, into smaller pieces.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 5 to 7, displays 17 to 28.

* major_decomp, page 7 display 28 first line. Cut into the inclusion M0 in M,
  PROVED here, the integrability of the three integrands of the period, PROVED,
  and the four term algebra, PROVED here from the two.
* T1_bound, page 6 display 22 for j = 1. Cut into the trivial bound Y + 1 and
  the decay bound C / |beta| from display 21 by partial summation. The case
  split at Y |beta| = 1 is PROVED here.
* T2_bound, page 6 display 22 for j = 2. Cut the same way into the trivial
  bound C Y^(1/2) and the Kuzmin Landau decay C / (Y^(1/2) |beta|).
* bound24, page 6 display 24. Cut into the mean value of display 17 for S1,
  the mean square of S2* over m0 from the Gauss sum bound and display 22, and
  Cauchy's inequality. The final arithmetic is PROVED here.

Each final result below admits no step of its own and proves the exact
statement of the parent leaf. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc
import LeanLab.KumchevLiu2007.Decomp129

namespace LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ## major_decomp -/

/-- PROVED. P0088 page 6 display 23: in the block range M0 lies in M, since
Q0 = Y P^(-3) is at least Q = H/P when H is at most Y P^(-4) and P is at least one. -/
theorem arcs_subset {X ε B H : ℝ} (hX : 3 ≤ X) (hB : 0 < B)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) :
    majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B) ⊆
      majorArcs H (Real.log X ^ B) := by
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hP : 0 < Real.log X ^ B := by linarith
  have hHpos : 0 < H :=
    lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hXpos _) (zpow_pos hP _)) hlo
  have hY : 0 ≤ windowY X ε := Real.rpow_nonneg hXpos.le _
  have h42 : (Real.log X ^ B) ^ (-4 : ℤ) ≤ (Real.log X ^ B) ^ (-2 : ℤ) :=
    zpow_le_zpow_right₀ hP1 (by norm_num)
  have hH2 : H ≤ windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) :=
    hhi.trans (mul_le_mul_of_nonneg_left h42 hY)
  have hinv : (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ ≤
      (H / Real.log X ^ B)⁻¹ :=
    inv_anti₀ (div_pos hHpos hP) (div_le_div_of_nonneg_right hH2 hP.le)
  rintro α ⟨q, hq1, hqP, a, hcop, hclose⟩
  exact ⟨q, hq1, hqP, a, hcop, hclose.trans hinv⟩

/-- PROVED. A trigonometric polynomial with coefficients w is bounded by the sum of
the norms of its coefficients. -/
theorem trig_norm_le (S : Finset ℕ) (w : ℕ → ℂ) (k : ℕ → ℤ) (x : AddCircle (1 : ℝ)) :
    ‖∑ m ∈ S, w m * fourier (k m) x‖ ≤ ∑ m ∈ S, ‖w m‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have h1 : ‖fourier (k m) x‖ = 1 := Circle.norm_coe _
  rw [norm_mul, h1, mul_one]

/-- PROVED. A trigonometric polynomial in the real variable is continuous. -/
theorem trig_continuous (S : Finset ℕ) (w : ℕ → ℂ) (k : ℕ → ℤ) :
    Continuous (fun α : ℝ => ∑ m ∈ S, w m * fourier (k m) (α : AddCircle (1 : ℝ))) :=
  continuous_finsetSum _ fun _ _ =>
    continuous_const.mul ((fourier _).continuous.comp (AddCircle.continuous_mk' 1))

/-- PROVED. A finite sum of indicators of measurable sets times continuous bounded
functions is measurable and bounded. -/
theorem indicator_sum_props {ι : Type*} (s : Finset ι) (A : ι → Set ℝ)
    (hA : ∀ v, MeasurableSet (A v)) (g : ι → ℝ → ℂ) (hg : ∀ v, Continuous (g v))
    (K : ι → ℝ) (hK : ∀ v x, ‖g v x‖ ≤ K v) :
    Measurable (fun α => ∑ v ∈ s, (A v).indicator (g v) α) ∧
      ∀ α, ‖∑ v ∈ s, (A v).indicator (g v) α‖ ≤ ∑ v ∈ s, K v := by
  refine ⟨Finset.measurable_sum s fun v _ => (hg v).measurable.indicator (hA v), fun α => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  exact (norm_indicator_le_norm_self _ _).trans (hK v α)

/-- PROVED. P0088 page 4 display 15: each closed arc is measurable. -/
theorem measurableSet_arc (R : ℝ) (v : ℕ × ℕ) : MeasurableSet (arc R v) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- PROVED. S1* is measurable and bounded. -/
theorem S1star_props (X Y H P : ℝ) :
    Measurable (S1star X Y H P) ∧ ∃ c : ℝ, ∀ α, ‖S1star X Y H P α‖ ≤ c := by
  have h := indicator_sum_props (arcPairs P) (arc (H / P)) (measurableSet_arc _)
    (fun v α => ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
      T1 X Y (α - v.2 / v.1))
    (fun v => continuous_const.mul ((trig_continuous _ _ _).comp (continuous_sub_right _)))
    (fun v => ‖((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ)‖ *
      ∑ m ∈ primeWindow X Y, ‖(((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖)
    (fun v x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (trig_norm_le _ _ _ _) (norm_nonneg _))
  exact ⟨h.1, _, h.2⟩

/-- PROVED. S2* is measurable and bounded. -/
theorem S2star_props (Y H P : ℝ) :
    Measurable (S2star Y H P) ∧ ∃ c : ℝ, ∀ α, ‖S2star Y H P α‖ ≤ c := by
  have h := indicator_sum_props (arcPairs P) (arc (H / P)) (measurableSet_arc _)
    (fun v α => U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P (α - v.2 / v.1))
    (fun v => continuous_const.mul ((trig_continuous _ _ _).comp (continuous_sub_right _)))
    (fun v => ‖U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ)‖ *
      ∑ m ∈ squareWindow Y,
        ‖(((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ))‖)
    (fun v x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (trig_norm_le _ _ _ _) (norm_nonneg _))
  exact ⟨h.1, _, h.2⟩

theorem cont_e (n : ℕ) : Continuous (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))) :=
  (fourier _).continuous.comp (AddCircle.continuous_mk' 1)

theorem cont_S1 (X Y : ℝ) : Continuous (fun α : ℝ => primeSum X Y α) := by
  unfold primeSum
  exact continuous_finsetSum _ fun m _ => (fourier _).continuous.comp (AddCircle.continuous_mk' 1)

theorem cont_S2 (Y P : ℝ) : Continuous (fun α : ℝ => roughSum Y P α) := by
  unfold roughSum
  exact trig_continuous _ _ _

/-- PROVED. P0088 page 7 display 28, the integrability used in the four term split.
On the period (0, 1] the integrands e(-n alpha) S1 S2, e(-n alpha) S1 S2* and
e(-n alpha) S1* S2* are integrable: S1 and S2 are trigonometric polynomials and
S1*, S2* are finite sums of indicators of closed arcs times continuous functions. -/
theorem major_integrands_integrable (X Y H P : ℝ) (n : ℕ) :
    IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        (primeSum X Y α * roughSum Y P α)) (Set.Ioc 0 1) ∧
    IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        (primeSum X Y α * S2star Y H P α)) (Set.Ioc 0 1) ∧
    IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        (S1star X Y H P α * S2star Y H P α)) (Set.Ioc 0 1) := by
  obtain ⟨m1, c1, b1⟩ := S1star_props X Y H P
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  refine ⟨((cont_e n).mul ((cont_S1 X Y).mul (cont_S2 Y P))).integrableOn_Ioc, ?_, ?_⟩
  · have he : (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        (primeSum X Y α * S2star Y H P α)) = fun α => S2star Y H P α *
          (fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * primeSum X Y α) := by
      funext α; ring
    rw [he]
    exact Integrable.bdd_mul ((cont_e n).mul (cont_S1 X Y)).integrableOn_Ioc
      m2.aestronglyMeasurable (Filter.Eventually.of_forall b2)
  · have he : (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
        (S1star X Y H P α * S2star Y H P α)) = fun α => S2star Y H P α *
          (S1star X Y H P α * fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))) := by
      funext α; ring
    rw [he]
    have hi : IntegrableOn (fun α : ℝ => S1star X Y H P α *
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))) (Set.Ioc 0 1) :=
      Integrable.bdd_mul (cont_e n).integrableOn_Ioc m1.aestronglyMeasurable
        (Filter.Eventually.of_forall b1)
    exact Integrable.bdd_mul hi m2.aestronglyMeasurable (Filter.Eventually.of_forall b2)

/-- PROVED. P0088 page 7 display 28 first line, for any parameters with M0 in M,
from the integrability leaf. -/
theorem major_decomp_general (X Y H P : ℝ) (n : ℕ)
    (hsub : majorArcs (Y * P ^ (-2 : ℤ)) P ⊆ majorArcs H P) :
    majorIntegral X Y H P n =
      termA X Y H P n + termB X Y H P n + termC X Y H P n + termD X Y H P n := by
  obtain ⟨hf, hg, hh⟩ := major_integrands_integrable X Y H P n
  set I : Set ℝ := Set.Ioc 0 1
  set M := majorArcs H P
  set M0 := majorArcs (Y * P ^ (-2 : ℤ)) P
  have hMm : MeasurableSet M := measurableSet_majorArcs H P
  have hM0m : MeasurableSet M0 := measurableSet_majorArcs _ P
  have hIM : I ∩ M ⊆ I := Set.inter_subset_left
  have hIM0 : I ∩ M0 ⊆ I := Set.inter_subset_left
  have hB : termB X Y H P n =
      (∫ α in I ∩ M, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (primeSum X Y α * roughSum Y P α)) -
        ∫ α in I ∩ M, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (primeSum X Y α * S2star Y H P α) := by
    rw [termB, ← integral_sub (hf.mono_set hIM) (hg.mono_set hIM)]
    congr 1
    ext α
    ring
  have hD : termD X Y H P n =
      (∫ α in I ∩ M0, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (primeSum X Y α * S2star Y H P α)) -
        ∫ α in I ∩ M0, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          (S1star X Y H P α * S2star Y H P α) := by
    rw [termD, ← integral_sub (hg.mono_set hIM0) (hh.mono_set hIM0)]
    congr 1
    ext α
    ring
  have hsplit := integral_inter_add_sdiff hM0m (hg.mono_set hIM)
  have e1 : I ∩ M ∩ M0 = I ∩ M0 := by
    ext α
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hsub h3⟩, h3⟩
  have e2 : (I ∩ M) \ M0 = I ∩ (M \ M0) := by
    ext α
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [e1, e2] at hsplit
  rw [hB, hD, termA, termC, majorIntegral]
  rw [← hsplit]
  ring

/-- The exact statement of Prep1121KLMajor.major_decomp, from arcs_subset and
major_decomp_general. No sorry of its own. -/
theorem major_decomp_of_pieces :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) → ∀ n : ℕ,
        majorIntegral X (windowY X ε) H (Real.log X ^ B) n =
          termA X (windowY X ε) H (Real.log X ^ B) n +
          termB X (windowY X ε) H (Real.log X ^ B) n +
          termC X (windowY X ε) H (Real.log X ^ B) n +
          termD X (windowY X ε) H (Real.log X ^ B) n := by
  intro B hB ε _ _
  refine ⟨3, fun X H hX hlo hhi n => ?_⟩
  exact major_decomp_general _ _ _ _ n (arcs_subset hX hB hlo hhi)

example : type_of% @major_decomp := major_decomp_of_pieces

/-! ## T1_bound -/

/-- PROVED. For eps at most 7/18 the window Y = X^(7/12 + eps/2) is at least one
when X is at least one. -/
theorem windowY_ge_one {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) : 1 ≤ windowY X ε :=
  Real.one_le_rpow hX (by linarith)


/-- PROVED. Every weight 1/log m of T1 is at most 2 in absolute value: it is 0 for
m at most 1 and log m is at least log 2 above 1/2 otherwise. -/
theorem inv_log_nat_le_two (m : ℕ) : ‖(((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp
  · have h2 : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm)
    have hl : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hpos : 0 < Real.log (m : ℝ) := by linarith
    rw [abs_of_pos (by positivity), div_le_iff₀ hpos]
    linarith

/-- PROVED. For X at least one and eps at most 7/18 the window Y is at most X. -/
theorem windowY_le {X ε : ℝ} (hX : 1 ≤ X) (hε' : ε ≤ 7 / 18) : windowY X ε ≤ X := by
  unfold windowY
  calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = X := Real.rpow_one X

/-- PROVED. P0088 page 6 display 22 for j = 1, the trivial bound: weights at most 2
and at most 2Y integers in the window [X - Y, X). -/
theorem T1_trivial :
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ X : ℝ, 1 ≤ X → ∀ β : ℝ,
      ‖T1 X (windowY X ε) β‖ ≤ 4 * windowY X ε := by
  intro ε hε hε' X hX β
  have hc := primeWindow_card_le (sub_nonneg.mpr (windowY_le hX hε'))
    (windowY_ge_one hX hε)
  refine (trig_norm_le (primeWindow X (windowY X ε)) _ (fun m => (m : ℤ)) _).trans ?_
  calc _ ≤ ∑ _m ∈ primeWindow X (windowY X ε), (2 : ℝ) :=
        Finset.sum_le_sum fun m _ => inv_log_nat_le_two m
    _ = 2 * ((primeWindow X (windowY X ε)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * windowY X ε := by linarith

/-- LEAF: P0088 page 6 display 22 for j = 1, the decay bound for beta away from
zero: display 21 for f1 = 1/log u, partial summation against the geometric sum
bound 1/(2|beta|), with the weights decreasing and at most one. -/
theorem T1_decay :
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ β : ℝ, 0 < |β| → |β| ≤ 1 / 2 →
        ‖T1 X (windowY X ε) β‖ ≤ C / |β| := by
  intro ε hε hε'
  obtain ⟨C, X0, hC, hbound⟩ := Prep1121KLMajor.T1_bound ε hε hε'
  refine ⟨C, max X0 3, hC, ?_⟩
  intro X hX β hβ hβ'
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hden : 0 < 1 + windowY X ε * |β| := by positivity
  refine (hbound X ((le_max_left _ _).trans hX) β hβ').trans ?_
  apply (div_le_div_iff₀ hden hβ).mpr
  nlinarith

/-- PROVED. The split at Y |beta| = 1 behind display 22: a bound a Y^s in the
range Y |beta| at most one and b Y^s / (Y |beta|) beyond it give
(2a + 2b) Y^s / (1 + Y |beta|). -/
theorem split_bound {N W Y β a b : ℝ} (hY : 0 < Y) (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (h1 : Y * |β| ≤ 1 → N ≤ a * W) (h2 : 1 < Y * |β| → N ≤ b * W / (Y * |β|)) :
    N ≤ (2 * a + 2 * b) * W / (1 + Y * |β|) := by
  have hYb : 0 ≤ Y * |β| := mul_nonneg hY.le (abs_nonneg β)
  have hden : 0 < 1 + Y * |β| := by linarith
  rw [le_div_iff₀ hden]
  by_cases hc : Y * |β| ≤ 1
  · have := h1 hc
    nlinarith [mul_nonneg hb hW, mul_nonneg ha hW, mul_nonneg (mul_nonneg hb hW) hYb]
  · have hc' : 1 < Y * |β| := lt_of_not_ge hc
    have hpos : 0 < Y * |β| := by linarith
    have := h2 hc'
    rw [le_div_iff₀ hpos] at this
    nlinarith [mul_nonneg ha hW, mul_nonneg hb hW, mul_nonneg (mul_nonneg ha hW) hYb]

/-- The exact statement of Prep1121KLMajor.T1_bound, from T1_trivial and
T1_decay. No sorry of its own. -/
theorem T1_bound_of_pieces : T1BoundProp := by
  intro ε hε hε'
  obtain ⟨C, X2, hC, k2⟩ := T1_decay ε hε hε'
  refine ⟨2 * 4 + 2 * C, max X2 1, by positivity, fun X hX β hβ => ?_⟩
  have hXb : X2 ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hY1 := windowY_ge_one hX1 hε
  have hY : 0 < windowY X ε := by linarith
  refine split_bound hY hY.le (by norm_num) hC.le (fun _ => ?_) (fun hc => ?_)
  · exact T1_trivial ε hε hε' X hX1 β
  · have hb : 0 < |β| := by
      by_contra h0
      have : |β| = 0 := le_antisymm (not_lt.mp h0) (abs_nonneg β)
      rw [this, mul_zero] at hc
      linarith
    refine (k2 X hXb β hb hβ).trans (le_of_eq ?_)
    field_simp

example : type_of% @T1_bound := T1_bound_of_pieces

/-- `‖e x - e y‖ ≤ 2π|x - y|`. -/
private lemma norm_e_sub_le (x y : ℝ) :
    ‖LeanLab.PNTPort.LargeSieve.e x - LeanLab.PNTPort.LargeSieve.e y‖ ≤ 2 * π * |x - y| := by
  have h1 : LeanLab.PNTPort.LargeSieve.e x - LeanLab.PNTPort.LargeSieve.e y =
      LeanLab.PNTPort.LargeSieve.e y * (LeanLab.PNTPort.LargeSieve.e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    ring_nf
  rw [h1, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
  have h2 : LeanLab.PNTPort.LargeSieve.e (x - y) - 1 =
      Complex.exp (I * ((2 * π * (x - y) : ℝ) : ℂ)) - 1 := rfl
  rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h3 : 2 * π * (x - y) / 2 = π * (x - y) := by ring
  rw [h3, Real.norm_eq_abs, abs_mul]
  have h4 : |(2 : ℝ)| = 2 := by norm_num
  rw [h4]
  have hs := Real.abs_sin_le_abs (x := π * (x - y))
  have hp : (0 : ℝ) ≤ π := pi_pos.le
  calc 2 * |Real.sin (π * (x - y))| ≤ 2 * |π * (x - y)| := by linarith
    _ = 2 * π * |x - y| := by rw [abs_mul, abs_of_nonneg hp]; ring

/-- On `(0, 2/3]` one has `2t ≤ ‖e t - 1‖`. -/
private lemma two_mul_le_norm_e_sub_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 2 / 3) :
    2 * t ≤ ‖LeanLab.PNTPort.LargeSieve.e t - 1‖ := by
  have hdist : t / 2 ≤ LeanLab.PNTPort.LargeSieve.dist0 t := by
    have hmin := LeanLab.PNTPort.Vinogradov.dist0_ge (x := t) (y := 0) (t := 0) h0.le
      (by linarith)
    simp only [abs_zero, sub_zero, add_zero, Int.cast_zero] at hmin
    rcases le_or_gt t (1 - t) with h | h
    · rw [min_eq_left h] at hmin; linarith
    · rw [min_eq_right h.le] at hmin; linarith
  have h4 := LeanLab.PNTPort.LargeSieve.four_dist0_le t
  linarith

private lemma inv_sub_inv_eq (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    y⁻¹ - x⁻¹ = (x - y) / (x * y) := by
  field_simp

/-- Kusmin-Landau: a sum `∑_{j<N} e(θ j)` whose first differences are increasing and
lie in `[δ, 4δ] ⊂ (0, 2/3]` is at most `6/δ`. -/
private theorem sum_e_le_of_mono_steps {θ : ℕ → ℝ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ j, j < N → 0 < θ (j + 1) - θ j)
    (hup : ∀ j, j < N → θ (j + 1) - θ j ≤ 2 / 3)
    (hlo : ∀ j, j < N → δ ≤ θ (j + 1) - θ j)
    (hhi : ∀ j, j < N → θ (j + 1) - θ j ≤ 4 * δ)
    (hmono : ∀ j, j + 1 < N → θ (j + 1) - θ j ≤ θ (j + 2) - θ (j + 1)) :
    ‖∑ j ∈ Finset.range N, LeanLab.PNTPort.LargeSieve.e (θ j)‖ ≤ 8 / δ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  set Δ : ℕ → ℝ := fun j => θ (j + 1) - θ j with hΔdef
  set z : ℕ → ℂ := fun j => LeanLab.PNTPort.LargeSieve.e (θ j) with hzdef
  set c : ℕ → ℂ := fun j => (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1)⁻¹ with hcdef
  have hΔpos : ∀ j, j < N → 0 < Δ j := fun j hj => hpos j hj
  have hΔup : ∀ j, j < N → Δ j ≤ 2 / 3 := fun j hj => hup j hj
  have hΔlo : ∀ j, j < N → δ ≤ Δ j := fun j hj => hlo j hj
  have hΔhi : ∀ j, j < N → Δ j ≤ 4 * δ := fun j hj => hhi j hj
  have hΔmono : ∀ j, j + 1 < N → Δ j ≤ Δ (j + 1) := fun j hj => hmono j hj
  have hzn : ∀ j, ‖z j‖ = 1 := fun j => LeanLab.PNTPort.LargeSieve.norm_e (θ j)
  have hxlow : ∀ j, j < N → 2 * δ ≤ ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖ := by
    intro j hj
    have h1 := two_mul_le_norm_e_sub_one (hΔpos j hj) (hΔup j hj)
    have h2 := hΔlo j hj
    linarith
  have hxne : ∀ j, j < N → LeanLab.PNTPort.LargeSieve.e (Δ j) - 1 ≠ 0 := by
    intro j hj h
    have h1 := hxlow j hj
    rw [h, norm_zero] at h1
    linarith
  have hkey : ∀ j, j < N → z j = c j * (z (j + 1) - z j) := by
    intro j hj
    have hstep : z (j + 1) = z j * LeanLab.PNTPort.LargeSieve.e (Δ j) := by
      show LeanLab.PNTPort.LargeSieve.e (θ (j + 1)) =
        LeanLab.PNTPort.LargeSieve.e (θ j) * LeanLab.PNTPort.LargeSieve.e (Δ j)
      rw [← LeanLab.PNTPort.LargeSieve.e_add]
      congr 1
      simp only [hΔdef]
      ring
    rw [hstep]
    show z j = (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1)⁻¹ *
      (z j * LeanLab.PNTPort.LargeSieve.e (Δ j) - z j)
    rw [show z j * LeanLab.PNTPort.LargeSieve.e (Δ j) - z j
      = (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1) * z j by ring,
      ← mul_assoc, inv_mul_cancel₀ (hxne j hj), one_mul]
  have htele : ∀ n : ℕ,
      ∑ j ∈ Finset.range (n + 1), c j * (z (j + 1) - z j) =
        c n * z (n + 1) - c 0 * z 0 -
          ∑ j ∈ Finset.range n, (c (j + 1) - c j) * z (j + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  have hsum_eq : ∑ j ∈ Finset.range N, z j =
      c (N - 1) * z N - c 0 * z 0 -
        ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1) := by
    have h := htele (N - 1)
    rw [Nat.sub_add_cancel hN] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j hj => hkey j (Finset.mem_range.mp hj)
  have hcbd : ∀ j, j < N → ‖c j‖ ≤ 1 / (2 * δ) := by
    intro j hj
    have h1 := hxlow j hj
    have h2 : ‖c j‖ = (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖)⁻¹ := by
      simp only [hcdef, norm_inv]
    rw [h2]
    have := inv_anti₀ (by linarith : (0 : ℝ) < 2 * δ) h1
    calc (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖)⁻¹ ≤ (2 * δ)⁻¹ := this
      _ = 1 / (2 * δ) := by rw [one_div]
  have hcdiff : ∀ j, j + 1 < N →
      ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
        (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) := by
    intro j hj
    rw [norm_mul, hzn, mul_one]
    have hle : Δ j ≤ Δ (j + 1) := hΔmono j hj
    have halg : c (j + 1) - c j =
        (LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))) /
          ((LeanLab.PNTPort.LargeSieve.e (Δ j) - 1) *
            (LeanLab.PNTPort.LargeSieve.e (Δ (j + 1)) - 1)) := by
      simp only [hcdef]
      rw [inv_sub_inv_eq _ _ (hxne j (by omega)) (hxne (j + 1) hj)]
      ring_nf
    rw [halg, norm_div, norm_mul]
    have hn : ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))‖
        ≤ 2 * π * (Δ (j + 1) - Δ j) := by
      have h := norm_e_sub_le (Δ j) (Δ (j + 1))
      have habs : |Δ j - Δ (j + 1)| = Δ (j + 1) - Δ j := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs] at h
      exact h
    have hd1 := hxlow j (by omega)
    have hd2 := hxlow (j + 1) hj
    have hstep : ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))‖ /
        (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖ *
          ‖LeanLab.PNTPort.LargeSieve.e (Δ (j + 1)) - 1‖) ≤
        (2 * π * (Δ (j + 1) - Δ j)) / ((2 * δ) * (2 * δ)) := by
      apply div_le_div₀ (by positivity) hn (by positivity)
      exact mul_le_mul hd1 hd2 (by linarith) (by positivity)
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have htelesc : ∑ j ∈ Finset.range (N - 1), (Δ (j + 1) - Δ j) = Δ (N - 1) - Δ 0 :=
    Finset.sum_range_sub Δ (N - 1)
  have htail : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
      (3 * π / 2) / δ := by
    have h1 : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
        ∑ j ∈ Finset.range (N - 1), (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) :=
      Finset.sum_le_sum fun i hi => hcdiff i (by have := Finset.mem_range.mp hi; omega)
    have h2 : ∑ j ∈ Finset.range (N - 1), (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) =
        (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) := by
      rw [← Finset.mul_sum, htelesc]
    have h3 : Δ (N - 1) - Δ 0 ≤ 3 * δ := by
      have h1 := hΔhi (N - 1) (by omega)
      have h2 := hΔlo 0 hN
      linarith
    have h4 : (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) ≤ (3 * π / 2) / δ := by
      have h1 : (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) ≤ (π / 2) / δ ^ 2 * (3 * δ) := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
      have h2 : (π / 2) / δ ^ 2 * (3 * δ) = (3 * π / 2) / δ := by
        field_simp
      linarith
    linarith
  have hN1 : ‖c (N - 1)‖ ≤ 1 / (2 * δ) := hcbd (N - 1) (by omega)
  have h0b : ‖c 0‖ ≤ 1 / (2 * δ) := hcbd 0 hN
  have hzN : ‖z N‖ = 1 := hzn N
  have hz0 : ‖z 0‖ = 1 := hzn 0
  rw [hsum_eq]
  have htri : ‖c (N - 1) * z N - c 0 * z 0 -
      ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
      ‖c (N - 1)‖ + ‖c 0‖ + ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ := by
    have ha : ‖c (N - 1) * z N - c 0 * z 0 -
        ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
        ‖c (N - 1) * z N - c 0 * z 0‖ +
          ‖∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ := norm_sub_le _ _
    have hb : ‖c (N - 1) * z N - c 0 * z 0‖ ≤ ‖c (N - 1)‖ + ‖c 0‖ := by
      have := norm_sub_le (c (N - 1) * z N) (c 0 * z 0)
      rwa [norm_mul, norm_mul, hzN, hz0, mul_one, mul_one] at this
    have hc : ‖∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
        ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ := norm_sum_le _ _
    linarith
  have hfin : ‖c (N - 1)‖ + ‖c 0‖ +
      ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤ 8 / δ := by
    have h1 : 1 / (2 * δ) + 1 / (2 * δ) = 1 / δ := by field_simp; norm_num
    have h2 : 3 * π / 2 / δ ≤ 6 / δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      nlinarith [pi_lt_four]
    have hB : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤ 6 / δ :=
      htail.trans h2
    have hC : 1 / δ + 6 / δ ≤ 8 / δ := by
      have h7 : (7 : ℝ) / δ ≤ 8 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
      have he : 1 / δ + 6 / δ = (7 : ℝ) / δ := by field_simp; norm_num
      rw [he]
      exact h7
    linarith
  linarith

/-- Abel: a monotone nonnegative weight against a sequence whose partial sums are
bounded by `B` costs twice the last weight times `B`. -/
private theorem norm_sum_mono_weight_le {f : ℕ → ℂ} {w : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (hw0 : ∀ j, 0 ≤ w j) (hmono : ∀ j, j < N → w j ≤ w (j + 1))
    (hB : ∀ k, k ≤ N → ‖∑ j ∈ Finset.range k, f j‖ ≤ B) :
    ‖∑ j ∈ Finset.range N, (w j : ℂ) * f j‖ ≤ 2 * w (N - 1) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    have h1 := hw0 0
    nlinarith
  set A : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, f j with hA
  have hid : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (w j : ℂ) * f j =
      (w n : ℂ) * A (n + 1) +
        ∑ j ∈ Finset.range n, ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, hA]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hf : f (m + 1) = A (m + 2) - A (m + 1) := by
        simp only [hA, Finset.sum_range_succ]
        ring
      rw [hf]
      ring
  have hid2 := hid (N - 1)
  rw [Nat.sub_add_cancel hN] at hid2
  rw [hid2]
  have h1 : ‖(w (N - 1) : ℂ) * A N‖ ≤ w (N - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 (N - 1))]
    exact mul_le_mul_of_nonneg_left (hB N le_rfl) (hw0 (N - 1))
  have h2 : ‖∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ ≤
      (w (N - 1) - w 0) * B := by
    have hterm : ∀ j ∈ Finset.range (N - 1),
        ‖((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ ≤ (w (j + 1) - w j) * B := by
      intro j hj
      have hjN : j < N := by
        have := Finset.mem_range.mp hj
        omega
      have hle := hmono j hjN
      have he : ((w j : ℂ) - (w (j + 1) : ℂ)) = ((w j - w (j + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : w j - w (j + 1) ≤ 0), neg_sub]
      exact mul_le_mul_of_nonneg_left (hB (j + 1) (by omega)) (by linarith)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
    rw [← Finset.sum_mul, Finset.sum_range_sub w (N - 1)]
  have h3 : (w (N - 1) - w 0) ≤ w (N - 1) := by
    have := hw0 0
    linarith
  have h4 : 0 ≤ w (N - 1) := hw0 _
  calc ‖(w (N - 1) : ℂ) * A N +
        ∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖
      ≤ ‖(w (N - 1) : ℂ) * A N‖ +
        ‖∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ :=
        norm_add_le _ _
    _ ≤ w (N - 1) * B + (w (N - 1) - w 0) * B := add_le_add h1 h2
    _ ≤ 2 * w (N - 1) * B := by nlinarith

private lemma sqrt_lt_self' {u : ℝ} (h1 : 1 < u) : Real.sqrt u < u := by
  have hpos : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
  nlinarith

private lemma hasDerivAt_f2antideriv {z0 u t : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u)
    (ht : t ∈ Set.uIcc z0 (Real.sqrt u)) :
    HasDerivAt (fun s => Real.log (Real.log s / (Real.log u - Real.log s)) / Real.log u)
      (1 / (t * Real.log t * Real.log (u / t))) t := by
  have hz0pos : 0 < z0 := by linarith
  have htsqrt : z0 ≤ Real.sqrt u := by
    calc z0 = Real.sqrt (z0 ^ 2) := (Real.sqrt_sq hz0pos.le).symm
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hz0u
  have hu1 : 1 < u := by nlinarith
  have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
  obtain ⟨ht1, ht2⟩ := htI
  have htpos : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hloglt : Real.log t < Real.log u := by
    apply Real.log_lt_log htpos
    exact lt_of_le_of_lt ht2 (sqrt_lt_self' hu1)
  have hdiff : 0 < Real.log u - Real.log t := by linarith
  have hldiv : Real.log (u / t) = Real.log u - Real.log t :=
    Real.log_div (by linarith) (ne_of_gt htpos)
  have h1 : HasDerivAt (fun s => Real.log s) (1 / t) t := by
    simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt htpos)
  have h2 : HasDerivAt (fun s => Real.log u - Real.log s) (-(1 / t)) t := by
    have h := (hasDerivAt_const (x := t) (c := Real.log u)).sub h1
    convert h using 1
    ring
  have h3 : HasDerivAt (fun s => Real.log s / (Real.log u - Real.log s))
      ((1 / t * (Real.log u - Real.log t) - Real.log t * (-(1 / t))) /
        (Real.log u - Real.log t) ^ 2) t :=
    h1.div h2 (ne_of_gt hdiff)
  have h4 : HasDerivAt (fun s => Real.log (Real.log s / (Real.log u - Real.log s)))
      (((1 / t * (Real.log u - Real.log t) - Real.log t * (-(1 / t))) /
        (Real.log u - Real.log t) ^ 2) / (Real.log t / (Real.log u - Real.log t))) t :=
    h3.log (by positivity)
  have h5 := h4.const_mul ((Real.log u)⁻¹)
  have hfun : (fun s => Real.log (Real.log s / (Real.log u - Real.log s)) / Real.log u)
      = fun y => (Real.log u)⁻¹ * Real.log (Real.log y / (Real.log u - Real.log y)) := by
    funext s
    ring
  rw [hfun]
  convert h5 using 1
  rw [hldiv]
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  field_simp
  ring

private theorem f2_integral_closed {z0 u : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u) :
    ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
      = Real.log ((Real.log u - Real.log z0) / Real.log z0) / Real.log u := by
  have hz0pos : 0 < z0 := by linarith
  have hu1 : 1 < u := by nlinarith
  have htsqrt : z0 ≤ Real.sqrt u := by
    calc z0 = Real.sqrt (z0 ^ 2) := (Real.sqrt_sq hz0pos.le).symm
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hz0u
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      volume z0 (Real.sqrt u) := by
    have hlogc : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc z0 (Real.sqrt u)) :=
      Real.continuousOn_log.mono (by
        intro t ht
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ne_of_gt (by linarith [htsqrt, hz0pos])
        · exact ne_of_gt (by linarith [htsqrt, hz0pos]))
    have hcont : ContinuousOn (fun t => 1 / (t * Real.log t * (Real.log u - Real.log t)))
        (Set.uIcc z0 (Real.sqrt u)) := by
      apply ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_id.mul hlogc).mul (continuousOn_const.sub hlogc)
      · intro t ht
        have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
          rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, h2⟩
          · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
        have htpos : 0 < t := by linarith [htI.1]
        have hloglt : Real.log t < Real.log u :=
          Real.log_lt_log htpos (lt_of_le_of_lt htI.2 (sqrt_lt_self' hu1))
        have hlogt : 0 < Real.log t := Real.log_pos (by linarith [htI.1])
        have h3 : 0 < Real.log u - Real.log t := by linarith
        apply ne_of_gt
        have : 0 < t * Real.log t * (Real.log u - Real.log t) := by positivity
        exact this
    refine (hcont.congr ?_).intervalIntegrable
    intro t ht
    simp only
    rw [Real.log_div (ne_of_gt (by linarith [htsqrt, hz0pos])) (by
      have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
      have : 0 < t := by linarith [htI.1]
      linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_f2antideriv hz0 hz0u ht) hint]
  have hlogsqrt : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt (by linarith)
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  have ha : Real.log z0 ≠ 0 := ne_of_gt (Real.log_pos hz0)
  have htop : Real.log (Real.log (Real.sqrt u) / (Real.log u - Real.log (Real.sqrt u))) = 0 := by
    rw [hlogsqrt, show Real.log u - Real.log u / 2 = Real.log u / 2 by ring,
      div_self (by positivity)]
    simp
  have hA : Real.log (Real.log (Real.sqrt u) / (Real.log u - Real.log (Real.sqrt u))) /
      Real.log u = 0 := by rw [htop, zero_div]
  have hpos' : 0 < Real.log u - Real.log z0 := by
    have h3 : 0 < Real.log z0 := Real.log_pos hz0
    have hsq : Real.log (z0 ^ 2) ≤ Real.log u := Real.log_le_log (by positivity) hz0u
    rw [Real.log_pow] at hsq
    norm_num at hsq
    linarith
  have hG : Real.log (Real.log z0 / (Real.log u - Real.log z0)) / Real.log u =
      -(Real.log ((Real.log u - Real.log z0) / Real.log z0) / Real.log u) := by
    have hinv : Real.log z0 / (Real.log u - Real.log z0) =
        ((Real.log u - Real.log z0) / Real.log z0)⁻¹ := by
      field_simp
    rw [hinv, Real.log_inv]
    ring
  rw [hA, zero_sub, hG]
  ring

/-- The weight `f2` of P0088 page 15 in closed form. -/
private theorem f2Weight_eq {z0 u : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u) :
    f2Weight z0 u =
      (1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) / Real.log u := by
  have hu1 : 1 < u := by nlinarith
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  unfold f2Weight
  rw [f2_integral_closed hz0 hz0u]
  field_simp

/-- `(1 + log r)/(1 + r)` is increasing on `[1, 3/2]`. -/
private lemma mono_ratio_log :
    MonotoneOn (fun r : ℝ => (1 + Real.log r) / (1 + r)) (Set.Icc 1 (3 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · -- continuity
    have hlogc : ContinuousOn (fun r : ℝ => Real.log r) (Set.Icc (1:ℝ) (3/2)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        exact ne_of_gt (by linarith [hx.1]))
    exact (continuousOn_const.add hlogc).div (by fun_prop) (by
      intro x hx
      linarith [hx.1])
  · -- differentiability on the interior
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hxpos : 0 < x := by linarith
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · exact (differentiableAt_const _).add (Real.differentiableAt_log (ne_of_gt hxpos))
    · exact differentiableAt_id.const_add 1
    · linarith
  · -- nonnegative derivative
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hxpos : 0 < x := by linarith
    have hdif2 : DifferentiableAt ℝ (fun r : ℝ => (1 + Real.log r)) x := by fun_prop
    have hdif3 : DifferentiableAt ℝ (fun r : ℝ => (1 + r)) x := by fun_prop
    have hden : (1 + x) ≠ 0 := by linarith
    have hderiv : deriv (fun r : ℝ => (1 + Real.log r) / (1 + r)) x
        = ((1 / x) * (1 + x) - (1 + Real.log x)) / (1 + x) ^ 2 := by
      change deriv ((fun r : ℝ => 1 + Real.log r) / (fun r : ℝ => 1 + r)) x = _
      rw [deriv_div hdif2 hdif3 hden]
      simp only [one_div]
      norm_num
    rw [hderiv]
    have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
    have hxle : x ≤ 3 / 2 := by linarith
    have hxge : 1 ≤ x := by linarith
    have hinv : 1 / x ≥ 2 / 3 := by
      rw [ge_iff_le, le_div_iff₀ hxpos]
      nlinarith
    have hkey : 0 ≤ (1 / x) * (1 + x) - (1 + Real.log x) := by nlinarith
    exact div_nonneg hkey (by positivity)

/-- The weight of `T2` is nondecreasing in the argument on the block window. -/
private theorem f2Weight_mono {z0 u v : ℝ} (hz0 : 1 < z0) (hu : z0 ^ 2 ≤ u) (huv : u ≤ v)
    (hv : Real.log v ≤ 5 / 2 * Real.log z0) : f2Weight z0 u ≤ f2Weight z0 v := by
  have hz0pos : 0 < z0 := by linarith
  have ha : 0 < Real.log z0 := Real.log_pos hz0
  have hu1 : 1 < u := by nlinarith
  have hv1 : 1 < v := by linarith
  have hz0v : z0 ^ 2 ≤ v := le_trans hu huv
  have hL1 : 2 * Real.log z0 ≤ Real.log u := by
    have hsq : Real.log (z0 ^ 2) ≤ Real.log u := Real.log_le_log (by positivity) hu
    rw [Real.log_pow] at hsq
    norm_num at hsq
    linarith
  have hL12 : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  rw [f2Weight_eq hz0 hu, f2Weight_eq hz0 hz0v]
  have e1 : (1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) / Real.log u =
      (1 / Real.log z0) * ((1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) /
        (1 + ((Real.log u - Real.log z0) / Real.log z0))) := by
    have h1 : 1 + (Real.log u - Real.log z0) / Real.log z0 = Real.log u / Real.log z0 := by
      field_simp
      ring
    rw [h1]
    field_simp
  have e2 : (1 + Real.log ((Real.log v - Real.log z0) / Real.log z0)) / Real.log v =
      (1 / Real.log z0) * ((1 + Real.log ((Real.log v - Real.log z0) / Real.log z0)) /
        (1 + ((Real.log v - Real.log z0) / Real.log z0))) := by
    have h1 : 1 + (Real.log v - Real.log z0) / Real.log z0 = Real.log v / Real.log z0 := by
      field_simp
      ring
    rw [h1]
    field_simp
  rw [e1, e2]
  have hr1 : (1:ℝ) ≤ (Real.log u - Real.log z0) / Real.log z0 := by
    rw [le_div_iff₀ ha]
    linarith
  have hr2 : (Real.log v - Real.log z0) / Real.log z0 ≤ 3 / 2 := by
    rw [div_le_iff₀ ha]
    linarith
  have hrr : (Real.log u - Real.log z0) / Real.log z0 ≤ (Real.log v - Real.log z0) / Real.log z0 := by
    rw [div_le_div_iff_of_pos_right ha]
    linarith
  have hmem1 : (Real.log u - Real.log z0) / Real.log z0 ∈ Set.Icc (1:ℝ) (3/2) := ⟨hr1, hrr.trans hr2⟩
  have hmem2 : (Real.log v - Real.log z0) / Real.log z0 ∈ Set.Icc (1:ℝ) (3/2) :=
    ⟨hr1.trans hrr, hr2⟩
  have hmain := mono_ratio_log hmem1 hmem2 hrr
  have hpos : (0:ℝ) < 1 / Real.log z0 := by positivity
  exact mul_le_mul_of_nonneg_left hmain hpos.le

/-! ## T2_bound -/

/-- LEAF: P0088 page 6 display 22 for j = 2, the trivial bound. The weight f2 of
page 15 is bounded on the window of m between Y^(1/2)/2 and Y^(1/2), since its
integral term is at most log(log u^(1/2) / log z0) / log u, and the window holds at
most Y^(1/2) + 1 integers. -/
theorem T2_trivial :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ,
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤ C * Real.sqrt (windowY X ε) := by
  intro B hB ε hε hε'
  set M := max (Real.exp (1 / B)) (max ((55 * B) ^ 2) 100) with hMdef
  have hM100 : 100 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM4 : 4 ≤ M := by linarith
  refine ⟨4, Real.exp M, by norm_num, ?_⟩
  intro X hX β
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set L := Real.log X with hL
  have hLM : M ≤ L := by rw [← Real.log_exp M]; exact Real.log_le_log (Real.exp_pos _) hX
  have hL4 : 4 ≤ L := le_trans hM4 hLM
  have hLB : (55 * B) ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLM
  have hLe : Real.exp (1 / B) ≤ L := le_trans (le_max_left _ _) hLM
  have hLpos : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓB : 1 / B ≤ ℓ := by
    rw [← Real.log_exp (1 / B)]; exact Real.log_le_log (Real.exp_pos _) hLe
  have hBℓ : 1 ≤ B * ℓ := by
    rw [div_le_iff₀ hB] at hℓB; linarith
  have hℓpos : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  have hsqL : 55 * B ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hLB
    rwa [Real.sqrt_sq (by positivity)] at this
  have hℓsq : ℓ ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
    rw [Real.log_sqrt hLpos.le] at h1; linarith
  have hsqsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hkey : 2 * B * ℓ ≤ 7 * L / 96 := by
    have h1 := mul_le_mul_of_nonneg_left hℓsq (by positivity : (0:ℝ) ≤ 2 * B)
    have h2 := mul_le_mul_of_nonneg_right hsqL (Real.sqrt_nonneg L)
    nlinarith
  set e := 7 / 12 + ε / 2 with he
  have he7 : 7 / 12 ≤ e := by linarith
  have hYdef : windowY X ε = X ^ e := rfl
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hXpos _
  have hlogY : Real.log Y = e * L := by rw [hYdef]; exact Real.log_rpow hXpos e
  set P := L ^ B with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos _
  have hlogP : Real.log P = B * ℓ := Real.log_rpow hLpos B
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) with hz0
  have hz0pos : 0 < z0 := by positivity
  have hlz : Real.log z0 = e * L / 4 - 2 * (B * ℓ) := by
    rw [hz0, Real.log_mul (by positivity) (by positivity), Real.log_rpow hYpos,
      Real.log_zpow, hlogY, hlogP]
    push_cast; ring
  have hlz8 : e * L / 8 ≤ Real.log z0 := by
    rw [hlz]; nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
  have hlz96 : 7 * L / 96 ≤ Real.log z0 := by
    nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
  have hlzpos : 0 < Real.log z0 := by linarith
  have hz1 : 1 < z0 := (Real.log_pos_iff hz0pos.le).mp hlzpos
  have hu : L ^ (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L
  have hsY : Real.log (Real.sqrt Y) = e * L / 2 := by
    rw [Real.log_sqrt hYpos.le, hlogY]
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hL100 : 100 ≤ L := hM100.trans hLM
  have per : ∀ m ∈ squareWindow Y, |f2Weight z0 (m : ℝ)| ≤ 2 := by
    intro v hv
    obtain ⟨_, hm2lo, hm2hi⟩ := Finset.mem_filter.mp hv
    set m : ℝ := (v : ℝ) with hm
    have hsYpos : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
    have hmpos : 0 < m := by linarith
    have hlmlo : e * L / 2 - Real.log 2 ≤ Real.log m := by
      have := Real.log_le_log (by positivity) hm2lo
      rwa [Real.log_div hsYpos.ne' (by norm_num), hsY] at this
    have hlmhi : Real.log m < e * L / 2 := by
      have := Real.log_lt_log hmpos hm2hi
      rwa [hsY] at this
    have hlm8 : 7 * L / 24 - 1 ≤ Real.log m := by
      nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
    have hlm1 : 1 ≤ Real.log m := by linarith
    have hlmpos : 0 < Real.log m := by linarith
    have hsm : Real.log (Real.sqrt m) = Real.log m / 2 := Real.log_sqrt hmpos.le
    have hsmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
    have hzle : z0 ≤ Real.sqrt m := by
      rw [← Real.log_le_log_iff hz0pos hsmpos, hsm, hlz]; linarith
    obtain ⟨hJ0, hJ1⟩ := Task129.f2_integral_bound (u := m) hz1 hzle
    have hlz1 : 1 ≤ Real.log z0 := by linarith
    have hsmLog : 0 < Real.log (Real.sqrt m) := by rw [hsm]; positivity
    have hratio : Real.log (Real.sqrt m / z0) ≤ Real.log (Real.sqrt m) := by
      rw [Real.log_div hsmpos.ne' hz0pos.ne']
      linarith
    have hJ2 : (∫ t in z0..Real.sqrt m, 1 / (t * Real.log t * Real.log (m / t))) ≤
        1 / Real.log z0 := by
      refine hJ1.trans ?_
      have hid : (1 / (Real.log z0 * Real.log (Real.sqrt m))) *
          Real.log (Real.sqrt m / z0) =
          Real.log (Real.sqrt m / z0) / (Real.log z0 * Real.log (Real.sqrt m)) := by ring
      rw [hid, div_le_div_iff₀ (mul_pos hlzpos hsmLog) hlzpos]
      nlinarith only [mul_le_mul_of_nonneg_right hratio hlzpos.le]
    have hmInv : 1 / Real.log m ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlm1
    have hzInv : 1 / Real.log z0 ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlz1
    change |1 / Real.log m + ∫ t in z0..Real.sqrt m,
      1 / (t * Real.log t * Real.log (m / t))| ≤ 2
    rw [abs_of_nonneg (add_nonneg (by positivity) hJ0)]
    linarith only [hmInv, hzInv, hJ2]
  have hcard : ((squareWindow Y).card : ℝ) ≤ Real.sqrt Y + 1 := by
    have h : (squareWindow Y).card ≤ ⌊Real.sqrt Y⌋₊ + 1 := by
      unfold squareWindow
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) ≤ Real.sqrt Y := Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ((squareWindow Y).card : ℝ) ≤ ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith [Real.add_one_le_exp M] : 1 ≤ X) (by linarith : 0 ≤ e)
  have hR1 : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.mpr hY1
  change ‖T2 Y P β‖ ≤ 4 * Real.sqrt Y
  refine (trig_norm_le (squareWindow Y) _ (fun m => ((m ^ 2 : ℕ) : ℤ)) _).trans ?_
  calc
    _ ≤ ∑ _m ∈ squareWindow Y, (2 : ℝ) := Finset.sum_le_sum fun m hm => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using per m hm
    _ = 2 * ((squareWindow Y).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * Real.sqrt Y := by linarith

set_option maxHeartbeats 4000000 in
/-- LEAF: P0088 page 6 display 22 for j = 2, the decay bound for 0 < |beta| at
most Y^(-1/2)/4: the Kuzmin Landau bound for the phase m^2 beta, whose
derivative 2 m beta is monotone with absolute value between Y^(1/2) |beta| and
1/2, and partial summation for the weight f2. -/
theorem T2_decay :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ, 0 < |β| →
        |β| ≤ 1 / (4 * Real.sqrt (windowY X ε)) →
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤
          C / (Real.sqrt (windowY X ε) * |β|) := by
  intro B hB ε hε hε'
  refine ⟨32, Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B))),
    by norm_num, ?_⟩
  intro X hX β hβ hβd
  set L := Real.log X with hLdef
  have hX1 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hM1 : (400 * (B + 1)) ^ 2 ≤ L := by
    have h1 : Real.log (Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B)))) ≤
        Real.log X := Real.log_le_log (Real.exp_pos _) hX
    rw [Real.log_exp, ← hLdef] at h1
    exact le_trans (le_max_left _ _) h1
  have hM2 : Real.exp (Real.log 2 / B) ≤ L := by
    have h1 : Real.log (Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B)))) ≤
        Real.log X := Real.log_le_log (Real.exp_pos _) hX
    rw [Real.log_exp, ← hLdef] at h1
    exact le_trans (le_max_right _ _) h1
  have hB1 : (0:ℝ) < B + 1 := by linarith
  have hL1 : 1 ≤ L := by nlinarith
  have hL400 : 400 * (B + 1) ≤ Real.sqrt L := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 400 * (B + 1))]
    exact Real.sqrt_le_sqrt hM1
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  set ℓ := Real.log L with hℓdef
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]
    exact Real.log_nonneg hL1
  have hℓ2 : ℓ ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos hsqL
    rw [Real.log_sqrt (by linarith)] at h1
    rw [hℓdef]
    linarith
  have hBℓ : Real.log 2 ≤ B * ℓ := by
    have h := Real.log_le_log (Real.exp_pos _) hM2
    rw [Real.log_exp, div_le_iff₀ hB, ← hℓdef] at h
    simpa only [mul_comm] using h
  set ex := 7 / 12 + ε / 2 with hexdef
  have hex7 : 7 / 12 ≤ ex := by rw [hexdef]; linarith
  have hexpos : 0 < ex := by rw [hexdef]; linarith
  set Y := X ^ ex with hYdef
  have hYdef' : windowY X ε = Y := rfl
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hX1 ex
  have hlogY : Real.log Y = ex * L := by
    rw [hYdef, Real.log_rpow hX1, ← hLdef]
  have hsqY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hY2 : 2 ≤ Real.sqrt Y := by
    rw [← Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) hsqY, Real.log_sqrt hYpos.le, hlogY]
    nlinarith [hM1, hex7, hlog2le]
  set P := L ^ B with hPdef
  have hPpos : 0 < P := Real.rpow_pos_of_pos (by linarith) B
  have hlogP : Real.log P = B * ℓ := by
    rw [hPdef, Real.log_rpow (by linarith), ← hℓdef]
  have hP2 : 2 ≤ P := by
    rw [← Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) hPpos, hlogP]
    linarith
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) with hz0def
  have hz0pos : 0 < z0 := by
    rw [hz0def]
    exact mul_pos (Real.rpow_pos_of_pos hYpos _) (zpow_pos hPpos _)
  have hlogz0 : Real.log z0 = ex * L / 4 - 2 * (B * ℓ) := by
    rw [hz0def, Real.log_mul (Real.rpow_pos_of_pos hYpos _).ne' (zpow_pos hPpos _).ne',
      Real.log_rpow hYpos, Real.log_zpow, hlogY, hlogP]
    push_cast
    ring
  have hz0diff : 2 * (B * ℓ) ≤ ex * L / 40 := by
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
    have h4 : 160 * B ≤ ex * Real.sqrt L := by nlinarith [hL400, hex7, hB.le]
    have h5 : (160 * B) * Real.sqrt L ≤ ex * L := by
      have h6 : (160 * B) * Real.sqrt L ≤ ex * (Real.sqrt L * Real.sqrt L) := by
        calc (160 * B) * Real.sqrt L ≤ (ex * Real.sqrt L) * Real.sqrt L :=
              mul_le_mul_of_nonneg_right h4 hsqL.le
          _ = ex * (Real.sqrt L * Real.sqrt L) := by ring
      nlinarith [h6, hsq]
    have h6 : 2 * (B * ℓ) ≤ 4 * B * Real.sqrt L := by nlinarith [hℓ2, hB.le]
    have h7 : 4 * B * Real.sqrt L ≤ ex * L / 40 := by nlinarith [h5]
    linarith
  have hlogz0_ge : 1 ≤ Real.log z0 := by
    rw [hlogz0]
    nlinarith [hz0diff, hM1, hex7]
  have hz0gt1 : 1 < z0 := (Real.log_pos_iff hz0pos.le).mp (by linarith)
  have hlogz0pos : 0 < Real.log z0 := Real.log_pos hz0gt1
  -- the window of integers
  set L0 := ⌈Real.sqrt Y / 2⌉₊ with hL0def
  set U0 := ⌈Real.sqrt Y⌉₊ with hU0def
  set N := U0 - L0 with hNdef
  have hL0le : Real.sqrt Y / 2 ≤ (L0 : ℝ) := Nat.le_ceil _
  have hU0le : Real.sqrt Y ≤ (U0 : ℝ) := Nat.le_ceil _
  have hU0ub : (U0 : ℝ) < Real.sqrt Y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL0U0 : L0 ≤ U0 := Nat.ceil_mono (by linarith)
  have hNL0 : L0 + N = U0 := by
    rw [hNdef]
    exact Nat.add_sub_cancel' hL0U0
  have hNpos : 1 ≤ N := by
    have hlt : L0 < U0 := by
      by_contra hcon
      have hle : U0 ≤ L0 := Nat.le_of_not_lt hcon
      have heq : L0 = U0 := le_antisymm hL0U0 hle
      have h1 : (L0 : ℝ) < Real.sqrt Y / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : Real.sqrt Y ≤ (L0 : ℝ) := by rw [heq]; exact hU0le
      linarith
    omega
  have hL0ge1 : (1:ℝ) ≤ (L0 : ℝ) := by linarith
  have hmU : ∀ j < N, ((L0 + j : ℕ) : ℝ) ≤ (U0 : ℝ) - 1 := by
    intro j hj
    have h1 : L0 + j ≤ U0 - 1 := by omega
    have h2 : ((L0 + j : ℕ) : ℝ) ≤ ((U0 - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((U0 - 1 : ℕ) : ℝ) = (U0 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ U0)]
      norm_num
    linarith
  have hm_ge : ∀ j < N, Real.sqrt Y / 2 ≤ ((L0 + j : ℕ) : ℝ) := by
    intro j hj
    have h2 : (L0 : ℝ) ≤ ((L0 + j : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hm_cast_pos : ∀ m : ℕ, L0 ≤ m → (0:ℝ) < (m : ℝ) := by
    intro m hm
    have h3 : (L0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  set w : ℕ → ℝ := fun j => f2Weight z0 ((L0 + j : ℕ) : ℝ) with hwdef
  have hmpos : ∀ m : ℕ, L0 ≤ m → 2 * Real.log z0 ≤ Real.log (m : ℝ) := by
    intro m hm
    have h2 : Real.log (Real.sqrt Y / 2) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log (by positivity)
      have h3 : (L0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h4 : Real.log (Real.sqrt Y / 2) = ex * L / 2 - Real.log 2 := by
      rw [Real.log_div hsqY.ne' (by norm_num), Real.log_sqrt hYpos.le, hlogY]
    have h5 : 2 * Real.log z0 = ex * L / 2 - 4 * (B * ℓ) := by
      rw [hlogz0]; ring
    have h6 : Real.log 2 ≤ 4 * (B * ℓ) := by
      have h7 : 0 ≤ B * ℓ := mul_nonneg hB.le hℓ0
      linarith
    linarith
  have hz0le : ∀ m : ℕ, L0 ≤ m → z0 ^ 2 ≤ (m : ℝ) := by
    intro m hm
    have h1 : Real.log (z0 ^ 2) = 2 * Real.log z0 := by
      rw [Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by positivity : (0:ℝ) < z0 ^ 2) (hm_cast_pos m hm), h1]
    exact hmpos m hm
  have hlogup : ∀ m : ℕ, L0 ≤ m → (m : ℝ) ≤ (U0 : ℝ) →
      Real.log (m : ℝ) ≤ 5 / 2 * Real.log z0 := by
    intro m hm hle
    have h1 : Real.log (m : ℝ) ≤ Real.log (U0 : ℝ) := Real.log_le_log (hm_cast_pos m hm) hle
    have h2 : Real.log (U0 : ℝ) ≤ Real.log (2 * Real.sqrt Y) := by
      apply Real.log_le_log (by positivity)
      have h4 : (U0 : ℝ) < Real.sqrt Y + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have h3 : Real.log (2 * Real.sqrt Y) = Real.log 2 + ex * L / 2 := by
      rw [Real.log_mul (by norm_num) hsqY.ne', Real.log_sqrt hYpos.le, hlogY]
    have h5 : 5 * (B * ℓ) ≤ ex * L / 16 := by nlinarith [hz0diff]
    have h6 : 1 ≤ ex * L / 16 := by nlinarith [hM1, hex7]
    nlinarith [h1, h2, h3, hlog2le, h5, h6]
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    simp only [hwdef]
    have hm1 : L0 ≤ L0 + j := Nat.le_add_right L0 j
    rw [f2Weight_eq hz0gt1 (hz0le _ hm1)]
    have hlogm : 0 < Real.log ((L0 + j : ℕ) : ℝ) := by
      have h := hmpos _ hm1
      linarith
    have hnum : 0 < 1 + Real.log ((Real.log ((L0 + j : ℕ) : ℝ) - Real.log z0) / Real.log z0) := by
      have hr : 1 ≤ (Real.log ((L0 + j : ℕ) : ℝ) - Real.log z0) / Real.log z0 := by
        rw [le_div_iff₀ hlogz0pos]
        linarith [hmpos _ hm1]
      have h2 := Real.log_nonneg hr
      linarith
    exact div_nonneg hnum.le hlogm.le
  have hw_mono : ∀ j, j < N → w j ≤ w (j + 1) := by
    intro j hj
    simp only [hwdef]
    have hz0m := hz0le (L0 + j) (Nat.le_add_right L0 j)
    have hle1 : ((L0 + j : ℕ) : ℝ) ≤ ((L0 + (j + 1) : ℕ) : ℝ) := by
      have h2 : L0 + j ≤ L0 + (j + 1) := by omega
      exact_mod_cast h2
    have hle2 : ((L0 + (j + 1) : ℕ) : ℝ) ≤ (U0 : ℝ) := by
      have h2 : L0 + (j + 1) ≤ U0 := by omega
      exact_mod_cast h2
    exact f2Weight_mono hz0gt1 hz0m hle1 (hlogup _ (by omega) hle2)
  have hw_two : w (N - 1) ≤ 2 := by
    simp only [hwdef]
    have hz0m := hz0le (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))
    have hle2 : ((L0 + (N - 1) : ℕ) : ℝ) ≤ (U0 : ℝ) := by
      have h2 : L0 + (N - 1) ≤ U0 := by omega
      exact_mod_cast h2
    rw [f2Weight_eq hz0gt1 hz0m]
    have hmup := hlogup (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1)) hle2
    have hlogm : 2 ≤ Real.log ((L0 + (N - 1) : ℕ) : ℝ) := by
      have h := hmpos (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))
      linarith
    have hlogm0 : 0 < Real.log ((L0 + (N - 1) : ℕ) : ℝ) := by linarith
    have hr : Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0 ≤ Real.log z0 * (3 / 2) := by
      nlinarith [hmup]
    have hlogr : Real.log ((Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0) ≤ 1 := by
      have hpos : 0 < (Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0 := by
        apply div_pos _ hlogz0pos
        linarith [hmpos (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))]
      have hr2 : (Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0 ≤ 3 / 2 := by
        rw [div_le_iff₀ hlogz0pos]
        linarith
      have h1 := Real.log_le_sub_one_of_pos hpos
      linarith
    rw [div_le_iff₀ hlogm0]
    linarith
  -- reindex the sum
  have hT2 : T2 Y P β = ∑ j ∈ Finset.range N,
      (w j : ℂ) * fourier (((L0 + j) ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [show T2 Y P β = ∑ m ∈ squareWindow Y, ((f2Weight z0 (m : ℝ) : ℝ) : ℂ) *
        fourier (((m ^ 2 : ℕ)) : ℤ) (β : AddCircle (1 : ℝ)) from by
      unfold T2
      rw [← hz0def]]
    rw [Task674.squareWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
  have hβY : |β| ≤ 1 / (4 * Real.sqrt Y) := by
    rw [hYdef'] at hβd
    exact hβd
  -- the exponential sum bound (Kusmin-Landau)
  have hθdiff : ∀ j : ℕ, (((L0 + (j + 1) : ℕ) : ℝ))^2 * |β| -
      (((L0 + j : ℕ) : ℝ))^2 * |β| = (2 * (((L0 + j : ℕ) : ℝ)) + 1) * |β| := by
    intro j
    have h2 : L0 + (j + 1) = L0 + j + 1 := by omega
    rw [h2]
    push_cast
    ring
  have hKL : ∀ k ≤ N, ‖∑ j ∈ Finset.range k,
      LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ ≤
      8 / (Real.sqrt Y * |β|) := by
    intro k hk
    refine sum_e_le_of_mono_steps (θ := fun j => (((L0 + j : ℕ) : ℝ))^2 * |β|)
      (δ := Real.sqrt Y * |β|) (by positivity) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [hθdiff j]
      have h1 : (0:ℝ) < 2 * (((L0 + j : ℕ) : ℝ)) + 1 := by positivity
      exact mul_pos h1 hβ
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have hmU := hmU j hjN
      have h2 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 2 * Real.sqrt Y + 1 := by
        nlinarith [hmU, hU0ub]
      have h3 : (2 * Real.sqrt Y + 1) * |β| ≤ 2 / 3 := by
        have h4 : (2 * Real.sqrt Y + 1) * |β| ≤
            (2 * Real.sqrt Y + 1) * (1 / (4 * Real.sqrt Y)) :=
          mul_le_mul_of_nonneg_left hβY (by positivity)
        have h5 : (2 * Real.sqrt Y + 1) * (1 / (4 * Real.sqrt Y)) ≤ 2 / 3 := by
          rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt Y)]
          nlinarith [hY2]
        linarith
      exact (mul_le_mul_of_nonneg_right h2 hβ.le).trans h3
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have h1 : Real.sqrt Y ≤ 2 * (((L0 + j : ℕ) : ℝ)) + 1 := by
        have h2 := hm_ge j hjN
        linarith
      exact mul_le_mul_of_nonneg_right h1 hβ.le
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have hmU := hmU j hjN
      have h2 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 4 * Real.sqrt Y := by
        nlinarith [hmU, hU0ub, hY2]
      calc (2 * (((L0 + j : ℕ) : ℝ)) + 1) * |β| ≤ (4 * Real.sqrt Y) * |β| :=
            mul_le_mul_of_nonneg_right h2 hβ.le
        _ = 4 * (Real.sqrt Y * |β|) := by ring
    · intro j hj
      rw [hθdiff j, hθdiff (j + 1)]
      have h1 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 2 * (((L0 + (j + 1) : ℕ) : ℝ)) + 1 := by
        have hidx : ((L0 + (j + 1) : ℕ) : ℝ) = ((L0 + j : ℕ) : ℝ) + 1 := by
          have h2 : L0 + (j + 1) = L0 + j + 1 := by omega
          rw [h2]
          push_cast
          ring
        rw [hidx]
        linarith
      exact mul_le_mul_of_nonneg_right h1 hβ.le
  -- the weights times the phases
  have hterm : ∀ j, (w j : ℂ) * fourier (((L0 + j) ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) =
      (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β) := by
    intro j
    rw [Task556d.fourier_nat_eq_e]
    congr 1
    push_cast
    ring
  have hnorm_eq : ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β)‖
      = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ := by
    have hβne : β ≠ 0 := by
      intro h0
      rw [h0] at hβ
      simp at hβ
    rcases lt_or_gt_of_ne hβne with hneg | hpos
    · have hconj : (∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β))
          = (starRingEnd ℂ) (∑ j ∈ Finset.range N,
            (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have harg : ((((L0 + j : ℕ) : ℝ))^2 * β) = -((((L0 + j : ℕ) : ℝ))^2 * |β|) := by
          rw [abs_of_neg hneg]
          ring
        rw [harg, LeanLab.PNTPort.LargeSieve.e_neg, map_mul, Complex.conj_ofReal]
      rw [hconj, RCLike.norm_conj]
    · rw [abs_of_pos hpos]
  have hAbel := norm_sum_mono_weight_le
    (f := fun j => LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|))
    (w := w) (B := 8 / (Real.sqrt Y * |β|)) (N := N) hw_nonneg hw_mono hKL
  rw [hYdef']
  change ‖T2 Y P β‖ ≤ 32 / (Real.sqrt Y * |β|)
  calc ‖T2 Y P β‖
      = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β)‖ := by
        rw [hT2, Finset.sum_congr rfl fun j hj => hterm j]
    _ = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ := hnorm_eq
    _ ≤ 2 * w (N - 1) * (8 / (Real.sqrt Y * |β|)) := hAbel
    _ ≤ 2 * 2 * (8 / (Real.sqrt Y * |β|)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hw_two]
    _ = 32 / (Real.sqrt Y * |β|) := by ring

/-- The exact statement of Prep1121KLMajor.T2_bound, from T2_trivial and
T2_decay. No sorry of its own. -/
theorem T2_bound_of_pieces : T2BoundProp := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := T2_trivial B hB ε hε hε'
  obtain ⟨C2, X2, hC2, k2⟩ := T2_decay B hB ε hε hε'
  refine ⟨2 * C1 + 2 * C2, max (max X1 X2) 1, by positivity, fun X hX β hβ => ?_⟩
  have hXa : X1 ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hY1 := windowY_ge_one hX1 hε
  have hY : 0 < windowY X ε := by linarith
  have hs : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY
  refine split_bound hY hs.le hC1.le hC2.le (fun _ => k1 X hXa β) (fun hc => ?_)
  have hb : 0 < |β| := by
    by_contra h0
    have : |β| = 0 := le_antisymm (not_lt.mp h0) (abs_nonneg β)
    rw [this, mul_zero] at hc
    linarith
  refine (k2 X hXb β hb hβ).trans (le_of_eq ?_)
  have hsq : Real.sqrt (windowY X ε) * Real.sqrt (windowY X ε) = windowY X ε :=
    Real.mul_self_sqrt hY.le
  have hb' : 0 < windowY X ε * |β| := by linarith
  rw [div_eq_div_iff (by positivity) hb'.ne']
  linear_combination (-(C2 * |β|)) * hsq

example : type_of% @T2_bound := T2_bound_of_pieces

/-! ## bound24 -/

/-- PROVED. P0088 page 6 display 17 for j = 1: Parseval for the prime sum over one
period, from Task556d.primeSum_parseval_le. -/
theorem S1_mean_square {X Y : ℝ} (hXY : 0 ≤ X - Y) (hY : 1 ≤ Y) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) ≤ 2 * Y := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact primeSum_parseval_le hXY hY

/-! ## The mean square of S2* over m0, display 24 (ported from S2starMinorSplit1122) -/

private lemma gauss_mean_square_sq_le (j : ℕ) : (j + 2) ^ 2 ≤ 5 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; norm_num
    · have : (j + 3) ^ 2 ≤ 2 * (j + 2) ^ 2 := by nlinarith
      calc (j + 1 + 2) ^ 2 = (j + 3) ^ 2 := by ring
        _ ≤ 2 * (j + 2) ^ 2 := this
        _ ≤ 2 * (5 * 2 ^ j) := by omega
        _ = 5 * 2 ^ (j + 1) := by ring


private lemma gauss_mean_square_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    (k + 1) ^ 2 * p ^ k ≤ (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) * (p ^ (k - 1) * (p - 1)) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 := hp.two_le
  have hpj : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left h2 j
  have hA : (j + 1 + 1) ^ 2 * p ^ (j + 1) ≤ 5 * p * (p ^ j) ^ 2 := by
    have := gauss_mean_square_sq_le j
    have h3 : (j + 2) ^ 2 ≤ 5 * p ^ j := le_trans this (by omega)
    calc (j + 1 + 1) ^ 2 * p ^ (j + 1) = (j + 2) ^ 2 * (p ^ j * p) := by ring
      _ ≤ (5 * p ^ j) * (p ^ j * p) := Nat.mul_le_mul_right _ h3
      _ = 5 * p * (p ^ j) ^ 2 := by ring
  have hB : 5 * p ≤ (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) * (p - 1) ^ 2 := by
    by_cases e2 : p = 2
    · subst e2; norm_num
    by_cases e3 : p = 3
    · subst e3; norm_num
    by_cases e5 : p = 5
    · subst e5; norm_num
    simp only [e2, e3, e5, ite_false, one_mul]
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    have h6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
    have h7 : 7 ≤ p := by omega
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  calc (j + 1 + 1) ^ 2 * p ^ (j + 1) ≤ 5 * p * (p ^ j) ^ 2 := hA
    _ ≤ (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) * (p - 1) ^ 2 * (p ^ j) ^ 2 := Nat.mul_le_mul_right _ hB
    _ = (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) * (p ^ j * (p - 1)) ^ 2 := by ring

private lemma gauss_mean_square_c_prod (s : Finset ℕ) : ∏ p ∈ s, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) ≤ 80 := by
  have h1 : ∏ p ∈ s, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) = ∏ p ∈ s ∩ {2, 3, 5}, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) := by
    symm
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hn
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, not_and] at hn
    have := hn hp
    simp only [not_or] at this
    simp [this.1, this.2.1, this.2.2]
  have h2 : ∏ p ∈ s ∩ {2, 3, 5}, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) ∣ ∏ p ∈ ({2, 3, 5} : Finset ℕ), (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) :=
    Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
  have h3 : ∏ p ∈ ({2, 3, 5} : Finset ℕ), (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) = 80 := by
    simp
  rw [h1]; rw [h3] at h2; exact Nat.le_of_dvd (by norm_num) h2

private lemma gauss_mean_square_tau_phi (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 2 * n ≤ 80 * (Nat.totient n) ^ 2 := by
  rw [Nat.card_divisors hn, Nat.totient_eq_prod_factorization hn, Finsupp.prod,
    Nat.support_factorization]
  have e : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have := Nat.prod_factorization_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  calc (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2) * n
      = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2 * p ^ n.factorization p := by
        rw [Finset.prod_mul_distrib, e]
    _ ≤ _ := ?_
  clear e
  calc ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2 * p ^ n.factorization p
      ≤ ∏ p ∈ n.primeFactors, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1) * (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 := by
        apply Finset.prod_le_prod' 
        intro p hp
        exact gauss_mean_square_prime_pow p _ (Nat.prime_of_mem_primeFactors hp)
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])))
    _ = (∏ p ∈ n.primeFactors, (if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1)) * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 := Finset.prod_mul_distrib
    _ ≤ 80 * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 :=
        Nat.mul_le_mul_right _ (gauss_mean_square_c_prod _)

private lemma gauss_mean_square_key (q x y : ℤ) (hq : 0 < q) (h : q ∣ x ^ 2 - y ^ 2) :
    q / (Int.gcd (y - x) q : ℤ) ∣ y + x := by
  have hd : 0 < Int.gcd (y - x) q := Int.gcd_pos_of_ne_zero_right _ hq.ne'
  have hcop := Int.gcd_div_gcd_div_gcd hd
  set d : ℤ := (Int.gcd (y - x) q : ℤ) with hd_def
  have hdpos : 0 < d := by rw [hd_def]; exact_mod_cast hd
  have h1 : (y - x) / d * d = y - x := Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  have h2 : q / d * d = q := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have h3 : q / d * d ∣ (y - x) / d * (y + x) * d := by
    rw [h2, mul_right_comm, h1]
    have : x ^ 2 - y ^ 2 = -((y - x) * (y + x)) := by ring
    rw [this] at h; exact (dvd_neg).mp h
  have h4 : q / d ∣ (y - x) / d * (y + x) := (mul_dvd_mul_iff_right hdpos.ne').mp h3
  have hc : IsCoprime (q / d) ((y - x) / d) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
  exact hc.dvd_of_dvd_mul_left h4

private lemma gauss_mean_square_inj (q x y y' : ℤ) (hq : 0 < q) (hx : IsCoprime q x)
    (hy : 0 ≤ y ∧ y < q) (hy' : 0 ≤ y' ∧ y' < q)
    (h : q ∣ x ^ 2 - y ^ 2) (h' : q ∣ x ^ 2 - y' ^ 2)
    (hg : Int.gcd (y - x) q = Int.gcd (y' - x) q) (hb : 2 * y < q ↔ 2 * y' < q) : y = y' := by
  have e1 := gauss_mean_square_key q x y hq h
  have e2 := gauss_mean_square_key q x y' hq h'
  rw [← hg] at e2
  set d : ℤ := (Int.gcd (y - x) q : ℤ) with hd_def
  have d1 : d ∣ y - x := Int.gcd_dvd_left _ _
  have d2 : d ∣ y' - x := by rw [hd_def, hg]; exact Int.gcd_dvd_left _ _
  have h2 : q / d * d = q := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have dz : d ∣ y - y' := by have := dvd_sub d1 d2; rwa [sub_sub_sub_cancel_right] at this
  have ez : q / d ∣ y - y' := by have := dvd_sub e1 e2; rwa [add_sub_add_right_eq_sub] at this
  have k1 : q / d * d ∣ (y + x) * (y - y') := mul_dvd_mul e1 dz
  have k2 : q / d * d ∣ (y - y') * (y - x) := mul_dvd_mul ez d1
  rw [h2] at k1 k2
  have k3 : q ∣ (2 * (y - y')) * x := by
    have := dvd_sub k1 k2
    have e : (y + x) * (y - y') - (y - y') * (y - x) = (2 * (y - y')) * x := by ring
    rwa [e] at this
  have k4 : q ∣ 2 * (y - y') := hx.dvd_of_dvd_mul_right k3
  obtain ⟨k, hk⟩ := k4
  have kl : -2 < k := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  have ku : k < 2 := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  interval_cases k <;> omega

private lemma gauss_mean_square_fiber (q x : ℕ) (hq : 1 ≤ q) (hx : Nat.Coprime x q) :
    (((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
      (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card ≤ 2 * q.divisors.card := by
  have hc : (((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
      (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card ≤
      (q.divisors ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun y : ℕ => (Int.gcd ((y : ℤ) - x) q, decide (2 * y < q)))
    · intro y _
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true,
        Nat.mem_divisors]
      refine ⟨?_, by omega⟩
      exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right _ _)
    · intro y hy y' hy' he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hy hy'
      simp only [Prod.mk.injEq, decide_eq_decide] at he
      have hqz : (0 : ℤ) < q := by exact_mod_cast hq
      have hxc : IsCoprime (q : ℤ) (x : ℤ) := Nat.isCoprime_iff_coprime.mpr hx.symm
      have := gauss_mean_square_inj q x y y' hqz hxc ⟨by positivity, by exact_mod_cast hy.1.1⟩
        ⟨by positivity, by exact_mod_cast hy'.1.1⟩ hy.2 hy'.2 he.1
        (by constructor <;> intro h <;> [exact_mod_cast he.2.mp (by exact_mod_cast h);
          exact_mod_cast he.2.mpr (by exact_mod_cast h)])
      exact_mod_cast this
  simpa [Finset.card_product, mul_comm] using hc

private lemma gauss_mean_square_ee_add (s t : ℝ) : U1534.ee (s + t) = U1534.ee s * U1534.ee t := by
  unfold U1534.ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma gauss_mean_square_conj (t : ℝ) : (starRingEnd ℂ) (U1534.ee t) = U1534.ee (-t) := by
  unfold U1534.ee; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]

private lemma gauss_mean_square_ee_nat_mul (n : ℕ) (t : ℝ) : U1534.ee (n * t) = U1534.ee t ^ n := by
  unfold U1534.ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private lemma gauss_mean_square_ee_int (m : ℤ) : U1534.ee m = 1 := by
  unfold U1534.ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

private lemma gauss_mean_square_geom (q : ℕ) (hq : 1 ≤ q) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 q, U1534.ee ((m : ℝ) / q) ^ a = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  set ζ := U1534.ee ((m : ℝ) / q) with hζ
  have hq0 : (q : ℝ) ≠ 0 := by have : (0:ℝ) < q := by exact_mod_cast hq
                               exact this.ne'
  have hζq : ζ ^ q = 1 := by
    rw [hζ, ← gauss_mean_square_ee_nat_mul, mul_div_cancel₀ _ hq0, gauss_mean_square_ee_int]
  have hI : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp_rw [pow_add, pow_one, ← Finset.mul_sum]
  split_ifs with hd
  · obtain ⟨n, hn⟩ := hd
    have : ζ = 1 := by
      rw [hζ, hn]; push_cast; rw [mul_div_cancel_left₀ _ hq0]; exact gauss_mean_square_ee_int n
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ] at h1; unfold U1534.ee at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      apply hd
      refine ⟨n, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (((m : ℝ) / q : ℝ) : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ hpi; rw [hn]; ring
      have h3 : ((m : ℝ) / q) = (n : ℝ) := by exact_mod_cast h2
      have h4 : (m : ℝ) = (q : ℝ) * n := by field_simp at h3; linarith
      exact_mod_cast h4
    rw [geom_sum_eq hne, hζq]; simp

private lemma gauss_mean_square_term (q a x y : ℕ) :
    U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / q) * (starRingEnd ℂ) (U1534.ee (((a * y ^ 2 : ℕ) : ℝ) / q)) =
      U1534.ee ((((x : ℤ) ^ 2 - (y : ℤ) ^ 2 : ℤ) : ℝ) / q) ^ a := by
  rw [gauss_mean_square_conj, ← gauss_mean_square_ee_add, ← gauss_mean_square_ee_nat_mul]
  congr 1; push_cast; ring

private lemma gauss_mean_square_parseval (q : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 =
      ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        (q : ℝ) * ((((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
          (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have hS : ∀ a, ((‖U1534.gaussS q a‖ : ℂ)) ^ 2 = U1534.gaussS q a * (starRingEnd ℂ) (U1534.gaussS q a) := by
    intro a
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [hS]
  unfold U1534.gaussS
  simp_rw [map_sum, Finset.sum_mul_sum, gauss_mean_square_term]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp_rw [gauss_mean_square_geom q hq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- PROVED. P0088 page 6 display 24 second line, the mean of the reduced quadratic
Gauss sums S(q, a) of page 3 display 8: the sum over 1 <= a <= q, (a, q) = 1, of
|S(q, a)|^2 / phi(q)^2 is << q^eta; here eta = 1/2. Split class HARD: needs
multiplicativity of S(q, a) in q and the prime power evaluation, or the
Parseval identity over a mod q with a count of square roots of unity. -/
theorem gauss_mean_square : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) := by
  refine ⟨18, by norm_num, ?_⟩
  intro q hq
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set τ : ℝ := (q.divisors.card : ℝ) with hτ
  have h1 : ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have hU : ((Finset.range q).filter (fun x => Nat.Coprime x q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro x _
    exact Nat.coprime_comm
  have h2 : ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 ≤
      (Nat.totient q : ℝ) * ((q : ℝ) * (2 * τ)) := by
    rw [gauss_mean_square_parseval q hq]
    calc _ ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), (q : ℝ) * (2 * τ) := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : Nat.Coprime x q := (Finset.mem_filter.mp hx).2
          have := gauss_mean_square_fiber q x hq hx'
          have : ((((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
              (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card : ℝ) ≤ 2 * τ := by
            rw [hτ]; exact_mod_cast this
          exact mul_le_mul_of_nonneg_left this hqpos.le
      _ = _ := by rw [Finset.sum_const, hU, nsmul_eq_mul]
  have h3 : ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      2 * q * τ / (Nat.totient q : ℝ) := by
    rw [← Finset.sum_div, div_le_div_iff₀ (by positivity) hφpos]
    calc _ ≤ (Nat.totient q : ℝ) * ((q : ℝ) * (2 * τ)) * (Nat.totient q : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hφpos.le
      _ = _ := by ring
  have hτφ : τ ^ 2 * q ≤ 80 * (Nat.totient q : ℝ) ^ 2 := by
    rw [hτ]; exact_mod_cast gauss_mean_square_tau_phi q (by omega)
  have hτ0 : 0 ≤ τ := by positivity
  have h4 : 2 * q * τ / (Nat.totient q : ℝ) ≤ 18 * (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hφpos, ← Real.sqrt_eq_rpow]
    have hs := Real.sq_sqrt hqpos.le
    have hs0 := Real.sqrt_nonneg (q : ℝ)
    have hlhs : 0 ≤ 2 * q * τ := by positivity
    have hrhs : 0 ≤ 18 * Real.sqrt q * (Nat.totient q : ℝ) := by positivity
    have hk := mul_le_mul_of_nonneg_left hτφ (by positivity : (0:ℝ) ≤ 4 * q)
    have hφ2 : 0 ≤ (q : ℝ) * (Nat.totient q : ℝ) ^ 2 := by positivity
    refine (pow_le_pow_iff_left₀ hlhs hrhs two_ne_zero).mp ?_
    have e1 : (2 * q * τ) ^ 2 = 4 * q * (τ ^ 2 * q) := by ring
    have e2 : (18 * Real.sqrt q * (Nat.totient q : ℝ)) ^ 2 =
        324 * (Real.sqrt q) ^ 2 * (Nat.totient q : ℝ) ^ 2 := by ring
    rw [e1, e2, hs]
    nlinarith [hk, hφ2]
  linarith [h1, h3, h4]

/-- PROVED. P0088 page 4 display 15, the arcs M(q, a) with q <= P are pairwise
disjoint when the width parameter R = Q = H/P exceeds 2P, used in the first sum
of page 6 display 24. Split class EASY: |a q' - a' q| <= (q + q')/R < 1 and coprimality. -/
theorem arcs_disjoint {P R : ℝ} (hR : 2 * P < R) {v w : ℕ × ℕ}
    (hv : v ∈ arcPairs P) (hw : w ∈ arcPairs P) {α : ℝ}
    (h1 : α ∈ arc R v) (h2 : α ∈ arc R w) : v = w := by
  obtain ⟨q, a⟩ := v
  obtain ⟨q2, a2⟩ := w
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hv hw
  simp only [arc, Set.mem_ofPred_eq] at h1 h2
  obtain ⟨⟨⟨hq1, hqP⟩, _⟩, _, hcop⟩ := hv
  obtain ⟨⟨⟨hq21, hq2P⟩, _⟩, _, hcop2⟩ := hw
  have hP0 : (0 : ℝ) ≤ P := by
    by_contra h
    push Not at h
    have : ⌊P⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  have hqle : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hqP) (Nat.floor_le hP0)
  have hq2le : (q2 : ℝ) ≤ P := le_trans (by exact_mod_cast hq2P) (Nat.floor_le hP0)
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hRpos : 0 < R := by linarith
  have hkey : |((a2 : ℝ) * q - a * q2)| < 1 := by
    have e : ((a2 : ℝ) * q - a * q2) = q2 * (q * α - a) - q * (q2 * α - a2) := by ring
    rw [e]
    have hq0 : (0:ℝ) ≤ q := by positivity
    have hq20 : (0:ℝ) ≤ q2 := by positivity
    calc |(q2:ℝ) * (q * α - a) - q * (q2 * α - a2)|
        ≤ |(q2:ℝ) * (q * α - a)| + |(q:ℝ) * (q2 * α - a2)| := abs_sub _ _
      _ = q2 * |(q:ℝ) * α - a| + q * |(q2:ℝ) * α - a2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq20]
      _ ≤ q2 * R⁻¹ + q * R⁻¹ := by gcongr
      _ = (q2 + q) / R := by ring
      _ < 1 := by rw [div_lt_one hRpos]; linarith
  have hint : ((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ) = 0 := by
    have : |(((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ) : ℝ)| < 1 := by
      push_cast; exact hkey
    have h' : |((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ)| < 1 := by exact_mod_cast this
    rw [abs_lt] at h'
    omega
  have heq : a2 * q = a * q2 := by omega
  have hd1 : q ∣ q2 := by
    have : q ∣ a * q2 := ⟨a2, by rw [← heq]; ring⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hd2 : q2 ∣ q := by
    have : q2 ∣ a2 * q := ⟨a, by rw [heq]; ring⟩
    exact (Nat.Coprime.symm hcop2).dvd_of_dvd_mul_left this
  have hqq : q = q2 := Nat.dvd_antisymm hd1 hd2
  subst hqq
  have : a = a2 := by
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) heq
    omega
  subst this
  rfl

/-- PROVED. P0088 page 6 display 23: a point of M(q, a) with q <= P outside M0 has
|q alpha - a| > 1/Q0 = P^3/Y, Q0 = Y P^(-3) of display 14. M0 is written as
majorArcs (Y P^(-2)) P. Split class EASY. -/
theorem off_M0 {Y P : ℝ} (hY : 0 < Y) (hP : 0 < P) {v : ℕ × ℕ} (hv : v ∈ arcPairs P)
    {α : ℝ} (hα : α ∉ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    P ^ 3 / Y < |(v.1 : ℝ) * α - v.2| := by
  by_contra h
  push Not at h
  apply hα
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hv
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _, hcop⟩ := hv
  have hinv : ((Y * P ^ (-2 : ℤ)) / P)⁻¹ = P ^ 3 / Y := by
    rw [zpow_neg, zpow_two]
    field_simp
  refine ⟨v.1, h1, ?_, (v.2 : ℤ), ?_, ?_⟩
  · exact le_trans (by exact_mod_cast h2) (Nat.floor_le hP.le)
  · exact Nat.isCoprime_iff_coprime.mpr hcop
  · rw [hinv]; push_cast; exact h

/-- PROVED. P0088 page 6 display 23 and the block range of display 24: for large X,
P = (log X)^B and Y = X^(7/12 + eps/2), one has 8 P^6 Y^(1/2) <= X^(7/18 + eps),
so H/P > 2P and P/H <= Y^(-1/2)/4 for H >= X^(7/18 + eps) P^(-4). Split class MEDIUM:
a power of log X against a power of X. -/
theorem eventually_large {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 3 ≤ X ∧
      8 * (Real.log X ^ B) ^ 6 * Real.sqrt (windowY X ε) ≤ X ^ (7 / 18 + ε) := by
  have hlo := isLittleO_log_rpow_rpow_atTop (6 * B) (show (0:ℝ) < 7 / 72 by norm_num)
  have hb := hlo.bound (show (0:ℝ) < 1 / 8 by norm_num)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 hb
  refine ⟨max X1 3, fun X hX => ?_⟩
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hX1' : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1'
  refine ⟨hX3, ?_⟩
  have h := hX1 X ((le_max_left _ _).trans hX)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _)] at h
  have hpow : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]; norm_num [mul_comm]
  have hsq : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    unfold windowY
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]; congr 1; ring
  have hmono : X ^ ((7:ℝ) / 72) ≤ X ^ (7 / 72 + 3 * ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
  have hsplit : X ^ (7 / 18 + ε) = X ^ (7 / 72 + 3 * ε / 4) * X ^ (7 / 24 + ε / 4) := by
    rw [← Real.rpow_add hXpos]; congr 1; ring
  rw [hpow, hsq, hsplit]
  have hpos : 0 ≤ X ^ (7 / 24 + ε / 4) := Real.rpow_nonneg hXpos.le _
  have : 8 * Real.log X ^ (6 * B) ≤ X ^ (7 / 72 + 3 * ε / 4) := by linarith
  exact mul_le_mul_of_nonneg_right this hpos

private theorem pointwise_bound_T2sq {Y C β : ℝ} {T : ℂ} (hY : 0 < Y) (hC : 0 < C)
    (hβ : 0 < |β|) (h : ‖T‖ ≤ C * Real.sqrt Y / (1 + Y * |β|)) :
    ‖T‖ ^ 2 ≤ C ^ 2 / Y / β ^ 2 := by
  have h1 : ‖T‖ ≤ C * Real.sqrt Y / (Y * |β|) :=
    h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hY.le, sq_abs]
  field_simp

/-- PROVED. P0088 page 6 display 24 first line, pointwise form. Off M0, with the arcs
disjoint and display 22 for T2 on every arc, |S2*(alpha)|^2 is at most the sum over
q, a of |S(q, a)|^2/phi(q)^2 C^2/(Y beta^2) on |beta| > P^3/(q Y), beta = alpha - a/q.
Class MEDIUM. -/
theorem pointwise_bound {Y H P C : ℝ} (hY : 0 < Y) (hP : 0 < P) (hC : 0 < C)
    (hRP : 2 * P < H / P)
    (hT2 : ∀ β : ℝ, |β| ≤ P / H → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|))
    (α : ℝ) (hα : α ∉ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    ‖S2star Y H P α‖ ^ 2 ≤
      ∑ v ∈ arcPairs P, Set.indicator
        {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
        (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
          (x - (v.2 : ℝ) / v.1) ^ 2) α := by
  have hnn : ∀ v ∈ arcPairs P, 0 ≤ Set.indicator
        {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
        (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
          (x - (v.2 : ℝ) / v.1) ^ 2) α := fun v _ =>
    Set.indicator_nonneg (fun x _ => by positivity) α
  by_cases hex : ∃ v0 ∈ arcPairs P, α ∈ arc (H / P) v0
  · obtain ⟨v0, hv0, hαv0⟩ := hex
    have hS : S2star Y H P α = U1534.gaussS v0.1 v0.2 / (Nat.totient v0.1 : ℂ) *
        T2 Y P (α - v0.2 / v0.1) := by
      unfold S2star
      rw [Finset.sum_eq_single v0]
      · exact Set.indicator_of_mem hαv0 _
      · intro v hv hne
        apply Set.indicator_of_notMem
        intro hαv
        exact hne (arcs_disjoint hRP hv hv0 hαv hαv0)
      · intro h; exact absurd hv0 h
    refine le_trans ?_ (Finset.single_le_sum hnn hv0)
    have hq1 : (1 : ℝ) ≤ v0.1 := by
      have h := hv0
      simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
      exact_mod_cast h.1.1.1
    have hq0 : (0 : ℝ) < v0.1 := by linarith
    set q : ℝ := (v0.1 : ℝ) with hqdef
    set a : ℝ := (v0.2 : ℝ) with hadef
    set β : ℝ := α - a / q with hβdef
    have hqβ : q * α - a = q * β := by rw [hβdef]; field_simp
    have habsβ : |q * α - a| = q * |β| := by rw [hqβ, abs_mul, abs_of_pos hq0]
    have hHpos : 0 < H / P := by linarith
    have hβle : |β| ≤ P / H := by
      have h := hαv0
      simp only [arc, Set.mem_ofPred_eq] at h
      rw [← hqdef, ← hadef, habsβ, inv_div] at h
      have hPH : 0 ≤ P / H := by
        rw [← inv_div]; exact inv_nonneg.mpr hHpos.le
      nlinarith [abs_nonneg β]
    have hoff := off_M0 hY hP hv0 hα
    rw [← hqdef, ← hadef, habsβ] at hoff
    have hmem : P ^ 3 / (q * Y) < |β| := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hY] at hoff
      nlinarith
    have hβpos : 0 < |β| := lt_trans (by positivity) hmem
    rw [Set.indicator_of_mem (show α ∈ {x : ℝ | P ^ 3 / ((v0.1 : ℝ) * Y) <
        |x - (v0.2 : ℝ) / v0.1|} from hmem)]
    rw [hS]
    have hT := pointwise_bound_T2sq hY hC hβpos (hT2 β hβle)
    have hφ : (0 : ℝ) < Nat.totient v0.1 := by
      exact_mod_cast Nat.totient_pos.mpr (by rw [hqdef] at hq0; exact_mod_cast hq0)
    rw [norm_mul, norm_div, Complex.norm_natCast, mul_pow, div_pow]
    calc ‖U1534.gaussS v0.1 v0.2‖ ^ 2 / (Nat.totient v0.1 : ℝ) ^ 2 * ‖T2 Y P β‖ ^ 2
        ≤ ‖U1534.gaussS v0.1 v0.2‖ ^ 2 / (Nat.totient v0.1 : ℝ) ^ 2 * (C ^ 2 / Y / β ^ 2) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by ring
  · push Not at hex
    have hS : S2star Y H P α = 0 := by
      unfold S2star
      exact Finset.sum_eq_zero fun v hv => Set.indicator_of_notMem (hex v hv) _
    rw [hS, norm_zero, sq, mul_zero]
    exact Finset.sum_nonneg hnn

private lemma tail_integral_G {r K : ℝ} (hr : 0 < r) :
    Integrable (Set.indicator (Set.Ioi r) fun y : ℝ => K / y ^ 2) ∧
      ∫ y, Set.indicator (Set.Ioi r) (fun y : ℝ => K / y ^ 2) y = K / r := by
  have hI : IntegrableOn (fun y : ℝ => K * y ^ (-2 : ℝ)) (Set.Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hr).const_mul K
  have heq : Set.EqOn (fun y : ℝ => K * y ^ (-2 : ℝ)) (fun y : ℝ => K / y ^ 2) (Set.Ioi r) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hr hy
    simp only
    rw [Real.rpow_neg hy0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).2 (hI.congr_fun heq measurableSet_Ioi), ?_⟩
  rw [integral_indicator measurableSet_Ioi, ← setIntegral_congr_fun measurableSet_Ioi heq,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hr]
  have : (-2:ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

/-- PROVED. P0088 page 6 display 24, the last integral: for r > 0 the function
K/(x - c)^2 on |x - c| > r is integrable with integral 2K/r. Split class MEDIUM. -/
theorem tail_integral {r K : ℝ} (hr : 0 < r) (c : ℝ) :
    Integrable (Set.indicator {x : ℝ | r < |x - c|} fun x => K / (x - c) ^ 2) ∧
      ∫ x, Set.indicator {x : ℝ | r < |x - c|} (fun x => K / (x - c) ^ 2) x = 2 * K / r := by
  obtain ⟨hGi, hGv⟩ := tail_integral_G (K := K) hr
  set G := Set.indicator (Set.Ioi r) fun y : ℝ => K / y ^ 2 with hG
  have hF : ∀ y : ℝ, Set.indicator {y : ℝ | r < |y|} (fun y => K / y ^ 2) y = G y + G (-y) := by
    intro y
    simp only [hG, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi, neg_sq]
    rcases lt_or_ge r y with h | h
    · have : ¬ r < -y := by linarith
      rw [if_pos (lt_abs.2 (Or.inl h)), if_pos h, if_neg this]; ring
    · rcases lt_or_ge r (-y) with h' | h'
      · rw [if_pos (lt_abs.2 (Or.inr h')), if_neg (not_lt.2 h), if_pos h']; ring
      · have : ¬ r < |y| := not_lt.2 (abs_le.2 ⟨by linarith, h⟩)
        rw [if_neg this, if_neg (not_lt.2 h), if_neg (not_lt.2 h')]; ring
  have hfun : (Set.indicator {x : ℝ | r < |x - c|} fun x => K / (x - c) ^ 2) =
      fun x => (fun y => G y + G (-y)) (x - c) := by
    funext x
    show _ = G (x - c) + G (-(x - c))
    rw [← hF (x - c)]
    simp only [Set.indicator, Set.mem_ofPred_eq]
  have hHi : Integrable (fun y => G y + G (-y)) := hGi.add hGi.comp_neg
  rw [hfun]
  refine ⟨hHi.comp_sub_right c, ?_⟩
  rw [integral_sub_right_eq_self (fun y => G y + G (-y)) c, integral_add hGi hGi.comp_neg,
    integral_neg_eq_self, hGv]
  ring

private lemma arc_sum_bound_g10 :
    ‖U1534.gaussS 1 0‖ ^ 2 / (Nat.totient 1 : ℝ) ^ 2 = 1 := by
  simp [U1534.gaussS, U1534.ee]

private lemma arc_sum_bound_inner {P Cg : ℝ} (q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ ⌊P⌋₊)
    (hG : ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Cg * (q : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      Cg * (q : ℝ) ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
  set g : ℕ → ℝ := fun a => ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 with hg
  set X := (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)
  have h1 : ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q), g a
      = ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          (if Nat.Coprime a q then g a else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter] at ha
    simp [ha.2.2]
  have h2 : ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          (if Nat.Coprime a q then g a else 0) ≤
        ∑ a ∈ insert 0 X, (if Nat.Coprime a q then g a else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      rcases Nat.eq_zero_or_pos a with h | h
      · simp [h]
      · apply Finset.mem_insert_of_mem
        simp only [X, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h, ha.2.1⟩, ha.2.2⟩
    · intro a _ _
      split_ifs <;> positivity
  have h0X : (0 : ℕ) ∉ X := by simp [X]
  rw [Finset.sum_insert h0X] at h2
  have h3 : ∑ a ∈ X, (if Nat.Coprime a q then g a else 0) = ∑ a ∈ X, g a := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [X, Finset.mem_filter] at ha
    simp [ha.2]
  have h4 : (if Nat.Coprime 0 q then g 0 else 0) = (if q = 1 then 1 else 0) := by
    simp only [Nat.coprime_zero_left]
    split_ifs with h
    · subst h; exact arc_sum_bound_g10
    · rfl
  rw [h3, h4] at h2
  rw [h1]
  linarith

/-- PROVED. P0088 page 6 display 24 last step: with the Gauss mean bound Cg q^(1/2)
over 1 <= a <= q, the sum over the arc pairs q <= P, 0 <= a <= q, of
q |S(q, a)|^2/phi(q)^2 is at most (Cg + 1) P^(5/2); the pair q = 1, a = 0 adds
at most 1. Split class EASY. -/
theorem arc_sum_bound {P Cg : ℝ} (hP : 1 ≤ P) (hCg : 0 ≤ Cg)
    (hG : ∀ q : ℕ, 1 ≤ q →
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Cg * (q : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ v ∈ arcPairs P, (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) ≤
      (Cg + 1) * P ^ (5 / 2 : ℝ) := by
  set N := ⌊P⌋₊ with hN
  have hNP : (N : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hP0 : 0 ≤ P := by linarith
  rw [arcPairs, Finset.sum_filter, Finset.sum_product]
  have step : ∀ q ∈ Finset.Icc 1 N,
      (∑ a ∈ Finset.range (N + 1), if a ≤ q ∧ Nat.Coprime a q then
        (q : ℝ) * (‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2) else 0) ≤
      Cg * P * P ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hi := arc_sum_bound_inner (P := P) q hq.1 hq.2 (hG q hq.1)
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hq.2) hNP
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hqs : (q : ℝ) ^ (1 / 2 : ℝ) ≤ P ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hq0 hqP (by norm_num)
    have hs0 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
    calc (q : ℝ) * ∑ a ∈ (Finset.range (N + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2
        ≤ (q : ℝ) * (Cg * (q : ℝ) ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0)) :=
          mul_le_mul_of_nonneg_left hi hq0
      _ ≤ Cg * P * P ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
          split_ifs with h
          · subst h
            simp only [Nat.cast_one, one_mul]
            have : Cg * (1 : ℝ) ^ (1 / 2 : ℝ) ≤ Cg * P * P ^ (1 / 2 : ℝ) := by
              rw [Real.one_rpow, mul_one]
              have h1 : (1 : ℝ) ≤ P ^ (1 / 2 : ℝ) := Real.one_le_rpow hP (by norm_num)
              have hCP : Cg ≤ Cg * P := by nlinarith
              nlinarith [mul_le_mul hCP h1 zero_le_one (by positivity)]
            linarith
          · simp only [add_zero]
            have := mul_le_mul hqs (le_refl Cg) hCg (by positivity)
            nlinarith [mul_le_mul hqP this (by positivity) hP0]
  refine (Finset.sum_le_sum step).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Finset.sum_ite_eq']
  have hP52 : P ^ (5 / 2 : ℝ) = P * P * P ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
      Real.rpow_two, sq]
  have h1 : (1 : ℝ) ≤ P ^ (5 / 2 : ℝ) := Real.one_le_rpow hP (by norm_num)
  have hs : 0 ≤ P ^ (1 / 2 : ℝ) := by positivity
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  have hA : (N : ℝ) * (Cg * P * P ^ (1 / 2 : ℝ)) ≤ P * (Cg * P * P ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hNP (by positivity)
  have hB : (if (1 : ℕ) ∈ Finset.Icc 1 N then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [hP52] at h1 ⊢
  nlinarith

/-- The first coordinate of an arc pair is at least one. -/
theorem one_le_of_mem_arcPairs {P : ℝ} {v : ℕ × ℕ} (hv : v ∈ arcPairs P) : 1 ≤ v.1 := by
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hv
  exact hv.1.1.1

/-- The exact statement of S2star_minor_mean_square, P0088 page 6
display 24, from gauss_mean_square, eventually_large, pointwise_bound, tail_integral
and arc_sum_bound, with display 22 for T2 as the hypothesis T2BoundProp, as in the
parent. No sorry of its own. -/
theorem S2star_minor_mean_square_of_pieces (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H (Real.log X ^ B) \
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B)),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  intro B hB ε hε hε'
  obtain ⟨C, X1, hC, hT⟩ := h2 B hB ε hε hε'
  obtain ⟨Cg, hCg, hG⟩ := gauss_mean_square
  obtain ⟨X2, hL⟩ := eventually_large hB hε
  refine ⟨2 * C ^ 2 * (Cg + 1), max X1 X2, by positivity, ?_⟩
  intro X H hX hlo _hhi
  have hX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hX2 : X2 ≤ X := (le_max_right _ _).trans hX
  obtain ⟨hX3, hbig⟩ := hL X hX2
  have hXpos : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX3
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hlog1 hB.le
  have hP : 0 < P := by linarith
  have hY1 : 1 ≤ Y := windowY_ge_one (by linarith) hε
  have hY : 0 < Y := by linarith
  have hsY1 : 1 ≤ Real.sqrt Y := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hY1
  have hsY : 0 < Real.sqrt Y := by linarith
  -- H is at least 8 P^2 Y^(1/2)
  have hz : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hH8 : 8 * P ^ 2 * Real.sqrt Y ≤ H := by
    refine le_trans ?_ hlo
    rw [hz]
    have h4 : 0 < P ^ 4 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h4]
    calc 8 * P ^ 2 * Real.sqrt Y * P ^ 4 = 8 * P ^ 6 * Real.sqrt Y := by ring
      _ ≤ _ := hbig
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hH8
  have hRP : 2 * P < H / P := by
    rw [lt_div_iff₀ hP]
    nlinarith [mul_le_mul_of_nonneg_left hsY1 (by positivity : (0 : ℝ) ≤ 8 * P ^ 2)]
  have hPH : P / H ≤ 1 / (4 * Real.sqrt Y) := by
    rw [div_le_div_iff₀ hHpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hP1 (by positivity : (0 : ℝ) ≤ 4 * P * Real.sqrt Y)]
  have hT2 : ∀ β : ℝ, |β| ≤ P / H → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|) :=
    fun β hβ => hT X hX1 β (hβ.trans hPH)
  -- the majorant
  set g : ℕ × ℕ → ℝ → ℝ := fun v => Set.indicator
    {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
    (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
      (x - (v.2 : ℝ) / v.1) ^ 2) with hgdef
  have hr : ∀ v ∈ arcPairs P, 0 < P ^ 3 / ((v.1 : ℝ) * Y) := fun v hv => by
    have : (1 : ℝ) ≤ v.1 := by exact_mod_cast one_le_of_mem_arcPairs hv
    positivity
  have hgi : ∀ v ∈ arcPairs P, Integrable (g v) := fun v hv =>
    (tail_integral (hr v hv) _).1
  have hGi : Integrable (fun x => ∑ v ∈ arcPairs P, g v x) := integrable_finsetSum _ hgi
  have hg0 : ∀ v x, 0 ≤ g v x := fun v x =>
    Set.indicator_nonneg (fun x _ => by positivity) x
  set S : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P)
  have hSm : MeasurableSet S := measurableSet_Ioc.inter
    ((measurableSet_majorArcs H P).diff (measurableSet_majorArcs _ P))
  have hSI : S ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSI).trans_lt measure_Ioc_lt_top).ne
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  have hfi : IntegrableOn (fun α => ‖S2star Y H P α‖ ^ 2) S := by
    refine (MemLp.of_bound (m2.norm.pow_const 2).aestronglyMeasurable (c2 ^ 2)
      (Filter.Eventually.of_forall fun α => ?_)).integrable le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (b2 α) 2
  -- step 1: pointwise majorant on S
  have step1 : (∫ α in S, ‖S2star Y H P α‖ ^ 2) ≤ ∫ α in S, ∑ v ∈ arcPairs P, g v α :=
    setIntegral_mono_on hfi hGi.integrableOn hSm fun α hα =>
      pointwise_bound hY hP hC hRP hT2 α hα.2.2
  -- step 2: enlarge to the whole line
  have step2 : (∫ α in S, ∑ v ∈ arcPairs P, g v α) ≤ ∫ α, ∑ v ∈ arcPairs P, g v α :=
    setIntegral_le_integral hGi
      (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun v _ => hg0 v x)
  -- step 3: the tail integrals
  have step3 : (∫ α, ∑ v ∈ arcPairs P, g v α) =
      2 * C ^ 2 / P ^ 3 * ∑ v ∈ arcPairs P,
        (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) := by
    rw [integral_finsetSum _ hgi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [(tail_integral (hr v hv) _).2]
    have hq : (0 : ℝ) < v.1 := by
      have : (1 : ℝ) ≤ v.1 := by exact_mod_cast one_le_of_mem_arcPairs hv
      linarith
    field_simp
  -- step 4: the arithmetic of display 24
  have step4 := arc_sum_bound hP1 hCg.le hG
  have hP3 : P ^ (5 / 2 : ℝ) / P ^ 3 = P ^ (-(1 / 2 : ℝ)) := by
    rw [show (P ^ 3 : ℝ) = P ^ (3 : ℝ) by norm_cast, ← Real.rpow_sub hP]
    norm_num
  calc (∫ α in S, ‖S2star Y H P α‖ ^ 2)
      ≤ 2 * C ^ 2 / P ^ 3 * ∑ v ∈ arcPairs P,
        (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) :=
        step1.trans (step2.trans step3.le)
    _ ≤ 2 * C ^ 2 / P ^ 3 * ((Cg + 1) * P ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left step4 (by positivity)
    _ = 2 * C ^ 2 * (Cg + 1) * (P ^ (5 / 2 : ℝ) / P ^ 3) := by ring
    _ = 2 * C ^ 2 * (Cg + 1) * P ^ (-(1 / 2 : ℝ)) := by rw [hP3]

/-- LEAF: P0088 page 6 display 24, the mean square of S2* over m0 = M minus M0.
On M(q, a) minus M0 one has |beta| above 1/(q Q0), Q0 = Y P^(-3); the Gauss sum
bound |S(q, a)| at most C q^(1/2 + eta) for the reduced sum of page 3 display 8,
display 22 for T2 on |beta| at most 1/(q Q),
which lies below Y^(-1/2)/4 in the block range, and the disjointness of the arcs
for large X give at most C P^(-1 + 2 eta + o(1)); P^(-1/2) is stated. -/
theorem S2star_minor_mean_square (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H (Real.log X ^ B) \
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B)),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) :=
  S2star_minor_mean_square_of_pieces h2

/-- PROVED. P0088 page 6 display 24, first step: Cauchy's inequality on m0, with the
mean square of S1 enlarged to the whole period. All integrands are bounded and
measurable on the period. -/
theorem termC_cauchy (X Y H P : ℝ) (n : ℕ) :
    ‖termC X Y H P n‖ ≤
      Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) *
        Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P),
          ‖S2star Y H P α‖ ^ 2) := by
  set S : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P)
  have hSm : MeasurableSet S := measurableSet_Ioc.inter
    ((measurableSet_majorArcs H P).diff (measurableSet_majorArcs _ P))
  have hSI : S ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSI).trans_lt measure_Ioc_lt_top).ne
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  have hS1c := cont_S1 X Y
  obtain ⟨c1, b1⟩ : ∃ c : ℝ, ∀ α, ‖primeSum X Y α‖ ≤ c :=
    ⟨_, fun α => (trig_norm_le ((primeWindow X Y).filter Nat.Prime) (fun _ => 1)
      (fun m => (m : ℤ)) α).trans_eq' (by simp [primeSum])⟩
  have hf : MemLp (fun α => ‖primeSum X Y α‖) (ENNReal.ofReal 2) (volume.restrict S) :=
    MemLp.of_bound hS1c.norm.aestronglyMeasurable c1
      (Filter.Eventually.of_forall fun α => by rw [norm_norm]; exact b1 α)
  have hg : MemLp (fun α => ‖S2star Y H P α‖) (ENNReal.ofReal 2) (volume.restrict S) :=
    MemLp.of_bound m2.norm.aestronglyMeasurable c2
      (Filter.Eventually.of_forall fun α => by rw [norm_norm]; exact b2 α)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun α => norm_nonneg (primeSum X Y α))
    (Filter.Eventually.of_forall fun α => norm_nonneg (S2star Y H P α)) hf hg
  have hnorm : ‖termC X Y H P n‖ ≤
      ∫ α in S, ‖primeSum X Y α‖ * ‖S2star Y H P α‖ := by
    rw [termC]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    ext α
    have h1 : ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
    rw [norm_mul, norm_mul, h1, one_mul]
  have hmono : (∫ α in S, ‖primeSum X Y α‖ ^ 2) ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2 :=
    setIntegral_mono_set (hS1c.norm.pow 2).integrableOn_Ioc
      (Filter.Eventually.of_forall fun α => by positivity)
      (Filter.Eventually.of_forall hSI)
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  refine hnorm.trans (hH.trans ?_)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)

/-- The exact statement of Prep1121KLMajor.bound24, from S1_mean_square,
S2star_minor_mean_square and termC_cauchy. No sorry of its own. -/
theorem bound24_of_pieces (h2 : T2BoundProp) : BlockErrorBound termC := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, k⟩ := S2star_minor_mean_square h2 B hB ε hε hε'
  refine ⟨Real.sqrt 2 * Real.sqrt C, max X0 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  have hc := termC_cauchy X Y H P n
  have h1 := S1_mean_square (sub_nonneg.mpr (windowY_le (by linarith) hε')) hY1
  have h3 := k X H hXa hlo hhi
  have hs1 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) ≤
      Real.sqrt 2 * Real.sqrt Y := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P), ‖S2star Y H P α‖ ^ 2) ≤
      Real.sqrt C * P ^ (-(1 / 4 : ℝ)) := by
    have hq : Real.sqrt (P ^ (-(1 / 2 : ℝ))) = P ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le]
      norm_num
    rw [← hq, ← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt h3
  have hnn1 : 0 ≤ Real.sqrt 2 * Real.sqrt Y := by positivity
  calc ‖termC X Y H P n‖ ≤ _ := hc
    _ ≤ (Real.sqrt 2 * Real.sqrt Y) * (Real.sqrt C * P ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul hs1 hs3 (Real.sqrt_nonneg _) hnn1
    _ = Real.sqrt 2 * Real.sqrt C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by ring

example : type_of% @bound24 := bound24_of_pieces

/-- PROVED. P0088 page 5 display 16: Cauchy's inequality on a measurable part S of
the period for S1 against a bounded measurable G, with the mean square of S1
enlarged to the whole period. -/
theorem cauchy_S1 (X Y : ℝ) (n : ℕ) (S : Set ℝ) (_hSm : MeasurableSet S)
    (hSI : S ⊆ Set.Ioc (0 : ℝ) 1) (G : ℝ → ℂ) (m2 : Measurable G) (c2 : ℝ)
    (b2 : ∀ α, ‖G α‖ ≤ c2) :
    ‖∫ α in S, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * G α)‖ ≤
      Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) *
        Real.sqrt (∫ α in S, ‖G α‖ ^ 2) := by
  have : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSI).trans_lt measure_Ioc_lt_top).ne
  have hS1c := cont_S1 X Y
  obtain ⟨c1, b1⟩ : ∃ c : ℝ, ∀ α, ‖primeSum X Y α‖ ≤ c :=
    ⟨_, fun α => (trig_norm_le ((primeWindow X Y).filter Nat.Prime) (fun _ => 1)
      (fun m => (m : ℤ)) α).trans_eq' (by simp [primeSum])⟩
  have hf : MemLp (fun α => ‖primeSum X Y α‖) (ENNReal.ofReal 2) (volume.restrict S) :=
    MemLp.of_bound hS1c.norm.aestronglyMeasurable c1
      (Filter.Eventually.of_forall fun α => by rw [norm_norm]; exact b1 α)
  have hg' : MemLp (fun α => ‖G α‖) (ENNReal.ofReal 2) (volume.restrict S) :=
    MemLp.of_bound m2.norm.aestronglyMeasurable c2
      (Filter.Eventually.of_forall fun α => by rw [norm_norm]; exact b2 α)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun α => norm_nonneg (primeSum X Y α))
    (Filter.Eventually.of_forall fun α => norm_nonneg (G α)) hf hg'
  have hnorm : ‖∫ α in S, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * G α)‖ ≤
      ∫ α in S, ‖primeSum X Y α‖ * ‖G α‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    ext α
    have h1 : ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
    rw [norm_mul, norm_mul, h1, one_mul]
  have hmono : (∫ α in S, ‖primeSum X Y α‖ ^ 2) ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2 :=
    setIntegral_mono_set (hS1c.norm.pow 2).integrableOn_Ioc
      (Filter.Eventually.of_forall fun α => by positivity)
      (Filter.Eventually.of_forall hSI)
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  refine hnorm.trans (hH.trans ?_)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)


/-! ## bound20 -/

/-- LEAF: P0088 page 5 displays 18 and 19 and page 6 display 20, the mean square of
S2 - S2* over M. On M(q, a), display 18 bounds |S2 - S2*|^2 by the sum over chi mod q
of |W2(beta, chi)|^2; Gallagher's lemma with the Saffari Vaughan device and
hypothesis (A2.2), here A22Corr, bound each arc integral by C P^(-3), which is what
displays 16 and 19 turn into display 20; with at most P^2 arcs the total is at most
C P^(-1). The weaker P^(-1/2) is stated. -/
theorem S2_sub_S2star_major_mean_square (h : A22Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H (Real.log X ^ B),
          ‖roughSum (windowY X ε) (Real.log X ^ B) α -
            S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  sorry

/-- The exact statement of Prep1121KLMajor.bound20, from cauchy_S1, S1_mean_square
and S2_sub_S2star_major_mean_square. No sorry of its own. -/
theorem bound20_of_pieces (h : A22Corr) : BlockErrorBound termB := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, k⟩ := S2_sub_S2star_major_mean_square h B hB ε hε hε'
  refine ⟨Real.sqrt 2 * Real.sqrt C, max X0 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  have hG : Measurable (fun α => roughSum Y P α - S2star Y H P α) :=
    (cont_S2 Y P).measurable.sub m2
  obtain ⟨c3, b3⟩ : ∃ c : ℝ, ∀ α, ‖roughSum Y P α‖ ≤ c :=
    ⟨∑ m ∈ squareWindow Y, ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖, fun α => by
      unfold roughSum
      exact trig_norm_le _ _ _ _⟩
  have hc := cauchy_S1 X Y n _ (measurableSet_Ioc.inter (measurableSet_majorArcs H P))
    Set.inter_subset_left _ hG (c3 + c2) (fun α => (norm_sub_le _ _).trans
      (add_le_add (b3 α) (b2 α)))
  have h1 := S1_mean_square (sub_nonneg.mpr (windowY_le (by linarith) hε')) hY1
  have h3 := k X H hXa hlo hhi
  have hs1 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) ≤
      Real.sqrt 2 * Real.sqrt Y := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        ‖roughSum Y P α - S2star Y H P α‖ ^ 2) ≤ Real.sqrt C * P ^ (-(1 / 4 : ℝ)) := by
    have hq : Real.sqrt (P ^ (-(1 / 2 : ℝ))) = P ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le]
      norm_num
    rw [← hq, ← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt h3
  have hnn1 : 0 ≤ Real.sqrt 2 * Real.sqrt Y := by positivity
  calc ‖termB X Y H P n‖ ≤ _ := hc
    _ ≤ (Real.sqrt 2 * Real.sqrt Y) * (Real.sqrt C * P ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul hs1 hs3 (Real.sqrt_nonneg _) hnn1
    _ = Real.sqrt 2 * Real.sqrt C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by ring

example : type_of% @bound20 := bound20_of_pieces

/-! ## bound26 -/

/-! ## S1 - S1* on M0, display 25 (ported from Prep1122S1StarM0Cut) -/

lemma pair_eq_of_cross (q q' a' : ℕ) (a : ℤ) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hcop' : Nat.Coprime a' q')
    (h : (q' : ℤ) * a = q * a') : q' = q ∧ a = a' := by
  have h1 : (q : ℤ) ∣ q' := by
    have : (q : ℤ) ∣ (q' : ℤ) * a := ⟨a', h⟩
    exact hcop.symm.dvd_of_dvd_mul_right this
  have hc' : IsCoprime (q' : ℤ) (a' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'.symm
  have h2 : (q' : ℤ) ∣ q := by
    have : (q' : ℤ) ∣ (q : ℤ) * a' := ⟨a, h.symm⟩
    exact hc'.dvd_of_dvd_mul_right this
  have hqq : q' = q := by
    have := Int.dvd_antisymm (by positivity) (by positivity) h2 h1
    exact_mod_cast this
  refine ⟨hqq, ?_⟩
  subst hqq
  have hq0 : (q' : ℤ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hq0 h

/-- PROVED, was LEAF: P0088 page 5, below display 15, "Since the intervals M(q, a) are disjoint,
this defines S_j* on M". MEDIUM. For alpha in the period interval with |q alpha - a|
at most (H/P)^(-1), q at most P and a coprime to q, no other arc of M contains alpha
once H exceeds 2 P^2, so S1*(alpha) is the single term mu(q)/phi(q) T1(alpha - a/q). -/
theorem S1star_on_arc (X Y H P α : ℝ) (q : ℕ) (a : ℤ) (hP : 1 ≤ P) (hH : 2 * P ^ 2 < H)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hq1 : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (hcop : IsCoprime a (q : ℤ))
    (hqa : |(q : ℝ) * α - a| ≤ (H / P)⁻¹) :
    S1star X Y H P α = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
      T1 X Y (α - (a : ℝ) / q) := by
  obtain ⟨hα0, hα1⟩ := hα
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by nlinarith
  have hRinv : (H / P)⁻¹ = P / H := by rw [inv_div]
  rw [hRinv] at hqa
  have hPH : P / H < 1 / (2 * P) := by
    rw [div_lt_div_iff₀ hH0 (by positivity)]; nlinarith
  have hhalf : 1 / (2 * P) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have habs := abs_le.mp hqa
  have ha0 : 0 ≤ a := by
    have : (-1 : ℝ) < a := by nlinarith
    have : (-1 : ℤ) < a := by exact_mod_cast this
    omega
  have haq : a ≤ q := by
    have : (a : ℝ) < q + 1 := by nlinarith
    have : a < (q : ℤ) + 1 := by exact_mod_cast this
    omega
  have hcast : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
    have : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    exact_mod_cast this
  have hcopN : Nat.Coprime a.toNat q := by
    have := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h2 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    rw [← h2] at hcop
    exact Nat.isCoprime_iff_coprime.mp hcop
  have hqfl : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
  have hatq : a.toNat ≤ q := by omega
  have hmem : (q, a.toNat) ∈ arcPairs P := by
    simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range]
    exact ⟨⟨⟨hq1, hqfl⟩, by omega⟩, hatq, hcopN⟩
  have harc : α ∈ arc (H / P) (q, a.toNat) := by
    show |(q : ℝ) * α - ((a.toNat : ℕ) : ℝ)| ≤ (H / P)⁻¹
    rw [hcast, hRinv]; exact hqa
  unfold S1star
  rw [Finset.sum_eq_single (q, a.toNat)]
  · rw [Set.indicator_of_mem harc]
    simp only
    rw [hcast]
  · intro v hv hne
    apply Set.indicator_of_notMem
    intro hv'
    apply hne
    obtain ⟨q', a'⟩ := v
    simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at hv
    obtain ⟨⟨⟨hq'1, hq'P⟩, _⟩, _, hcop'⟩ := hv
    have hv'' : |(q' : ℝ) * α - (a' : ℝ)| ≤ P / H := by
      have := hv'; simp only [arc, Set.mem_ofPred_eq] at this; rwa [hRinv] at this
    have hq'R : (q' : ℝ) ≤ P := by
      have : (q' : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast hq'P
      exact this.trans (Nat.floor_le hP0.le)
    have hk : |(((q' : ℤ) * a - q * a' : ℤ) : ℝ)| < 1 := by
      push_cast
      have e : (q' : ℝ) * a - q * a' = (q' : ℝ) * (a - q * α) + q * (q' * α - a') := by ring
      rw [e]
      calc |(q' : ℝ) * (a - q * α) + q * (q' * α - a')|
          ≤ |(q' : ℝ) * (a - q * α)| + |(q : ℝ) * (q' * α - a')| := abs_add_le _ _
        _ = q' * |(a : ℝ) - q * α| + q * |(q' : ℝ) * α - a'| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ q'),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ q)]
        _ ≤ P * (P / H) + P * (P / H) := by
            rw [abs_sub_comm]
            gcongr
        _ < 1 := by
            have : P * (P / H) + P * (P / H) = 2 * P ^ 2 / H := by ring
            rw [this, div_lt_one hH0]; exact hH
    have hk' : (q' : ℤ) * a - q * a' = 0 := by
      have : |((q' : ℤ) * a - q * a')| < 1 := by exact_mod_cast hk
      rw [abs_lt] at this; omega
    obtain ⟨h1, h2⟩ := pair_eq_of_cross q q' a' a hq1 hcop hcop' (by linarith)
    subst h1
    rw [h2]; simp
  · intro h; exact absurd hmem h

/-- Orthogonality: for `c` a unit mod `q`, the sum over characters of
`χ⁻¹ b * χ c` is `φ(q)` when `b = c` and `0` otherwise. -/
lemma sum_inv_mul_char (q : ℕ) [NeZero q] {c : ZMod q} (hc : IsUnit c) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = if b = c then (Nat.totient q : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · have : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = χ (Ring.inverse b * c) := by
      intro χ; rw [MulChar.inv_apply, map_mul]
    simp_rw [this, DirichletCharacter.sum_characters_eq, Ring.inverse_mul_eq_iff_eq_mul _ _ _ hb,
      mul_one]
    by_cases h : b = c
    · simp [h]
    · simp [h, Ne.symm h]
  · have hbc : b ≠ c := fun h => hb (h ▸ hc)
    rw [show (if b = c then (Nat.totient q : ℂ) else 0) = 0 from by simp [hbc]]
    exact Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ hb, zero_mul]

/-- PROVED, was LEAF: P0088 page 6 display 25, first step, "similarly to (18)", the orthogonality
of the characters modulo q. MEDIUM. For a and m coprime to q,
e(am/q) = sum over chi mod q of tau(chi^(-1)) chi(a) chi(m) / phi(q), where tau is the
Gauss sum with the additive character e(x/q). -/
theorem char_expansion (q : ℕ) [NeZero q] (a : ℤ) (m : ℕ) (ha : IsCoprime a (q : ℤ))
    (hm : Nat.Coprime m q) :
    ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) * χ (a : ZMod q) /
        (Nat.totient q : ℂ) * χ (m : ZMod q) =
      fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) := by
  set c : ZMod q := (a : ZMod q) * (m : ZMod q) with hcdef
  have hua : IsUnit (a : ZMod q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha.symm
  have hum : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hm
  have hc : IsUnit c := hua.mul hum
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have step : ∀ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) * χ (a : ZMod q) / (Nat.totient q : ℂ) *
        χ (m : ZMod q) =
      ∑ b : ZMod q, (ZMod.stdAddChar (N := q) b / (Nat.totient q : ℂ)) * (χ⁻¹ b * χ c) := by
    intro χ
    rw [gaussSum, hcdef, map_mul]
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl fun χ _ => step χ, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_inv_mul_char q hc]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [div_mul_cancel₀ _ hφ]
  have hc' : c = ((a * (m : ℤ) : ℤ) : ZMod q) := by rw [hcdef]; push_cast; rfl
  rw [hc', ZMod.stdAddChar_coe, fourier_coe_apply]
  congr 1
  push_cast
  field_simp


/-- The sum of all complex `n`-th roots of unity is `1` for `n = 1` and `0` for `n > 1`. -/
lemma sum_nthRootsFinset_one (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), x = if n = 1 then 1 else 0 := by
  have hn0 : n ≠ 0 := hn.ne'
  have : NeZero n := ⟨hn0⟩
  set ζ := Complex.exp (2 * π * I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have : ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), x = ∑ i ∈ Finset.range n, ζ ^ i := by
    symm
    refine Finset.sum_nbij (fun i => ζ ^ i) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro i _
      rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow]
    · intro i hi j hj hij
      exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · intro x hx
      try rw [Finset.mem_coe] at hx
      rw [Polynomial.mem_nthRootsFinset hn] at hx
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      exact ⟨i, by simpa using hi, rfl⟩
  rw [this]
  by_cases h1 : n = 1
  · subst h1; simp
  · rw [show (if n = 1 then (1:ℂ) else 0) = 0 from by simp [h1]]
    exact hζ.geom_sum_eq_zero (by omega)

/-- The sum of the primitive complex `n`-th roots of unity is `μ(n)`. -/
lemma sum_primitiveRoots_eq_moebius (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ primitiveRoots n ℂ, x = ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => ∑ x ∈ primitiveRoots n ℂ, x) (g := fun n => if n = 1 then (1 : ℂ) else 0)).mp
    (by
      intro n hn
      rw [← sum_nthRootsFinset_one n hn, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
        Finset.sum_biUnion]
      intro i _ j _ hij
      exact IsPrimitiveRoot.disjoint hij) n hn
  rw [← key, Finset.sum_eq_single (n, 1)]
  · simp
  · rintro ⟨d, e⟩ hde hne
    have he : e ≠ 1 := by
      rintro rfl
      rw [Nat.mem_divisorsAntidiagonal] at hde
      apply hne; simp at hde; simp [hde.1]
    simp [he]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn.ne'⟩) h

/-- PROVED, was LEAF: P0088 page 6 display 25, the principal character term, which gives
mu(q)/phi(q) T1 as in the definition of S1* on page 5. MEDIUM. The Gauss sum of the
principal character mod q is the Ramanujan sum c_q(1), the sum of the primitive q-th
roots of unity, which is mu(q). -/
theorem gaussSum_one_eq_moebius (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar (N := q)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← sum_primitiveRoots_eq_moebius q hq, gaussSum]
  have h1 : ∀ b : ZMod q, (1 : DirichletCharacter ℂ q) b * ZMod.stdAddChar b =
      if IsUnit b then ZMod.stdAddChar b else 0 := by
    intro b
    split_ifs with hb
    · rw [MulChar.one_apply hb, one_mul]
    · rw [MulChar.map_nonunit _ hb, zero_mul]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun b => ZMod.stdAddChar b) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [mem_primitiveRoots hq, Complex.isPrimitiveRoot_iff _ _ hq.ne']
    refine ⟨b.val, ZMod.val_lt b, ?_, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact hb.2
    · rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; congr 1; ring
  · intro b _ c _ h
    exact ZMod.injective_stdAddChar h
  · intro x hx
    try rw [Finset.mem_coe] at hx
    rw [mem_primitiveRoots hq, Complex.isPrimitiveRoot_iff _ _ hq.ne'] at hx
    obtain ⟨i, _, hi, rfl⟩ := hx
    refine ⟨(i : ZMod q), ?_, ?_⟩
    · try rw [Finset.mem_coe]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime i q).mpr hi⟩
    · show ZMod.stdAddChar (i : ZMod q) = _
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]; congr 1; ring


/-- PROVED. The bound for the Gauss sum of page 3 display 8 that display 25 needs: for
every character chi modulo q, primitive or not, |tau(chi)| is at most q, q terms each of
modulus at most one. P0088 page 6 display 25 uses q^(1/2); the factor q^(1/2) is not
needed, since the defect bound C Y P^(-5) of (A1.2) leaves the room of P^(3/2). -/
theorem gaussSum_norm_le_card (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ≤ (q : ℝ) := by
  have hψ : ∀ a : ZMod q, ‖ZMod.stdAddChar a‖ = 1 := by
    intro a
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  change ‖∑ a : ZMod q, χ a * ZMod.stdAddChar a‖ ≤ (q : ℝ)
  calc ‖∑ a : ZMod q, χ a * ZMod.stdAddChar a‖
      ≤ ∑ a : ZMod q, ‖χ a * ZMod.stdAddChar a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, hψ a, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = (q : ℝ) := by simp

lemma psum_norm_fourier (n : ℤ) (x : AddCircle (1 : ℝ)) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-- The step bound |e(beta) - 1| at most 2 pi |beta|. -/
lemma psum_step (β : ℝ) :
    ‖fourier (1 : ℤ) (β : AddCircle (1 : ℝ)) - 1‖ ≤ 2 * π * |β| := by
  rw [fourier_coe_apply]
  have h : (2 * (π : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (β : ℂ) / ((1 : ℝ) : ℂ))
      = Complex.I * ((2 * π * β : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos]

/-- PROVED, was LEAF: P0088 page 6, the line after display 25, "Using partial summation, we
deduce from (25) and (A1.2)". MEDIUM. If every sum of the coefficients c over the
window primes' interval I1 cut to u at most m below v is at most K, then the sum of
c(m) e(m beta) over I1 is at most K (1 + 2 pi |beta| (Y + 1)). -/
theorem partial_summation_window (X Y K β : ℝ) (hY : 0 ≤ Y) (c : ℕ → ℂ)
    (hK : ∀ u v : ℝ, X - Y ≤ u → u ≤ v → v ≤ X →
      ‖∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v), c m‖ ≤ K) :
    ‖∑ m ∈ primeWindow X Y, c m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ ≤
      K * (1 + 2 * π * |β| * (Y + 1)) := by
  set W := primeWindow X Y with hW
  have memW : ∀ m, m ∈ W ↔ m < ⌊X⌋₊ + 1 ∧ X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    intro m; simp [hW, primeWindow]
  -- K is nonnegative
  have hK0 : 0 ≤ K := by
    have := hK (X - Y) (X - Y) le_rfl le_rfl (by linarith)
    exact (norm_nonneg _).trans this
  set a : ℕ → ℂ := fun i => if i ∈ W then c i else 0 with ha
  set G : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, a j with hG
  have hGeq : ∀ k, G k = ∑ m ∈ W.filter (fun m => m < k), c m := by
    intro k
    simp only [hG, ha]
    rw [← Finset.sum_filter]
    congr 1
    ext m; simp [and_comm]
  have hGK : ∀ k, ‖G k‖ ≤ K := by
    intro k
    rw [hGeq]
    by_cases hk : (k : ℝ) ≤ X - Y
    · have : W.filter (fun m => m < k) = ∅ := by
        ext m
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hm hmk
        have := ((memW m).1 hm).2.1
        have : (m : ℝ) < k := by exact_mod_cast hmk
        linarith
      rw [this, Finset.sum_empty, norm_zero]; exact hK0
    · push Not at hk
      have := hK (X - Y) (min (k : ℝ) X) le_rfl (le_min hk.le (by linarith)) (min_le_right _ _)
      convert this using 3
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hm, hmk⟩
        have h := (memW m).1 hm
        refine ⟨hm, h.2.1, lt_min (by exact_mod_cast hmk) h.2.2⟩
      · rintro ⟨hm, -, hmv⟩
        exact ⟨hm, by exact_mod_cast (lt_of_lt_of_le hmv (min_le_left _ _))⟩
  set N := ⌈X - Y⌉₊ with hN
  set L := ⌊X⌋₊ + 1 with hL
  have hWsub : ∀ m ∈ W, N ≤ m ∧ m < L := by
    intro m hm
    have h := (memW m).1 hm
    exact ⟨Nat.ceil_le.2 h.2.1, h.1⟩
  have hG0 : G N = 0 := by
    rw [hGeq]
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_filter] at hm
    exact absurd (hWsub m hm.1).1 (by omega)
  set f : ℕ → ℂ := fun i => fourier (i : ℤ) (β : AddCircle (1 : ℝ)) with hf
  have hsum : ∑ m ∈ W, c m * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) =
      ∑ i ∈ Finset.Ico N L, f i • a i := by
    simp only [hf, ha, smul_eq_mul, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have : (Finset.Ico N L).filter (fun i => i ∈ W) = W := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · exact fun h => h.2
      · intro hm; exact ⟨hWsub m hm, hm⟩
    rw [this]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [hsum]
  by_cases hNL : N < L
  · rw [Finset.sum_Ico_by_parts f a hNL]
    have hGN : (∑ j ∈ Finset.range N, a j) = 0 := hG0
    rw [hGN, smul_zero, sub_zero]
    have hdiff : ∀ i, ‖f (i + 1) - f i‖ ≤ 2 * π * |β| := by
      intro i
      have : f (i + 1) - f i = f i * (fourier (1 : ℤ) (β : AddCircle (1 : ℝ)) - 1) := by
        simp only [hf]
        rw [mul_sub, mul_one, ← fourier_add]
        push_cast; ring_nf
      rw [this, norm_mul, hf]
      simp only
      rw [psum_norm_fourier, one_mul]
      exact psum_step β
    have hcount : ((Finset.Ico N (L - 1)).card : ℝ) ≤ Y + 1 := by
      rw [Nat.card_Ico]
      have h1 : (⌊X⌋₊ : ℝ) ≤ X ∨ ⌊X⌋₊ = 0 := by
        by_cases hX : 0 ≤ X
        · exact Or.inl (Nat.floor_le hX)
        · right; exact Nat.floor_of_nonpos (by linarith)
      have h2 : X - Y ≤ (N : ℝ) := Nat.le_ceil _
      have hL1 : L - 1 = ⌊X⌋₊ := by omega
      rw [hL1]
      rcases h1 with h1 | h1
      · rcases le_total N ⌊X⌋₊ with h | h
        · rw [Nat.cast_sub h]; linarith
        · rw [Nat.sub_eq_zero_of_le h]; simp; linarith
      · rw [h1]; simp; linarith
    calc ‖f (L - 1) • G L - ∑ i ∈ Finset.Ico N (L - 1), (f (i + 1) - f i) • G (i + 1)‖
        ≤ ‖f (L - 1) • G L‖ + ‖∑ i ∈ Finset.Ico N (L - 1), (f (i + 1) - f i) • G (i + 1)‖ :=
          norm_sub_le _ _
      _ ≤ K + ∑ i ∈ Finset.Ico N (L - 1), (2 * π * |β|) * K := by
          gcongr
          · rw [norm_smul, hf]; simp only; rw [psum_norm_fourier, one_mul]; exact hGK L
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_smul]
            exact mul_le_mul (hdiff i) (hGK _) (norm_nonneg _) (by positivity)
      _ = K + ((Finset.Ico N (L - 1)).card : ℝ) * (2 * π * |β|) * K := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ K + (Y + 1) * (2 * π * |β|) * K := by gcongr
      _ = K * (1 + 2 * π * |β| * (Y + 1)) := by ring
  · push Not at hNL
    rw [Finset.Ico_eq_empty_of_le hNL, Finset.sum_empty, norm_zero]
    positivity

/-! ## Proved pieces -/

/-- PROVED. The size facts of the block range: for large X, with P = (log X)^B,
2 P^6 is below X^(7/18), 4 P is at most X, and 2 X^(7/9) is at most X. -/
theorem block_large (B : ℝ) (_hB : 0 < B) : ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X →
    2 * (Real.log X ^ B) ^ 6 < X ^ (7 / 18 : ℝ) ∧ 4 * Real.log X ^ B ≤ X ∧
      2 * X ^ (7 / 9 : ℝ) ≤ X ∧ 1 ≤ X := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 7 / 18)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h3 := (isLittleO_log_rpow_rpow_atTop 0 (by norm_num : (0 : ℝ) < 2 / 9)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp
    (((h1.and h2).and h3).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨X1, fun X hX => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, hX1'⟩ := hX1 X hX
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1'
  have hp1 : 0 < X ^ (7 / 18 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hp3 : 0 < X ^ (2 / 9 : ℝ) := Real.rpow_pos_of_pos hX0 _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _), Real.norm_of_nonneg hp1.le] at k1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _), Real.norm_of_nonneg (by positivity),
    Real.rpow_one] at k2
  rw [Real.rpow_zero, norm_one, Real.norm_of_nonneg hp3.le] at k3
  have h6 : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num; ring_nf
  refine ⟨?_, by linarith, ?_, hX1'⟩
  · rw [h6]; linarith
  · have hsplit : X = X ^ (2 / 9 : ℝ) * X ^ (7 / 9 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h79 : 0 ≤ X ^ (7 / 9 : ℝ) := (Real.rpow_pos_of_pos hX0 _).le
    calc 2 * X ^ (7 / 9 : ℝ) ≤ X ^ (2 / 9 : ℝ) * X ^ (7 / 9 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) h79
      _ = X := hsplit.symm

/-- The exact statement of S1_sub_S1star_on_M0, from the five
pieces above and block_large, CONDITIONAL ON A12Corr. No sorry of its own. -/
theorem S1_sub_S1star_on_M0_of_leaves (hA : A12Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α ∈ Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖primeSum X (windowY X ε) α - S1star X (windowY X ε) H (Real.log X ^ B) α‖ ≤
            C * windowY X ε * (Real.log X ^ B) ^ (-2 : ℝ) := by
  intro B hB ε hε hε'
  obtain ⟨CA, XA, hCA, hA'⟩ := hA B hB ε hε hε'
  obtain ⟨X1, hX1⟩ := block_large B hB
  refine ⟨CA * (1 + 4 * π), max (max XA X1) 3, by positivity, ?_⟩
  intro X H hX hlo hhi α hα
  have hXA : XA ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXX1 : X1 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  obtain ⟨k6, k4, k79, -⟩ := hX1 X hXX1
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX3
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hY1 := windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  have hYX : windowY X ε ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX718 : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := by linarith
  have hY : 0 < Y := by linarith
  obtain ⟨hαI, q, hq1, hqP, a, hcop, hclose⟩ := hα
  have : NeZero q := ⟨by omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  -- the block range gives H above 2 P^2
  have hP4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hH : 2 * P ^ 2 < H := by
    have h1 : 2 * P ^ 2 = 2 * P ^ 6 * (P ^ 4)⁻¹ := by field_simp
    have h2 : 2 * P ^ 6 * (P ^ 4)⁻¹ < X ^ (7 / 18 + ε) * (P ^ 4)⁻¹ :=
      mul_lt_mul_of_pos_right (k6.trans_le hX718) (by positivity)
    rw [hP4] at hlo
    linarith
  have hHpos : 0 < H := by nlinarith
  -- M0 lies in M, as in arcs_subset
  have hP2 : P ^ (-4 : ℤ) ≤ P ^ (-2 : ℤ) := zpow_le_zpow_right₀ hP1 (by norm_num)
  have hH2 : H ≤ Y * P ^ (-2 : ℤ) := hhi.trans (mul_le_mul_of_nonneg_left hP2 hY.le)
  have hinv : (Y * P ^ (-2 : ℤ) / P)⁻¹ ≤ (H / P)⁻¹ :=
    inv_anti₀ (div_pos hHpos hP) (div_le_div_of_nonneg_right hH2 hP.le)
  have hstar := S1star_on_arc X Y H P α q a hP1 hH hαI hq1 hqP hcop (hclose.trans hinv)
  have hw : (Y * P ^ (-2 : ℤ) / P)⁻¹ = P ^ 3 / Y := by
    rw [zpow_neg, zpow_two]; field_simp
  set β := α - (a : ℝ) / q with hβdef
  have hqβ : (q : ℝ) * |β| ≤ P ^ 3 / Y := by
    have e1 : (q : ℝ) * α - a = q * β := by rw [hβdef]; field_simp
    rw [e1, abs_mul, abs_of_pos hq0, hw] at hclose
    exact hclose
  -- no prime of the window divides q
  have hcopm : ∀ m ∈ primeWindow X Y, m.Prime → Nat.Coprime m q := by
    intro m hm hp
    simp only [primeWindow, Finset.mem_filter] at hm
    have hmX : X - Y ≤ (m : ℝ) := hm.2.1
    have hqm : (q : ℝ) < m := by linarith
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => ?_)
    have h' := Nat.le_of_dvd (by omega) h
    have h'' : (m : ℝ) ≤ q := by exact_mod_cast h'
    linarith
  have haU : IsUnit (a : ZMod q) := by
    obtain ⟨u, v, huv⟩ := hcop
    refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
    have := congrArg (fun z : ℤ => (z : ZMod q)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero, Int.cast_one] at this
    rw [mul_comm]; exact this
  have hsplit : ∀ m : ℕ, fourier (m : ℤ) (α : AddCircle (1 : ℝ)) =
      fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) *
        fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
    intro m
    rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
    congr 1
    rw [hβdef]; push_cast; ring
  -- the character expansion of display 25
  set ψ := (ZMod.stdAddChar (N := q)) with hψ
  let c : DirichletCharacter ℂ q → ℂ := fun χ =>
    gaussSum χ⁻¹ ψ * χ (a : ZMod q) / (Nat.totient q : ℂ)
  let d : DirichletCharacter ℂ q → ℕ → ℂ := fun χ m =>
    (if m.Prime then χ m else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)
  have hc1 : c 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) := by
    simp only [c, inv_one, hψ, gaussSum_one_eq_moebius, MulChar.one_apply haU, mul_one]
  have hid : primeSum X Y α - S1star X Y H P α =
      ∑ χ : DirichletCharacter ℂ q, c χ *
        ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [hstar]
    unfold primeSum T1
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hd : ∀ χ : DirichletCharacter ℂ q,
        c χ * (d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))) =
        (c χ * (if m.Prime then χ m else 0) -
          (if χ = 1 then c χ * ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) *
            fourier (m : ℤ) (β : AddCircle (1 : ℝ)) := by
      intro χ; simp only [d]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun χ _ => hd χ), ← Finset.sum_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc1]
    by_cases hp : m.Prime
    · have hce : ∑ χ : DirichletCharacter ℂ q, c χ * χ (m : ZMod q) =
          fourier (m : ℤ) ((((a : ℝ) / q : ℝ)) : AddCircle (1 : ℝ)) :=
        char_expansion q a m hcop (hcopm m hm hp)
      simp only [hp, ite_true]
      rw [hce, hsplit m]
      ring
    · simp only [hp, ite_false, mul_zero, Finset.sum_const_zero]
      ring
  -- each W1 by partial summation and A12Corr
  have hW : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ ≤
        CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1)) := by
    intro χ
    refine partial_summation_window X Y _ β hY.le (d χ) ?_
    intro u v hu huv hv
    exact hA' X hXA q hq1 hqP χ u v hu huv hv
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hcn : ∀ χ : DirichletCharacter ℂ q, ‖c χ‖ ≤ (q : ℝ) / (Nat.totient q : ℝ) := by
    intro χ
    simp only [c, norm_div, norm_mul, Complex.norm_natCast]
    have h1 := gaussSum_norm_le_card q χ⁻¹
    have h2 := DirichletCharacter.norm_le_one χ (a : ZMod q)
    refine div_le_div_of_nonneg_right ?_ hφ.le
    calc ‖gaussSum χ⁻¹ ψ‖ * ‖χ (a : ZMod q)‖ ≤ (q : ℝ) * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (q : ℝ) := mul_one _
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = Nat.totient q := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hP5 : 0 < P ^ (-5 : ℤ) := zpow_pos hP _
  have hK0 : 0 ≤ CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1)) := by
    have : 0 ≤ 1 + 2 * π * |β| * (Y + 1) := by
      have := abs_nonneg β; have := Real.pi_pos; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hCA.le hY.le) hP5.le) this
  -- the final arithmetic of display 25 with |beta| at most P^3/(qY)
  have hP3 : P ≤ P ^ 3 := le_self_pow₀ hP1 (by norm_num)
  have hsP : (q : ℝ) ≤ P ^ 3 := hqP.trans hP3
  have hsβ : (q : ℝ) * |β| ≤ P ^ 3 / Y := hqβ
  have hinner : (q : ℝ) * (1 + 2 * π * |β| * (Y + 1)) ≤ (1 + 4 * π) * P ^ 3 := by
    have h1 : (q : ℝ) * |β| * (Y + 1) ≤ 2 * P ^ 3 := by
      calc (q : ℝ) * |β| * (Y + 1) ≤ P ^ 3 / Y * (2 * Y) :=
            mul_le_mul hsβ (by linarith) (by positivity) (by positivity)
        _ = 2 * P ^ 3 := by field_simp
    have h2 : 2 * π * ((q : ℝ) * |β| * (Y + 1)) ≤ 2 * π * (2 * P ^ 3) :=
      mul_le_mul_of_nonneg_left h1 (by have := Real.pi_pos; positivity)
    have h3 : (q : ℝ) * (1 + 2 * π * |β| * (Y + 1)) =
        (q : ℝ) + 2 * π * ((q : ℝ) * |β| * (Y + 1)) := by ring
    rw [h3]
    nlinarith [h2, hsP, hP3]
  have hpow : P ^ (-5 : ℤ) * P ^ 3 = P ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, ← zpow_natCast,
      ← zpow_add₀ hP.ne']
    norm_num
  rw [hid]
  calc ‖∑ χ : DirichletCharacter ℂ q, c χ *
          ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖c χ *
          ∑ m ∈ primeWindow X Y, d χ m * fourier (m : ℤ) (β : AddCircle (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, (q : ℝ) / (Nat.totient q : ℝ) *
          (CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1))) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hcn χ) (hW χ) (norm_nonneg _) (div_nonneg (by positivity) hφ.le)
    _ = (q : ℝ) * (CA * Y * P ^ (-5 : ℤ) * (1 + 2 * π * |β| * (Y + 1))) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp
    _ = CA * Y * P ^ (-5 : ℤ) * ((q : ℝ) * (1 + 2 * π * |β| * (Y + 1))) := by ring
    _ ≤ CA * Y * P ^ (-5 : ℤ) * ((1 + 4 * π) * P ^ 3) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (mul_nonneg hCA.le hY.le) hP5.le)
    _ = CA * (1 + 4 * π) * Y * (P ^ (-5 : ℤ) * P ^ 3) := by ring
    _ = CA * (1 + 4 * π) * Y * P ^ (-2 : ℝ) := by rw [hpow]

/-- LEAF: P0088 page 6 display 25, the pointwise form. For alpha in M0 near a/q,
beta = alpha - a/q has |beta| at most P^3/(qY). The character expansion of
S1(a/q + beta), the bound |tau(chi)| at most q^(1/2), and partial summation
against e(m beta) with hypothesis (A1.2), here A12Corr, give
|S1 - S1*| at most C Y P^(-5) q^(1/2) (1 + Y |beta|), at most C Y P^(-2). No prime
of the window divides q, since q is at most P. The arcs of M are disjoint for
large X, so S1* at alpha is the single term of that arc. -/
theorem S1_sub_S1star_on_M0 (hA : A12Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α ∈ Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖primeSum X (windowY X ε) α - S1star X (windowY X ε) H (Real.log X ^ B) α‖ ≤
            C * windowY X ε * (Real.log X ^ B) ^ (-2 : ℝ) :=
  S1_sub_S1star_on_M0_of_leaves hA

/-! ## The L1 norm of S2* over M0, display 26 second factor (ported from Prep1122S2starL1) -/

theorem sum_range_zmod_gc (m : ℕ) [NeZero m] (f : ZMod m → ℂ) :
    ∑ a ∈ Finset.range m, f (a : ZMod m) = ∑ a : ZMod m, f a := by
  apply Finset.sum_bij (s := Finset.range m) (t := (Finset.univ : Finset (ZMod m))) (fun a _ => (a : ZMod m))
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
  · intro a ha
    exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
  · intro a ha; rfl

theorem card_two_kernel_gc (m : ℕ) [NeZero m] :
    (Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun h : ZMod m => 2 * h = 0) ⊆ {0, ((m/2 : ℕ) : ZMod m)} := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    have h1 : m ∣ 2 * h.val := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact hh
    have hlt := ZMod.val_lt h
    obtain ⟨k, hk⟩ := h1
    have hk2 : k < 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    interval_cases k
    · have : h.val = 0 := by omega
      rw [ZMod.val_eq_zero] at this
      simp [this]
    · have : h.val = m / 2 := by omega
      have h2 : h = ((m/2 : ℕ) : ZMod m) := by
        rw [← this, ZMod.natCast_zmod_val]
      simp [h2]
  calc _ ≤ ({0, ((m/2 : ℕ) : ZMod m)} : Finset (ZMod m)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- PROVED. P0088 page 3 display 8 as used on page 6 displays 24 and 26, the complete
quadratic Gauss sum. For m at least one and c coprime to m the sum over y modulo m
of e(c y^2 / m) has modulus at most (2m)^(1/2), by Weyl differencing: the square
modulus is a sum over h of e(c h^2/m) times a complete linear sum that vanishes
unless m divides 2h. -/
theorem complete_gauss_coprime (m c : ℕ) (hm : 1 ≤ m) (hc : Nat.Coprime c m) :
    ‖∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))‖ ≤
      Real.sqrt (2 * m) := by
  have : NeZero m := ⟨by omega⟩
  set ψ := (ZMod.stdAddChar (N := m)) with hψ
  have std_int (a : ℤ) : U1534.ee ((a : ℝ) / m) = ψ (a : ZMod m) := by
    rw [hψ, ZMod.stdAddChar_coe]
    unfold U1534.ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : U1534.ee ((a : ℝ) / m) = ψ (a : ZMod m) := by
    simpa using std_int (a : ℤ)
  set c' : ZMod m := (c : ZMod m) with hc'
  have hG : ∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ)) =
      ∑ x : ZMod m, ψ (c' * x ^ 2) := by
    simp_rw [std_nat]
    push_cast
    exact sum_range_zmod_gc m (fun a => ψ (c' * a ^ 2))
  rw [hG]
  set G := ∑ x : ZMod m, ψ (c' * x ^ 2) with hGdef
  have hconj : (starRingEnd ℂ) G = ∑ y : ZMod m, ψ (-(c' * y ^ 2)) := by
    rw [hGdef, map_sum]
    simp_rw [AddChar.map_neg_eq_conj]
  have hprod : G * (starRingEnd ℂ) G =
      ∑ h : ZMod m, ψ (c' * h ^ 2) * ∑ y : ZMod m, ψ (y * (2 * c' * h)) := by
    rw [hconj, hGdef, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Equiv.sum_comp (Equiv.addRight y)]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [Equiv.coe_addRight]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hprim := ZMod.isPrimitive_stdAddChar m
  have hprod2 : G * (starRingEnd ℂ) G =
      ∑ h : ZMod m, ψ (c' * h ^ 2) * (if 2 * h = 0 then (m : ℂ) else 0) := by
    rw [hprod]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [AddChar.sum_mulShift _ hprim, ZMod.card]
    have hu : IsUnit c' := (ZMod.isUnit_iff_coprime c m).mpr hc
    have : (2 * c' * h = 0) ↔ (2 * h = 0) := by
      rw [show 2 * c' * h = c' * (2 * h) by ring]
      exact hu.mul_right_eq_zero
    simp only [this]
    push_cast
    rfl
  have hnorm : ‖G‖ ^ 2 ≤ 2 * m := by
    have e1 : ‖G‖ ^ 2 = ‖G * (starRingEnd ℂ) G‖ := by
      rw [norm_mul, RCLike.norm_conj, sq]
    rw [e1, hprod2]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h : ZMod m, ‖ψ (c' * h ^ 2) * (if 2 * h = 0 then (m : ℂ) else 0)‖
        = ∑ h : ZMod m, (if 2 * h = 0 then (m : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [norm_mul, hψ, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
          split_ifs <;> simp
      _ = ((Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card : ℝ) * m := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * m := by
          have := card_two_kernel_gc m
          have h2 : ((Finset.univ.filter (fun h : ZMod m => 2 * h = 0)).card : ℝ) ≤ 2 := by
            exact_mod_cast this
          nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  exact Real.le_sqrt_of_sq_le hnorm

/-! Helpers for complete_gauss_gcd, proved by a workflow prover of session S37. -/

lemma ee_add_nat_gcd (x : ℝ) (N : ℕ) : U1534.ee (x + N) = U1534.ee x := by
  unfold U1534.ee
  have : (2 * (Real.pi : ℂ) * Complex.I * ((x + N : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (x : ℂ) + (N : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma ee_period_gcd (c' n k y : ℕ) (hn : 0 < n) :
    U1534.ee (((c' * (n * k + y) ^ 2 : ℕ) : ℝ) / (n : ℝ)) =
      U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ((c' * (n * k + y) ^ 2 : ℕ) : ℝ) / (n : ℝ) =
      ((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ) + ((c' * (n * k ^ 2 + 2 * k * y) : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [this, ee_add_nat_gcd]

lemma sum_blocks_gcd (c' n : ℕ) (hn : 0 < n) (g : ℕ) :
    (∑ y ∈ Finset.range (n * g), U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ))) =
      (g : ℂ) * ∑ y ∈ Finset.range n, U1534.ee (((c' * y ^ 2 : ℕ) : ℝ) / (n : ℝ)) := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [ee_period_gcd c' n k _ hn]
    push_cast; ring

/-- PROVED. P0088 page 3 display 8 as used on page 6, the common factor step for the
complete quadratic sum. With g = (c, m), each term e(c y^2 / m) equals
e((c/g) y^2 / (m/g)), which has period m/g in y, so the sum over y modulo m is g
times the sum over y modulo m/g. -/
theorem complete_gauss_gcd (m c : ℕ) (hm : 1 ≤ m) :
    (∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))) =
      (Nat.gcd c m : ℂ) * ∑ y ∈ Finset.range (m / Nat.gcd c m),
        U1534.ee ((((c / Nat.gcd c m) * y ^ 2 : ℕ) : ℝ) / ((m / Nat.gcd c m : ℕ) : ℝ)) := by
  set g := Nat.gcd c m with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hm' : m = (m / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right c m)).symm
  have hc' : c = (c / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left c m)).symm
  have hnpos : 0 < m / g := Nat.div_pos (Nat.gcd_le_right _ hm) hgpos
  rw [← sum_blocks_gcd (c / g) (m / g) hnpos g, ← hm']
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  conv_lhs => rw [hc', hm']
  push_cast
  field_simp

/-! Helpers for gaussS_moebius, proved by a workflow prover of session S37. -/

theorem moebius_sum_divisors_complex (n : ℕ) (_hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

theorem filter_dvd_range_eq (a q d : ℕ) (hd : d ∣ q) (hd0 : 0 < d) :
    ∑ x ∈ (Finset.range q).filter (fun x => d ∣ x), (fun x => U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))) x
      = ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ)) := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left k hd0]
  symm
  refine Finset.sum_nbij' (fun y => d * y) (fun x => x / d) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left hy hd0, dvd_mul_right _ _⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact Nat.div_lt_of_lt_mul hx.1
  · intro y _
    simp [Nat.mul_div_cancel_left y hd0]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Nat.mul_div_cancel' hx.2
  · intro y hy
    simp only [Finset.mem_range] at hy
    have hk : 0 < k := by omega
    congr 1
    push_cast
    field_simp

/-- PROVED. P0088 page 3 display 8, the reduced sum S(q, a) by Moebius inversion of
the condition (x, q) = 1: the residues x = d y with d dividing q give
S(q, a) = sum over d dividing q of mu(d) times the complete sum over y modulo q/d
of e(a d y^2 / (q/d)). -/
theorem gaussS_moebius (q a : ℕ) (hq : 1 ≤ q) :
    U1534.gaussS q a = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ)) := by
  unfold U1534.gaussS
  rw [Finset.sum_filter]
  have step : ∀ x ∈ Finset.range q,
      (if Nat.Coprime x q then U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ)) else 0)
        = ∑ d ∈ q.divisors, (if d ∣ x then ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ)) else 0) := by
    intro x _
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hfil : q.divisors.filter (fun d => d ∣ x) = (Nat.gcd x q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_pos_of_pos_right _ (by omega) |>.ne'⟩
      · rintro ⟨⟨h3, h1⟩, _⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    rw [hfil, moebius_sum_divisors_complex _ (Nat.gcd_pos_of_pos_right _ (by omega))]
    unfold Nat.Coprime
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have hd' := Nat.mem_divisors.mp hd
  exact filter_dvd_range_eq a q d hd'.1 (Nat.pos_of_mem_divisors hd)

/-- PROVED. P0088 page 3 display 8, the complete quadratic sum with any coefficient:
modulus at most (2 m (c, m))^(1/2), from complete_gauss_gcd and complete_gauss_coprime. -/
theorem complete_gauss_le (m c : ℕ) (hm : 1 ≤ m) :
    ‖∑ y ∈ Finset.range m, U1534.ee (((c * y ^ 2 : ℕ) : ℝ) / (m : ℝ))‖ ≤
      Real.sqrt (2 * m * Nat.gcd c m) := by
  set g := Nat.gcd c m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right c (by omega)
  have hgm : g ∣ m := Nat.gcd_dvd_right c m
  have hgc : g ∣ c := Nat.gcd_dvd_left c m
  have hm' : 1 ≤ m / g := (Nat.one_le_div_iff hg0).mpr (Nat.le_of_dvd (by omega) hgm)
  have hcop : Nat.Coprime (c / g) (m / g) := Nat.coprime_div_gcd_div_gcd hg0
  rw [complete_gauss_gcd m c hm, norm_mul, Complex.norm_natCast]
  have h1 := complete_gauss_coprime (m / g) (c / g) hm' hcop
  have hmg : ((m / g : ℕ) : ℝ) = (m : ℝ) / g := by
    rw [Nat.cast_div hgm (by exact_mod_cast hg0.ne')]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  calc (g : ℝ) * ‖_‖ ≤ g * Real.sqrt (2 * ((m / g : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hgR.le
    _ = Real.sqrt (2 * m * g) := by
        rw [hmg, show (2 : ℝ) * m * g = (g : ℝ) ^ 2 * (2 * ((m : ℝ) / g)) by field_simp,
          Real.sqrt_mul (x := (g : ℝ) ^ 2) (by positivity), Real.sqrt_sq hgR.le]

/-- PROVED. The divisor bound with exponent 1/8. Copy of the proved
BHP1997.Decomp312c.card_divisors_le_rpow, which is private there. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- PROVED. P0088 page 3 display 8, the bound used on page 6: for a coprime to q,
|S(q, a)| is at most C q^(1/2 + eta) with eta = 1/8. From gaussS_moebius,
complete_gauss_le, (a d, q/d) = (d, q/d) at most d, and the divisor bound. -/
theorem gaussS_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
    ‖U1534.gaussS q a‖ ≤ C * (q : ℝ) ^ (5 / 8 : ℝ) := by
  obtain ⟨Cd, hCd, hd⟩ := card_divisors_le_rpow (ε := 1 / 8) (by norm_num)
  refine ⟨Cd * Real.sqrt 2, by positivity, fun q a hq ha => ?_⟩
  rw [gaussS_moebius q a hq]
  have hterm : ∀ d ∈ q.divisors, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ y ∈ Finset.range (q / d), U1534.ee ((((a * d) * y ^ 2 : ℕ) : ℝ) / ((q / d : ℕ) : ℝ))‖ ≤
        Real.sqrt (2 * q) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hqd : 1 ≤ q / d := (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdq)
    have hmu : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hcop : Nat.Coprime a (q / d) := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdq) ha
    have hgcd : Nat.gcd (a * d) (q / d) ≤ d := by
      rw [Nat.Coprime.gcd_mul_left_cancel d hcop]
      exact Nat.le_of_dvd hd0 (Nat.gcd_dvd_left _ _)
    have hprod : ((q / d : ℕ) : ℝ) * (Nat.gcd (a * d) (q / d) : ℝ) ≤ q := by
      have h : (q / d) * Nat.gcd (a * d) (q / d) ≤ q :=
        (Nat.mul_le_mul_left _ hgcd).trans (Nat.div_mul_cancel hdq).le
      exact_mod_cast h
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖_‖
        ≤ 1 * Real.sqrt (2 * ((q / d : ℕ) : ℝ) * (Nat.gcd (a * d) (q / d) : ℝ)) :=
          mul_le_mul hmu (complete_gauss_le (q / d) (a * d) hqd) (norm_nonneg _) zero_le_one
      _ ≤ Real.sqrt (2 * q) := by
          rw [one_mul, mul_assoc]
          exact Real.sqrt_le_sqrt (by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc ‖∑ d ∈ q.divisors, _‖ ≤ ∑ d ∈ q.divisors, Real.sqrt (2 * q) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (q.divisors.card : ℝ) * Real.sqrt (2 * q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cd * (q : ℝ) ^ (1 / 8 : ℝ)) * Real.sqrt (2 * q) :=
        mul_le_mul_of_nonneg_right (hd q) (Real.sqrt_nonneg _)
    _ = Cd * Real.sqrt 2 * (q : ℝ) ^ (5 / 8 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (q : ℝ)]
        have : (q : ℝ) ^ (1 / 8 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (5 / 8 : ℝ) := by
          rw [← Real.rpow_add hq0]; norm_num
        rw [← this]; ring

/-! ## The arcs of displays 15 and 23 -/

/-- PROVED. P0088 page 4 display 15: the closed arc of width R^(-1) in q alpha is the
interval of half length R^(-1)/q about a/q. -/
theorem arc_eq_Icc (R : ℝ) (v : ℕ × ℕ) (hq : 1 ≤ v.1) :
    arc R v = Set.Icc ((v.2 : ℝ) / v.1 - R⁻¹ / v.1) ((v.2 : ℝ) / v.1 + R⁻¹ / v.1) := by
  have hq0 : (0 : ℝ) < v.1 := by exact_mod_cast hq
  ext α
  simp only [arc, Set.mem_setOf_eq, Set.mem_Icc]
  have h : (v.1 : ℝ) * α - v.2 = v.1 * (α - v.2 / v.1) := by field_simp
  rw [h, abs_mul, abs_of_pos hq0, ← le_div_iff₀' hq0, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- PROVED. P0088 page 4 display 15 and page 6 display 23: an arc about a/q and an arc
about a'/q', both fractions reduced, meet only when q = q' and a = a', once
q' r1 + q r2 < 1, since otherwise |a q' - a' q| is at least one. -/
theorem arc_localize {q q' a : ℕ} {a' : ℤ} {α r1 r2 : ℝ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : Nat.Coprime a q) (ha' : IsCoprime a' (q' : ℤ))
    (h1 : |(q : ℝ) * α - a| ≤ r1) (h2 : |(q' : ℝ) * α - a'| ≤ r2)
    (hsmall : (q' : ℝ) * r1 + q * r2 < 1) : q = q' ∧ (a : ℤ) = a' := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq0' : (0 : ℝ) ≤ q' := by positivity
  have hk : |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| < 1 := by
    have e : (((a : ℤ) * q' - a' * q : ℤ) : ℝ) =
        q * ((q' : ℝ) * α - a') - q' * ((q : ℝ) * α - a) := by push_cast; ring
    rw [e]
    calc |(q : ℝ) * ((q' : ℝ) * α - a') - q' * ((q : ℝ) * α - a)|
        ≤ |(q : ℝ) * ((q' : ℝ) * α - a')| + |(q' : ℝ) * ((q : ℝ) * α - a)| := abs_sub _ _
      _ = q * |(q' : ℝ) * α - a'| + q' * |(q : ℝ) * α - a| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq0']
      _ ≤ q * r2 + q' * r1 :=
          add_le_add (mul_le_mul_of_nonneg_left h2 hq0) (mul_le_mul_of_nonneg_left h1 hq0')
      _ < 1 := by linarith
  have hk' : |((a : ℤ) * q' - a' * q)| < 1 := by
    have : ((|((a : ℤ) * q' - a' * q)| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hk
    exact_mod_cast this
  have hk0 : (a : ℤ) * q' = a' * q := by
    have := Int.abs_lt_one_iff.mp hk'
    linarith
  have hca : IsCoprime (a : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ha
  have hd1 : (q : ℤ) ∣ q' := by
    apply hca.symm.dvd_of_dvd_mul_right
    exact ⟨a', by rw [mul_comm, hk0, mul_comm]⟩
  have hd2 : (q' : ℤ) ∣ q := by
    apply ha'.symm.dvd_of_dvd_mul_right
    exact ⟨a, by rw [mul_comm, ← hk0, mul_comm]⟩
  have hqq : q = q' := Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hd1)
    (Int.natCast_dvd_natCast.mp hd2)
  refine ⟨hqq, ?_⟩
  subst hqq
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  exact mul_right_cancel₀ hqz hk0

/-- PROVED. P0088 page 6 display 26, the pointwise step: on M0, for large X, every wide
arc M(q, a) of display 15 through alpha is the narrow arc of display 23 with the same
q and a, so |S2*(alpha)| is at most the sum over the narrow arcs through alpha of
|S(q, a)|/phi(q) |T2(alpha - a/q)|. -/
theorem S2star_norm_le_on_M0 {Y H P α : ℝ} (hP : 1 ≤ P)
    (hsmall : P * (H / P)⁻¹ + P * (Y * P ^ (-2 : ℤ) / P)⁻¹ < 1)
    (hα : α ∈ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    ‖S2star Y H P α‖ ≤ ∑ v ∈ arcPairs P, (arc (Y * P ^ (-2 : ℤ) / P) v).indicator
      (fun α => ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) *
        ‖T2 Y P (α - v.2 / v.1)‖) α := by
  obtain ⟨q', hq'1, hq'P, a', ha', hclose⟩ := hα
  unfold S2star
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v hv => ?_)
  obtain ⟨hvprod, _, hvcop⟩ := Finset.mem_filter.mp hv
  rw [Finset.mem_product, Finset.mem_Icc] at hvprod
  have hq1 : 1 ≤ v.1 := hvprod.1.1
  have hqP : (v.1 : ℝ) ≤ P := (Nat.cast_le.mpr hvprod.1.2).trans (Nat.floor_le (by linarith))
  by_cases hin : α ∈ arc (H / P) v
  · rw [Set.indicator_of_mem hin]
    have hin' : |(v.1 : ℝ) * α - v.2| ≤ (H / P)⁻¹ := hin
    have hr1 : 0 ≤ (H / P)⁻¹ := (abs_nonneg _).trans hin'
    have hr2 : 0 ≤ (Y * P ^ (-2 : ℤ) / P)⁻¹ := (abs_nonneg _).trans hclose
    have hq'P' : (q' : ℝ) ≤ P := hq'P
    obtain ⟨hqq, haa⟩ := arc_localize hq1 hq'1 hvcop ha' hin' hclose (by
      have := mul_le_mul_of_nonneg_right hq'P' hr1
      have := mul_le_mul_of_nonneg_right hqP hr2
      linarith)
    have hin0 : α ∈ arc (Y * P ^ (-2 : ℤ) / P) v := by
      show |(v.1 : ℝ) * α - v.2| ≤ _
      have e1 : (v.1 : ℝ) = q' := by exact_mod_cast hqq
      have e2 : ((v.2 : ℕ) : ℝ) = (a' : ℝ) := by
        rw [← haa]; norm_cast
      rw [e1, e2]; exact hclose
    rw [Set.indicator_of_mem hin0, norm_mul, norm_div, Complex.norm_natCast]
  · rw [Set.indicator_of_notMem hin, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

/-! ## The arc integral of T2 from display 22 -/

/-- PROVED. P0088 page 6 display 26: on an arc of width R^(-1) in q alpha, display 22
for T2, |T2(beta)| at most C Y^(1/2)/(1 + Y |beta|), integrates to at most
2 C Y^(-1/2) log(1 + Y R^(-1)). -/
theorem T2_arc_integral {Y P C R : ℝ} (v : ℕ × ℕ) (hq : 1 ≤ v.1) (hY : 0 < Y) (hR : 0 < R)
    (hC : 0 ≤ C)
    (hT : ∀ β : ℝ, |β| ≤ R⁻¹ → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|)) :
    ∫ α in arc R v, ‖T2 Y P (α - v.2 / v.1)‖ ≤
      2 * C * Real.log (1 + Y * R⁻¹) / Real.sqrt Y := by
  have hq0 : (0 : ℝ) < v.1 := by exact_mod_cast hq
  have hw : 0 ≤ R⁻¹ / v.1 := by positivity
  have hwR : R⁻¹ / v.1 ≤ R⁻¹ := div_le_self (inv_nonneg.mpr hR.le) (by exact_mod_cast hq)
  set w := R⁻¹ / v.1 with hwdef
  rw [arc_eq_Icc R v hq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun β => ‖T2 Y P β‖)]
  have e1 : (v.2 : ℝ) / v.1 - w - v.2 / v.1 = -w := by ring
  have e2 : (v.2 : ℝ) / v.1 + w - v.2 / v.1 = w := by ring
  rw [e1, e2]
  set g : ℝ → ℝ := fun β => C * Real.sqrt Y / (1 + Y * |β|) with hg
  have hgc : Continuous g := by
    refine Continuous.div continuous_const (by fun_prop) (fun β => ?_)
    have : 0 ≤ Y * |β| := by positivity
    linarith
  have hTc : Continuous fun β => ‖T2 Y P β‖ := (trig_continuous _ _ _).norm
  have h1 : (∫ β in -w..w, ‖T2 Y P β‖) ≤ ∫ β in -w..w, g β :=
    intervalIntegral.integral_mono_on (by linarith) (hTc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
      (fun β hβ => hT β (by rw [abs_le]; constructor <;> linarith [hβ.1, hβ.2]))
  have hsplit : (∫ β in -w..w, g β) = 2 * ∫ β in (0 : ℝ)..w, g β := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := w) g
    rw [neg_zero] at h
    have hge : (fun x => g (-x)) = g := by
      funext x; simp only [hg, abs_neg]
    rw [hge] at h
    rw [← h]; ring
  have heval : (∫ β in (0 : ℝ)..w, g β) = C * Real.sqrt Y * (Real.log (1 + Y * w) / Y) := by
    have hcongr : (∫ β in (0 : ℝ)..w, g β) =
        ∫ β in (0 : ℝ)..w, C * Real.sqrt Y * (1 + Y * β)⁻¹ := by
      refine intervalIntegral.integral_congr (fun β hβ => ?_)
      rw [Set.uIcc_of_le hw] at hβ
      simp only [hg, abs_of_nonneg hβ.1, div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_comp_add_mul (fun x : ℝ => x⁻¹) hY.ne' 1 (a := 0) (b := w)
    rw [this, mul_zero, add_zero, integral_inv_of_pos one_pos (by positivity), div_one,
      smul_eq_mul]
    ring
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hlog : Real.log (1 + Y * w) ≤ Real.log (1 + Y * R⁻¹) :=
    Real.log_le_log (by positivity) (by nlinarith)
  calc (∫ β in -w..w, ‖T2 Y P β‖) ≤ ∫ β in -w..w, g β := h1
    _ = 2 * (C * Real.sqrt Y * (Real.log (1 + Y * w) / Y)) := by rw [hsplit, heval]
    _ = 2 * C * Real.log (1 + Y * w) * (Real.sqrt Y / Y) := by ring
    _ = 2 * C * Real.log (1 + Y * w) / Real.sqrt Y := by
        have : Real.sqrt Y / Y = 1 / Real.sqrt Y := by
          rw [div_eq_div_iff hY.ne' hsY.ne', one_mul, Real.mul_self_sqrt hY.le]
        rw [this]; ring
    _ ≤ 2 * C * Real.log (1 + Y * R⁻¹) / Real.sqrt Y := by
        apply div_le_div_of_nonneg_right _ hsY.le
        exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-! ## The sum over the arcs -/

/-- PROVED. P0088 page 6 display 26, the sum over q at most P and a of |S(q, a)|/phi(q):
with |S(q, a)| at most C q^(5/8), at most phi(q) + 1 values of a for each q, and
q at most P, the sum is at most 2 C P^(13/8). -/
theorem arcPairs_sum_le {C P : ℝ} (hC : 0 < C) (hP : 1 ≤ P)
    (hS : ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ‖U1534.gaussS q a‖ ≤ C * (q : ℝ) ^ (5 / 8 : ℝ)) :
    ∑ v ∈ arcPairs P, ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) ≤
      2 * C * P ^ (13 / 8 : ℝ) := by
  have hP0 : 0 ≤ P := by linarith
  have hinner : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊,
      (∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
        ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ)) ≤ 2 * C * P ^ (5 / 8 : ℝ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hφpos : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφpos
    have hcard : ((Finset.range (⌊P⌋₊ + 1)).filter
        (fun a => a ≤ q ∧ Nat.Coprime a q)).card ≤ 2 * Nat.totient q := by
      have hsub : (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q) ⊆
          insert q ((Finset.range q).filter (fun a => q.Coprime a)) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        rcases eq_or_lt_of_le ha.2.1 with h | h
        · simp [h]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, ha.2.2.symm⟩)
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ((Finset.range q).filter (fun a => q.Coprime a)).card + 1 :=
            Finset.card_insert_le _ _
        _ = Nat.totient q + 1 := by rw [Nat.totient_eq_card_coprime]
        _ ≤ 2 * Nat.totient q := by omega
    have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hP0)
    have hterm : ∀ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
        ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ) ≤ C * P ^ (5 / 8 : ℝ) / Nat.totient q := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      apply div_le_div_of_nonneg_right _ hφ.le
      exact (hS q a hq.1 ha'.2).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hqP (by norm_num)) hC.le)
    calc _ ≤ ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          C * P ^ (5 / 8 : ℝ) / Nat.totient q := Finset.sum_le_sum hterm
      _ = (((Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q)).card : ℝ) *
          (C * P ^ (5 / 8 : ℝ) / Nat.totient q) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Nat.totient q : ℝ) * (C * P ^ (5 / 8 : ℝ) / Nat.totient q) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 2 * C * P ^ (5 / 8 : ℝ) := by field_simp
  have hsplit : (∑ v ∈ arcPairs P, ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ)) =
      ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
        ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          ‖U1534.gaussS q a‖ / (Nat.totient q : ℝ) := by
    unfold arcPairs
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_filter]
  rw [hsplit]
  calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, 2 * C * P ^ (5 / 8 : ℝ) := Finset.sum_le_sum hinner
    _ = (⌊P⌋₊ : ℝ) * (2 * C * P ^ (5 / 8 : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ P * (2 * C * P ^ (5 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hP0) (by positivity)
    _ = 2 * C * P ^ (13 / 8 : ℝ) := by
        rw [show (13 / 8 : ℝ) = 1 + 5 / 8 by norm_num, Real.rpow_add (by linarith),
          Real.rpow_one]
        ring

/-- PROVED. log(1 + P^3) is at most 25 P^(1/8) for P at least one; the log factor of
display 26 is absorbed by eta = 1/8. -/
theorem log_one_add_cube_le {P : ℝ} (hP : 1 ≤ P) :
    Real.log (1 + P ^ 3) ≤ 25 * P ^ (1 / 8 : ℝ) := by
  have hP0 : 0 < P := by linarith
  have hP3 : 1 ≤ P ^ 3 := one_le_pow₀ hP
  have h1 : Real.log (1 + P ^ 3) ≤ Real.log (2 * P ^ 3) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have h2 : Real.log P ≤ P ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div hP0.le (by norm_num)
  have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have h4 : 1 ≤ P ^ (1 / 8 : ℝ) := Real.one_le_rpow hP (by norm_num)
  push_cast at h1
  have h2' : Real.log P ≤ 8 * P ^ (1 / 8 : ℝ) := by
    have : P ^ (1 / 8 : ℝ) / (1 / 8) = 8 * P ^ (1 / 8 : ℝ) := by ring
    linarith
  linarith

/-- PROVED. For large X, 4 (log X)^(6B) is at most X^(1/4), since every power of
log X is o(X^(1/4)). -/
theorem eventually_small (B : ℝ) :
    ∃ X0 : ℝ, ∀ X, X0 ≤ X → 3 ≤ X ∧ 4 * (Real.log X ^ B) ^ 6 ≤ X ^ (1 / 4 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X1 3, fun X hX => ⟨(le_max_right _ _).trans hX, ?_⟩⟩
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hb := hX1 X ((le_max_left _ _).trans hX)
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
  have hpow : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; ring_nf
  rw [hpow]; linarith

/-! ## Assembly -/

/-- The exact statement of S2star_M0_L1, P0088 page 6 display 26
second factor, from S2star_norm_le_on_M0, T2_arc_integral, arcPairs_sum_le,
gaussS_norm_le and log_one_add_cube_le. No sorry anywhere: PROVED,
CONDITIONAL ON T2BoundProp, display 22 for T2. -/
theorem S2star_M0_L1_of_pieces (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖) ≤
            C * (Real.log X ^ B) ^ (7 / 4 : ℝ) / Real.sqrt (windowY X ε) := by
  intro B hB ε hε hε'
  obtain ⟨CT, XT, hCT, hT⟩ := h2 B hB ε hε hε'
  obtain ⟨CG, hCG, hG⟩ := gaussS_norm_le
  obtain ⟨XE, hE⟩ := eventually_small B
  refine ⟨2 * CG * (2 * CT * 25), max XT XE, by positivity, ?_⟩
  intro X H hX hlo _hhi
  obtain ⟨hX3, hsm⟩ := hE X ((le_max_right _ _).trans hX)
  have hT' := hT X ((le_max_left _ _).trans hX)
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX3
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hY1 := windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  have hsY : X ^ (1 / 4 : ℝ) ≤ Real.sqrt (windowY X ε) := by
    rw [windowY, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX14 : X ^ (1 / 4 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP0 : 0 < P := by linarith
  have hY0 : 0 < Y := by linarith
  have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
  have hsqY : Real.sqrt Y ≤ Y := by nlinarith
  have hP3 : P ^ 3 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP4 : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  -- the narrow arc width
  set R0 := Y * P ^ (-2 : ℤ) / P with hR0
  have hR0pos : 0 < R0 := by positivity
  have hR0inv : R0⁻¹ = P ^ 3 / Y := by
    rw [hR0, zpow_neg, zpow_ofNat]; field_simp
  -- the lower bound for H
  have hPm4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hH : 4 * P ^ 2 ≤ H := by
    rw [hPm4] at hlo
    have h4 : X ^ (1 / 4 : ℝ) * (P ^ 4)⁻¹ ≤ H :=
      (mul_le_mul_of_nonneg_right hX14 (by positivity)).trans hlo
    have h5 : 4 * P ^ 2 = 4 * P ^ 6 * (P ^ 4)⁻¹ := by field_simp
    rw [h5]
    exact (mul_le_mul_of_nonneg_right hsm (by positivity)).trans h4
  have hH0 : 0 < H := by nlinarith
  have hsmall : P * (H / P)⁻¹ + P * R0⁻¹ < 1 := by
    have e1 : P * (H / P)⁻¹ = P ^ 2 / H := by field_simp
    rw [e1, hR0inv]
    have a1 : P ^ 2 / H ≤ 1 / 4 := by
      rw [div_le_iff₀ hH0]; linarith
    have a2 : P * (P ^ 3 / Y) ≤ 1 / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ hY0]; nlinarith
    linarith
  -- display 22 for T2 on the narrow arcs
  have hTarc : ∀ β : ℝ, |β| ≤ R0⁻¹ → ‖T2 Y P β‖ ≤ CT * Real.sqrt Y / (1 + Y * |β|) := by
    intro β hβ
    apply hT' β
    rw [hR0inv] at hβ
    refine hβ.trans ?_
    have h4 : 4 * P ^ 3 ≤ Real.sqrt Y := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h4 hsY0.le
    rw [div_le_div_iff₀ hY0 (by positivity)]
    nlinarith
  have hlogP : Real.log (1 + Y * R0⁻¹) ≤ 25 * P ^ (1 / 8 : ℝ) := by
    rw [hR0inv, mul_div_cancel₀ _ hY0.ne']
    exact log_one_add_cube_le hP1
  -- the majorant
  set K : ℕ × ℕ → ℝ := fun v => ‖U1534.gaussS v.1 v.2‖ / (Nat.totient v.1 : ℝ) with hK
  set G : ℝ → ℝ := fun α => ∑ v ∈ arcPairs P, (arc R0 v).indicator
    (fun α => K v * ‖T2 Y P (α - v.2 / v.1)‖) α with hGdef
  have hv1 : ∀ v ∈ arcPairs P, 1 ≤ v.1 := by
    intro v hv
    obtain ⟨hvprod, _⟩ := Finset.mem_filter.mp hv
    rw [Finset.mem_product, Finset.mem_Icc] at hvprod
    exact hvprod.1.1
  have hint : ∀ v ∈ arcPairs P,
      Integrable ((arc R0 v).indicator (fun α => K v * ‖T2 Y P (α - v.2 / v.1)‖)) := by
    intro v hv
    rw [integrable_indicator_iff (measurableSet_arc R0 v), arc_eq_Icc R0 v (hv1 v hv)]
    exact (continuous_const.mul
      ((trig_continuous _ _ _).comp (continuous_sub_right _)).norm).integrableOn_Icc
  have hGint : Integrable G := integrable_finsetSum _ hint
  have hG0 : ∀ α, 0 ≤ G α := fun α =>
    Finset.sum_nonneg fun v _ => Set.indicator_nonneg (fun _ _ => by positivity) _
  set S := Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P with hS
  have hSm : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_majorArcs _ P)
  have step1 : (∫ α in S, ‖S2star Y H P α‖) ≤ ∫ α in S, G α :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun α => norm_nonneg _)
      hGint.integrableOn
      (ae_restrict_of_forall_mem hSm fun α hα => S2star_norm_le_on_M0 hP1 hsmall hα.2)
  have step2 : (∫ α in S, G α) ≤ ∫ α, G α :=
    setIntegral_le_integral hGint (Filter.Eventually.of_forall hG0)
  have step3 : (∫ α, G α) = ∑ v ∈ arcPairs P, K v * ∫ α in arc R0 v,
      ‖T2 Y P (α - v.2 / v.1)‖ := by
    rw [hGdef, integral_finset_sum _ hint]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_indicator (measurableSet_arc R0 v), integral_const_mul]
  have hL0 : 0 ≤ Real.log (1 + Y * R0⁻¹) := Real.log_nonneg (by
    have : 0 ≤ Y * R0⁻¹ := by positivity
    linarith)
  have step4 : (∑ v ∈ arcPairs P, K v * ∫ α in arc R0 v, ‖T2 Y P (α - v.2 / v.1)‖) ≤
      (∑ v ∈ arcPairs P, K v) * (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => ?_
    exact mul_le_mul_of_nonneg_left
      (T2_arc_integral v (hv1 v hv) hY0 hR0pos hCT.le hTarc) (by positivity)
  have step5 : (∑ v ∈ arcPairs P, K v) ≤ 2 * CG * P ^ (13 / 8 : ℝ) :=
    arcPairs_sum_le hCG hP1 hG
  have hfin : (∑ v ∈ arcPairs P, K v) * (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) ≤
      2 * CG * (2 * CT * 25) * P ^ (7 / 4 : ℝ) / Real.sqrt Y := by
    have hA : (2 * CT * Real.log (1 + Y * R0⁻¹) / Real.sqrt Y) ≤
        2 * CT * (25 * P ^ (1 / 8 : ℝ)) / Real.sqrt Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogP (by positivity)) hsY0.le
    have hpp : P ^ (13 / 8 : ℝ) * P ^ (1 / 8 : ℝ) = P ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_add hP0]; norm_num
    calc _ ≤ (2 * CG * P ^ (13 / 8 : ℝ)) * (2 * CT * (25 * P ^ (1 / 8 : ℝ)) / Real.sqrt Y) :=
          mul_le_mul step5 hA (by positivity) (by positivity)
      _ = 2 * CG * (2 * CT * 25) * (P ^ (13 / 8 : ℝ) * P ^ (1 / 8 : ℝ)) / Real.sqrt Y := by
          ring
      _ = _ := by rw [hpp]
  exact step1.trans (step2.trans (step3.le.trans (step4.trans hfin)))

/-- LEAF: P0088 page 6 display 26, the L1 norm of S2* over M0. On each arc
|beta| is at most P^3/(qY), display 22 for T2 gives the integral at most
2 Y^(-1/2) log(1 + P^3), and the sum over q at most P and a of
|S(q, a)|/phi(q), with |S(q, a)| at most C q^(1/2 + eta), is at most C P^(3/2 + eta).
With eta = 1/8 the total is at most C P^(7/4) Y^(-1/2). -/
theorem S2star_M0_L1 (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖) ≤
            C * (Real.log X ^ B) ^ (7 / 4 : ℝ) / Real.sqrt (windowY X ε) :=
  S2star_M0_L1_of_pieces h2

/-- PROVED. P0088 page 6 display 26, first step: a pointwise bound K for S1 - S1*
on M0 gives the bound K times the L1 norm of S2* over M0. -/
theorem termD_le (X Y H P K : ℝ) (n : ℕ)
    (hK : ∀ α ∈ Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P,
      ‖primeSum X Y α - S1star X Y H P α‖ ≤ K) :
    ‖termD X Y H P n‖ ≤
      K * ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P, ‖S2star Y H P α‖ := by
  set S : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P
  have hSm : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_majorArcs _ P)
  have hSI : S ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSI).trans_lt measure_Ioc_lt_top).ne
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  have hgi : Integrable (fun α => K * ‖S2star Y H P α‖) (volume.restrict S) :=
    (Integrable.of_bound m2.norm.aestronglyMeasurable c2
      (Filter.Eventually.of_forall fun α => by rw [norm_norm]; exact b2 α)).const_mul K
  rw [termD, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun α => norm_nonneg _) hgi ?_
  refine (ae_restrict_of_forall_mem hSm fun α hα => ?_)
  have h1 : ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
  show ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      ((primeSum X Y α - S1star X Y H P α) * S2star Y H P α)‖ ≤ K * ‖S2star Y H P α‖
  rw [norm_mul, norm_mul, h1, one_mul]
  exact mul_le_mul_of_nonneg_right (hK α hα) (norm_nonneg _)

/-- The exact statement of Prep1121KLMajor.bound26, from S1_sub_S1star_on_M0,
S2star_M0_L1 and termD_le. No sorry of its own. -/
theorem bound26_of_pieces (hA : A12Corr) (h2 : T2BoundProp) : BlockErrorBound termD := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := S1_sub_S1star_on_M0 hA B hB ε hε hε'
  obtain ⟨C2, X2, hC2, k2⟩ := S2star_M0_L1 h2 B hB ε hε hε'
  refine ⟨C1 * C2, max (max X1 X2) 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X1 ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  have hY : 0 < Y := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hd := termD_le X Y H P _ n (k1 X H hXa hlo hhi)
  have hKnn : 0 ≤ C1 * Y * P ^ (-2 : ℝ) := by positivity
  refine hd.trans ((mul_le_mul_of_nonneg_left (k2 X H hXb hlo hhi) hKnn).trans (le_of_eq ?_))
  have hp : P ^ (-2 : ℝ) * P ^ (7 / 4 : ℝ) = P ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hP]; norm_num
  have hyy : Y / Real.sqrt Y = Real.sqrt Y := Real.div_sqrt
  calc C1 * Y * P ^ (-2 : ℝ) * (C2 * P ^ (7 / 4 : ℝ) / Real.sqrt Y)
      = C1 * C2 * (Y / Real.sqrt Y) * (P ^ (-2 : ℝ) * P ^ (7 / 4 : ℝ)) := by ring
    _ = C1 * C2 * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by rw [hp, hyy]

example : type_of% @bound26 := bound26_of_pieces

end LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.arcs_subset
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.major_integrands_integrable
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.major_decomp_general
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.split_bound
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.T1_trivial
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.S1_mean_square
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.termC_cauchy
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.major_decomp_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.T1_bound_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.T2_bound_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.bound24_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.termD_le
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.cauchy_S1
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.bound20_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLMajorCut.bound26_of_pieces

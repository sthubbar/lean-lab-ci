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
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  sorry

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
            C * windowY X ε * (Real.log X ^ B) ^ (-2 : ℝ) := by
  sorry

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
            C * (Real.log X ^ B) ^ (7 / 4 : ℝ) / Real.sqrt (windowY X ε) := by
  sorry

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

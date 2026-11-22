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
  sorry

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

/-! ## T2_bound -/

/-- LEAF: P0088 page 6 display 22 for j = 2, the trivial bound. The weight f2 of
page 15 is bounded on the window of m between Y^(1/2)/2 and Y^(1/2), since its
integral term is at most log(log u^(1/2) / log z0) / log u, and the window holds at
most Y^(1/2) + 1 integers. -/
theorem T2_trivial :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ,
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤ C * Real.sqrt (windowY X ε) := by
  sorry

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
  sorry

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

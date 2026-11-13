/-
ROUTE BURST session 8, part 2 of the LZPowersOfTwo split: the leaf
`prime_integer_l2_small418`, P0079 page 8, Lemmas 6 and 7, and page 9, the J3 estimate.
Paper: P0079 A. Languasco and A. Zaccagnini, arXiv 0811.3663v2, 2 Apr 2009.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`prime_integer_l2_small_p2` has the exact statement of `prime_integer_l2_small418` and is
proved here with no open step of its own from two cited outside inputs:
* `gallagher_lemma6_p2`: Lemma 6 of the paper, Gallagher's lemma in the form of
  Bruedern, Cook and Perelli, Lemma 1, page 8.
* `saffari_vaughan_lemma7_p2`: Lemma 7 of the paper, Saffari and Vaughan section 6, page 8.
The substitution `β = λα`, the choice `Y = |λ| P / X`, `P = X^{1/3}`, of page 9, and the
final comparison with `X / log X` are PROVED.
-/
import LeanLab.LZPowersOfTwo.Decomp418c

open Real Finset MeasureTheory Filter Asymptotics
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

open LeanLab.LZPowersOfTwo

/-- P0079 page 8, display (31): the Selberg integral `J(X, h) = ∫_{εX}^{X} (θ(x+h) - θ(x) - h)^2 dx`. -/
def selbergJ (ε X h : ℝ) : ℝ :=
  ∫ x in (ε * X)..X, (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2

/-- LEAF: CITED. P0079 page 8, Lemma 6 (Gallagher [5], Lemma 1, in the form of
Bruedern, Cook and Perelli [2], Lemma 1): for `1/X ≤ Y ≤ 1/2`,
`∫_{-Y}^{Y} |S(α) - U(α)|^2 dα ≪_ε log X / Y + Y^2 X + Y^2 J(X, 1/Y)`. -/
theorem gallagher_lemma6_p2 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ Y : ℝ, 1 / X ≤ Y → Y ≤ 1 / 2 →
      (∫ α in (-Y)..Y, ‖primeSum293 ε X α - discretePrime396 ε X α‖ ^ 2) ≤
        C * (log X / Y + Y ^ 2 * X + Y ^ 2 * selbergJ ε X (1 / Y)) := by
  sorry

/-- LEAF: CITED. P0079 page 8, Lemma 7 (Saffari and Vaughan [24], section 6): for every
`A > 0` there is `B > 0` with `J(X, h) ≪_ε h^2 X / (log X)^A` uniformly for
`h ≥ X^{1/6} (log X)^B`; here also `h ≤ X`, which only weakens the cited statement. -/
theorem saffari_vaughan_lemma7_p2 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ h : ℝ,
      X ^ ((1 : ℝ) / 6) * (log X) ^ B ≤ h → h ≤ X →
        selbergJ ε X h ≤ C * h ^ 2 * X / (log X) ^ A := by
  sorry

/-- P0079 page 9: the substitution `β = λα` on a symmetric interval. PROVED. -/
theorem symm_subst_p2 (f : ℝ → ℝ) (l R : ℝ) (hl : l ≠ 0) (hR : 0 ≤ R) :
    (∫ α in {α : ℝ | |α| ≤ R}, f (l * α)) = |l|⁻¹ * ∫ β in (-(|l| * R))..(|l| * R), f β := by
  have hset : {α : ℝ | |α| ≤ R} = Set.Icc (-R) R := by
    ext α; simp [abs_le]
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_mul_left (fun x => f x) hl, smul_eq_mul]
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · rw [abs_of_neg hneg, intervalIntegral.integral_symm]
    have e1 : l * R = -(-l * R) := by ring
    have e2 : l * -R = -l * R := by ring
    rw [e1, e2, inv_neg]
    ring
  · rw [abs_of_pos hpos, show l * -R = -(l * R) by ring]

set_option maxHeartbeats 1600000 in
/-- P0079 page 9, the J3 estimate with Lemmas 6 and 7, `A = 3`, `Y = |λ| P / X`,
`P = X^{1/3}`: the exact statement of the leaf `prime_integer_l2_small418`.
CONDITIONAL ON `gallagher_lemma6_p2` and `saffari_vaughan_lemma7_p2`;
this proof has no open step of its own. -/
theorem prime_integer_l2_small_p2 (ε l : ℝ) (hl : l ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      (∫ α in major293 X,
        ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) ≤ δ * X / log X := by
  obtain ⟨C, hC, H6⟩ := gallagher_lemma6_p2 ε hε hε'
  obtain ⟨B, hB, C', hC', H7⟩ := saffari_vaughan_lemma7_p2 ε hε hε' 3 (by norm_num)
  intro δ hδ
  obtain ⟨a, ha_def⟩ : ∃ a, a = |l| := ⟨_, rfl⟩
  have ha : 0 < a := ha_def ▸ abs_pos.mpr hl
  -- the small quantity
  obtain ⟨K, hK⟩ : ∃ K, K = a⁻¹ * C * (9 * a⁻¹ + 3 * a ^ 2 + C' / 9) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = δ / K := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  -- asymptotics in `t = X^{1/3}`
  have hlog2 : Tendsto (fun t : ℝ => log t ^ 2 / t) atTop (nhds 0) := by
    simpa using (isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hlog1 : Tendsto (fun t : ℝ => log t ^ 1 / t) atTop (nhds 0) := by
    simpa using (isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
  have hinvlog : Tendsto (fun t : ℝ => (log t ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp tendsto_log_atTop)
  have hB' : (fun t : ℝ => log t ^ B) =o[atTop] (fun t : ℝ => t ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop B one_pos
  have hBt := hB'.bound (c := (a * 3 ^ B)⁻¹) (by positivity)
  have ht : ∀ᶠ t : ℝ in atTop,
      log t ^ 2 / t ≤ e ∧ log t ^ 1 / t ≤ e ∧ (log t ^ 2)⁻¹ ≤ e ∧ 1 ≤ log t ∧
      2 * a ≤ t ^ 2 ∧ 1 ≤ a * t ∧ ‖log t ^ B‖ ≤ (a * 3 ^ B)⁻¹ * ‖t ^ (1 : ℝ)‖ := by
    filter_upwards [hlog2.eventually (eventually_le_nhds he0),
      hlog1.eventually (eventually_le_nhds he0),
      hinvlog.eventually (eventually_le_nhds he0),
      tendsto_log_atTop.eventually (eventually_ge_atTop 1),
      (tendsto_pow_atTop (n := 2) (by norm_num)).eventually (eventually_ge_atTop (2 * a)),
      eventually_ge_atTop (1 / a), hBt] with t h1 h2 h3 h4 h5 h6 h7
    refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
    rwa [div_le_iff₀ ha, mul_comm] at h6
  have hcube : Tendsto (fun X : ℝ => X ^ ((1 : ℝ) / 3)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [H6, H7, hcube.eventually ht, eventually_ge_atTop (1 : ℝ)] with
    X h6 h7 htX hX1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := htX
  set t := X ^ ((1 : ℝ) / 3) with htdef
  have hX0 : 0 < X := by linarith
  have ht0 : 0 < t := by positivity
  have hXt : X = t ^ 3 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hlogX : log X = 3 * log t := by rw [hXt, Real.log_pow]; norm_num
  have hlt : 0 < log t := by linarith
  clear_value t
  have ht1 : 1 ≤ t := by
    by_contra h; push_neg at h
    have := Real.log_nonpos ht0.le h.le; linarith
  -- the radius
  have hR : X ^ ((1 : ℝ) / 3) / X = 1 / t ^ 2 := by
    rw [← htdef, hXt]; field_simp
  obtain ⟨Y, hY⟩ : ∃ Y, Y = a / t ^ 2 := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hsub : (∫ α in major293 X,
      ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) =
      a⁻¹ * ∫ β in (-Y)..Y, ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2 := by
    have := symm_subst_p2 (fun β => ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2) l
      (X ^ ((1 : ℝ) / 3) / X) hl (by positivity)
    rw [hR] at this
    unfold major293
    rw [hR, this, hY, ← ha_def]
    congr 2 <;> ring
  -- Lemma 6 applies
  have hY1 : 1 / X ≤ Y := by
    rw [hXt, hY, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hY2 : Y ≤ 1 / 2 := by
    rw [hY, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have L6 := h6 Y hY1 hY2
  -- Lemma 7 at `h = 1/Y = t^2/a`
  have hh : 1 / Y = t ^ 2 / a := by rw [hY]; field_simp
  have h16 : X ^ ((1 : ℝ) / 6) ≤ t := by
    rw [htdef]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hlogB : (log X) ^ B = 3 ^ B * (log t) ^ B := by
    rw [hlogX, Real.mul_rpow (by norm_num) hlt.le]
  have h7' : (log t) ^ B ≤ (a * 3 ^ B)⁻¹ * t := by
    have := t7
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg hlt.le _), Real.rpow_one,
      Real.norm_of_nonneg ht0.le] at this
  have hlow : X ^ ((1 : ℝ) / 6) * (log X) ^ B ≤ 1 / Y := by
    rw [hh, hlogB]
    have hp : 0 ≤ 3 ^ B * (log t) ^ B := by positivity
    have h3B : 0 < (3 : ℝ) ^ B := by positivity
    calc X ^ ((1 : ℝ) / 6) * (3 ^ B * log t ^ B) ≤ t * (3 ^ B * ((a * 3 ^ B)⁻¹ * t)) := by
          apply mul_le_mul h16 (mul_le_mul_of_nonneg_left h7' h3B.le) hp ht0.le
      _ = t ^ 2 / a := by field_simp
  have hup : 1 / Y ≤ X := by
    rw [hh, hXt, div_le_iff₀ ha]; nlinarith
  have L7 := h7 (1 / Y) hlow hup
  have hJ : Y ^ 2 * selbergJ ε X (1 / Y) ≤ C' * t ^ 3 / (27 * log t ^ 3) := by
    have hl3 : (log X) ^ (3 : ℝ) = 27 * log t ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hlogX]; ring
    rw [hl3] at L7
    have hY2' : 0 ≤ Y ^ 2 := by positivity
    calc Y ^ 2 * selbergJ ε X (1 / Y) ≤ Y ^ 2 * (C' * (1 / Y) ^ 2 * X / (27 * log t ^ 3)) :=
          mul_le_mul_of_nonneg_left L7 hY2'
      _ = C' * t ^ 3 / (27 * log t ^ 3) := by rw [hXt]; field_simp
  -- final comparison
  rw [hsub]
  have hint := L6.trans (mul_le_mul_of_nonneg_left (show log X / Y + Y ^ 2 * X +
    Y ^ 2 * selbergJ ε X (1 / Y) ≤ log X / Y + Y ^ 2 * X + C' * t ^ 3 / (27 * log t ^ 3) by
      linarith) hC.le)
  have hT1 : log X / Y = 3 * a⁻¹ * t ^ 2 * log t := by rw [hlogX, hY]; field_simp
  have hT2 : Y ^ 2 * X = a ^ 2 / t := by rw [hY, hXt]; field_simp
  rw [hT1, hT2] at hint
  have hfin : a⁻¹ * (C * (3 * a⁻¹ * t ^ 2 * log t + a ^ 2 / t +
      C' * t ^ 3 / (27 * log t ^ 3))) ≤ δ * X / log X := by
    rw [hlogX, hXt]
    have hlt3 : 0 < 3 * log t := by positivity
    rw [le_div_iff₀ hlt3]
    -- divide by `t^3`
    have key : a⁻¹ * C * (9 * a⁻¹ * (log t ^ 2 / t) + 3 * a ^ 2 * (log t ^ 1 / t) +
        C' / 9 * (log t ^ 2)⁻¹) ≤ δ := by
      have hb1 : 9 * a⁻¹ * (log t ^ 2 / t) ≤ 9 * a⁻¹ * e :=
        mul_le_mul_of_nonneg_left t1 (by positivity)
      have hb2 : 3 * a ^ 2 * (log t ^ 1 / t) ≤ 3 * a ^ 2 * e :=
        mul_le_mul_of_nonneg_left t2 (by positivity)
      have hb3 : C' / 9 * (log t ^ 2)⁻¹ ≤ C' / 9 * e :=
        mul_le_mul_of_nonneg_left t3 (by positivity)
      have hsum : 9 * a⁻¹ * (log t ^ 2 / t) + 3 * a ^ 2 * (log t ^ 1 / t) +
          C' / 9 * (log t ^ 2)⁻¹ ≤ (9 * a⁻¹ + 3 * a ^ 2 + C' / 9) * e := by linarith
      have hp : 0 ≤ a⁻¹ * C := by positivity
      calc _ ≤ a⁻¹ * C * ((9 * a⁻¹ + 3 * a ^ 2 + C' / 9) * e) :=
            mul_le_mul_of_nonneg_left hsum hp
        _ = (K - 1) * e := by rw [hK]; ring
        _ ≤ K * e := by nlinarith
        _ = δ := by rw [he]; field_simp [hK0.ne']
    have hlog4 : log t ^ 1 / t ^ 4 ≤ log t ^ 1 / t := by
      apply div_le_div_of_nonneg_left (by positivity) ht0
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    have expand : a⁻¹ * (C * (3 * a⁻¹ * t ^ 2 * log t + a ^ 2 / t +
        C' * t ^ 3 / (27 * log t ^ 3))) * (3 * log t) =
        t ^ 3 * (a⁻¹ * C * (9 * a⁻¹ * (log t ^ 2 / t) + 3 * a ^ 2 * (log t ^ 1 / t ^ 4) +
          C' / 9 * (log t ^ 2)⁻¹)) := by
      have h1 : a ≠ 0 := ha.ne'
      have h2 : t ≠ 0 := ht0.ne'
      have h3 : log t ≠ 0 := hlt.ne'
      field_simp
      ring
    rw [expand]
    have hp : 0 ≤ a⁻¹ * C := by positivity
    have : a⁻¹ * C * (9 * a⁻¹ * (log t ^ 2 / t) + 3 * a ^ 2 * (log t ^ 1 / t ^ 4) +
        C' / 9 * (log t ^ 2)⁻¹) ≤ δ := by
      refine le_trans ?_ key
      apply mul_le_mul_of_nonneg_left _ hp
      have := mul_le_mul_of_nonneg_left hlog4 (show (0 : ℝ) ≤ 3 * a ^ 2 by positivity)
      linarith
    calc t ^ 3 * (a⁻¹ * C * (9 * a⁻¹ * (log t ^ 2 / t) + 3 * a ^ 2 * (log t ^ 1 / t ^ 4) +
          C' / 9 * (log t ^ 2)⁻¹)) ≤ t ^ 3 * δ :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ * t ^ 3 := by ring
  calc a⁻¹ * ∫ β in (-Y)..Y, ‖primeSum293 ε X β - discretePrime396 ε X β‖ ^ 2
      ≤ a⁻¹ * (C * (3 * a⁻¹ * t ^ 2 * log t + a ^ 2 / t +
          C' * t ^ 3 / (27 * log t ^ 3))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ δ * X / log X := hfin

/-- The type agrees with the existing leaf. -/
example : ∀ (ε l : ℝ) (_ : l ≠ 0) (_ : 0 < ε) (_ : ε < 1),
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      (∫ α in major293 X,
        ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) ≤ δ * X / log X :=
  prime_integer_l2_small_p2

end LeanLab.LZPowersOfTwo.Burst8P2

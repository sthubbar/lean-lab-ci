/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364.

ROUTE BURST session 9, 2026-11-12. The two end blocks for `clip_average_proved`, PROVED:

* `left_end_one`, `left_end_sum`: the moving sums from `a` of length `< h`, averaged over the
  left end block, are bounded by `3 ∫_0^h W(u) du + 2 K₀ (log 2N + 1)²`.
* `right_end_one`, `right_end_sum`: the moving sums ending at `b`, averaged over the right
  end block, have the same bound.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Clip2

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem Fm_iInt (x : ℝ) {lo hi R : ℝ} (hlh : lo ≤ hi) (hR : x + hi ≤ R) :
    IntervalIntegrable (fun u => Fm χ x u) volume lo hi := by
  refine IntegrableOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hlh]
  exact Fm_int_u χ measurableSet_Icc measure_Icc_lt_top.ne (R := R)
    fun u hu => by linarith [hu.2]

theorem Fm_comp_measurable (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun x : ℝ => Fm χ x (g x)) := by
  have h1 : Measurable (fun x : ℝ => (x, g x)) := measurable_id'.prodMk hg
  have h2 := (Fm_measurable χ).comp h1
  exact h2

/-- `Φ(x) = ∫_0^h |S(x, u)|² du`. -/
def Phi (h x : ℝ) : ℝ := ∫ u in Ioc 0 h, Fm χ x u

theorem Phi_nonneg (h x : ℝ) : 0 ≤ Phi χ h x :=
  setIntegral_nonneg measurableSet_Ioc fun u _ => Fm_nonneg χ x u

theorem Phi_intOn {J : Set ℝ} (hJ : MeasurableSet J) (hJf : volume J ≠ ⊤) {h R : ℝ}
    (hR : ∀ x ∈ J, x + h ≤ R) : IntegrableOn (Phi χ h) J :=
  (Fm_int_prod χ hJ measurableSet_Ioc hJf measure_Ioc_lt_top.ne (R := R)
    fun x hx u hu => by linarith [hR x hx, hu.2]).integral_prod_left

/-- **One left end**: `∫_0^h |S(a, u)|² du ≤ 3 ∫_{a-1}^{a} Φ(x) dx + 2 (log 2N + 1)²`. PROVED. -/
theorem left_end_one {N : ℕ} (hN : 1 ≤ N) {a : ℕ} (ha : 1 ≤ a) {h : ℝ} (h2 : 2 ≤ h)
    (hah : (a : ℝ) + h ≤ 2 * N) :
    (∫ u in (0 : ℝ)..h, Fm χ a u) ≤
      3 * (∫ x in Ioo ((a : ℝ) - 1) a, Phi χ h x) + 2 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have iA : ∀ lo hi : ℝ, lo ≤ hi → hi ≤ h → IntervalIntegrable (fun u => Fm χ a u) volume lo hi :=
    fun lo hi hlh hh => Fm_iInt χ a hlh (R := 2 * N) (by linarith)
  -- the top unit of windows
  have hstep : (∫ u in (h - 1)..h, Fm χ a u) ≤ 2 * (∫ u in (h - 2)..(h - 1), Fm χ a u) + 2 * β ^ 2 := by
    have hpt : ∀ u ∈ Icc (h - 1) h, Fm χ a u ≤ 2 * Fm χ a (u - 1) + 2 * β ^ 2 := by
      intro u hu
      have hu1 : 1 ≤ u := by linarith [hu.1]
      have hc : ‖cf χ (a + ⌊u⌋₊)‖ ≤ β := by
        refine norm_cf_le_log χ hN ?_
        have : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have : ((a + ⌊u⌋₊ : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith [hu.2]
        exact_mod_cast this
      unfold Fm
      rw [movingSum_top χ a hu1]
      refine (norm_add_sq_le _ _).trans ?_
      have := pow_le_pow_left₀ (norm_nonneg _) hc 2
      linarith
    have i1 : IntervalIntegrable (fun u => 2 * Fm χ a (u - 1) + 2 * β ^ 2) volume (h - 1) h := by
      refine ((Fm_iInt χ a (lo := h - 2) (hi := h - 1) (by linarith) (R := 2 * N) (by linarith)
        ).comp_sub_right 1).const_mul 2 |>.add intervalIntegrable_const |>.mono_set ?_
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc (∫ u in (h - 1)..h, Fm χ a u)
        ≤ ∫ u in (h - 1)..h, (2 * Fm χ a (u - 1) + 2 * β ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith) (iA _ _ (by linarith) le_rfl) i1 hpt
      _ = 2 * (∫ u in (h - 2)..(h - 1), Fm χ a u) + 2 * β ^ 2 := by
          rw [intervalIntegral.integral_add ?_ intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
              (fun u => Fm χ a u) 1, intervalIntegral.integral_const]
          · simp only [smul_eq_mul]
            rw [show h - 1 - 1 = h - 2 by ring, show h - 1 = h - 1 by ring]; ring
          · exact (((Fm_iInt χ a (lo := h - 2) (hi := h - 1) (by linarith) (R := 2 * N)
              (by linarith)).comp_sub_right 1).const_mul 2).mono_set (by
              rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
              intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hmono : (∫ u in (h - 2)..(h - 1), Fm χ a u) ≤ ∫ u in (0 : ℝ)..(h - 1), Fm χ a u :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Eventually.of_forall fun u => Fm_nonneg χ a u) (iA _ _ (by linarith) (by linarith))
  -- the shift to the start points `x ∈ (a - 1, a)`
  have key : ∀ x ∈ Ioo ((a : ℝ) - 1) a,
      (∫ u in (0 : ℝ)..(h - 1), Fm χ a u) ≤ Phi χ h x := by
    intro x hx
    have e1 : (∫ u in (0 : ℝ)..(h - 1), Fm χ a u) =
        ∫ u in (0 : ℝ)..(h - 1), Fm χ x (u + (a - x)) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [Fm, movingSum_shift_left χ ha hx.1 hx.2.le]
    rw [e1, intervalIntegral.integral_comp_add_right (fun u => Fm χ x u) (a - x), Phi,
      ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_mono_interval (by linarith [hx.2]) (by linarith)
      (by linarith [hx.1]) (Eventually.of_forall fun u => Fm_nonneg χ x u)
      (Fm_iInt χ x (by linarith) (R := 2 * N) (by linarith [hx.2]))
  have hvol : volume (Ioo ((a : ℝ) - 1) a) = 1 := by
    rw [Real.volume_Ioo]; norm_num
  have hD : (∫ u in (0 : ℝ)..(h - 1), Fm χ a u) ≤ ∫ x in Ioo ((a : ℝ) - 1) a, Phi χ h x := by
    have hc : (∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in (0 : ℝ)..(h - 1), Fm χ a u)) =
        ∫ u in (0 : ℝ)..(h - 1), Fm χ a u := by
      rw [setIntegral_const, measureReal_def, hvol, ENNReal.toReal_one, one_smul]
    rw [← hc]
    refine setIntegral_mono_on (integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top))
      (Phi_intOn χ measurableSet_Ioo (by rw [hvol]; exact ENNReal.one_ne_top) (R := 2 * N)
        fun x hx => by linarith [hx.2]) measurableSet_Ioo key
  have hsplit : (∫ u in (0 : ℝ)..h, Fm χ a u) =
      (∫ u in (0 : ℝ)..(h - 1), Fm χ a u) + ∫ u in (h - 1)..h, Fm χ a u :=
    (intervalIntegral.integral_add_adjacent_intervals (iA _ _ (by linarith) (by linarith))
      (iA _ _ (by linarith) le_rfl)).symm
  rw [hsplit]
  set I0 := ∫ u in (0 : ℝ)..(h - 1), Fm χ a u with hI0
  set I1 := ∫ u in (h - 1)..h, Fm χ a u with hI1
  set I2 := ∫ u in (h - 2)..(h - 1), Fm χ a u with hI2
  set P := ∫ x in Ioo ((a : ℝ) - 1) a, Phi χ h x with hP
  clear_value I0 I1 I2 P β
  linarith

#print axioms left_end_one

theorem card_Aset (N K0 : ℕ) : (Aset N K0).card = K0 := by
  unfold Aset; rw [Nat.card_Ico]; omega

theorem card_Bset (N K0 : ℕ) (hK : K0 ≤ 2 * N) : (Bset N K0).card = K0 := by
  unfold Bset; rw [Nat.card_Ioc]; omega

/-- **The left end block**: `Σ_a ∫_0^h |S(a, u)|² du ≤ 3 ∫_0^h W(u) du + 2 K₀ (log 2N + 1)²`.
PROVED. -/
theorem left_end_sum {N K0 : ℕ} (hN : 64 ≤ N) (hK1 : 1 ≤ K0) (hK4 : 4 * K0 ≤ N) {h : ℝ}
    (h2 : 2 ≤ h) (h8 : 8 * h ≤ N) :
    (∑ a ∈ Aset N K0, ∫ u in (0 : ℝ)..h, Fm χ a u) ≤
      3 * (∫ u in Ioc 0 h, windowMean N χ u) + 2 * K0 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have hone : ∀ a ∈ Aset N K0, (∫ u in (0 : ℝ)..h, Fm χ a u) ≤
      3 * (∫ x in Ioo ((a : ℝ) - 1) a, Phi χ h x) + 2 * β ^ 2 := by
    intro a ha
    have ha' := Finset.mem_Ico.mp ha
    have hlt : a + 1 ≤ N + K0 := ha'.2
    have har : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast hlt
    exact left_end_one χ (by omega) (by omega) h2 (by linarith)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_Aset, nsmul_eq_mul]
  have hdisj : Set.Pairwise (↑(Aset N K0) : Set ℕ)
      (Function.onFun Disjoint fun a : ℕ => Ioo ((a : ℝ) - 1) a) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    have h1 : (a : ℝ) < b + 1 := by linarith [hxa.1, hxb.2]
    have h2 : (b : ℝ) < a + 1 := by linarith [hxb.1, hxa.2]
    have h1' : a < b + 1 := by exact_mod_cast h1
    have h2' : b < a + 1 := by exact_mod_cast h2
    omega
  have hsub : (⋃ a ∈ Aset N K0, Ioo ((a : ℝ) - 1) a) ⊆ Ioo ((N : ℝ) - 1) (N + K0) := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have ha' := Finset.mem_Ico.mp ha
    have h1 : (N : ℝ) ≤ a := by exact_mod_cast ha'.1
    have h2 : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast ha'.2
    exact ⟨by linarith [hxa.1], by linarith [hxa.2]⟩
  have hJU : Ioo ((N : ℝ) - 1) (N + K0) ⊆ Ioc ((N : ℝ) / 2) (3 * N) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hPhiJ : IntegrableOn (Phi χ h) (Ioo ((N : ℝ) - 1) (N + K0)) :=
    Phi_intOn χ measurableSet_Ioo measure_Ioo_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hsum : (∑ a ∈ Aset N K0, ∫ x in Ioo ((a : ℝ) - 1) a, Phi χ h x) ≤
      ∫ u in Ioc 0 h, windowMean N χ u := by
    rw [← integral_biUnion_finset _ (fun a _ => measurableSet_Ioo) hdisj
      (fun a _ => hPhiJ.mono_set (fun x hx => hsub (by
        simp only [mem_iUnion]; exact ⟨a, by assumption, hx⟩)))]
    refine (setIntegral_mono_set hPhiJ (Eventually.of_forall fun x => Phi_nonneg χ h x)
      (Eventually.of_forall hsub)).trans ?_
    exact swap_le χ N measurableSet_Ioo hJU (by linarith)
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  nlinarith

/-- **One right end**: `∫_{b-h}^{b} |S(x, b - x)|² dx ≤ 3 ∫_{b-h+1}^{b} |S(x, b - x)|² dx +
2 (log 2N + 1)²`. PROVED. -/
theorem right_end_one {N : ℕ} (hN : 1 ≤ N) {b : ℕ} (hb2 : b ≤ 2 * N) {h : ℝ} (h2 : 2 ≤ h)
    (hbh : h ≤ b) :
    (∫ x in ((b : ℝ) - h)..b, Fm χ x (b - x)) ≤
      3 * (∫ x in ((b : ℝ) - h + 1)..b, Fm χ x (b - x)) + 2 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hGm' : Measurable (fun x : ℝ => Fm χ x ((b : ℝ) - x)) :=
    Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop)
  set G : ℝ → ℝ := fun x => Fm χ x (b - x) with hG
  have hGm : Measurable G := hGm'
  have hGi : ∀ lo hi : ℝ, lo ≤ hi → IntervalIntegrable G volume lo hi := by
    intro lo hi hlh
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hlh]
    refine intOn_bdd hGm measurableSet_Icc measure_Icc_lt_top.ne (SR χ b ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (by linarith)
  have hpt : ∀ x ∈ Icc ((b : ℝ) - h) (b - h + 1), G x ≤ 2 * β ^ 2 + 2 * G (x + 1) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hxb : x < b := by linarith [hx.2]
    have hc : ‖cf χ ⌈x⌉₊‖ ≤ β := by
      refine norm_cf_le_log χ hN ((Nat.ceil_le.mpr hxb.le).trans hb2)
    simp only [hG, Fm]
    rw [movingSum_right_split χ hx0 hxb]
    refine (norm_add_sq_le _ _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hc 2
    linarith
  have hshift : (∫ x in ((b : ℝ) - h)..(b - h + 1), G (x + 1)) =
      ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
    rw [intervalIntegral.integral_comp_add_right G 1]
    congr 1 <;> ring
  have h1 : (∫ x in ((b : ℝ) - h)..(b - h + 1), G x) ≤
      2 * β ^ 2 + 2 * ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
    have i3 : IntervalIntegrable (fun x => 2 * G (x + 1)) volume ((b : ℝ) - h) (b - h + 1) := by
      refine IntervalIntegrable.const_mul ?_ 2
      refine IntegrableOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by linarith)]
      have hm1 : Measurable (fun x : ℝ => x + 1) := by fun_prop
      refine intOn_bdd (hGm.comp hm1) measurableSet_Icc
        measure_Icc_lt_top.ne (SR χ b ^ 2) fun x _ => ?_
      show |Fm χ (x + 1) (b - (x + 1))| ≤ _
      rw [abs_of_nonneg (Fm_nonneg χ _ _)]
      exact Fm_le χ (by linarith)
    have i2 : IntervalIntegrable (fun x => 2 * β ^ 2 + 2 * G (x + 1)) volume ((b : ℝ) - h)
        (b - h + 1) := intervalIntegrable_const.add i3
    calc (∫ x in ((b : ℝ) - h)..(b - h + 1), G x)
        ≤ ∫ x in ((b : ℝ) - h)..(b - h + 1), (2 * β ^ 2 + 2 * G (x + 1)) :=
          intervalIntegral.integral_mono_on (by linarith) (hGi _ _ (by linarith)) i2 hpt
      _ = 2 * β ^ 2 + 2 * ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
          rw [intervalIntegral.integral_add intervalIntegrable_const i3,
            intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, hshift]
          simp only [smul_eq_mul]; ring
  have h3 : (∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x) ≤ ∫ x in ((b : ℝ) - h + 1)..b, G x :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Eventually.of_forall fun x => Fm_nonneg χ _ _) (hGi _ _ (by linarith))
  have hsplit : (∫ x in ((b : ℝ) - h)..b, G x) =
      (∫ x in ((b : ℝ) - h)..(b - h + 1), G x) + ∫ x in ((b : ℝ) - h + 1)..b, G x :=
    (intervalIntegral.integral_add_adjacent_intervals (hGi _ _ (by linarith))
      (hGi _ _ (by linarith))).symm
  show (∫ x in ((b : ℝ) - h)..b, G x) ≤ 3 * (∫ x in ((b : ℝ) - h + 1)..b, G x) + 2 * β ^ 2
  rw [hsplit]
  linarith

#print axioms left_end_sum
#print axioms right_end_one

end
end LeanLab.PerelliPintz1992.Burst9

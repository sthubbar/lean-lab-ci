import LeanLab.ChenDoubleSieve.KCertificate
import LeanLab.ChenDoubleSieve.I2Range
import LeanLab.ChenDoubleSieve.I1Bounds

/-!
# Burst 9: certified panels for the scalar parts of Wu's Ψ₂ and a box bound for I₂

Source: J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114 (2004), arXiv 0705.1652, Lemma 5.2, pages 25 and 26, the definition of
`Ψ₂(s) = Ψ₂(s, s', κ₁, κ₂, κ₃)`:
`Ψ₂ = −2/5 ∫_2^{s'−1} log(t−1)/t dt − 2/5 ∫_2^{κ₁−1} … − 1/5 ∫_2^{κ₂−1} …
  + 1/5 ∫_{1−1/s}^{1−1/s'} log(s't−1)/(t(1−t)) dt + 1/5 ∫_{1−1/κ₃}^{1−1/κ₁} log(κ₁t−1)/(t(1−t)) dt
  − 2/5 ∑_{i=9}^{21} I_{2,i}(s)`.

This file holds generic certified tools, all PROVED:
* `J_upper_of_cert`: a rational upper bound for `J 2 c`, `c ≥ 2`, from a panel certificate,
  reusing the folder's `Wu04Panels.J_partition_arithmetic`.
* `J_rev_upper_of_cert`: the same for `1 < c ≤ 2`, where the integral runs backwards; this is
  the term `∫_2^{κ₂−1}` with `κ₂ − 1 < 2` in all four rows of Table 1.
* `K_lower_of_cert`: a rational lower bound for `K r lo hi`, reusing
  `Wu04Panels.K_partition_arithmetic`.
* `buchstabSup_le_box`: for `ω ≤ 1`, each `I_{2,i}` is at most the sup of its kernel
  `1/(t u² v)`, and analogues, times the volume of the enclosing box.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst9Psi2
open Wu04Functional
open Wu04Integral (logLowerQ logUpperQ logLowerQ_cast logUpperQ_cast logLower logUpper log_bounds)
open Wu04JCertificate (down up down_le le_up)

/-! ### J with `c ≥ 2` -/

/-- Uniform rational nodes on `[2, c]`. -/
def jNode (c : ℚ) (m j : ℕ) : ℚ := 2 + j * (c - 2) / m

/-- The rounded rational panel sum bounding `J 2 c` from above. -/
def jUpperSum (c : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ range m, up (Wu04JCertificate.upperPanelQ (jNode c m j) (jNode c m (j + 1)))

/-- A rational certificate gives an upper bound for `J 2 c = ∫_2^c log(t−1)/t dt`, `c ≥ 2`.
Wu 2004 Lemma 5.2, page 26, the three `J` terms of `Ψ₂`. PROVED. -/
theorem J_upper_of_cert {c : ℚ} {m : ℕ} (hm : 0 < m) (hc : 2 ≤ c) {U : ℚ}
    (h : jUpperSum c m ≤ U) : J 2 (c : ℝ) ≤ U := by
  let x : ℕ → ℝ := fun j => (jNode c m j : ℝ)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc' : (0 : ℝ) ≤ (c : ℝ) - 2 := by
    have : (2 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have hx (j : ℕ) : x j = 2 + (j : ℝ) * ((c : ℝ) - 2) / m := by simp [x, jNode]
  have hxp (j : ℕ) (_ : j < m) : 2 ≤ x j ∧ x j ≤ x (j + 1) := by
    rw [hx j, hx (j + 1)]
    push_cast
    have h0 : 0 ≤ (j : ℝ) * ((c : ℝ) - 2) / m :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg j) hc') hm'.le
    have h1 : (j : ℝ) * ((c : ℝ) - 2) / m ≤ ((j : ℝ) + 1) * ((c : ℝ) - 2) / m :=
      div_le_div_of_nonneg_right (by nlinarith) hm'.le
    constructor <;> linarith
  have hp := (Wu04Panels.J_partition_arithmetic 16 m x hxp).2
  have hcell (j : ℕ) : Wu04Panels.JUpper 16 (x j) (x (j + 1)) ≤
      ((up (Wu04JCertificate.upperPanelQ (jNode c m j) (jNode c m (j + 1))) : ℚ) : ℝ) := by
    have hu : ((Wu04JCertificate.upperPanelQ (jNode c m j) (jNode c m (j + 1)) : ℚ) : ℝ) ≤
        ((up (Wu04JCertificate.upperPanelQ (jNode c m j) (jNode c m (j + 1))) : ℚ) : ℝ) := by
      exact_mod_cast le_up _
    refine le_trans (le_of_eq ?_) hu
    simp [Wu04JCertificate.upperPanelQ, Wu04Panels.JUpper, x]
  have hx0 : x 0 = 2 := by rw [hx]; norm_num
  have hxm : x m = c := by rw [hx]; field_simp; ring
  rw [hx0, hxm] at hp
  have hs : (∑ j ∈ range m,
      ((up (Wu04JCertificate.upperPanelQ (jNode c m j) (jNode c m (j + 1))) : ℚ) : ℝ)) ≤ U := by
    have : ((jUpperSum c m : ℚ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast h
    simpa [jUpperSum] using this
  unfold J
  exact hp.trans ((sum_le_sum fun j _ => hcell j).trans hs)

/-! ### J with `1 < c ≤ 2`, the reversed integral -/

/-- Uniform rational nodes on `[c, 2]`. -/
def rNode (c : ℚ) (m j : ℕ) : ℚ := c + j * (2 - c) / m

/-- Left endpoint panel value for the decreasing integrand `−log(t−1)/t` on `[c, 2]`. -/
def rCell (c : ℚ) (m j : ℕ) : ℚ :=
  up ((2 - c) / m * logUpperQ 8 (1 / (rNode c m j - 1)) / rNode c m j)

/-- On a panel `[a, b] ⊆ (1, 2]`, `∫_a^b −log(t−1)/t dt ≤ (b − a) · log(1/(a−1))/a`. PROVED. -/
theorem rev_panel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ t in a..b, -(log (t - 1) / t)) ≤ (b - a) * (logUpper 8 (1 / (a - 1)) / a) := by
  have ha0 : 0 < a := by linarith
  have hint : IntervalIntegrable (fun t => -(log (t - 1) / t)) volume a b :=
    (Wu04Panels.J_integrable ha hab).neg
  have hpt : ∀ t ∈ Icc a b, -(log (t - 1) / t) ≤ logUpper 8 (1 / (a - 1)) / a := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl1 : log (t - 1) ≤ 0 := log_nonpos (by linarith [ht.1]) (by linarith [ht.2])
    have hl2 : log (a - 1) ≤ log (t - 1) := log_le_log (by linarith) (by linarith [ht.1])
    have hrec : log (1 / (a - 1)) = -log (a - 1) := by rw [one_div, log_inv]
    have hy : 1 ≤ 1 / (a - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hub := (log_bounds 8 hy).2
    have hnum : -log (t - 1) ≤ logUpper 8 (1 / (a - 1)) := by linarith
    have hn0 : 0 ≤ -log (t - 1) := by linarith
    calc -(log (t - 1) / t) = -log (t - 1) / t := by ring
      _ ≤ logUpper 8 (1 / (a - 1)) / t := div_le_div_of_nonneg_right hnum ht0.le
      _ ≤ logUpper 8 (1 / (a - 1)) / a :=
          div_le_div_of_nonneg_left (hn0.trans hnum) ha0 ht.1
  have hm := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  exact hm

/-- A rational certificate gives an upper bound for `J 2 c` when `1 < c ≤ 2`, where
`J 2 c = ∫_c^2 −log(t−1)/t dt ≥ 0`. Wu 2004 Lemma 5.2, page 26, the term `−1/5 ∫_2^{κ₂−1}`.
PROVED. -/
theorem J_rev_upper_of_cert {c : ℚ} {m : ℕ} (hm : 0 < m) (hc1 : 1 < c) (hc2 : c ≤ 2) {U : ℚ}
    (h : ∑ j ∈ range m, rCell c m j ≤ U) : J 2 (c : ℝ) ≤ U := by
  let x : ℕ → ℝ := fun j => (rNode c m j : ℝ)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc1' : (1 : ℝ) < c := by exact_mod_cast hc1
  have hc2' : (c : ℝ) ≤ 2 := by exact_mod_cast hc2
  have hx (j : ℕ) : x j = (c : ℝ) + (j : ℝ) * (2 - (c : ℝ)) / m := by simp [x, rNode]
  have hxp (j : ℕ) (hj : j < m) : 1 < x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) ≤ 2 := by
    rw [hx j, hx (j + 1)]
    push_cast
    have hj1 : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have h0 : 0 ≤ (j : ℝ) * (2 - (c : ℝ)) / m :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg j) (by linarith)) hm'.le
    have h1 : (j : ℝ) * (2 - (c : ℝ)) / m ≤ ((j : ℝ) + 1) * (2 - (c : ℝ)) / m :=
      div_le_div_of_nonneg_right (by nlinarith) hm'.le
    have h2 : ((j : ℝ) + 1) * (2 - (c : ℝ)) / m ≤ 2 - c := by
      rw [div_le_iff₀ hm']; nlinarith
    refine ⟨by linarith, by linarith, by linarith⟩
  have hint : ∀ j < m, IntervalIntegrable (fun t => -(log (t - 1) / t)) volume (x j) (x (j + 1)) :=
    fun j hj => (Wu04Panels.J_integrable (hxp j hj).1 (hxp j hj).2.1).neg
  have he := intervalIntegral.sum_integral_adjacent_intervals hint
  have hx0 : x 0 = c := by rw [hx]; norm_num
  have hxm : x m = 2 := by rw [hx]; field_simp; ring
  rw [hx0, hxm] at he
  have hJ : J 2 (c : ℝ) = ∫ t in (c : ℝ)..2, -(log (t - 1) / t) := by
    unfold J
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_neg]
  have hw (j : ℕ) : x (j + 1) - x j = (2 - (c : ℝ)) / m := by
    rw [hx, hx]; push_cast; ring
  have hcell (j : ℕ) (hj : j < m) : (∫ t in x j..x (j + 1), -(log (t - 1) / t)) ≤
      ((rCell c m j : ℚ) : ℝ) := by
    have hp := rev_panel (hxp j hj).1 (hxp j hj).2.1 (hxp j hj).2.2
    rw [hw j] at hp
    have hu : ((((2 - c) / m * logUpperQ 8 (1 / (rNode c m j - 1)) / rNode c m j) : ℚ) : ℝ) ≤
        ((rCell c m j : ℚ) : ℝ) := by
      exact_mod_cast le_up _
    refine hp.trans (le_trans (le_of_eq ?_) hu)
    simp [x]
    ring
  rw [hJ, ← he]
  have hs : (∑ j ∈ range m, ((rCell c m j : ℚ) : ℝ)) ≤ U := by
    have : (((∑ j ∈ range m, rCell c m j) : ℚ) : ℝ) ≤ (U : ℝ) := by exact_mod_cast h
    simpa using this
  exact (sum_le_sum fun j hj => hcell j (mem_range.mp hj)).trans hs

/-! ### K lower bounds -/

/-- Uniform rational nodes on `[lo, hi]`. -/
def kNode (lo hi : ℚ) (m j : ℕ) : ℚ := lo + j * (hi - lo) / m

/-- The rounded rational panel sum bounding `K r lo hi` from below. -/
def kLowerSum (r lo hi : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ range m, down (Wu04KCertificate.lowerPanelQ (kNode lo hi m j) (kNode lo hi m (j + 1)) r)

/-- A rational certificate gives a lower bound for `K r lo hi = ∫_lo^hi log(rt−1)/(t(1−t)) dt`.
Wu 2004 Lemma 5.2, page 26, the two `K` terms of `Ψ₂`. PROVED. -/
theorem K_lower_of_cert {r lo hi : ℚ} {m : ℕ} (hm : 0 < m)
    (hpar : 0 < lo ∧ lo ≤ hi ∧ hi < 1 ∧ 0 < r ∧ 1 ≤ r * lo - 1) {L : ℚ}
    (h : L ≤ kLowerSum r lo hi m) : (L : ℝ) ≤ K r lo hi := by
  have hpar' : 0 < (lo : ℝ) ∧ (lo : ℝ) ≤ hi ∧ (hi : ℝ) < 1 ∧ 0 < (r : ℝ) ∧
      1 ≤ (r : ℝ) * lo - 1 := by exact_mod_cast hpar
  obtain ⟨ha, hab, hb, hr, hra⟩ := hpar'
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let x : ℕ → ℝ := fun j => (kNode lo hi m j : ℝ)
  have hx (j : ℕ) : x j = (lo : ℝ) + (j : ℝ) * ((hi : ℝ) - lo) / m := by simp [x, kNode]
  have hxp (j : ℕ) (hj : j < m) :
      0 < x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) < 1 ∧ 1 ≤ (r : ℝ) * x j - 1 := by
    have hj1 : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have h0 : 0 ≤ (j : ℝ) * ((hi : ℝ) - lo) / m :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg j) (by linarith)) hm'.le
    have h1 : (j : ℝ) * ((hi : ℝ) - lo) / m ≤ ((j : ℝ) + 1) * ((hi : ℝ) - lo) / m :=
      div_le_div_of_nonneg_right (by nlinarith) hm'.le
    have h2 : ((j : ℝ) + 1) * ((hi : ℝ) - lo) / m ≤ (hi : ℝ) - lo := by
      rw [div_le_iff₀ hm']; nlinarith
    have hxa : (lo : ℝ) ≤ x j := by rw [hx]; linarith
    refine ⟨by linarith, ?_, ?_, by nlinarith⟩
    · rw [hx, hx]; push_cast; linarith
    · rw [hx]; push_cast; linarith
  have hp := (Wu04Panels.K_partition_arithmetic 16 m x hr hxp).1
  have hcell (j : ℕ) :
      ((down (Wu04KCertificate.lowerPanelQ (kNode lo hi m j) (kNode lo hi m (j + 1)) r) : ℚ) : ℝ)
        ≤ Wu04Panels.KLower 16 (x j) (x (j + 1)) r := by
    have hl : ((down (Wu04KCertificate.lowerPanelQ (kNode lo hi m j) (kNode lo hi m (j + 1)) r)
        : ℚ) : ℝ) ≤
        ((Wu04KCertificate.lowerPanelQ (kNode lo hi m j) (kNode lo hi m (j + 1)) r : ℚ) : ℝ) := by
      exact_mod_cast down_le _
    refine hl.trans (le_of_eq ?_)
    simp [Wu04KCertificate.lowerPanelQ, Wu04KCertificate.wLowerQ, Wu04KCertificate.wUpperQ,
      Wu04Panels.KLower, Wu04Panels.KWLower, Wu04Panels.KWUpper, x]
  have hx0 : x 0 = lo := by rw [hx]; norm_num
  have hxm : x m = hi := by rw [hx]; field_simp; ring
  rw [hx0, hxm] at hp
  have hs : (L : ℝ) ≤ ∑ j ∈ range m,
      ((down (Wu04KCertificate.lowerPanelQ (kNode lo hi m j) (kNode lo hi m (j + 1)) r) : ℚ) : ℝ) := by
    have : (L : ℝ) ≤ ((kLowerSum r lo hi m : ℚ) : ℝ) := by exact_mod_cast h
    simpa [kLowerSum] using this
  unfold K
  exact hs.trans ((sum_le_sum fun j _ => hcell j).trans hp)

/-! ### The box bound for the Buchstab suprema -/

/-- For `ω ≤ 1` everywhere, every `φ`-integral of Wu's Lemma 5.2, page 26, is at most the
supremum `1/((∏ lo) · lo_n)` of its kernel times the volume `∏ (hi − lo)` of the enclosing box,
so the same holds for the maximum over `φ ≥ 2`. PROVED. -/
theorem buchstabSup_le_box {ω : ℝ → ℝ} (hω1 : ∀ u, ω u ≤ 1) {n : ℕ}
    (lo hi : Fin (n + 2) → ℝ) (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j) :
    buchstabSup ω n lo hi ≤
      1 / ((∏ j, lo j) * lo ⟨n, by omega⟩) * ∏ j, (hi j - lo j) := by
  set C := 1 / ((∏ j, lo j) * lo ⟨n, by omega⟩) with hCdef
  have hP : 0 < (∏ j, lo j) * lo ⟨n, by omega⟩ :=
    mul_pos (prod_pos fun j _ => hlo j) (hlo _)
  have hC : 0 ≤ C := (one_div_pos.mpr hP).le
  have hV0 : 0 ≤ ∏ j, (hi j - lo j) := prod_nonneg fun j _ => sub_nonneg.mpr (hle j)
  have hcpt := Wu04I1.domain_isCompact lo hi
  have hmeas : MeasurableSet (domain lo hi) := hcpt.measurableSet
  have hsub : domain lo hi ⊆ Icc lo hi := fun x hx => ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩
  have hvol : volume.real (domain lo hi) ≤ ∏ j, (hi j - lo j) := by
    have h1 : volume (domain lo hi) ≤ ∏ j, ENNReal.ofReal (hi j - lo j) :=
      (measure_mono hsub).trans (le_of_eq Real.volume_Icc_pi)
    have h2 : (∏ j, ENNReal.ofReal (hi j - lo j)).toReal = ∏ j, (hi j - lo j) := by
      rw [ENNReal.toReal_prod]
      exact prod_congr rfl fun j _ => ENNReal.toReal_ofReal (sub_nonneg.mpr (hle j))
    rw [Measure.real, ← h2]
    exact ENNReal.toReal_mono (by simp [ENNReal.prod_ne_top]) h1
  apply csSup_le
  · exact ⟨buchstabIntegral ω n lo hi 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, _, rfl⟩
    unfold buchstabIntegral
    have hbound : ∀ x ∈ domain lo hi,
        ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩) ≤ C := by
      intro x hx
      have hxl : ∀ j, lo j ≤ x j := fun j => (hx.2 j).1
      have hD : (∏ j, lo j) * lo ⟨n, by omega⟩ ≤ (∏ j, x j) * x ⟨n, by omega⟩ :=
        mul_le_mul (prod_le_prod₀ (fun j _ => (hlo j).le) (fun j _ => hxl j)) (hxl _)
          (hlo _).le (prod_nonneg fun j _ => (hlo j).le.trans (hxl j))
      have hDp : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := hP.trans_le hD
      calc ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩)
          ≤ 1 / ((∏ j, x j) * x ⟨n, by omega⟩) := div_le_div_of_nonneg_right (hω1 _) hDp.le
        _ ≤ C := one_div_le_one_div_of_le hP hD
    by_cases hint : IntegrableOn (fun x : Fin (n + 2) → ℝ =>
        ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩)) (domain lo hi) volume
    · have hm := setIntegral_mono_on hint
        (integrableOn_const (hcpt.measure_lt_top.ne)) hmeas hbound
      rw [setIntegral_const, smul_eq_mul] at hm
      calc _ ≤ volume.real (domain lo hi) * C := hm
        _ ≤ (∏ j, (hi j - lo j)) * C := mul_le_mul_of_nonneg_right hvol hC
        _ = C * ∏ j, (hi j - lo j) := mul_comm _ _
    · rw [integral_undef hint]
      exact mul_nonneg hC hV0

end LeanLab.ChenDoubleSieve.Burst9Psi2


import LeanLab.ChenDoubleSieve.Task587CapChain1122

/-!
The Buchstab cap omega u at most 562 / 1000 from 16 / 5 on, used by the window split
of Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30, cell r0j13. The numerical
value of omega is from Lemma 2.10 page 9. Source: https://arxiv.org/abs/0705.1652.
Fifty delay steps of width 1 / 100 from 3 to 7 / 2 use omega u = (1 + log (u - 1)) / u
on 2 to 5 / 2 with rational logarithm certificates, and the cap is checked at every
node from 16 / 5 on, where omega stays within 4 / 10000 of the cap.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Task587.CapChain562
open Wu04Functional

/-- One delay step of Wu 2004 Lemma 2.10 page 9 from a to b inside 3 to 7 / 2,
with the delayed values bounded through log (b - 2) at most L. -/
theorem cap_step_log {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a b L P : ℝ} (h3a : 3 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7 / 2) (hL : log (b - 2) ≤ L) (hP : a * ω a ≤ P) :
    ∀ u ∈ Icc a b, u * ω u ≤ P + (u - a) * ((1 + L) / (a - 1)) := by
  intro u hu
  have ha0 : 0 < a := by linarith
  have hbase : ω a ≤ P / a := by
    rw [le_div_iff₀ ha0]
    linarith
  have h := Task587.delay_affine_upper hω (a := a) (u := u) (B := P / a)
    (C := (1 + L) / (a - 1)) (by linarith) hu.1 hbase (fun t ht => by
      have hf := Wu04Buchstab.formula_two_three hω (u := t - 1)
        ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
      rw [hf]
      have hlog0 : 0 ≤ log (t - 1 - 1) := log_nonneg (by linarith [ht.1])
      have hlog : log (t - 1 - 1) ≤ L :=
        (log_le_log (by linarith [ht.1]) (by linarith [ht.2, hu.2])).trans hL
      rw [div_le_div_iff₀ (by linarith [ht.1]) (by linarith)]
      have h1 : (1 + log (t - 1 - 1)) * (a - 1) ≤ (1 + L) * (a - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h2 : (1 + L) * (a - 1) ≤ (1 + L) * (t - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by linarith)
      linarith)
  have hcancel : a * (P / a) = P := by field_simp
  linarith

/-- A cap c on one step, from the cap at both nodes of the affine bound,
Wu 2004 Lemma 2.10 page 9. -/
theorem cap_on_step {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a b L P c u : ℝ} (h3a : 3 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7 / 2) (hL : log (b - 2) ≤ L) (hP : a * ω a ≤ P)
    (hc1 : P ≤ c * a) (hc2 : P + (b - a) * ((1 + L) / (a - 1)) ≤ c * b)
    (hu : u ∈ Icc a b) : ω u ≤ c := by
  have h := cap_step_log hω h3a hab hb hL hP u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hw : u * ω u ≤ u * c := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have : u = a := by linarith [hu.1, hu.2]
      subst this
      nlinarith
    · have hθ : P + (u - a) * ((1 + L) / (a - 1)) ≤ c * u := by
        have hlin : P + (u - a) * ((1 + L) / (a - 1)) =
            (b - u) / (b - a) * P + (u - a) / (b - a) * (P + (b - a) * ((1 + L) / (a - 1))) := by
          field_simp
          ring
        have e1 : (b - u) / (b - a) * P ≤ (b - u) / (b - a) * (c * a) :=
          mul_le_mul_of_nonneg_left hc1 (div_nonneg (by linarith [hu.2]) (by linarith))
        have e2 : (u - a) / (b - a) * (P + (b - a) * ((1 + L) / (a - 1))) ≤
            (u - a) / (b - a) * (c * b) :=
          mul_le_mul_of_nonneg_left hc2 (div_nonneg (by linarith [hu.1]) (by linarith))
        have hcu : (b - u) / (b - a) * (c * a) + (u - a) / (b - a) * (c * b) = c * u := by
          field_simp
          ring
        linarith
      linarith
  exact le_of_mul_le_mul_left hw hu0

/-- Rational logarithm certificates at the fifty nodes, from the enclosure of
Wu04Integral.log_bounds. -/
theorem log_cert_0 : log ((301 / 100 : ℝ) - 2) ≤ (9950331 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (301 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_1 : log ((151 / 50 : ℝ) - 2) ≤ (4950657 / 250000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (151 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_2 : log ((303 / 100 : ℝ) - 2) ≤ (29558803 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (303 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_3 : log ((76 / 25 : ℝ) - 2) ≤ (19610357 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (76 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_4 : log ((61 / 20 : ℝ) - 2) ≤ (9758033 / 200000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (61 / 20 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_5 : log ((153 / 50 : ℝ) - 2) ≤ (58268909 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (153 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_6 : log ((307 / 100 : ℝ) - 2) ≤ (67658649 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (307 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_7 : log ((77 / 25 : ℝ) - 2) ≤ (38480521 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (77 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_8 : log ((309 / 100 : ℝ) - 2) ≤ (86177697 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (309 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_9 : log ((31 / 10 : ℝ) - 2) ≤ (4765509 / 50000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (31 / 10 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_10 : log ((311 / 100 : ℝ) - 2) ≤ (6522501 / 62500000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (311 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_11 : log ((78 / 25 : ℝ) - 2) ≤ (56664343 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (78 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_12 : log ((313 / 100 : ℝ) - 2) ≤ (122217633 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (313 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_13 : log ((157 / 50 : ℝ) - 2) ≤ (131028263 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (157 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_14 : log ((63 / 20 : ℝ) - 2) ≤ (139761943 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (63 / 20 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_15 : log ((79 / 25 : ℝ) - 2) ≤ (74210003 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (79 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_16 : log ((317 / 100 : ℝ) - 2) ≤ (125603 / 800000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (317 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_17 : log ((159 / 50 : ℝ) - 2) ≤ (165514439 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (159 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_18 : log ((319 / 100 : ℝ) - 2) ≤ (43488327 / 250000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (319 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_19 : log ((16 / 5 : ℝ) - 2) ≤ (91160779 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (16 / 5 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_20 : log ((321 / 100 : ℝ) - 2) ≤ (190620361 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (321 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_21 : log ((161 / 50 : ℝ) - 2) ≤ (198850861 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (161 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_22 : log ((323 / 100 : ℝ) - 2) ≤ (51753543 / 250000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (323 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_23 : log ((81 / 25 : ℝ) - 2) ≤ (215111383 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (81 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_24 : log ((13 / 4 : ℝ) - 2) ≤ (55785889 / 250000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (13 / 4 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_25 : log ((163 / 50 : ℝ) - 2) ≤ (14444483 / 62500000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (163 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_26 : log ((327 / 100 : ℝ) - 2) ≤ (23901691 / 100000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (327 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_27 : log ((82 / 25 : ℝ) - 2) ≤ (24686009 / 100000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (82 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_28 : log ((329 / 100 : ℝ) - 2) ≤ (127321117 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (329 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_29 : log ((33 / 10 : ℝ) - 2) ≤ (52472857 / 200000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (33 / 10 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_30 : log ((331 / 100 : ℝ) - 2) ≤ (270027163 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (331 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_31 : log ((83 / 25 : ℝ) - 2) ≤ (27763177 / 100000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (83 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_32 : log ((333 / 100 : ℝ) - 2) ≤ (35647373 / 125000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (333 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_33 : log ((167 / 50 : ℝ) - 2) ≤ (292669667 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (167 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_34 : log ((67 / 20 : ℝ) - 2) ≤ (300104659 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (67 / 20 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_35 : log ((84 / 25 : ℝ) - 2) ≤ (153742391 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (84 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_36 : log ((337 / 100 : ℝ) - 2) ≤ (314810841 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (337 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_37 : log ((169 / 50 : ℝ) - 2) ≤ (322083623 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (169 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_38 : log ((339 / 100 : ℝ) - 2) ≤ (164651949 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (339 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_39 : log ((17 / 5 : ℝ) - 2) ≤ (336472419 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (17 / 5 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_40 : log ((341 / 100 : ℝ) - 2) ≤ (85897481 / 250000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (341 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_41 : log ((171 / 50 : ℝ) - 2) ≤ (175328567 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (171 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_42 : log ((343 / 100 : ℝ) - 2) ≤ (357674757 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (343 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_43 : log ((86 / 25 : ℝ) - 2) ≤ (72928697 / 200000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (86 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_44 : log ((69 / 20 : ℝ) - 2) ≤ (74312799 / 200000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (69 / 20 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_45 : log ((173 / 50 : ℝ) - 2) ≤ (47304619 / 125000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (173 / 50 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_46 : log ((347 / 100 : ℝ) - 2) ≤ (77052601 / 200000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (347 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_47 : log ((87 / 25 : ℝ) - 2) ≤ (392042793 / 1000000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (87 / 25 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_48 : log ((349 / 100 : ℝ) - 2) ≤ (19938847 / 50000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (349 / 100 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

theorem log_cert_49 : log ((7 / 2 : ℝ) - 2) ≤ (202733029 / 500000000 : ℝ) := by
  have h := (Wu04Integral.log_bounds 4 (y := (7 / 2 : ℝ) - 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

/-- The node bounds node_k : x_k omega x_k at most P_k along the fifty steps,
Wu 2004 Lemma 2.10 page 9. -/
theorem node_bounds {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    (3 / 1 : ℝ) * ω (3 / 1 : ℝ) ≤ (4233 / 2500 : ℝ) ∧
    (301 / 100 : ℝ) * ω (301 / 100 : ℝ) ≤ (212281219 / 125000000 : ℝ) ∧
    (151 / 50 : ℝ) * ω (151 / 50 : ℝ) ≤ (1703323397 / 1000000000 : ℝ) ∧
    (303 / 100 : ℝ) * ω (303 / 100 : ℝ) ≤ (1708420223 / 1000000000 : ℝ) ∧
    (76 / 25 : ℝ) * ω (76 / 25 : ℝ) ≤ (1713539537 / 1000000000 : ℝ) ∧
    (61 / 20 : ℝ) * ω (61 / 20 : ℝ) ≤ (859340333 / 500000000 : ℝ) ∧
    (153 / 50 : ℝ) * ω (153 / 50 : ℝ) ≤ (861921477 / 500000000 : ℝ) ∧
    (307 / 100 : ℝ) * ω (307 / 100 : ℝ) ≤ (1729025763 / 1000000000 : ℝ) ∧
    (77 / 25 : ℝ) * ω (77 / 25 : ℝ) ≤ (867114237 / 500000000 : ℝ) ∧
    (309 / 100 : ℝ) * ω (309 / 100 : ℝ) ≤ (1739450483 / 1000000000 : ℝ) ∧
    (31 / 10 : ℝ) * ω (31 / 10 : ℝ) ≤ (872345601 / 500000000 : ℝ) ∧
    (311 / 100 : ℝ) * ω (311 / 100 : ℝ) ≤ (87497503 / 50000000 : ℝ) ∧
    (78 / 25 : ℝ) * ω (78 / 25 : ℝ) ≤ (3510453 / 2000000 : ℝ) ∧
    (313 / 100 : ℝ) * ω (313 / 100 : ℝ) ≤ (88025999 / 50000000 : ℝ) ∧
    (157 / 50 : ℝ) * ω (157 / 50 : ℝ) ≤ (441457493 / 250000000 : ℝ) ∧
    (63 / 20 : ℝ) * ω (63 / 20 : ℝ) ≤ (1771155963 / 1000000000 : ℝ) ∧
    (79 / 25 : ℝ) * ω (79 / 25 : ℝ) ≤ (444124363 / 250000000 : ℝ) ∧
    (317 / 100 : ℝ) * ω (317 / 100 : ℝ) ≤ (1781853951 / 1000000000 : ℝ) ∧
    (159 / 50 : ℝ) * ω (159 / 50 : ℝ) ≤ (893612493 / 500000000 : ℝ) ∧
    (319 / 100 : ℝ) * ω (319 / 100 : ℝ) ≤ (1792610093 / 1000000000 : ℝ) ∧
    (16 / 5 : ℝ) * ω (16 / 5 : ℝ) ≤ (899004411 / 500000000 : ℝ) ∧
    (321 / 100 : ℝ) * ω (321 / 100 : ℝ) ≤ (1803420733 / 1000000000 : ℝ) ∧
    (161 / 50 : ℝ) * ω (161 / 50 : ℝ) ≤ (904422699 / 500000000 : ℝ) ∧
    (323 / 100 : ℝ) * ω (323 / 100 : ℝ) ≤ (1814282399 / 1000000000 : ℝ) ∧
    (81 / 25 : ℝ) * ω (81 / 25 : ℝ) ≤ (1819731329 / 1000000000 : ℝ) ∧
    (13 / 4 : ℝ) * ω (13 / 4 : ℝ) ≤ (114074487 / 62500000 : ℝ) ∧
    (163 / 50 : ℝ) * ω (163 / 50 : ℝ) ≤ (9153317 / 5000000 : ℝ) ∧
    (327 / 100 : ℝ) * ω (327 / 100 : ℝ) ≤ (114759111 / 62500000 : ℝ) ∧
    (82 / 25 : ℝ) * ω (82 / 25 : ℝ) ≤ (230204819 / 125000000 : ℝ) ∧
    (329 / 100 : ℝ) * ω (329 / 100 : ℝ) ≤ (1847141369 / 1000000000 : ℝ) ∧
    (33 / 10 : ℝ) * ω (33 / 10 : ℝ) ≤ (1852653877 / 1000000000 : ℝ) ∧
    (331 / 100 : ℝ) * ω (331 / 100 : ℝ) ≤ (371635147 / 200000000 : ℝ) ∧
    (83 / 25 : ℝ) * ω (83 / 25 : ℝ) ≤ (1863706609 / 1000000000 : ℝ) ∧
    (333 / 100 : ℝ) * ω (333 / 100 : ℝ) ≤ (934623087 / 500000000 : ℝ) ∧
    (167 / 50 : ℝ) * ω (167 / 50 : ℝ) ≤ (1874794113 / 1000000000 : ℝ) ∧
    (67 / 20 : ℝ) * ω (67 / 20 : ℝ) ≤ (470087529 / 250000000 : ℝ) ∧
    (84 / 25 : ℝ) * ω (84 / 25 : ℝ) ≤ (942956941 / 500000000 : ℝ) ∧
    (337 / 100 : ℝ) * ω (337 / 100 : ℝ) ≤ (378297023 / 200000000 : ℝ) ∧
    (169 / 50 : ℝ) * ω (169 / 50 : ℝ) ≤ (1897063527 / 1000000000 : ℝ) ∧
    (339 / 100 : ℝ) * ω (339 / 100 : ℝ) ≤ (951324419 / 500000000 : ℝ) ∧
    (17 / 5 : ℝ) * ω (17 / 5 : ℝ) ≤ (1908240773 / 1000000000 : ℝ) ∧
    (341 / 100 : ℝ) * ω (341 / 100 : ℝ) ≤ (382767813 / 200000000 : ℝ) ∧
    (171 / 50 : ℝ) * ω (171 / 50 : ℝ) ≤ (479860863 / 250000000 : ℝ) ∧
    (343 / 100 : ℝ) * ω (343 / 100 : ℝ) ≤ (1925053679 / 1000000000 : ℝ) ∧
    (86 / 25 : ℝ) * ω (86 / 25 : ℝ) ≤ (241333687 / 125000000 : ℝ) ∧
    (69 / 20 : ℝ) * ω (69 / 20 : ℝ) ≤ (96814533 / 50000000 : ℝ) ∧
    (173 / 50 : ℝ) * ω (173 / 50 : ℝ) ≤ (970958467 / 500000000 : ℝ) ∧
    (347 / 100 : ℝ) * ω (347 / 100 : ℝ) ≤ (389509617 / 200000000 : ℝ) ∧
    (87 / 25 : ℝ) * ω (87 / 25 : ℝ) ≤ (976591943 / 500000000 : ℝ) ∧
    (349 / 100 : ℝ) * ω (349 / 100 : ℝ) ≤ (489706029 / 250000000 : ℝ) ∧
    (7 / 2 : ℝ) * ω (7 / 2 : ℝ) ≤ (982234279 / 500000000 : ℝ) := by
  have n0 : (3 / 1 : ℝ) * ω (3 / 1 : ℝ) ≤ (4233 / 2500 : ℝ) := by
    have := CapChain.three_omega_three hω
    norm_num at this ⊢
    linarith
  have n1 : (301 / 100 : ℝ) * ω (301 / 100 : ℝ) ≤ (212281219 / 125000000 : ℝ) := by
    have h := cap_step_log hω (a := (3 / 1 : ℝ)) (b := (301 / 100 : ℝ)) (L := (9950331 / 1000000000 : ℝ)) (P := (4233 / 2500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_0 n0 (301 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n2 : (151 / 50 : ℝ) * ω (151 / 50 : ℝ) ≤ (1703323397 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (301 / 100 : ℝ)) (b := (151 / 50 : ℝ)) (L := (4950657 / 250000000 : ℝ)) (P := (212281219 / 125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_1 n1 (151 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n3 : (303 / 100 : ℝ) * ω (303 / 100 : ℝ) ≤ (1708420223 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (151 / 50 : ℝ)) (b := (303 / 100 : ℝ)) (L := (29558803 / 1000000000 : ℝ)) (P := (1703323397 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_2 n2 (303 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n4 : (76 / 25 : ℝ) * ω (76 / 25 : ℝ) ≤ (1713539537 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (303 / 100 : ℝ)) (b := (76 / 25 : ℝ)) (L := (19610357 / 500000000 : ℝ)) (P := (1708420223 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_3 n3 (76 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n5 : (61 / 20 : ℝ) * ω (61 / 20 : ℝ) ≤ (859340333 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (76 / 25 : ℝ)) (b := (61 / 20 : ℝ)) (L := (9758033 / 200000000 : ℝ)) (P := (1713539537 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_4 n4 (61 / 20 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n6 : (153 / 50 : ℝ) * ω (153 / 50 : ℝ) ≤ (861921477 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (61 / 20 : ℝ)) (b := (153 / 50 : ℝ)) (L := (58268909 / 1000000000 : ℝ)) (P := (859340333 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_5 n5 (153 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n7 : (307 / 100 : ℝ) * ω (307 / 100 : ℝ) ≤ (1729025763 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (153 / 50 : ℝ)) (b := (307 / 100 : ℝ)) (L := (67658649 / 1000000000 : ℝ)) (P := (861921477 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_6 n6 (307 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n8 : (77 / 25 : ℝ) * ω (77 / 25 : ℝ) ≤ (867114237 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (307 / 100 : ℝ)) (b := (77 / 25 : ℝ)) (L := (38480521 / 500000000 : ℝ)) (P := (1729025763 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_7 n7 (77 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n9 : (309 / 100 : ℝ) * ω (309 / 100 : ℝ) ≤ (1739450483 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (77 / 25 : ℝ)) (b := (309 / 100 : ℝ)) (L := (86177697 / 1000000000 : ℝ)) (P := (867114237 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_8 n8 (309 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n10 : (31 / 10 : ℝ) * ω (31 / 10 : ℝ) ≤ (872345601 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (309 / 100 : ℝ)) (b := (31 / 10 : ℝ)) (L := (4765509 / 50000000 : ℝ)) (P := (1739450483 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_9 n9 (31 / 10 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n11 : (311 / 100 : ℝ) * ω (311 / 100 : ℝ) ≤ (87497503 / 50000000 : ℝ) := by
    have h := cap_step_log hω (a := (31 / 10 : ℝ)) (b := (311 / 100 : ℝ)) (L := (6522501 / 62500000 : ℝ)) (P := (872345601 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_10 n10 (311 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n12 : (78 / 25 : ℝ) * ω (78 / 25 : ℝ) ≤ (3510453 / 2000000 : ℝ) := by
    have h := cap_step_log hω (a := (311 / 100 : ℝ)) (b := (78 / 25 : ℝ)) (L := (56664343 / 500000000 : ℝ)) (P := (87497503 / 50000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_11 n11 (78 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n13 : (313 / 100 : ℝ) * ω (313 / 100 : ℝ) ≤ (88025999 / 50000000 : ℝ) := by
    have h := cap_step_log hω (a := (78 / 25 : ℝ)) (b := (313 / 100 : ℝ)) (L := (122217633 / 1000000000 : ℝ)) (P := (3510453 / 2000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_12 n12 (313 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n14 : (157 / 50 : ℝ) * ω (157 / 50 : ℝ) ≤ (441457493 / 250000000 : ℝ) := by
    have h := cap_step_log hω (a := (313 / 100 : ℝ)) (b := (157 / 50 : ℝ)) (L := (131028263 / 1000000000 : ℝ)) (P := (88025999 / 50000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_13 n13 (157 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n15 : (63 / 20 : ℝ) * ω (63 / 20 : ℝ) ≤ (1771155963 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (157 / 50 : ℝ)) (b := (63 / 20 : ℝ)) (L := (139761943 / 1000000000 : ℝ)) (P := (441457493 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_14 n14 (63 / 20 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n16 : (79 / 25 : ℝ) * ω (79 / 25 : ℝ) ≤ (444124363 / 250000000 : ℝ) := by
    have h := cap_step_log hω (a := (63 / 20 : ℝ)) (b := (79 / 25 : ℝ)) (L := (74210003 / 500000000 : ℝ)) (P := (1771155963 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_15 n15 (79 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n17 : (317 / 100 : ℝ) * ω (317 / 100 : ℝ) ≤ (1781853951 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (79 / 25 : ℝ)) (b := (317 / 100 : ℝ)) (L := (125603 / 800000 : ℝ)) (P := (444124363 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_16 n16 (317 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n18 : (159 / 50 : ℝ) * ω (159 / 50 : ℝ) ≤ (893612493 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (317 / 100 : ℝ)) (b := (159 / 50 : ℝ)) (L := (165514439 / 1000000000 : ℝ)) (P := (1781853951 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_17 n17 (159 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n19 : (319 / 100 : ℝ) * ω (319 / 100 : ℝ) ≤ (1792610093 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (159 / 50 : ℝ)) (b := (319 / 100 : ℝ)) (L := (43488327 / 250000000 : ℝ)) (P := (893612493 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_18 n18 (319 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n20 : (16 / 5 : ℝ) * ω (16 / 5 : ℝ) ≤ (899004411 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (319 / 100 : ℝ)) (b := (16 / 5 : ℝ)) (L := (91160779 / 500000000 : ℝ)) (P := (1792610093 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_19 n19 (16 / 5 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n21 : (321 / 100 : ℝ) * ω (321 / 100 : ℝ) ≤ (1803420733 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (16 / 5 : ℝ)) (b := (321 / 100 : ℝ)) (L := (190620361 / 1000000000 : ℝ)) (P := (899004411 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_20 n20 (321 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n22 : (161 / 50 : ℝ) * ω (161 / 50 : ℝ) ≤ (904422699 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (321 / 100 : ℝ)) (b := (161 / 50 : ℝ)) (L := (198850861 / 1000000000 : ℝ)) (P := (1803420733 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_21 n21 (161 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n23 : (323 / 100 : ℝ) * ω (323 / 100 : ℝ) ≤ (1814282399 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (161 / 50 : ℝ)) (b := (323 / 100 : ℝ)) (L := (51753543 / 250000000 : ℝ)) (P := (904422699 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_22 n22 (323 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n24 : (81 / 25 : ℝ) * ω (81 / 25 : ℝ) ≤ (1819731329 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (323 / 100 : ℝ)) (b := (81 / 25 : ℝ)) (L := (215111383 / 1000000000 : ℝ)) (P := (1814282399 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_23 n23 (81 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n25 : (13 / 4 : ℝ) * ω (13 / 4 : ℝ) ≤ (114074487 / 62500000 : ℝ) := by
    have h := cap_step_log hω (a := (81 / 25 : ℝ)) (b := (13 / 4 : ℝ)) (L := (55785889 / 250000000 : ℝ)) (P := (1819731329 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_24 n24 (13 / 4 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n26 : (163 / 50 : ℝ) * ω (163 / 50 : ℝ) ≤ (9153317 / 5000000 : ℝ) := by
    have h := cap_step_log hω (a := (13 / 4 : ℝ)) (b := (163 / 50 : ℝ)) (L := (14444483 / 62500000 : ℝ)) (P := (114074487 / 62500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_25 n25 (163 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n27 : (327 / 100 : ℝ) * ω (327 / 100 : ℝ) ≤ (114759111 / 62500000 : ℝ) := by
    have h := cap_step_log hω (a := (163 / 50 : ℝ)) (b := (327 / 100 : ℝ)) (L := (23901691 / 100000000 : ℝ)) (P := (9153317 / 5000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_26 n26 (327 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n28 : (82 / 25 : ℝ) * ω (82 / 25 : ℝ) ≤ (230204819 / 125000000 : ℝ) := by
    have h := cap_step_log hω (a := (327 / 100 : ℝ)) (b := (82 / 25 : ℝ)) (L := (24686009 / 100000000 : ℝ)) (P := (114759111 / 62500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_27 n27 (82 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n29 : (329 / 100 : ℝ) * ω (329 / 100 : ℝ) ≤ (1847141369 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (82 / 25 : ℝ)) (b := (329 / 100 : ℝ)) (L := (127321117 / 500000000 : ℝ)) (P := (230204819 / 125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_28 n28 (329 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n30 : (33 / 10 : ℝ) * ω (33 / 10 : ℝ) ≤ (1852653877 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (329 / 100 : ℝ)) (b := (33 / 10 : ℝ)) (L := (52472857 / 200000000 : ℝ)) (P := (1847141369 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_29 n29 (33 / 10 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n31 : (331 / 100 : ℝ) * ω (331 / 100 : ℝ) ≤ (371635147 / 200000000 : ℝ) := by
    have h := cap_step_log hω (a := (33 / 10 : ℝ)) (b := (331 / 100 : ℝ)) (L := (270027163 / 1000000000 : ℝ)) (P := (1852653877 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_30 n30 (331 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n32 : (83 / 25 : ℝ) * ω (83 / 25 : ℝ) ≤ (1863706609 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (331 / 100 : ℝ)) (b := (83 / 25 : ℝ)) (L := (27763177 / 100000000 : ℝ)) (P := (371635147 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_31 n31 (83 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n33 : (333 / 100 : ℝ) * ω (333 / 100 : ℝ) ≤ (934623087 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (83 / 25 : ℝ)) (b := (333 / 100 : ℝ)) (L := (35647373 / 125000000 : ℝ)) (P := (1863706609 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_32 n32 (333 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n34 : (167 / 50 : ℝ) * ω (167 / 50 : ℝ) ≤ (1874794113 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (333 / 100 : ℝ)) (b := (167 / 50 : ℝ)) (L := (292669667 / 1000000000 : ℝ)) (P := (934623087 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_33 n33 (167 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n35 : (67 / 20 : ℝ) * ω (67 / 20 : ℝ) ≤ (470087529 / 250000000 : ℝ) := by
    have h := cap_step_log hω (a := (167 / 50 : ℝ)) (b := (67 / 20 : ℝ)) (L := (300104659 / 1000000000 : ℝ)) (P := (1874794113 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_34 n34 (67 / 20 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n36 : (84 / 25 : ℝ) * ω (84 / 25 : ℝ) ≤ (942956941 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (67 / 20 : ℝ)) (b := (84 / 25 : ℝ)) (L := (153742391 / 500000000 : ℝ)) (P := (470087529 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_35 n35 (84 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n37 : (337 / 100 : ℝ) * ω (337 / 100 : ℝ) ≤ (378297023 / 200000000 : ℝ) := by
    have h := cap_step_log hω (a := (84 / 25 : ℝ)) (b := (337 / 100 : ℝ)) (L := (314810841 / 1000000000 : ℝ)) (P := (942956941 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_36 n36 (337 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n38 : (169 / 50 : ℝ) * ω (169 / 50 : ℝ) ≤ (1897063527 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (337 / 100 : ℝ)) (b := (169 / 50 : ℝ)) (L := (322083623 / 1000000000 : ℝ)) (P := (378297023 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_37 n37 (169 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n39 : (339 / 100 : ℝ) * ω (339 / 100 : ℝ) ≤ (951324419 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (169 / 50 : ℝ)) (b := (339 / 100 : ℝ)) (L := (164651949 / 500000000 : ℝ)) (P := (1897063527 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_38 n38 (339 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n40 : (17 / 5 : ℝ) * ω (17 / 5 : ℝ) ≤ (1908240773 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (339 / 100 : ℝ)) (b := (17 / 5 : ℝ)) (L := (336472419 / 1000000000 : ℝ)) (P := (951324419 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_39 n39 (17 / 5 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n41 : (341 / 100 : ℝ) * ω (341 / 100 : ℝ) ≤ (382767813 / 200000000 : ℝ) := by
    have h := cap_step_log hω (a := (17 / 5 : ℝ)) (b := (341 / 100 : ℝ)) (L := (85897481 / 250000000 : ℝ)) (P := (1908240773 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_40 n40 (341 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n42 : (171 / 50 : ℝ) * ω (171 / 50 : ℝ) ≤ (479860863 / 250000000 : ℝ) := by
    have h := cap_step_log hω (a := (341 / 100 : ℝ)) (b := (171 / 50 : ℝ)) (L := (175328567 / 500000000 : ℝ)) (P := (382767813 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_41 n41 (171 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n43 : (343 / 100 : ℝ) * ω (343 / 100 : ℝ) ≤ (1925053679 / 1000000000 : ℝ) := by
    have h := cap_step_log hω (a := (171 / 50 : ℝ)) (b := (343 / 100 : ℝ)) (L := (357674757 / 1000000000 : ℝ)) (P := (479860863 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_42 n42 (343 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n44 : (86 / 25 : ℝ) * ω (86 / 25 : ℝ) ≤ (241333687 / 125000000 : ℝ) := by
    have h := cap_step_log hω (a := (343 / 100 : ℝ)) (b := (86 / 25 : ℝ)) (L := (72928697 / 200000000 : ℝ)) (P := (1925053679 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_43 n43 (86 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n45 : (69 / 20 : ℝ) * ω (69 / 20 : ℝ) ≤ (96814533 / 50000000 : ℝ) := by
    have h := cap_step_log hω (a := (86 / 25 : ℝ)) (b := (69 / 20 : ℝ)) (L := (74312799 / 200000000 : ℝ)) (P := (241333687 / 125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_44 n44 (69 / 20 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n46 : (173 / 50 : ℝ) * ω (173 / 50 : ℝ) ≤ (970958467 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (69 / 20 : ℝ)) (b := (173 / 50 : ℝ)) (L := (47304619 / 125000000 : ℝ)) (P := (96814533 / 50000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_45 n45 (173 / 50 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n47 : (347 / 100 : ℝ) * ω (347 / 100 : ℝ) ≤ (389509617 / 200000000 : ℝ) := by
    have h := cap_step_log hω (a := (173 / 50 : ℝ)) (b := (347 / 100 : ℝ)) (L := (77052601 / 200000000 : ℝ)) (P := (970958467 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_46 n46 (347 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n48 : (87 / 25 : ℝ) * ω (87 / 25 : ℝ) ≤ (976591943 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (347 / 100 : ℝ)) (b := (87 / 25 : ℝ)) (L := (392042793 / 1000000000 : ℝ)) (P := (389509617 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_47 n47 (87 / 25 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n49 : (349 / 100 : ℝ) * ω (349 / 100 : ℝ) ≤ (489706029 / 250000000 : ℝ) := by
    have h := cap_step_log hω (a := (87 / 25 : ℝ)) (b := (349 / 100 : ℝ)) (L := (19938847 / 50000000 : ℝ)) (P := (976591943 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_48 n48 (349 / 100 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  have n50 : (7 / 2 : ℝ) * ω (7 / 2 : ℝ) ≤ (982234279 / 500000000 : ℝ) := by
    have h := cap_step_log hω (a := (349 / 100 : ℝ)) (b := (7 / 2 : ℝ)) (L := (202733029 / 500000000 : ℝ)) (P := (489706029 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_49 n49 (7 / 2 : ℝ) ⟨by norm_num, le_rfl⟩
    norm_num at h ⊢
    linarith
  exact ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50⟩

/-- Omega is at most 562 / 1000 from 16 / 5 on, Wu 2004 Lemma 2.10 page 9 values,
for the r0j13 window split of Lemma 5.2 page 26. -/
theorem cap_562 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (16 / 5 : ℝ) ≤ u) :
    ω u ≤ (562 / 1000 : ℝ) := by
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50⟩ := node_bounds hω
  rcases le_total u (321 / 100 : ℝ) with h20 | h20
  · exact cap_on_step hω (a := (16 / 5 : ℝ)) (b := (321 / 100 : ℝ)) (L := (190620361 / 1000000000 : ℝ)) (P := (899004411 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_20 n20 (by norm_num) (by norm_num)
      ⟨by linarith, h20⟩
  rcases le_total u (161 / 50 : ℝ) with h21 | h21
  · exact cap_on_step hω (a := (321 / 100 : ℝ)) (b := (161 / 50 : ℝ)) (L := (198850861 / 1000000000 : ℝ)) (P := (1803420733 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_21 n21 (by norm_num) (by norm_num)
      ⟨by linarith, h21⟩
  rcases le_total u (323 / 100 : ℝ) with h22 | h22
  · exact cap_on_step hω (a := (161 / 50 : ℝ)) (b := (323 / 100 : ℝ)) (L := (51753543 / 250000000 : ℝ)) (P := (904422699 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_22 n22 (by norm_num) (by norm_num)
      ⟨by linarith, h22⟩
  rcases le_total u (81 / 25 : ℝ) with h23 | h23
  · exact cap_on_step hω (a := (323 / 100 : ℝ)) (b := (81 / 25 : ℝ)) (L := (215111383 / 1000000000 : ℝ)) (P := (1814282399 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_23 n23 (by norm_num) (by norm_num)
      ⟨by linarith, h23⟩
  rcases le_total u (13 / 4 : ℝ) with h24 | h24
  · exact cap_on_step hω (a := (81 / 25 : ℝ)) (b := (13 / 4 : ℝ)) (L := (55785889 / 250000000 : ℝ)) (P := (1819731329 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_24 n24 (by norm_num) (by norm_num)
      ⟨by linarith, h24⟩
  rcases le_total u (163 / 50 : ℝ) with h25 | h25
  · exact cap_on_step hω (a := (13 / 4 : ℝ)) (b := (163 / 50 : ℝ)) (L := (14444483 / 62500000 : ℝ)) (P := (114074487 / 62500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_25 n25 (by norm_num) (by norm_num)
      ⟨by linarith, h25⟩
  rcases le_total u (327 / 100 : ℝ) with h26 | h26
  · exact cap_on_step hω (a := (163 / 50 : ℝ)) (b := (327 / 100 : ℝ)) (L := (23901691 / 100000000 : ℝ)) (P := (9153317 / 5000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_26 n26 (by norm_num) (by norm_num)
      ⟨by linarith, h26⟩
  rcases le_total u (82 / 25 : ℝ) with h27 | h27
  · exact cap_on_step hω (a := (327 / 100 : ℝ)) (b := (82 / 25 : ℝ)) (L := (24686009 / 100000000 : ℝ)) (P := (114759111 / 62500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_27 n27 (by norm_num) (by norm_num)
      ⟨by linarith, h27⟩
  rcases le_total u (329 / 100 : ℝ) with h28 | h28
  · exact cap_on_step hω (a := (82 / 25 : ℝ)) (b := (329 / 100 : ℝ)) (L := (127321117 / 500000000 : ℝ)) (P := (230204819 / 125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_28 n28 (by norm_num) (by norm_num)
      ⟨by linarith, h28⟩
  rcases le_total u (33 / 10 : ℝ) with h29 | h29
  · exact cap_on_step hω (a := (329 / 100 : ℝ)) (b := (33 / 10 : ℝ)) (L := (52472857 / 200000000 : ℝ)) (P := (1847141369 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_29 n29 (by norm_num) (by norm_num)
      ⟨by linarith, h29⟩
  rcases le_total u (331 / 100 : ℝ) with h30 | h30
  · exact cap_on_step hω (a := (33 / 10 : ℝ)) (b := (331 / 100 : ℝ)) (L := (270027163 / 1000000000 : ℝ)) (P := (1852653877 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_30 n30 (by norm_num) (by norm_num)
      ⟨by linarith, h30⟩
  rcases le_total u (83 / 25 : ℝ) with h31 | h31
  · exact cap_on_step hω (a := (331 / 100 : ℝ)) (b := (83 / 25 : ℝ)) (L := (27763177 / 100000000 : ℝ)) (P := (371635147 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_31 n31 (by norm_num) (by norm_num)
      ⟨by linarith, h31⟩
  rcases le_total u (333 / 100 : ℝ) with h32 | h32
  · exact cap_on_step hω (a := (83 / 25 : ℝ)) (b := (333 / 100 : ℝ)) (L := (35647373 / 125000000 : ℝ)) (P := (1863706609 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_32 n32 (by norm_num) (by norm_num)
      ⟨by linarith, h32⟩
  rcases le_total u (167 / 50 : ℝ) with h33 | h33
  · exact cap_on_step hω (a := (333 / 100 : ℝ)) (b := (167 / 50 : ℝ)) (L := (292669667 / 1000000000 : ℝ)) (P := (934623087 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_33 n33 (by norm_num) (by norm_num)
      ⟨by linarith, h33⟩
  rcases le_total u (67 / 20 : ℝ) with h34 | h34
  · exact cap_on_step hω (a := (167 / 50 : ℝ)) (b := (67 / 20 : ℝ)) (L := (300104659 / 1000000000 : ℝ)) (P := (1874794113 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_34 n34 (by norm_num) (by norm_num)
      ⟨by linarith, h34⟩
  rcases le_total u (84 / 25 : ℝ) with h35 | h35
  · exact cap_on_step hω (a := (67 / 20 : ℝ)) (b := (84 / 25 : ℝ)) (L := (153742391 / 500000000 : ℝ)) (P := (470087529 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_35 n35 (by norm_num) (by norm_num)
      ⟨by linarith, h35⟩
  rcases le_total u (337 / 100 : ℝ) with h36 | h36
  · exact cap_on_step hω (a := (84 / 25 : ℝ)) (b := (337 / 100 : ℝ)) (L := (314810841 / 1000000000 : ℝ)) (P := (942956941 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_36 n36 (by norm_num) (by norm_num)
      ⟨by linarith, h36⟩
  rcases le_total u (169 / 50 : ℝ) with h37 | h37
  · exact cap_on_step hω (a := (337 / 100 : ℝ)) (b := (169 / 50 : ℝ)) (L := (322083623 / 1000000000 : ℝ)) (P := (378297023 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_37 n37 (by norm_num) (by norm_num)
      ⟨by linarith, h37⟩
  rcases le_total u (339 / 100 : ℝ) with h38 | h38
  · exact cap_on_step hω (a := (169 / 50 : ℝ)) (b := (339 / 100 : ℝ)) (L := (164651949 / 500000000 : ℝ)) (P := (1897063527 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_38 n38 (by norm_num) (by norm_num)
      ⟨by linarith, h38⟩
  rcases le_total u (17 / 5 : ℝ) with h39 | h39
  · exact cap_on_step hω (a := (339 / 100 : ℝ)) (b := (17 / 5 : ℝ)) (L := (336472419 / 1000000000 : ℝ)) (P := (951324419 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_39 n39 (by norm_num) (by norm_num)
      ⟨by linarith, h39⟩
  rcases le_total u (341 / 100 : ℝ) with h40 | h40
  · exact cap_on_step hω (a := (17 / 5 : ℝ)) (b := (341 / 100 : ℝ)) (L := (85897481 / 250000000 : ℝ)) (P := (1908240773 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_40 n40 (by norm_num) (by norm_num)
      ⟨by linarith, h40⟩
  rcases le_total u (171 / 50 : ℝ) with h41 | h41
  · exact cap_on_step hω (a := (341 / 100 : ℝ)) (b := (171 / 50 : ℝ)) (L := (175328567 / 500000000 : ℝ)) (P := (382767813 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_41 n41 (by norm_num) (by norm_num)
      ⟨by linarith, h41⟩
  rcases le_total u (343 / 100 : ℝ) with h42 | h42
  · exact cap_on_step hω (a := (171 / 50 : ℝ)) (b := (343 / 100 : ℝ)) (L := (357674757 / 1000000000 : ℝ)) (P := (479860863 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_42 n42 (by norm_num) (by norm_num)
      ⟨by linarith, h42⟩
  rcases le_total u (86 / 25 : ℝ) with h43 | h43
  · exact cap_on_step hω (a := (343 / 100 : ℝ)) (b := (86 / 25 : ℝ)) (L := (72928697 / 200000000 : ℝ)) (P := (1925053679 / 1000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_43 n43 (by norm_num) (by norm_num)
      ⟨by linarith, h43⟩
  rcases le_total u (69 / 20 : ℝ) with h44 | h44
  · exact cap_on_step hω (a := (86 / 25 : ℝ)) (b := (69 / 20 : ℝ)) (L := (74312799 / 200000000 : ℝ)) (P := (241333687 / 125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_44 n44 (by norm_num) (by norm_num)
      ⟨by linarith, h44⟩
  rcases le_total u (173 / 50 : ℝ) with h45 | h45
  · exact cap_on_step hω (a := (69 / 20 : ℝ)) (b := (173 / 50 : ℝ)) (L := (47304619 / 125000000 : ℝ)) (P := (96814533 / 50000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_45 n45 (by norm_num) (by norm_num)
      ⟨by linarith, h45⟩
  rcases le_total u (347 / 100 : ℝ) with h46 | h46
  · exact cap_on_step hω (a := (173 / 50 : ℝ)) (b := (347 / 100 : ℝ)) (L := (77052601 / 200000000 : ℝ)) (P := (970958467 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_46 n46 (by norm_num) (by norm_num)
      ⟨by linarith, h46⟩
  rcases le_total u (87 / 25 : ℝ) with h47 | h47
  · exact cap_on_step hω (a := (347 / 100 : ℝ)) (b := (87 / 25 : ℝ)) (L := (392042793 / 1000000000 : ℝ)) (P := (389509617 / 200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_47 n47 (by norm_num) (by norm_num)
      ⟨by linarith, h47⟩
  rcases le_total u (349 / 100 : ℝ) with h48 | h48
  · exact cap_on_step hω (a := (87 / 25 : ℝ)) (b := (349 / 100 : ℝ)) (L := (19938847 / 50000000 : ℝ)) (P := (976591943 / 500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_48 n48 (by norm_num) (by norm_num)
      ⟨by linarith, h48⟩
  rcases le_total u (7 / 2 : ℝ) with h49 | h49
  · exact cap_on_step hω (a := (349 / 100 : ℝ)) (b := (7 / 2 : ℝ)) (L := (202733029 / 500000000 : ℝ)) (P := (489706029 / 250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) log_cert_49 n49 (by norm_num) (by norm_num)
      ⟨by linarith, h49⟩
  exact (Task587.buchstab_le_5618 hω h49).trans (by norm_num)

end LeanLab.ChenDoubleSieve.Task587.CapChain562

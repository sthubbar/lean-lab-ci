import LeanLab.ChenDoubleSieve.Task587R0J9
import LeanLab.ChenDoubleSieve.Task587R0J10
import LeanLab.ChenDoubleSieve.Task587R0J11
import LeanLab.ChenDoubleSieve.Task587R0J12
import LeanLab.ChenDoubleSieve.Task587R0J13

/-!
Smaller compact profile obligations for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Table 1 page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- The sharp reciprocal certificate needs only a uniform lower bound of `7/2` on the
kernel argument; the `φ` threshold of `cell_tail_integral` is one way to obtain it.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
private theorem cell_integral_of_argument {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (N : ℕ) (lo hi : Fin (n + 2) → ℚ) {φ : ℝ}
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j)
    (harg : ∀ x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    buchstabIntegral ω n (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ ≤
      (5618 / 10000 : ℝ) * ∫ x in domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
        cellPoly N ⟨n, by omega⟩ lo hi x := by
  have hl (j : Fin (n + 2)) : (0 : ℝ) < lo j := by exact_mod_cast hlo j
  have hf := kernel_integrable_above_one hω (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ hl
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 7 / 2).trans (harg x hx))
  have hm := setIntegral_mono_on hf
    ((cellPoly_integrable N ⟨n, by omega⟩ lo hi).const_mul (5618 / 10000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hl j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (buchstab_le_5618 hω (harg x hx)) hd.le
      calc
        _ ≤ (5618 / 10000 : ℝ) / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = (5618 / 10000 : ℝ) * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_le_cellPoly N _ lo hi hlo hle hx)
          (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

/-- A corner bound with `P ≤ φ` puts the kernel argument above seven halves on the
whole ordered box. Wu 2004 page 26, derived corner arithmetic. -/
private theorem argument_ge_of_corner_gen {lo hi : Fin 3 → ℚ} {φ P A : ℝ}
    (hA : 0 ≤ A)
    (hlo : ∀ j, 0 < lo j)
    (hφ : P ≤ φ)
    (hcorner : A * (hi 1 : ℝ) + ∑ j, (hi j : ℝ) ≤ P)
    {x : Fin 3 → ℝ} (hx : x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) :
    A ≤ (φ - ∑ j, x j) / x 1 := by
  have hx1 : (0 : ℝ) < x 1 := by
    have h : (0 : ℝ) < (lo 1 : ℝ) := by exact_mod_cast hlo 1
    exact h.trans_le (hx.2 1).1
  exact Task562.argument_ge_of_box (k := (1 : Fin 3)) (a := A) (P := P)
    (lo := fun j => (lo j : ℝ)) (hi := fun j => (hi j : ℝ))
    hA ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩ hx1 hφ hcorner

/-- The same corner bound specialised to the seven-halves threshold. -/
private theorem argument_ge_of_corner {lo hi : Fin 3 → ℚ} {φ P : ℝ}
    (hlo : ∀ j, 0 < lo j) (hφ : P ≤ φ)
    (hcorner : (7 / 2 : ℝ) * (hi 1 : ℝ) + ∑ j, (hi j : ℝ) ≤ P)
    {x : Fin 3 → ℝ} (hx : x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ))) :
    (7 / 2 : ℝ) ≤ (φ - ∑ j, x j) / x 1 :=
  argument_ge_of_corner_gen (A := (7 / 2 : ℝ)) (by norm_num) hlo hφ hcorner hx

/-- `r0j9_short` holds on `8/3 ≤ φ`. Wu 2004 Lemma 5.2 page 26, D2,9. -/
private theorem r0j9_large_phi {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (8 / 3 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤
      ((870161 / 62500000) : ℝ) := by
  have h := cell_integral_of_argument hω (n := 1) 6 r0j9_lo r0j9_hi
    (by intro j; fin_cases j <;> norm_num [r0j9_lo])
    (by intro j; fin_cases j <;> norm_num [r0j9_lo, r0j9_hi])
    (fun x hx => argument_ge_of_corner (lo := r0j9_lo) (hi := r0j9_hi)
      (by intro j; fin_cases j <;> norm_num [r0j9_lo]) hφ
      (by norm_num [r0j9_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)),
      cellPoly 6 (1 : Fin 3) r0j9_lo r0j9_hi x) at h
  rw [r0j9_integral] at h
  exact h.trans (by norm_num)

/-- `r0j10_short` holds on `12/5 ≤ φ`. Wu 2004 Lemma 5.2 page 26, D2,10. -/
private theorem r0j10_large_phi {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (12 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤
      ((9342453 / 1000000000) : ℝ) := by
  have h := cell_integral_of_argument hω (n := 1) 4 r0j10_lo r0j10_hi
    (by intro j; fin_cases j <;> norm_num [r0j10_lo])
    (by intro j; fin_cases j <;> norm_num [r0j10_lo, r0j10_hi])
    (fun x hx => argument_ge_of_corner (lo := r0j10_lo) (hi := r0j10_hi)
      (by intro j; fin_cases j <;> norm_num [r0j10_lo]) hφ
      (by norm_num [r0j10_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)),
      cellPoly 4 (1 : Fin 3) r0j10_lo r0j10_hi x) at h
  rw [r0j10_integral] at h
  exact h.trans (by norm_num)

/-- `r0j11_short` holds on `13/5 ≤ φ`. Wu 2004 Lemma 5.2 page 26, D2,11. -/
private theorem r0j11_large_phi {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (13 / 5 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤
      ((2272569 / 500000000) : ℝ) := by
  have h := cell_integral_of_argument hω (n := 1) 4 r0j11_lo r0j11_hi
    (by intro j; fin_cases j <;> norm_num [r0j11_lo])
    (by intro j; fin_cases j <;> norm_num [r0j11_lo, r0j11_hi])
    (fun x hx => argument_ge_of_corner (lo := r0j11_lo) (hi := r0j11_hi)
      (by intro j; fin_cases j <;> norm_num [r0j11_lo]) hφ
      (by norm_num [r0j11_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)),
      cellPoly 4 (1 : Fin 3) r0j11_lo r0j11_hi x) at h
  rw [r0j11_integral] at h
  exact h.trans (by norm_num)

/-- `r0j12_short` holds on `41/20 ≤ φ`. Wu 2004 Lemma 5.2 page 26, D2,12. -/
private theorem r0j12_large_phi {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (41 / 20 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) φ ≤
      ((7085137 / 1000000000) : ℝ) := by
  have h := cell_integral_of_argument hω (n := 1) 6 r0j12_lo r0j12_hi
    (by intro j; fin_cases j <;> norm_num [r0j12_lo])
    (by intro j; fin_cases j <;> norm_num [r0j12_lo, r0j12_hi])
    (fun x hx => argument_ge_of_corner (lo := r0j12_lo) (hi := r0j12_hi)
      (by intro j; fin_cases j <;> norm_num [r0j12_lo]) hφ
      (by norm_num [r0j12_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)),
      cellPoly 6 (1 : Fin 3) r0j12_lo r0j12_hi x) at h
  rw [r0j12_integral] at h
  exact h.trans (by norm_num)

/-- `r0j13_short` holds on `23/10 ≤ φ`. Wu 2004 Lemma 5.2 page 26, D2,13. -/
private theorem r0j13_large_phi {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : (23 / 10 : ℝ) ≤ φ) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤
      ((24633499 / 1000000000) : ℝ) := by
  have h := cell_integral_of_argument hω (n := 1) 4 r0j13_lo r0j13_hi
    (by intro j; fin_cases j <;> norm_num [r0j13_lo])
    (by intro j; fin_cases j <;> norm_num [r0j13_lo, r0j13_hi])
    (fun x hx => argument_ge_of_corner (lo := r0j13_lo) (hi := r0j13_hi)
      (by intro j; fin_cases j <;> norm_num [r0j13_lo]) hφ
      (by norm_num [r0j13_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤
    (5618 / 10000 : ℝ) * (∫ x in domain (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)),
      cellPoly 4 (1 : Fin 3) r0j13_lo r0j13_hi x) at h
  rw [r0j13_integral] at h
  exact h.trans (by norm_num)


/-! ### Closing the `r0j12` window `2 ≤ φ ≤ 41/20`

The corner of the `r0j12` box only reaches `2811/1000 ≈ …`; its exact value is
`(691/200)·(100/353) + (100/353 + 100/353 + 5/11) = 1.99990 ≤ 2`, so for `φ ≥ 2`
the kernel argument is already at least `691/200 = 3.455` on the whole box.
On `[691/200, 7/2]` a *backward* delay step gives a sharper cap than the global
`5618/10000`: `ω (7/2) ≤ 5609/10000` and `ω ≥ 55/100` on `[2.455, 2.5]` yield
`u ω u ≤ 1.96315 - 0.55 (7/2 - u)`, hence `ω u ≤ 0.55 + 0.03815/u ≤ 0.5611`. -/

/-- A backward delay step turns an endpoint bound and a delayed lower bound into an
affine bound.  Wu 2004 Lemma 2.10 page 9, derived integration tool. -/
private theorem delay_affine_lower {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a u Top B C : ℝ}
    (ha : 2 ≤ a) (hau : a ≤ u) (hut : u ≤ Top) (hTop : Top * ω Top ≤ B)
    (hdelay : ∀ t ∈ Set.Icc u Top, C ≤ ω (t - 1)) :
    u * ω u ≤ B - (Top - u) * C := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Set.Icc u Top) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1, ha]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc u Top) := by
    rw [uIcc_of_le hut]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1, ha]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hut hc
    (fun t ht => hω.2.2 t (by linarith [ht.1, ha])) hci.intervalIntegrable
  have hi : (Top - u) * C ≤ (∫ t in u..Top, ω (t - 1)) := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) hut intervalIntegrable_const
      hci.intervalIntegrable hdelay
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  linarith

/-- The delayed values used on `[691/200, 7/2]` are at least `549/1000`.
Wu 2004 Lemma 2.10 page 9, derived local enclosure. -/
private theorem buchstab_delayed_lower {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {t : ℝ} (ht : t ∈ Set.Icc (691 / 200 : ℝ) (7 / 2)) : (549 / 1000 : ℝ) ≤ ω (t - 1) := by
  have h1 : (2 : ℝ) ≤ t - 1 := by linarith [ht.1]
  have h2 : t - 1 ≤ (3 : ℝ) := by linarith [ht.2]
  have hlog : (3749 / 10000 : ℝ) ≤ log (291 / 200 : ℝ) := by
    refine le_trans ?_ (Wu04Integral.log_bounds 12 (y := (291 / 200)) (by norm_num)).1
    norm_num [Wu04Integral.logLower, Wu04Integral.logUpper, sum_range_succ]
  have hy : (291 / 200 : ℝ) ≤ t - 1 - 1 := by linarith [ht.1]
  have hmono : log (291 / 200 : ℝ) ≤ log (t - 1 - 1) := Real.log_le_log (by norm_num) hy
  rw [Wu04Buchstab.formula_two_three hω ⟨h1, h2⟩]
  have hpos : (0 : ℝ) < t - 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hb : (549 / 1000 : ℝ) * (t - 1) ≤ 549 / 1000 * (5 / 2 : ℝ) := by
    have h5 : t - 1 ≤ (5 / 2 : ℝ) := by linarith [ht.2]
    nlinarith
  linarith

/-- `ω u ≤ 562/1000` from `u = 691/200` on.
Wu 2004 Lemma 2.10 page 9, derived sharp tail for the `r0j12` box. -/
private theorem buchstab_le_562 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ}
    (hu : (691 / 200 : ℝ) ≤ u) : ω u ≤ (562 / 1000 : ℝ) := by
  by_cases hle : u ≤ (7 / 2 : ℝ)
  · have hTop : (7 / 2 : ℝ) * ω (7 / 2) ≤ 39263 / 20000 := by
      have h := buchstab_seven_halves_le hω
      nlinarith
    have hmain := delay_affine_lower hω (a := (691 / 200 : ℝ)) (u := u) (Top := (7 / 2 : ℝ))
      (B := 39263 / 20000) (C := 549 / 1000) (by norm_num) hu hle hTop
      (fun t ht => buchstab_delayed_lower hω ⟨by linarith [ht.1], ht.2⟩)
    have hu0 : (0 : ℝ) < u := by linarith
    have hstep : ω u ≤ (39263 / 20000 - ((7 / 2 : ℝ) - u) * (549 / 1000)) / u := by
      rw [le_div_iff₀ hu0]
      linarith [hmain]
    refine hstep.trans ?_
    rw [div_le_iff₀ hu0]
    nlinarith [hu]
  · exact (buchstab_le_5618 hω (le_of_not_ge hle)).trans (by norm_num)

/-- The reciprocal certificate with the sharper `562/1000` cap.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
private theorem cell_integral_562 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (N : ℕ) (lo hi : Fin (n + 2) → ℚ) {φ : ℝ}
    (hlo : ∀ j, 0 < lo j) (hle : ∀ j, lo j ≤ hi j)
    (harg : ∀ x ∈ domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
      (691 / 200 : ℝ) ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    buchstabIntegral ω n (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ ≤
      (562 / 1000 : ℝ) * ∫ x in domain (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)),
        cellPoly N ⟨n, by omega⟩ lo hi x := by
  have hl (j : Fin (n + 2)) : (0 : ℝ) < lo j := by exact_mod_cast hlo j
  have hf := kernel_integrable_above_one hω (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) φ hl
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 691 / 200).trans (harg x hx))
  have hm := setIntegral_mono_on hf
    ((cellPoly_integrable N ⟨n, by omega⟩ lo hi).const_mul (562 / 1000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hl j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ := mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (buchstab_le_562 hω (harg x hx)) hd.le
      calc
        _ ≤ (562 / 1000 : ℝ) / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = (562 / 1000 : ℝ) * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_le_cellPoly N _ lo hi hlo hle hx)
          (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm


/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_9 leaf. -/
theorem r0j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  sorry

/-- The exact original I2_r0_9 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j9_short. -/
theorem I2_r0_9_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 0 ≤ ((870161 / 62500000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) ≤ ((870161 / 62500000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j9_short hω hz hφ ht
      · exact r0j9_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j9_lo, r0j9_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_10 leaf. -/
theorem r0j10_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_10 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j10_short. -/
theorem I2_r0_10_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 1 ≤ ((9342453 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) ≤ ((9342453 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j10_short hω hz hφ ht
      · exact r0j10_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j10_lo, r0j10_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_11 leaf. -/
theorem r0j11_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_11 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j11_short. -/
theorem I2_r0_11_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 2 ≤ ((2272569 / 500000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) ≤ ((2272569 / 500000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j11_short hω hz hφ ht
      · exact r0j11_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j11_lo, r0j11_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,12, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_12 leaf. -/
theorem r0j12_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) φ ≤ ((7085137 / 1000000000) : ℝ) := by
  have h := cell_integral_562 hω (n := 1) 6 r0j12_lo r0j12_hi
    (by intro j; fin_cases j <;> norm_num [r0j12_lo])
    (by intro j; fin_cases j <;> norm_num [r0j12_lo, r0j12_hi])
    (fun x hx => argument_ge_of_corner_gen (lo := r0j12_lo) (hi := r0j12_hi) (A := (691 / 200 : ℝ))
      (P := (2 : ℝ)) (by norm_num) (by intro j; fin_cases j <;> norm_num [r0j12_lo]) hφ
      (by norm_num [r0j12_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) φ ≤
    (562 / 1000 : ℝ) * (∫ x in domain (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)),
      cellPoly 6 (1 : Fin 3) r0j12_lo r0j12_hi x) at h
  rw [r0j12_integral] at h
  exact h.trans (by norm_num)

/-- The exact original I2_r0_12 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j12_short. -/
theorem I2_r0_12_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 3 ≤ ((7085137 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) ≤ ((7085137 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j12_lo j : ℝ)) (fun j => (r0j12_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j12_short hω hz hφ ht
      · exact r0j12_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j12_lo, r0j12_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30.
Certify the Buchstab integral only for phi between two and seven halves.
The complementary unbounded phi range follows from the reciprocal polynomial
and its exact rational moments. This piece has no supremum and is strictly
smaller than the original I2_r0_13 leaf. -/
theorem r0j13_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- The exact original I2_r0_13 statement follows from its smaller profile certificate.
Wu 2004 page 26, Table 1 row 1 page 30. CONDITIONAL ON r0j13_short. -/
theorem I2_r0_13_from_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 4 ≤ ((24633499 / 1000000000) : ℝ) := by
  have hb : buchstabSup ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) ≤ ((24633499 / 1000000000) : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) 2, 2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (7 / 2 : ℝ)
      · exact r0j13_short hω hz hφ ht
      · exact r0j13_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams, r0j13_lo, r0j13_hi] <;> congr 1 <;> ext j <;> fin_cases j <;> norm_num

end LeanLab.ChenDoubleSieve.Task587

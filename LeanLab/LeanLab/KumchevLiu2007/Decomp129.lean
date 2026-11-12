/-
Theorem 1 of Kumchev and Liu, arXiv 0801.0130, page 2.
Decomposition of the end of Section 4, page 16, eq. 55 and Proposition 2.
The analytic leaves remain CITED. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c
import LeanLab.KumchevLiu2007.Decomp129a
import LeanLab.KumchevLiu2007.Circle129f

namespace LeanLab.KumchevLiu2007.Task129

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The parameter Y of page 2 before eq. 4. -/
noncomputable def windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)

/-- Integer solutions in the half open windows of page 2 eqs. 4 to 6.
For large X in the nonempty H range of Theorem 1, Y is less than X. -/
noncomputable def windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
    (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
      Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)

/-- The representation count R2 of page 2 eq. 4. -/
noncomputable def primeCount (X Y : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ v.2.Prime)).card

/-- The logarithmically weighted integer count r2 of page 2 eq. 6. -/
noncomputable def integerMain (X Y : ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))

/-- The truncated singular series of page 2 eq. 7, using the existing A2. -/
noncomputable def series2 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q

/-- The main term r2 times the truncated singular series in page 2 eq. 9. -/
noncomputable def main2 (X Y P : ℝ) (n : ℕ) : ℂ := integerMain X Y n * series2 n P

/-- The sifted count R of page 8 eqs. 12 and 34. -/
noncomputable def roughCount (X Y P : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
    ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card

/-- The residual R0 in page 8 eq. 35, defined as the difference of counts.
This definition does not assert its prime factorization description. -/
noncomputable def residualCount (X Y P : ℝ) (n : ℕ) : ℝ :=
  (roughCount X Y P n : ℝ) - (primeCount X Y n : ℝ)

/-- CITED. Theorem 1, page 2 eq. 9. The exponent B depends only on A.
C bounds the exceptional set and K bounds the relative error. -/
def kumchev_liu_thm1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- Page 2 displays 4 to 6. No window pair can reach n at least X + Y. -/
theorem windowPairs_empty_above (X Y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : X + Y ≤ (n : ℝ)) : windowPairs X Y n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨_, hlo, hhi, hqlo, hqhi, heq⟩ := Finset.mem_filter.mp hv
  have hq2 : (v.2 : ℝ) ^ 2 ≤ Y := by
    have hsq := (sq_le_sq₀ (Nat.cast_nonneg v.2) (Real.sqrt_nonneg Y)).mpr hqhi.le
    nlinarith only [hsq, Real.sq_sqrt hY]
  have hcast : (v.1 : ℝ) + (v.2 : ℝ)^2 = (n : ℝ) := by exact_mod_cast heq
  linarith

/-- Page 2 displays 4 to 6 and page 8 display 35. The counts and main term
vanish beyond the support of the fixed representation windows. -/
theorem counts_vanish_above (X Y P : ℝ) (hY : 0 ≤ Y) (n : ℕ) (hn : X + Y ≤ (n : ℝ)) :
    primeCount X Y n = 0 ∧ roughCount X Y P n = 0 ∧
      main2 X Y P n = 0 ∧ residualCount X Y P n = 0 := by
  simp [primeCount, roughCount, main2, integerMain, residualCount,
    windowPairs_empty_above X Y hY n hn]

/-! ### Split of `circle_input`, route burst 2026-11-12.
Pieces of page 16, Section 4, displays 53 to 55, together with the inputs
eq. 48 and Lemma 3.8 eq. 49 on page 13. AI wrote the Lean code. Goldbach is open. -/

/-- The weight f2 of page 15, Section 4, before display 52:
f2 of u is 1 over log u plus the integral from z0 to the square root of u of
dt over t log t log of u over t. -/
noncomputable def f2Weight (z0 u : ℝ) : ℝ :=
  1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))

/-- The singular integral I of n, varpi, lambda0, page 6 display 27, with
f1 of u equal to 1 over log u, page 15, and f2 as above with z0 from display 34. -/
noncomputable def singInt (X Y P : ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ windowPairs X Y n,
    (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)

/-- The error in display 53 of page 16: R of n, varpi, lambda0 minus S2 of n, P times I. -/
noncomputable def err53 (X ε B : ℝ) (n : ℕ) : ℝ :=
  ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
    series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖

/-! ### Split of `eq53_prop1`, route burst session 9, 2026-11-12.
Display 53 of page 16 is the Chebyshev consequence of the mean square bound
display 33 of Proposition 1, page 7. The Chebyshev step is proved here; the
mean square bound is the remaining CITED leaf `prop1_meansq`.
AI wrote the Lean code. Goldbach is open. -/

/-- The integers n with X less than n at most X plus H, the summation range of
display 33 on page 7 and of display 49 on page 14. -/
noncomputable def iocNat (X H : ℝ) : Finset ℕ :=
  (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))

/-- Bookkeeping: `cntIoc` counts a filter of `iocNat`. -/
theorem cntIoc_eq_card (S : ℕ → Prop) (X H : ℝ) :
    cntIoc S X H = ((iocNat X H).filter S).card := by
  unfold cntIoc iocNat
  rw [Finset.filter_filter]

/-- Chebyshev's inequality in the form used after display 33 on page 7 and
after display 49 on page 14: the number of n in X, X plus H with property S,
times T squared, is at most the sum of f squared, whenever S forces f to have
size at least T. -/
theorem cnt_le_meansq (S : ℕ → Prop) (f : ℕ → ℝ) (X H T : ℝ) (hT : 0 < T)
    (hS : ∀ n, S n → T ≤ |f n|) :
    (cntIoc S X H : ℝ) * T ^ 2 ≤ ∑ n ∈ iocNat X H, f n ^ 2 := by
  rw [cntIoc_eq_card]
  refine le_trans ?_ (U1534.chebyshev_count (iocNat X H) f hT)
  have hsub : (iocNat X H).filter S ⊆ (iocNat X H).filter (fun n => T ≤ |f n|) :=
    Finset.monotone_filter_right _ (fun n _ hn => hS n hn)
  have hcard : (((iocNat X H).filter S).card : ℝ) ≤
      (((iocNat X H).filter (fun n => T ≤ |f n|)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact mul_le_mul_of_nonneg_right hcard (sq_nonneg T)

/-- Bookkeeping for display 53: a mean square bound with saving L to the minus
3 A gives at most C H L to the minus A integers where the error exceeds
Y to the 1/2 times L to the minus A. -/
theorem count_of_meansq {X ε B A C H : ℝ} (hX : 3 ≤ X)
    (hsum : ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
      C * H * windowY X ε * Real.log X ^ (-(3 * A))) :
    (cntIoc (fun n => InH2 n ∧
      Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
      C * H / Real.log X ^ A := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos hXpos _
  set a := Real.log X ^ A with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hL _
  have hnegA : Real.log X ^ (-A) = a⁻¹ := Real.rpow_neg hL.le A
  have h3 : Real.log X ^ (-(3 * A)) = (a ^ 3)⁻¹ := by
    rw [Real.rpow_neg hL.le, show 3 * A = A * ((3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul_natCast hL.le]
  set T := Real.sqrt (windowY X ε) * Real.log X ^ (-A) with hT_def
  have hT : 0 < T := mul_pos (Real.sqrt_pos.mpr hY) (Real.rpow_pos_of_pos hL _)
  have hT2 : T ^ 2 = windowY X ε * (a⁻¹) ^ 2 := by
    rw [hT_def, mul_pow, Real.sq_sqrt hY.le, hnegA]
  have hc := cnt_le_meansq (fun n => InH2 n ∧ T < err53 X ε B n) (err53 X ε B) X H T hT
    (fun n hn => hn.2.le.trans (le_abs_self _))
  rw [h3] at hsum
  set N := (cntIoc (fun n => InH2 n ∧ T < err53 X ε B n) X H : ℝ)
  have hmain : N * (windowY X ε * (a⁻¹) ^ 2) ≤ C * H * windowY X ε * (a ^ 3)⁻¹ := by
    rw [← hT2]; exact hc.trans hsum
  have hfac : 0 ≤ a ^ 3 / windowY X ε := by positivity
  have hm := mul_le_mul_of_nonneg_right hmain hfac
  have e1 : N * (windowY X ε * (a⁻¹) ^ 2) * (a ^ 3 / windowY X ε) = N * a := by
    field_simp
  have e2 : C * H * windowY X ε * (a ^ 3)⁻¹ * (a ^ 3 / windowY X ε) = C * H := by
    field_simp
  rw [e1, e2] at hm
  rw [le_div_iff₀ ha]
  exact hm

/-! ### Split of `prop1_meansq`, route burst session 8 p3, 2026-11-12.
Proposition 1 display 33 on page 7 for R of n, varpi, lambda0 follows from the
orthogonality identity display 13 and the arcs of display 15, both proved in
`Circle129d`, together with the major arc asymptotic display 28 and the minor arc
mean square display 32, the two LEAF statements of `Circle129d`.
AI wrote the Lean code. Goldbach is open. -/

/-- Route burst session 8 p3, PROVED. Page 4 display 12 and page 8 display 34:
the sifted count R of n, varpi, lambda0 of `roughCount` is the representation
function R of n, lambda1, lambda2 of `Task129d` with lambda1 equal to varpi and
lambda2 equal to lambda0. -/
theorem roughCount_eq_repR (X Y P : ℝ) (n : ℕ) :
    (roughCount X Y P n : ℝ) = Task129d.repR Task129d.lam1 (Task129d.lam2 Y P) X Y n := by
  unfold roughCount windowPairs Task129d.repR Task129d.win1 Task129d.win2
  rw [Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
  rw [show (Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1)) =
    (Finset.range (⌊X⌋₊ + 1)) ×ˢ (Finset.range (⌊Real.sqrt Y⌋₊ + 1)) from rfl,
    Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [Finset.sum_filter]
  split_ifs with h1
  · refine Finset.sum_congr rfl (fun m2 _ => ?_)
    simp only [Task129d.lam1, Task129d.lam2, ite_zero_mul_ite_zero, mul_one]
    split_ifs <;> first | (push_cast; rfl) | (exfalso; tauto)
  · refine (Finset.sum_eq_zero (fun m2 _ => ?_))
    split_ifs <;> first | (push_cast; rfl) | (exfalso; tauto)

/-- Route burst session 8 p3, PROVED. Page 6 after display 27: `singInt` is the
double sum form of I of n, lambda1, lambda2 used in `Task129d`. -/
theorem singInt_eq_singIntW (X Y P : ℝ) (n : ℕ) :
    singInt X Y P n = Task129d.singIntW X Y P n := by
  unfold singInt windowPairs Task129d.singIntW Task129d.win1 Task129d.win2
  rw [Finset.sum_filter,
    show (Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1)) =
    (Finset.range (⌊X⌋₊ + 1)) ×ˢ (Finset.range (⌊Real.sqrt Y⌋₊ + 1)) from rfl,
    Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [Finset.sum_filter]
  split_ifs with h1
  · refine Finset.sum_congr rfl (fun m2 _ => ?_)
    split_ifs <;> first | rfl | (exfalso; tauto)
  · refine (Finset.sum_eq_zero (fun m2 _ => ?_))
    split_ifs <;> first | rfl | (exfalso; tauto)

/-- Route burst session 8 p3, PROVED. Bookkeeping: the range X less than n at most
X plus H of display 33 has at most H plus 1 integers. -/
theorem card_iocNat_le {X H : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) :
    ((iocNat X H).card : ℝ) ≤ H + 1 := by
  have hsub : iocNat X H ⊆ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
    intro n hn
    simp only [iocNat, Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hX).mpr hn.2, Nat.lt_succ_iff.mp hn.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at h1
  have hmono : ⌊X⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_le_floor (by linarith)
  have h2 : ((⌊X + H⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) = (⌊X + H⌋₊ : ℝ) - (⌊X⌋₊ : ℝ) := by
    rw [Nat.cast_sub hmono]
  have h3 : (⌊X + H⌋₊ : ℝ) ≤ X + H := Nat.floor_le (by linarith)
  have h4 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have h5 : ((iocNat X H).card : ℝ) ≤ ((⌊X + H⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- Route burst session 8 p3, PROVED. Bookkeeping for display 33: the range
X less than n at most X plus H is covered by the ceiling of H over H' intervals
X plus j H' less than n at most X plus j H' plus H', so a sum of nonnegative terms
over it is at most the sum of the sums over these intervals. -/
theorem sum_iocNat_cover {X H H' : ℝ} (hH' : 0 < H') (hX : 0 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ iocNat X H, f n ≤
      ∑ j ∈ Finset.range ⌈H / H'⌉₊, ∑ n ∈ iocNat (X + j * H') H', f n := by
  have hcov : ∀ n ∈ iocNat X H, ∃ j ∈ Finset.range ⌈H / H'⌉₊,
      n ∈ iocNat (X + j * H') H' := by
    intro n hn
    simp only [iocNat, Finset.mem_filter, Finset.mem_range] at hn
    have hnX : X < (n : ℝ) := hn.2
    have hnfl : (n : ℝ) ≤ (⌊X + H⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn.1
    have hXH : 0 ≤ X + H := by
      by_contra hneg
      push_neg at hneg
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hnfl
      push_cast at hnfl
      linarith
    have hnH : (n : ℝ) ≤ X + H := hnfl.trans (Nat.floor_le hXH)
    set t := ((n : ℝ) - X) / H' with ht_def
    have ht : 0 < t := div_pos (by linarith) hH'
    set c := ⌈t⌉₊ with hc_def
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ht).ne'
    refine ⟨c - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have : c ≤ ⌈H / H'⌉₊ :=
        Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith) hH'.le)
      omega
    · simp only [iocNat, Finset.mem_filter, Finset.mem_range]
      have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1]; simp
      have hlt : (c : ℝ) - 1 < t := by have := Nat.ceil_lt_add_one ht.le; linarith
      have hle : t ≤ (c : ℝ) := Nat.le_ceil t
      rw [hcast]
      have e1 : ((c : ℝ) - 1) * H' < (n : ℝ) - X := by
        rw [ht_def, lt_div_iff₀ hH'] at hlt; linarith
      have e2 : (n : ℝ) - X ≤ (c : ℝ) * H' := by
        rw [ht_def, div_le_iff₀ hH'] at hle; linarith
      constructor
      · apply Nat.lt_succ_of_le
        apply Nat.le_floor
        linarith
      · linarith
  calc ∑ n ∈ iocNat X H, f n
      ≤ ∑ n ∈ iocNat X H, ∑ j ∈ Finset.range ⌈H / H'⌉₊,
          (if n ∈ iocNat (X + j * H') H' then f n else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨j, hj, hnj⟩ := hcov n hn
        have := Finset.single_le_sum (s := Finset.range ⌈H / H'⌉₊)
          (f := fun i : ℕ => if n ∈ iocNat (X + (i : ℝ) * H') H' then f n else 0)
          (fun i _ => by split_ifs; exact hf n; exact le_rfl) hj
        simp only [hnj, if_true] at this
        exact this
    _ = ∑ j ∈ Finset.range ⌈H / H'⌉₊, ∑ n ∈ iocNat X H,
          (if n ∈ iocNat (X + j * H') H' then f n else 0) := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range ⌈H / H'⌉₊, ∑ n ∈ iocNat (X + j * H') H', f n := by
        apply Finset.sum_le_sum
        intro j _
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (Finset.mem_filter.mp hn).2)
          (fun n _ _ => hf n)

/-- Route burst session 8 p3, PROVED. Real analysis for display 14: for B and s
positive, P squared with P equal to L to the B is at most one half of X to the s
for X large. -/
theorem P_sq_le_rpow (B s : ℝ) (hs : 0 < s) :
    ∃ X3 : ℝ, 1 ≤ X3 ∧ ∀ X : ℝ, X3 ≤ X → (Real.log X ^ B) ^ 2 ≤ 1 / 2 * X ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 * B) hs).bound (c := 1 / 2) (by norm_num)
  obtain ⟨X3, hX3⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X3 1, le_max_right _ _, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hb := hX3 X ((le_max_left _ _).trans hX)
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  convert hb using 2
  push_cast; ring

/-- Route burst session 8 p3, PROVED. Display 33 from the arc bounds: if the major
arc bound display 28 holds for every n and the minor arc bound display 32 holds on
every interval of length H' with Q equal to H' over P, then the mean square of
display 33 over X less than n at most X plus H, for any H at least H', is at most
a constant times H Y L to the minus A. -/
theorem meansq_from_arcs {A B ε X H H' C1 C2 : ℝ} (hX3 : 3 ≤ X) (hB : 2 * A ≤ B)
    (hH'1 : 1 ≤ H') (hH'H : H' ≤ H) (hC2 : 0 ≤ C2)
    (hmaj : ∀ n : ℕ, ‖Task129d.majorInt X (windowY X ε) (Real.log X ^ B)
        (H' / Real.log X ^ B) n - Task129d.series2W n (Real.log X ^ B) *
          (Task129d.singIntW X (windowY X ε) (Real.log X ^ B) n : ℂ)‖ ≤
        C1 * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-(1 / 4 : ℝ)))
    (hmin : ∀ N0 : ℝ, 0 ≤ N0 → ∑ n ∈ iocNat N0 H',
        ‖Task129d.minorInt X (windowY X ε) (Real.log X ^ B) (H' / Real.log X ^ B) n‖ ^ 2 ≤
        C2 * H' * windowY X ε * Real.log X ^ (-A)) :
    ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
      (2 * (4 * C1 ^ 2 + 2 * C2)) * H * windowY X ε * Real.log X ^ (-A) := by
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans hX3)
  have hL0 : 0 < Real.log X := by linarith
  set Y := windowY X ε with hY_def
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hXpos _
  set P := Real.log X ^ B with hP_def
  have hPpos : 0 < P := Real.rpow_pos_of_pos hL0 _
  set Q := H' / P with hQ_def
  set M := C1 * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) with hM_def
  have hpt : ∀ n : ℕ, err53 X ε B n ^ 2 ≤ 2 * M ^ 2 +
      2 * ‖Task129d.minorInt X Y P Q n‖ ^ 2 := by
    intro n
    have hm := hmaj n
    have hrep := Task129d.rep_eq_major_add_minor X Y P Q n
    have herr : err53 X ε B n = ‖(Task129d.majorInt X Y P Q n -
        Task129d.series2W n P * (Task129d.singIntW X Y P n : ℂ)) +
        Task129d.minorInt X Y P Q n‖ := by
      unfold err53
      rw [← hY_def, ← hP_def, show ((roughCount X Y P n : ℕ) : ℂ) =
        (((roughCount X Y P n : ℕ) : ℝ) : ℂ) by push_cast; rfl, roughCount_eq_repR, hrep,
        singInt_eq_singIntW]
      congr 1
      simp only [series2, Task129d.series2W]
      ring
    rw [herr]
    set a := ‖Task129d.majorInt X Y P Q n -
        Task129d.series2W n P * (Task129d.singIntW X Y P n : ℂ)‖ with ha_def
    set b := ‖Task129d.minorInt X Y P Q n‖ with hb_def
    have ht : ‖Task129d.majorInt X Y P Q n -
        Task129d.series2W n P * (Task129d.singIntW X Y P n : ℂ) +
        Task129d.minorInt X Y P Q n‖ ≤ a + b := norm_add_le _ _
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have h1 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have h2 : a ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ ha0 hm 2
    nlinarith [sq_nonneg (a - b)]
  have hPq : P ^ (-(1 / 2 : ℝ)) ≤ Real.log X ^ (-A) := by
    rw [hP_def, ← Real.rpow_mul hL0.le]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    linarith
  have hM2 : M ^ 2 = C1 ^ 2 * Y * P ^ (-(1 / 2 : ℝ)) := by
    rw [hM_def, mul_pow, mul_pow, Real.sq_sqrt hYpos.le]
    rw [show (P ^ (-(1 / 4 : ℝ))) ^ 2 = P ^ (-(1 / 2 : ℝ)) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]; norm_num]
  have hM2le : M ^ 2 ≤ C1 ^ 2 * Y * Real.log X ^ (-A) := by
    rw [hM2]; exact mul_le_mul_of_nonneg_left hPq (by positivity)
  have hLA : 0 ≤ Real.log X ^ (-A) := (Real.rpow_pos_of_pos hL0 _).le
  set K := (4 * C1 ^ 2 + 2 * C2) * Y * Real.log X ^ (-A) with hK_def
  have hK : 0 ≤ K := by positivity
  have hpiece : ∀ N0 : ℝ, 0 ≤ N0 → ∑ n ∈ iocNat N0 H', err53 X ε B n ^ 2 ≤ K * H' := by
    intro N0 hN0
    have hcard := card_iocNat_le (H := H') hN0 (by linarith)
    have hminsum := hmin N0 hN0
    calc ∑ n ∈ iocNat N0 H', err53 X ε B n ^ 2
        ≤ ∑ n ∈ iocNat N0 H', (2 * M ^ 2 + 2 * ‖Task129d.minorInt X Y P Q n‖ ^ 2) :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = (iocNat N0 H').card * (2 * M ^ 2) +
          2 * ∑ n ∈ iocNat N0 H', ‖Task129d.minorInt X Y P Q n‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      _ ≤ (2 * H') * (2 * (C1 ^ 2 * Y * Real.log X ^ (-A))) +
          2 * (C2 * H' * Y * Real.log X ^ (-A)) := by
          have hc2 : ((iocNat N0 H').card : ℝ) ≤ 2 * H' := by linarith
          have hm2 : 2 * M ^ 2 ≤ 2 * (C1 ^ 2 * Y * Real.log X ^ (-A)) := by linarith
          have := mul_le_mul hc2 hm2 (by positivity) (by linarith)
          linarith
      _ = K * H' := by rw [hK_def]; ring
  have hH'pos : 0 < H' := by linarith
  have hcov := sum_iocNat_cover (H := H) hH'pos hXpos.le (fun n => err53 X ε B n ^ 2)
    (fun n => sq_nonneg _)
  have hk : (⌈H / H'⌉₊ : ℝ) < H / H' + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hH'pos.le)
  calc ∑ n ∈ iocNat X H, err53 X ε B n ^ 2
      ≤ ∑ j ∈ Finset.range ⌈H / H'⌉₊, ∑ n ∈ iocNat (X + j * H') H', err53 X ε B n ^ 2 := hcov
    _ ≤ ∑ j ∈ Finset.range ⌈H / H'⌉₊, K * H' :=
        Finset.sum_le_sum (fun j _ => hpiece _
          (add_nonneg hXpos.le (mul_nonneg (Nat.cast_nonneg j) hH'pos.le)))
    _ = (⌈H / H'⌉₊ : ℝ) * (K * H') := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (H / H' + 1) * (K * H') := by gcongr
    _ = K * (H + H') := by field_simp
    _ ≤ K * (2 * H) := by gcongr; linarith
    _ = (2 * (4 * C1 ^ 2 + 2 * C2)) * H * Y * Real.log X ^ (-A) := by rw [hK_def]; ring

/-- SPLIT, route burst session 9; PROVED from the leaves
`Task129d.major_arc_display28` and, through display 29 in `Circle129f`,
`Task129f.minor_dist_display30` in session 8 p3. Proposition 1 display 33 on page 7,
applied on pages 15 and 16 to R of n, varpi, lambda0 with varpi the prime
indicator and lambda0 of display 34: the sum over X less than n at most X plus H
of the square of R of n, varpi, lambda0 minus S2 of n, P times I of n, varpi,
lambda0 is at most a constant times H Y L to the minus A. The range is the
written one, X to the 7/18 plus epsilon up to X to the 1 minus epsilon, page 16
after display 55. CITED: needs hypotheses A1.2, A2.2 and A2.3 verified on page
15, which rest on the short interval Siegel Walfisz theorem and Lemma 3.4. -/
theorem prop1_meansq (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
          C * H * windowY X ε * Real.log X ^ (-A) := by
  obtain ⟨B1, hB1, hmin⟩ := Task129f.minor_arc_display32 A hA
  refine ⟨max B1 (2 * A), lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := lt_of_lt_of_le hB1 ((le_max_left _ _).trans hB)
  have hB2 : 2 * A ≤ B := (le_max_right _ _).trans hB
  obtain ⟨C1, X1, hC1, hX1, hmaj⟩ := Task129d.major_arc_display28 B hBpos ε hε
  obtain ⟨C2, X2, hC2, hX2, hmin'⟩ := hmin B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨X3, hX3, hP2⟩ := P_sq_le_rpow B (1 / 24) (by norm_num)
  refine ⟨2 * (4 * C1 ^ 2 + 2 * C2), max (max X1 X2) (max X3 3), by positivity,
    le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro X H hX hH1 hH2
  have hX1' : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3' : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX3'' : 3 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have hXgt1 : 1 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos hXgt1
  -- the range forces epsilon at most 11/36
  have hε2 : ε ≤ 11 / 36 := by
    have := (Real.rpow_le_rpow_left_iff hXgt1).mp (hH1.trans hH2)
    linarith
  set P2 := (Real.log X ^ B) ^ 2 with hP2_def
  have hP2pos : 0 < P2 := by positivity
  have hP2le : P2 ≤ X ^ (1 / 24 : ℝ) := by
    have := hP2 X hX3'
    have : 0 ≤ X ^ (1 / 24 : ℝ) := Real.rpow_nonneg hXpos.le _
    linarith
  -- Y P to the minus 2 is at least X to the 7/18 plus epsilon
  have hYP : X ^ (7 / 18 + ε) ≤ windowY X ε / P2 := by
    rw [le_div_iff₀ hP2pos]
    calc X ^ (7 / 18 + ε) * P2 ≤ X ^ (7 / 18 + ε) * X ^ (1 / 24 : ℝ) :=
          mul_le_mul_of_nonneg_left hP2le (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (7 / 18 + ε + 1 / 24) := (Real.rpow_add hXpos _ _).symm
      _ ≤ windowY X ε := by
          unfold windowY
          exact Real.rpow_le_rpow_of_exponent_le hXgt1.le (by linarith)
  set H' := min H (windowY X ε / P2) with hH'_def
  have hH'1 : X ^ (7 / 18 + ε) ≤ H' := le_min hH1 hYP
  have hH'2 : H' ≤ X ^ (1 - ε) := (min_le_left _ _).trans hH2
  have hH'3 : H' ≤ windowY X ε / P2 := min_le_right _ _
  have hH'one : 1 ≤ H' := le_trans (Real.one_le_rpow hXgt1.le (by linarith)) hH'1
  exact meansq_from_arcs hX3'' hB2 hH'one (min_le_left _ _) hC2.le
    (fun n => hmaj X H' hX1' hH'1 hH'2 hH'3 n)
    (fun N0 hN0 => hmin' X H' hX2' hH'1 hH'2 hH'3 N0 hN0)

/-- SPLIT LEAF. Page 16 display 53, from Proposition 1 display 33 on page 7 by
Chebyshev's inequality, with the hypotheses verified on page 15. The written
range is X to the 7 over 18 plus epsilon up to X to the 1 minus epsilon, page 16
after display 55. CITED: needs the short interval Siegel Walfisz input and Lemma 3.4. -/
theorem eq53_prop1 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := prop1_meansq (3 * A) (by linarith)
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, h⟩ := h B hB ε hε
  refine ⟨C, max X0 3, hC, le_trans hX0 (le_max_left _ _), ?_⟩
  intro X H hX hH1 hH2
  exact count_of_meansq (le_trans (le_max_right _ _) hX)
    (h X H (le_trans (le_max_left _ _) hX) hH1 hH2)

/-- SPLIT LEAF, UNWRITTEN RESIDUE. Display 53 of page 16 when epsilon exceeds
5 over 18 and H exceeds X to the 1 minus epsilon. For epsilon at most 5 over 18
this range reduces to the written one by the support of the windows, proved
below in `eq53_full_range`. The paper treats epsilon as a small fixed number and
does not write this case; it is recorded as BLOCKED NO WRITTEN PROOF in PROGRESS.md.
SUPERSEDED, route burst session 9: this statement omits the lower bound X to the
7/18 plus epsilon on H, so for epsilon above 11/36 it reaches below the range of
Theorem 1. It is no longer used by `eq53_full_range`, which now uses
`eq53_large_eps_range`; it stays here unchanged and off the path of `circle_input`. -/
theorem eq53_large_eps (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → X ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

/-- Helper for display 54, page 16, proved 2026-11-12 PROVE PASS: the integral
term of f2 on page 15 is nonnegative and at most log of sqrt u over z0 divided by
log z0 times log sqrt u, since log t is at least log z0 and log of u over t is at
least log sqrt u on the range of integration. AI wrote the Lean code. -/
theorem f2_integral_bound {a u : ℝ} (ha : 1 < a) (hab : a ≤ Real.sqrt u) :
    0 ≤ ∫ t in a..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) ∧
    ∫ t in a..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) ≤
      (1 / (Real.log a * Real.log (Real.sqrt u))) * Real.log (Real.sqrt u / a) := by
  have hb1 : 1 < Real.sqrt u := lt_of_lt_of_le ha hab
  have hu0 : 0 < u := by
    by_contra h; push Not at h; rw [Real.sqrt_eq_zero'.mpr h] at hb1; linarith
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log (Real.sqrt u) := Real.log_pos hb1
  have key : ∀ t ∈ Set.Icc a (Real.sqrt u), 0 < t ∧ Real.log a ≤ Real.log t ∧
      Real.log (Real.sqrt u) ≤ Real.log (u / t) := by
    intro t ⟨h1, h2⟩
    have ht : 0 < t := by linarith
    refine ⟨ht, Real.log_le_log (by linarith) h1, Real.log_le_log (by linarith) ?_⟩
    rw [le_div_iff₀ ht]; nlinarith
  have hcont : ContinuousOn (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      (Set.uIcc a (Real.sqrt u)) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul (ContinuousOn.mul continuousOn_id ?_) ?_
      · exact Real.continuousOn_log.mono (fun t ht => by
          have := (key t ht).1; simp; linarith)
      · apply ContinuousOn.log (continuousOn_const.div continuousOn_id
          (fun t ht => ((key t ht).1).ne')) (fun t ht => ?_)
        exact div_ne_zero hu0.ne' (key t ht).1.ne'
    · intro t ht
      obtain ⟨h0, h1, h2⟩ := key t ht
      have : 0 < t * Real.log t * Real.log (u / t) := by
        have := lt_of_lt_of_le hla h1; have := lt_of_lt_of_le hlb h2; positivity
      exact this.ne'
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      MeasureTheory.volume a (Real.sqrt u) := hcont.intervalIntegrable
  refine ⟨intervalIntegral.integral_nonneg hab (fun t ht => ?_), ?_⟩
  · obtain ⟨h0, h1, h2⟩ := key t ht
    have := lt_of_lt_of_le hla h1; have := lt_of_lt_of_le hlb h2; positivity
  · rw [← integral_one_div_of_pos (by linarith) (by linarith), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hint
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht; exact ((key t ht).1).ne'
    · intro t ht
      obtain ⟨h0, h1, h2⟩ := key t ht
      rw [one_div_mul_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have : Real.log a * Real.log (Real.sqrt u) ≤ Real.log t * Real.log (u / t) :=
        mul_le_mul h1 h2 hlb.le (by linarith)
      nlinarith

/-- SPLIT LEAF. Page 16 display 54: I of n, varpi, lambda0 equals r2 of n times
1 plus O of L to the minus 1 times log L, from the formula for f2 on page 15.
Elementary real analysis: the integral term is relatively O of log P over log z0. -/
theorem eq54_singInt (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ K1 X0 : ℝ, 0 < K1 ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ,
      |singInt X (windowY X ε) (Real.log X ^ B) n - integerMain X (windowY X ε) n| ≤
        K1 * integerMain X (windowY X ε) n *
          (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) := by
  set M := max (Real.exp (1 / B)) (max ((55 * B) ^ 2) 4) with hMdef
  have hM4 : 4 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨55 * B, Real.exp M, by positivity, ?_, ?_⟩
  · have := Real.add_one_le_exp M; linarith
  intro X hX n
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
  -- per term bound
  have per : ∀ v ∈ windowPairs X Y n,
      |(1 / Real.log (v.1 : ℝ)) * f2Weight z0 (v.2 : ℝ) -
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))| ≤
        55 * B * (L ^ (-1 : ℝ) * ℓ) * (1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) := by
    intro v hv
    obtain ⟨_, _, _, hm2lo, hm2hi, _⟩ := Finset.mem_filter.mp hv
    set m : ℝ := (v.2 : ℝ) with hm
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
    have hlmpos : 0 < Real.log m := by linarith
    have hsm : Real.log (Real.sqrt m) = Real.log m / 2 := Real.log_sqrt hmpos.le
    have hsmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
    have hzle : z0 ≤ Real.sqrt m := by
      rw [← Real.log_le_log_iff hz0pos hsmpos, hsm, hlz]; linarith
    obtain ⟨hJ0, hJ1⟩ := f2_integral_bound (u := m) hz1 hzle
    have hf2 : f2Weight z0 m = 1 / Real.log m +
        ∫ t in z0..Real.sqrt m, 1 / (t * Real.log t * Real.log (m / t)) := rfl
    generalize (∫ t in z0..Real.sqrt m, 1 / (t * Real.log t * Real.log (m / t))) = J at hJ0 hJ1 hf2
    have hlq : Real.log (Real.sqrt m / z0) ≤ 2 * (B * ℓ) := by
      rw [Real.log_div hsmpos.ne' hz0pos.ne', hsm, hlz]; linarith
    have hJ2 : J ≤ 4 * (B * ℓ) / (Real.log z0 * Real.log m) := by
      refine hJ1.trans ?_
      rw [hsm]
      have hc : 0 ≤ 1 / (Real.log z0 * (Real.log m / 2)) := by positivity
      refine (mul_le_mul_of_nonneg_left hlq hc).trans (le_of_eq ?_)
      field_simp; ring
    have hJ3 : J ≤ 55 * B * (L⁻¹ * ℓ) * (1 / Real.log m) := by
      refine hJ2.trans ?_
      have hr : 55 * B * (L⁻¹ * ℓ) * (1 / Real.log m) = (55 * (B * ℓ)) / (L * Real.log m) := by
        field_simp
      rw [hr, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : 4 * L ≤ 55 * Real.log z0 := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ B * ℓ * Real.log m)
      calc 4 * (B * ℓ) * (L * Real.log m) = B * ℓ * Real.log m * (4 * L) := by ring
        _ ≤ B * ℓ * Real.log m * (55 * Real.log z0) := h5
        _ = 55 * (B * ℓ) * (Real.log z0 * Real.log m) := by ring
    have hq : 0 ≤ 1 / Real.log (v.1 : ℝ) := by
      have := Real.log_natCast_nonneg v.1; positivity
    have hexpr : (1 / Real.log (v.1 : ℝ)) * f2Weight z0 m -
        1 / (Real.log (v.1 : ℝ) * Real.log m) = (1 / Real.log (v.1 : ℝ)) * J := by
      rw [hf2]; ring
    rw [hexpr, abs_of_nonneg (mul_nonneg hq hJ0), hu]
    calc (1 / Real.log (v.1 : ℝ)) * J
        ≤ (1 / Real.log (v.1 : ℝ)) * (55 * B * (L⁻¹ * ℓ) * (1 / Real.log m)) :=
          mul_le_mul_of_nonneg_left hJ3 hq
      _ = _ := by ring
  unfold singInt integerMain
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum per).trans (le_of_eq ?_))
  rw [← Finset.mul_sum]; ring

/-! ### Split of `eq48_49_series_lower`, route burst session 9, 2026-11-12.
The lower bound display 48 of page 13 for P2 and Lemma 3.8 display 49 of page 14
are the remaining CITED leaves; the passage from them to the exceptional set
bound, by Chebyshev's inequality with x equal to X, y equal to H and Q equal to P,
is proved here. AI wrote the Lean code. Goldbach is open. -/

/-- The product P2 of n, Q of page 13 display 45 for j equal to 2. The factors
for higher prime powers vanish because A2 carries the Moebius function, so each
local factor is 1 plus A2 of n, p. By definition this equals `product2` of
`Decomp129b`, which imports this file. -/
noncomputable def eulerP2 (n : ℕ) (Q : ℝ) : ℂ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)

/-- Route burst session 9, PROVED. The lower half of display 48, page 13, for
j equal to 2: P2 of n, P is at least a constant over log P for n in H2. The paper
states it after display 47 from the local factors of display 46 and property iii
on page 13. The proof is `Task129a.P2_lower_explicit`, with c equal to exp of
minus 44, from display 47 at primes and the lab Mertens bound. -/
theorem eq48_P2_lower :
    ∃ c P0 : ℝ, 0 < c ∧ 2 ≤ P0 ∧ ∀ P : ℝ, P0 ≤ P → ∀ n : ℕ, InH2 n →
      c / Real.log P ≤ ‖eulerP2 n P‖ :=
  Task129a.P2_lower_explicit

/-- SPLIT LEAF, route burst session 9. Lemma 3.8, display 49 on page 14, for
j equal to 2. The statement matches `lemma38_two` of `Decomp129b` term for term,
which reduces it to the leaves `truncation_input` and `tail_mean_square_input`;
the bridge is `eq49_lemma38_of_lemma38_two` in `Decomp129c`. -/
theorem eq49_lemma38 (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x →
      0 < P → P ≤ Q → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - eulerP2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  sorry

/-- Bookkeeping: for nonnegative X the integers of `iocNat` lie in the
interval of Lemma 3.8 on page 14. -/
theorem iocNat_subset_Ioc {X H : ℝ} (hX : 0 ≤ X) :
    iocNat X H ⊆ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
  intro n hn
  simp only [iocNat, Finset.mem_filter, Finset.mem_range] at hn
  rw [Finset.mem_Ioc]
  exact ⟨(Nat.floor_lt hX).mpr hn.2, Nat.lt_succ_iff.mp hn.1⟩

/-- Real analysis used on page 16 with P equal to L to the B: B log L squared is
at most L once L is at least 256 B to the fourth. -/
theorem logpow_sq_le {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hLB : 256 * B ^ 4 ≤ L) :
    (B * Real.log L) ^ 2 ≤ L := by
  have hL0 : 0 ≤ L := by linarith
  set s := L ^ (1 / 4 : ℝ) with hs_def
  have hs0 : 0 ≤ s := Real.rpow_nonneg hL0 _
  have hs4 : s ^ 4 = L := by
    rw [hs_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hlog : Real.log L ≤ 4 * s := by
    have := Real.log_le_rpow_div hL0 (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hs_def] at this
    linarith [show s / (1 / 4) = 4 * s by ring]
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hsB : 4 * B ≤ s := by
    have h44 : (4 * B) ^ 4 ≤ s ^ 4 := by rw [hs4]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp h44
  have h1 : B * Real.log L ≤ B * (4 * s) := mul_le_mul_of_nonneg_left hlog hB
  have h2 : (B * Real.log L) ^ 2 ≤ (B * (4 * s)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hB hlog0) h1 2
  have h3 : (B * (4 * s)) ^ 2 ≤ s ^ 4 := by
    have : (4 * B) * s ≤ s * s := mul_le_mul_of_nonneg_right hsB hs0
    have h4 : 0 ≤ (4 * B) * s := by positivity
    nlinarith
  exact h2.trans (h3.trans hs4.le)

/-- SPLIT LEAF. Page 13 display 48, the lower bound of P2 of n, P by
log P to the minus 1 on H2, together with Lemma 3.8 display 49 with y equal to H
and Chebyshev's inequality: S2 of n, P is at least c over log P for all but
O of H L to the minus A integers n in H2 in the interval X, X plus H.
CITED: Lemma 3.8 and display 48 are proved on pages 13 and 14. -/
theorem eq48_49_series_lower (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          ‖series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨c, P0, hc, hP0, h48⟩ := eq48_P2_lower
  obtain ⟨C49, x0, hC49, hx0, h49⟩ := eq49_lemma38 (A + 2) (7 / 18) (by linarith) (by norm_num)
  refine ⟨A + 3, by linarith, ?_⟩
  intro B hB ε hε
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  refine ⟨c / 2, 8 * C49 / c ^ 2, max (max x0 3) (Real.exp (256 * B ^ 4 + P0 + 3)), by positivity, by positivity,
    le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX
  have hx0X : x0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX3 : 3 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (256 * B ^ 4 + P0 + 3) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  set L := Real.log X with hL_def
  have hLK : 256 * B ^ 4 + P0 + 3 ≤ L := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hP0pos : 0 < P0 := by linarith
  have hL1 : 1 ≤ L := by nlinarith [pow_nonneg hB0 4]
  have hLpos : 0 < L := by linarith
  have hLB4 : 256 * B ^ 4 ≤ L := by linarith
  set P := L ^ B with hP_def
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos _
  have hLP : L ≤ P := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hB1
    rwa [Real.rpow_one] at this
  have hP0P : P0 ≤ P := by linarith [pow_nonneg hB0 4]
  have hlogP : Real.log P = B * Real.log L := Real.log_rpow hLpos B
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith [pow_nonneg hB0 4])
  set lP := Real.log P with hlP_def
  have hlPpos : 0 < lP := by rw [hlogP]; positivity
  have hlP2 : lP ^ 2 ≤ L := by rw [hlogP]; exact logpow_sq_le hB0 hL1 hLB4
  -- Chebyshev with T = c / (2 lP)
  set T := c / (2 * lP) with hT_def
  have hT : 0 < T := by positivity
  have hS : ∀ n, (InH2 n ∧ ‖series2 n P‖ < c / 2 / lP) →
      T ≤ |‖series2 n P - eulerP2 n P‖| := by
    intro n ⟨hn, hlt⟩
    rw [abs_of_nonneg (norm_nonneg _)]
    have hlow := h48 P hP0P n hn
    have htri : ‖eulerP2 n P‖ ≤ ‖series2 n P‖ + ‖series2 n P - eulerP2 n P‖ := by
      have := norm_sub_le (series2 n P) (series2 n P - eulerP2 n P)
      simpa only [sub_sub_cancel] using this
    have e1 : c / 2 / lP = T := by rw [hT_def]; field_simp
    have e2 : c / lP = 2 * T := by rw [hT_def]; field_simp
    rw [e1] at hlt
    rw [e2] at hlow
    linarith
  have hcheb := cnt_le_meansq _ (fun n => ‖series2 n P - eulerP2 n P‖) X H T hT hS
  have hsub := iocNat_subset_Ioc (H := H) hXpos.le
  have hsum : ∑ n ∈ iocNat X H, ‖series2 n P - eulerP2 n P‖ ^ 2 ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, ‖series2 n P - eulerP2 n P‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  -- hypotheses of Lemma 3.8 with x = X, y = H, Q = P
  have hy : X ^ (7 / 18 : ℝ) ≤ H :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH
  have hQ : P ≤ Real.exp (L ^ (1 - 7 / 18 : ℝ)) := by
    rw [← Real.exp_log hPpos]
    apply Real.exp_le_exp.mpr
    have h1 : lP ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hlP2
    rw [Real.sqrt_eq_rpow] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hlem := h49 X H P P hx0X hy hHX hPpos le_rfl hQ
  set a := L ^ A with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hLpos _
  have hA2 : L ^ (A + 2) = a * L ^ 2 := by
    rw [Real.rpow_add hLpos, ha_def]; norm_cast
  have hA3 : a * L ^ 3 ≤ P := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show A + 3 ≤ B by linarith)
    rw [Real.rpow_add hLpos] at this
    have e : L ^ (3 : ℝ) = L ^ 3 := by norm_cast
    rw [e] at this; exact this
  have hHpos : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
  set N := (cntIoc (fun n => InH2 n ∧ ‖series2 n P‖ < c / 2 / lP) X H : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hmain : N * T ^ 2 ≤ C49 * (H / P * L + H / (a * L ^ 2)) := by
    rw [← hA2]; exact hcheb.trans (hsum.trans hlem)
  -- bound the right side
  have hb1 : H / P * L ≤ H / (a * L) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hPpos (by positivity)]
    have : H * L * (a * L) = H * (a * L ^ 2) := by ring
    rw [this]
    have h' : a * L ^ 2 ≤ P :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) ha.le) hA3
    exact mul_le_mul_of_nonneg_left h' hHpos
  have hb2 : H / (a * L ^ 2) ≤ H / (a * L) := by
    apply div_le_div_of_nonneg_left hHpos (by positivity)
    have : L ^ 1 ≤ L ^ 2 := pow_le_pow_right₀ hL1 (by norm_num)
    rw [pow_one] at this
    exact mul_le_mul_of_nonneg_left this ha.le
  have hT2 : T ^ 2 = c ^ 2 / (4 * lP ^ 2) := by rw [hT_def]; field_simp; ring
  have hfin : N * (c ^ 2 / (4 * lP ^ 2)) ≤ C49 * (2 * (H / (a * L))) := by
    rw [← hT2]; refine hmain.trans ?_
    apply mul_le_mul_of_nonneg_left _ hC49.le; linarith
  have hgoal : N ≤ 8 * C49 / c ^ 2 * H / a := by
    have hc2 : 0 < c ^ 2 := by positivity
    have hl2 : 0 < lP ^ 2 := by positivity
    have step : N * c ^ 2 ≤ 8 * C49 * H * lP ^ 2 / (a * L) := by
      have := mul_le_mul_of_nonneg_right hfin (by positivity : (0 : ℝ) ≤ 4 * lP ^ 2)
      have e1 : N * (c ^ 2 / (4 * lP ^ 2)) * (4 * lP ^ 2) = N * c ^ 2 := by field_simp
      have e2 : C49 * (2 * (H / (a * L))) * (4 * lP ^ 2) = 8 * C49 * H * lP ^ 2 / (a * L) := by
        field_simp; ring
      rw [e1, e2] at this; exact this
    have step2 : 8 * C49 * H * lP ^ 2 / (a * L) ≤ 8 * C49 * H / a := by
      rw [div_le_div_iff₀ (by positivity) ha]
      have h0 : 0 ≤ 8 * C49 * H := mul_nonneg (mul_nonneg (by norm_num) hC49.le) hHpos
      have h1 : lP ^ 2 * a ≤ a * L := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hlP2 ha.le
      calc 8 * C49 * H * lP ^ 2 * a = 8 * C49 * H * (lP ^ 2 * a) := by ring
        _ ≤ 8 * C49 * H * (a * L) := mul_le_mul_of_nonneg_left h1 h0
    have := step.trans step2
    rw [le_div_iff₀ ha]
    rw [le_div_iff₀ ha] at this
    calc N * a = (N * c ^ 2 * a) / c ^ 2 := by field_simp
      _ ≤ (8 * C49 * H) / c ^ 2 := div_le_div_of_nonneg_right this hc2.le
      _ = 8 * C49 / c ^ 2 * H := by ring
  exact hgoal

/-- Helper: a finite set of naturals inside the open real interval a, b has at most
b minus a plus 1 elements. Counting bookkeeping for page 16. AI wrote the Lean code. -/
theorem card_le_of_Ioo_real (S : Finset ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a < (n : ℝ) ∧ (n : ℝ) < b) : (S.card : ℝ) ≤ b - a + 1 := by
  have hsub : S ⊆ Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    exact Finset.mem_Ioo.mpr ⟨(Nat.floor_lt ha).mpr h1, Nat.lt_ceil.mpr h2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ioo] at hc
  have hq := Nat.ceil_lt_add_one (le_trans ha hab)
  have hp := Nat.sub_one_lt_floor a
  have hcR : (S.card : ℝ) ≤ ((⌈b⌉₊ - ⌊a⌋₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hc
  rw [Nat.sub_sub] at hcR
  by_cases h : ⌊a⌋₊ + 1 ≤ ⌈b⌉₊
  · rw [Nat.cast_sub h] at hcR; push_cast at hcR; linarith
  · push Not at h
    rw [Nat.sub_eq_zero_of_le h.le] at hcR; push_cast at hcR; linarith

/-- Helper for page 16, the size of r2 of page 2 display 6: every m2 in a set K of
integers in the window I2 with m2 squared above n minus X gives the admissible pair
n minus m2 squared, m2, of weight at least L to the minus 2. AI wrote the Lean code. -/
theorem r2_ge_card (X Y : ℝ) (n : ℕ) (K : Finset ℕ) (hX4 : 4 ≤ X) (hYX : 2 * Y ≤ X)
    (hs4 : 4 ≤ Real.sqrt Y) (hXn : X < (n : ℝ))
    (hK : ∀ k ∈ K, Real.sqrt Y / 2 ≤ (k : ℝ) ∧ (k : ℝ) < Real.sqrt Y ∧
      (n : ℝ) - X < (k : ℝ) ^ 2) :
    (K.card : ℝ) * (1 / (Real.log X * Real.log X)) ≤ integerMain X Y n := by
  set s := Real.sqrt Y with hs
  have hYpos : 0 < Y := by
    by_contra h; push Not at h; rw [hs, Real.sqrt_eq_zero'.mpr h] at hs4; linarith
  have hss : s * s = Y := Real.mul_self_sqrt hYpos.le
  have hsY : s ≤ Y := by nlinarith
  set L := Real.log X with hL
  let f : ℕ → ℕ × ℕ := fun k => (n - k ^ 2, k)
  have hfacts : ∀ k ∈ K, f k ∈ windowPairs X Y n ∧
      1 / (L * L) ≤ 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := hK k hk
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hkY : (k : ℝ) ^ 2 < Y := by nlinarith
    have hkn : k ^ 2 ≤ n := by
      have : ((k ^ 2 : ℕ) : ℝ) ≤ n := by push_cast; linarith
      exact_mod_cast this
    have hm1 : ((n - k ^ 2 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) ^ 2 := by
      rw [Nat.cast_sub hkn]; push_cast; ring
    have hm1lo : X - Y < ((n - k ^ 2 : ℕ) : ℝ) := by rw [hm1]; linarith
    have hm1hi : ((n - k ^ 2 : ℕ) : ℝ) < X := by rw [hm1]; linarith
    refine ⟨?_, ?_⟩
    · rw [windowPairs, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hm1hi.le)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hk2.le))⟩,
        hm1lo.le, hm1hi, hk1, hk2, Nat.sub_add_cancel hkn⟩
    · simp only [f]
      have hl1 : 0 < Real.log ((n - k ^ 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hl1' : Real.log ((n - k ^ 2 : ℕ) : ℝ) ≤ L := Real.log_le_log (by linarith) hm1hi.le
      have hl2 : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
      have hl2' : Real.log (k : ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul hl1' hl2' hl2.le (by linarith)
  have hinj : Set.InjOn f K := fun a _ b _ h => congrArg Prod.snd h
  have hnonneg : ∀ v ∈ windowPairs X Y n, v ∉ K.image f →
      0 ≤ 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) := by
    intro v _ _
    have := Real.log_natCast_nonneg v.1
    have := Real.log_natCast_nonneg v.2
    positivity
  have hsub : K.image f ⊆ windowPairs X Y n := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact (hfacts k hk).1
  unfold integerMain
  calc (K.card : ℝ) * (1 / (L * L)) = ∑ k ∈ K, 1 / (L * L) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ K, 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) :=
        Finset.sum_le_sum (fun k hk => (hfacts k hk).2)
    _ = ∑ v ∈ K.image f, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) :=
        by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

/-- SPLIT LEAF. Size of r2 of n, page 2 display 6, used implicitly on page 16
in passing from the absolute error of display 53 to the relative error of
display 55: r2 of n is at least Y to the one half times L to the minus A minus 3
except for O of H L to the minus A integers n below X plus Y. Elementary count.
PROVED 2026-11-12 PROVE PASS: r2 of n is small only when n minus X exceeds
Y minus O of Y^(1/2) plus Y L^(-A-1), a range of that length. AI wrote the Lean code. -/
theorem r2_lower (A : ℝ) (hA : 0 < A) (ε : ℝ) (hε : 0 < ε) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
      (cntIoc (fun n => (n : ℝ) < X + windowY X ε ∧
        integerMain X (windowY X ε) n <
          Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 3))) X H : ℝ) ≤
        C * H / Real.log X ^ A := by
  set T := (16 * A + 8) ^ 2 with hT
  have hT64 : 64 ≤ T := by nlinarith
  refine ⟨5, Real.exp T, by norm_num, ?_, ?_⟩
  · have := Real.add_one_le_exp T; linarith
  intro X H hX hH hHX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set L := Real.log X with hL
  have hLT : T ≤ L := by rw [← Real.log_exp T]; exact Real.log_le_log (Real.exp_pos _) hX
  have hL64 : 64 ≤ L := le_trans hT64 hLT
  have hLpos : 0 < L := by linarith
  have hX4 : 4 ≤ X := by
    have h1 := Real.add_one_le_exp T
    have h2 : Real.exp T ≤ X := hX
    linarith
  have hX1 : 1 < X := by linarith
  -- the case epsilon above 11/18 is vacuous
  have hε1 : ε ≤ 11 / 18 := by
    by_contra hc; push Not at hc
    have : X ^ (1 : ℝ) < X ^ (7 / 18 + ε) := Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    rw [Real.rpow_one] at this; linarith
  have hHnn : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
  set e := 7 / 12 + ε / 2 with he
  have he7 : 7 / 12 ≤ e := by linarith
  have he8 : e ≤ 8 / 9 := by linarith
  have hYdef : windowY X ε = X ^ e := rfl
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hXpos _
  have hlogY : Real.log Y = e * L := by rw [hYdef]; exact Real.log_rpow hXpos e
  set s := Real.sqrt Y with hs
  have hss : s * s = Y := Real.mul_self_sqrt hYpos.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hYpos
  have hlogs : Real.log s = e * L / 2 := by rw [hs, Real.log_sqrt hYpos.le, hlogY]
  have hlog2 : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hX2Y : 2 * Y ≤ X := by
    calc 2 * Y = Real.exp (Real.log 2 + Real.log Y) := by
          rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hYpos]
      _ ≤ Real.exp L := by
          apply Real.exp_le_exp.mpr; rw [hlogY]
          linarith [mul_le_mul_of_nonneg_right he8 hLpos.le]
      _ = X := Real.exp_log hXpos
  have hs8 : 8 ≤ s := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    calc (8:ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log s) := by
          apply Real.exp_le_exp.mpr; rw [hlogs, h8]
          linarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
      _ = s := Real.exp_log hspos
  -- lambda = L^(-A), rho = lambda / L
  set lam := L ^ (-A) with hlam
  have hlampos : 0 < lam := Real.rpow_pos_of_pos hLpos _
  have hlam1 : lam ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hlamA : lam = (L ^ A)⁻¹ := Real.rpow_neg hLpos.le A
  have hA3 : L ^ (-(A + 3)) = lam / (L * L) / L := by
    rw [show -(A + 3) = -A + (-3 : ℝ) by ring, Real.rpow_add hLpos, ← hlam,
      Real.rpow_neg hLpos.le 3]
    rw [show (3:ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  set ρ := lam / L with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ8 : ρ ≤ 1 / 8 := by
    rw [hρ, div_le_iff₀ hLpos]; linarith
  have hρlam : ρ ≤ lam := by
    rw [hρ, div_le_iff₀ hLpos]
    have := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ L) hlampos.le; linarith
  -- growth: 6 ≤ s * lam
  have hgrowth : 6 ≤ s * lam := by
    set ℓ := Real.log L with hℓ
    have hsqT : 16 * A + 8 ≤ Real.sqrt L := by
      have := Real.sqrt_le_sqrt hLT
      rwa [hT, Real.sqrt_sq (by positivity)] at this
    have hℓsq : ℓ ≤ 2 * Real.sqrt L := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
      rw [Real.log_sqrt hLpos.le] at h1; linarith
    have hsqsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
    have hlog6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6); linarith
    have hkey : Real.log 6 + A * ℓ ≤ e * L / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hℓsq hA.le
      have h2 := mul_le_mul_of_nonneg_right hsqT (Real.sqrt_nonneg L)
      have h3 := mul_nonneg hA.le (Real.sqrt_nonneg L)
      linarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
    have hLA : L ^ A = Real.exp (A * ℓ) := by
      rw [Real.rpow_def_of_pos hLpos, mul_comm]
    rw [hlamA, hLA, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    calc 6 * Real.exp (A * ℓ) = Real.exp (Real.log 6 + A * ℓ) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (Real.log s) := Real.exp_le_exp.mpr (by rw [hlogs]; exact hkey)
      _ = s := Real.exp_log hspos
  set W := 2 * s + 2 * Y * ρ with hW
  have hWY : W ≤ Y / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hs8 hspos.le
    have h2 := mul_le_mul_of_nonneg_left hρ8 (by positivity : (0:ℝ) ≤ 2 * Y)
    rw [hW]; linarith
  -- pointwise: every bad n lies in X + Y - W, X + Y
  have hpt : ∀ n : ℕ, X < (n : ℝ) → (n : ℝ) < X + Y →
      integerMain X Y n < s * L ^ (-(A + 3)) → X + Y - W < (n : ℝ) := by
    intro n hXn hnY hbad
    set d := (n : ℝ) - X with hd
    have hd0 : 0 < d := by linarith
    set t := Real.sqrt d with ht
    have htt : t * t = d := Real.mul_self_sqrt hd0.le
    have ht0 : 0 ≤ t := Real.sqrt_nonneg d
    set η := 1 + s * ρ with hη
    have hηs : η ≤ s / 2 := by
      have := mul_le_mul_of_nonneg_left hρ8 hspos.le; rw [hη]; linarith
    by_contra hcon
    push Not at hcon
    -- then t ≤ s - η
    have hts : t ≤ s - η := by
      by_contra h2; push Not at h2
      have h3 : 0 ≤ s - η := by linarith
      have h4 : (s - η) * (s - η) < t * t := mul_self_lt_mul_self h3 h2
      have h5 : (s - η) * (s - η) = Y - W + η * η := by rw [hη, hW, ← hss]; ring
      have h6 := mul_self_nonneg η
      linarith
    set p := max ⌈s / 2⌉₊ (⌊t⌋₊ + 1) with hp
    set K := Finset.Ico p ⌈s⌉₊ with hK
    have hpR : (p : ℝ) ≤ s - η + 1 := by
      rw [hp, Nat.cast_max]
      apply max_le
      · have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ s / 2); linarith
      · have := Nat.floor_le ht0; push_cast; linarith
    have hqR : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    have hpq : p ≤ ⌈s⌉₊ := by
      have : (p : ℝ) ≤ (⌈s⌉₊ : ℝ) := by have := mul_pos hspos hρpos; linarith
      exact_mod_cast this
    have hKcard : s * ρ ≤ (K.card : ℝ) := by
      rw [hK, Nat.card_Ico, Nat.cast_sub hpq]; linarith
    have hKmem : ∀ k ∈ K, s / 2 ≤ (k : ℝ) ∧ (k : ℝ) < s ∧ (n : ℝ) - X < (k : ℝ) ^ 2 := by
      intro k hk
      rw [hK, Finset.mem_Ico] at hk
      have h1 : ⌈s / 2⌉₊ ≤ k := le_trans (le_max_left _ _) hk.1
      have h2 : ⌊t⌋₊ + 1 ≤ k := le_trans (le_max_right _ _) hk.1
      have h2' : t < (k : ℝ) := by
        have := Nat.lt_floor_add_one t
        have : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h2
        push_cast at this; linarith
      refine ⟨Nat.ceil_le.mp h1, Nat.lt_ceil.mp hk.2, ?_⟩
      rw [← hd, ← htt, sq]; exact mul_self_lt_mul_self ht0 h2'
    have hr2 := r2_ge_card X Y n K hX4 hX2Y (by linarith) hXn hKmem
    have hcmp : s * L ^ (-(A + 3)) ≤ (K.card : ℝ) * (1 / (L * L)) := by
      rw [hA3]
      calc s * (lam / (L * L) / L) = s * ρ * (1 / (L * L)) := by rw [hρ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKcard (by positivity)
    linarith
  -- count
  have hXH : 0 ≤ X + H := by linarith
  have hcnt : (cntIoc (fun n => (n : ℝ) < X + Y ∧
      integerMain X Y n < s * L ^ (-(A + 3))) X H : ℝ) ≤ W + 1 := by
    have hW0 : 0 ≤ W := by have := mul_pos hYpos hρpos; rw [hW]; linarith
    generalize hSp : (fun n : ℕ => (n : ℝ) < X + Y ∧
      integerMain X Y n < s * L ^ (-(A + 3))) = Sp
    unfold cntIoc
    refine (card_le_of_Ioo_real _ (X + Y - W) (X + Y) (by linarith) (by linarith) ?_).trans
      (by linarith)
    intro n hn
    obtain ⟨_, hXn, hS⟩ := Finset.mem_filter.mp hn
    rw [← hSp] at hS
    obtain ⟨hnY, hb⟩ := hS
    exact ⟨hpt n hXn hnY hb, hnY⟩
  have hempty : H < Y / 2 → cntIoc (fun n => (n : ℝ) < X + Y ∧
      integerMain X Y n < s * L ^ (-(A + 3))) X H = 0 := by
    intro hHY
    generalize hSp : (fun n : ℕ => (n : ℝ) < X + Y ∧
      integerMain X Y n < s * L ^ (-(A + 3))) = Sp
    unfold cntIoc
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro n hn'
    obtain ⟨hn, hXn, hS⟩ := Finset.mem_filter.mp hn'
    rw [← hSp] at hS
    obtain ⟨hnY, hb⟩ := hS
    have h1 := hpt n hXn hnY hb
    have h2 : (n : ℝ) ≤ X + H := by
      have := Finset.mem_range.mp hn
      have h3 : n ≤ ⌊X + H⌋₊ := Nat.lt_succ_iff.mp this
      exact le_trans (by exact_mod_cast h3) (Nat.floor_le hXH)
    linarith
  have hgoal : 5 * H / L ^ A = 5 * H * lam := by rw [hlamA, div_eq_mul_inv]
  rw [hgoal]
  by_cases hHY : H < Y / 2
  · rw [hempty hHY]; simp; positivity
  · push Not at hHY
    refine hcnt.trans ?_
    have h1 : 2 * Y * ρ ≤ 4 * H * lam := by
      have := mul_le_mul_of_nonneg_left hρlam (by positivity : (0:ℝ) ≤ 2 * Y)
      have := mul_le_mul_of_nonneg_right hHY hlampos.le
      linarith
    have h2 : 2 * s + 1 ≤ H * lam := by
      have h3 := mul_le_mul_of_nonneg_right hHY hlampos.le
      have h4 := mul_le_mul_of_nonneg_left hgrowth hspos.le
      rw [← hss] at h3
      linarith
    rw [hW]; linarith

/-- Pages 2 and 8, displays 4 to 6 and 34: the error of display 53 vanishes
beyond the support of the windows. -/
theorem err53_vanish (X ε B : ℝ) (n : ℕ) (hY : 0 ≤ windowY X ε)
    (hn : X + windowY X ε ≤ (n : ℝ)) : err53 X ε B n = 0 := by
  simp [err53, roughCount, singInt, windowPairs_empty_above X _ hY n hn]

/-- Counting bookkeeping: a predicate supported below X plus Y has no more
points in X, X plus H than in X, X plus Y when Y is at most H. -/
theorem cnt_le_of_support (S : ℕ → Prop) (X Y H : ℝ) (hYH : Y ≤ H)
    (hS : ∀ n, S n → (n : ℝ) < X + Y) : cntIoc S X H ≤ cntIoc S X Y := by
  unfold cntIoc
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  obtain ⟨_, hXn, hSn⟩ := hn
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor (hS n hSn).le), hXn, hSn⟩

/-- SPLIT, route burst session 9, UNWRITTEN RANGE; PROVED in session 8 p3 from the
leaves `Task129e.major_arc_display28_large` and, through display 29 in `Circle129f`,
`Task129f.minor_dist_display30_large`. The mean square bound
display 33 of Proposition 1, page 7, for R of n, varpi, lambda0 when epsilon
lies in 5/18, 11/18 and X to the 1 minus epsilon is less than H, with H at most
Y and H at least the smaller of X to the 7/18 plus epsilon and Y. Here H is Y to
the theta2 with theta2 at least 2/3 and at most 1, so the verification of
hypothesis A2.3 on page 15 by Lemma 3.4 with x equal to Y and y equal to H is the
same argument as on the written range. The paper does not write it: page 16
states display 55 only for H at most X to the 1 minus epsilon. -/
theorem prop1_meansq_large (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → ε ≤ 11 / 18 →
        min (X ^ (7 / 18 + ε)) (windowY X ε) ≤ H → X ^ (1 - ε) < H →
        H ≤ windowY X ε →
        ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
          C * H * windowY X ε * Real.log X ^ (-A) := by
  obtain ⟨B1, hB1, hmin⟩ := Task129f.minor_arc_display32_large A hA
  refine ⟨max B1 (2 * A), lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := lt_of_lt_of_le hB1 ((le_max_left _ _).trans hB)
  have hB2 : 2 * A ≤ B := (le_max_right _ _).trans hB
  obtain ⟨C1, X1, hC1, hX1, hmaj⟩ := Task129e.major_arc_display28_large B hBpos ε hε
  obtain ⟨C2, X2, hC2, hX2, hmin'⟩ := hmin B ((le_max_left _ _).trans hB) ε hε
  by_cases hε5 : ¬ 5 / 18 < ε
  · refine ⟨1, 2, one_pos, le_rfl, fun X H _ he1 => absurd he1 hε5⟩
  push_neg at hε5
  obtain ⟨X3, hX3, hP2⟩ := P_sq_le_rpow B (3 * ε / 2 - 5 / 12) (by linarith)
  refine ⟨2 * (4 * C1 ^ 2 + 2 * C2), max (max X1 X2) (max X3 3), by positivity,
    le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro X H hX he1 he2 hH0 hH1 hH2
  have hX1' : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3' : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX3'' : 3 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have hXgt1 : 1 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos hXgt1
  have hL1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans hX3'')
  set s := 3 * ε / 2 - 5 / 12 with hs
  set P2 := (Real.log X ^ B) ^ 2 with hP2_def
  have hP2pos : 0 < P2 := by positivity
  have hP2one : 1 ≤ P2 := one_le_pow₀ (Real.one_le_rpow hL1 hBpos.le)
  have hP2le : P2 ≤ 1 / 2 * X ^ s := hP2 X hX3'
  have hXs : 0 < X ^ s := Real.rpow_pos_of_pos hXpos _
  -- X to the 1 minus epsilon is less than Y P to the minus 2
  have hYP : X ^ (1 - ε) < windowY X ε / P2 := by
    rw [lt_div_iff₀ hP2pos]
    have e : windowY X ε = X ^ (1 - ε) * X ^ s := by
      unfold windowY; rw [← Real.rpow_add hXpos]; congr 1; ring
    rw [e]
    have h1 : 0 < X ^ (1 - ε) := Real.rpow_pos_of_pos hXpos _
    nlinarith
  have hYP2 : windowY X ε / P2 ≤ windowY X ε :=
    div_le_self (Real.rpow_pos_of_pos hXpos _).le hP2one
  set H' := min H (windowY X ε / P2) with hH'_def
  have hH'0 : min (X ^ (7 / 18 + ε)) (windowY X ε / P2) ≤ H' := by
    rcases le_total H (windowY X ε / P2) with h | h
    · rw [hH'_def, min_eq_left h]
      exact le_trans (min_le_min_left _ hYP2) hH0
    · rw [hH'_def, min_eq_right h]; exact min_le_right _ _
  have hH'1 : X ^ (1 - ε) < H' := lt_min hH1 hYP
  have hH'3 : H' ≤ windowY X ε / P2 := min_le_right _ _
  have hH'one : 1 ≤ H' := le_trans (Real.one_le_rpow hXgt1.le (by linarith)) hH'1.le
  exact meansq_from_arcs hX3'' hB2 hH'one (min_le_left _ _) hC2.le
    (fun n => hmaj X H' hX1' he1 he2 hH'0 hH'1 hH'3 n)
    (fun N0 hN0 => hmin' X H' hX2' he1 he2 hH'0 hH'1 hH'3 N0 hN0)

/-- Route burst session 9. Display 53 of page 16 for epsilon above 5/18 and H
above X to the 1 minus epsilon, with the lower bound X to the 7/18 plus epsilon of
Theorem 1 kept. When epsilon exceeds 11/18 this range is empty. When H exceeds Y
the windows of displays 4 to 6 reduce the count to H equal to Y. The rest is
`prop1_meansq_large` with the Chebyshev step. This replaces `eq53_large_eps` in
the proof of `eq53_full_range`; that lemma drops the lower bound on H. -/
theorem eq53_large_eps_range (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → X ^ (7 / 18 + ε) ≤ H → X ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := prop1_meansq_large (3 * A) (by linarith)
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, h⟩ := h B hB ε hε
  refine ⟨C, max X0 3, hC, le_trans hX0 (le_max_left _ _), ?_⟩
  intro X H hX heps hH hHlow hHX
  have hX0' : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 < X := by linarith
  have hXpos : 0 < X := by linarith
  have heps2 : ε ≤ 11 / 18 := by
    by_contra hc
    push_neg at hc
    have : X ^ (1 : ℝ) < X ^ (7 / 18 + ε) := Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hYnn : 0 ≤ windowY X ε := Real.rpow_nonneg hXpos.le _
  by_cases hHY : H ≤ windowY X ε
  · exact count_of_meansq hX3
      (h X H hX0' heps heps2 ((min_le_left _ _).trans hH) hHlow hHY)
  · push_neg at hHY
    have hsupp : ∀ n, (InH2 n ∧
        Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) →
        (n : ℝ) < X + windowY X ε := by
      intro n ⟨_, hn⟩
      by_contra hc
      push_neg at hc
      rw [err53_vanish X ε B n hYnn hc] at hn
      have : 0 ≤ Real.sqrt (windowY X ε) * Real.log X ^ (-A) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.log_nonneg hX1.le) _)
      linarith
    have hc := cnt_le_of_support _ X (windowY X ε) H hHY.le hsupp
    have hYlow : X ^ (1 - ε) < windowY X ε := by
      unfold windowY; exact Real.rpow_lt_rpow_of_exponent_lt hX1 (by linarith)
    have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg hX1.le) _
    calc (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ)
        ≤ (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n)
            X (windowY X ε) : ℝ) := by exact_mod_cast hc
      _ ≤ C * windowY X ε / Real.log X ^ A :=
          count_of_meansq hX3 (h X _ hX0' heps heps2 (min_le_right _ _) hYlow le_rfl)
      _ ≤ C * H / Real.log X ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHY.le hC.le) hLA

/-- Display 53 of page 16 on the full range X to the 7 over 18 plus epsilon up
to X. For epsilon at most 5 over 18, Y is at most X to the 1 minus epsilon and the
range above Y adds nothing by `err53_vanish`. -/
theorem eq53_full_range (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := eq53_prop1 A hA
  obtain ⟨B2, hB2, h2⟩ := eq53_large_eps_range A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := h1 B (le_trans (le_max_left _ _) hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, h2⟩ := h2 B (le_trans (le_max_right _ _) hB) ε hε
  refine ⟨C1 + C2, max X1 X2, by positivity, le_trans hX1 (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hX1' : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hX2' : X2 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hHnn : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
  have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg hXone) _
  have hmono : ∀ C' : ℝ, C' ≤ C1 + C2 →
      C' * H / Real.log X ^ A ≤ (C1 + C2) * H / Real.log X ^ A := fun C' hC' =>
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hHnn) hLA
  by_cases hsmall : H ≤ X ^ (1 - ε)
  · exact (h1 X H hX1' hH hsmall).trans (hmono C1 (by linarith))
  · push_neg at hsmall
    by_cases heps : ε ≤ 5 / 18
    · have hYle : windowY X ε ≤ X ^ (1 - ε) := by
        unfold windowY; exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      have hYH : windowY X ε ≤ H := hYle.trans hsmall.le
      have hYlow : X ^ (7 / 18 + ε) ≤ windowY X ε := by
        unfold windowY; exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      have hYnn : 0 ≤ windowY X ε := Real.rpow_nonneg hXpos.le _
      have hsupp : ∀ n, (InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) →
          (n : ℝ) < X + windowY X ε := by
        intro n ⟨_, hn⟩
        by_contra hc
        push_neg at hc
        rw [err53_vanish X ε B n hYnn hc] at hn
        have : 0 ≤ Real.sqrt (windowY X ε) * Real.log X ^ (-A) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.log_nonneg hXone) _)
        linarith
      have hc := cnt_le_of_support _ X (windowY X ε) H hYH hsupp
      calc (cntIoc (fun n => InH2 n ∧
            Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ)
          ≤ (cntIoc (fun n => InH2 n ∧
            Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n)
              X (windowY X ε) : ℝ) := by exact_mod_cast hc
        _ ≤ C1 * windowY X ε / Real.log X ^ A := h1 X _ hX1' hYlow hYle
        _ ≤ C1 * H / Real.log X ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYH hC1.le) hLA
        _ ≤ _ := hmono C1 (by linarith)
    · push_neg at heps
      exact (h2 X H hX2' heps hH hsmall hHX).trans (hmono C2 (by linarith))

/-- Real arithmetic of the passage from displays 53 and 54 to display 55 on
page 16: an absolute error s u u and a relative error K1 r u l combine to a
relative error 1 plus K1 times r g u l once g is at least c over B l and u is at
most c over B. -/
theorem eq55_arith {e g r s u l d K1 c B : ℝ} (hE : e ≤ s * u * u)
    (hS : c / (B * l) ≤ g) (hr : s ≤ r) (hd : d ≤ K1 * r * (u * l))
    (hs0 : 0 ≤ s) (hg0 : 0 ≤ g) (hu : 0 < u) (hl : 0 < l) (hB : 0 < B)
    (hucB : u ≤ c / B) : e + g * d ≤ (1 + K1) * (r * g) * (u * l) := by
  have h1 : c / (B * l) * s ≤ g * r := mul_le_mul hS hr hs0 hg0
  have h2 : c / (B * l) * s * (u * l) = c / B * s * u := by
    field_simp
  have h3 : s * u * u ≤ c / B * s * u := by
    have := mul_le_mul_of_nonneg_left hucB (mul_nonneg hs0 hu.le)
    linarith [this]
  have h4 : c / (B * l) * s * (u * l) ≤ g * r * (u * l) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg hu.le hl.le)
  have h5 : g * d ≤ g * (K1 * r * (u * l)) := mul_le_mul_of_nonneg_left hd hg0
  nlinarith [h2, h3, h4, h5]

/-- LEAF. Page 16 eq. 55 from eqs. 48, 49, 53 and 54.
This includes extension to H at most X by subdivision, which is not written out
in the paper. It requires the short interval Siegel Walfisz input on page 15,
Lemma 3.4 and the singular series estimates. The external sources include Liu
and Zhan 1997 Lemma 5.1 and Mikawa and Peneva 2007 Lemma 2, as cited on
page 15. It remains CITED.
SPLIT 2026-11-12: derived without sorry of its own from `eq53_full_range`,
`eq54_singInt`, `eq48_49_series_lower`, `r2_lower` and `eq55_arith`. -/
theorem circle_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
            (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
          ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B1, hB1, h53⟩ := eq53_full_range (A + 5) (by linarith)
  obtain ⟨B3, hB3, h48⟩ := eq48_49_series_lower A hA
  refine ⟨max B1 B3, lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := lt_of_lt_of_le hB1 (le_trans (le_max_left _ _) hB)
  obtain ⟨C1, X1, hC1, hX1, h53⟩ := h53 B (le_trans (le_max_left _ _) hB) ε hε
  obtain ⟨K1, X2, hK1, hX2, h54⟩ := eq54_singInt B hBpos ε hε
  obtain ⟨c, C3, X3, hc, hC3, hX3, h48⟩ := h48 B (le_trans (le_max_right _ _) hB) ε hε
  obtain ⟨C4, X4, hC4, hX4, hr2⟩ := r2_lower A hA ε hε
  refine ⟨C1 + C3 + C4, 1 + K1,
    max (max (max X1 X2) (max X3 X4)) (Real.exp (max (Real.exp 1) (B / c))),
    by positivity, by positivity,
    le_trans hX1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro X H hX hH hHX
  have hX1' : X1 ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hX
  have hX2' : X2 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hX
  have hX3' : X3 ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hX
  have hX4' : X4 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hX
  have hXe : Real.exp (max (Real.exp 1) (B / c)) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have hLge : max (Real.exp 1) (B / c) ≤ Real.log X := by
    rw [← Real.log_exp (max (Real.exp 1) (B / c))]
    exact Real.log_le_log (Real.exp_pos _) hXe
  have hLe : Real.exp 1 ≤ Real.log X := le_trans (le_max_left _ _) hLge
  have hBc : B / c ≤ Real.log X := le_trans (le_max_right _ _) hLge
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hL1 : 1 ≤ Real.log X := le_trans he1 hLe
  have hLpos : 0 < Real.log X := by linarith
  have hlogL : 1 ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hLe
  have hlogP : Real.log (Real.log X ^ B) = B * Real.log (Real.log X) :=
    Real.log_rpow hLpos B
  have hYnn : 0 ≤ windowY X ε := Real.rpow_nonneg hXpos.le _
  have hu : Real.log X ^ (-1 : ℝ) = (Real.log X)⁻¹ := Real.rpow_neg_one _
  have hupos : 0 < Real.log X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hucB : Real.log X ^ (-1 : ℝ) ≤ c / B := by
    rw [hu]
    have : B / c ≤ Real.log X := hBc
    rw [div_le_iff₀ hc] at this
    rw [inv_eq_one_div, div_le_div_iff₀ hLpos hBpos]
    linarith
  have hsplit : Real.log X ^ (-(A + 5)) =
      Real.log X ^ (-(A + 3)) * Real.log X ^ (-1 : ℝ) * Real.log X ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1
    ring
  let badA := fun n => InH2 n ∧
    Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 5)) < err53 X ε B n
  let badC := fun n => InH2 n ∧
    ‖series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)
  let badD := fun n : ℕ => (n : ℝ) < X + windowY X ε ∧
    integerMain X (windowY X ε) n <
      Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 3))
  have sub : ∀ n, (InH2 n ∧
      (1 + K1) * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
        (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
      ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
        main2 X (windowY X ε) (Real.log X ^ B) n‖) → badA n ∨ (badC n ∨ badD n) := by
    intro n ⟨hn, hbad⟩
    by_contra h
    simp only [not_or] at h
    obtain ⟨hA', hC', hD'⟩ := h
    by_cases hnY : X + windowY X ε ≤ (n : ℝ)
    · obtain ⟨_, hr0, hm0, _⟩ :=
        counts_vanish_above X (windowY X ε) (Real.log X ^ B) hYnn n hnY
      rw [hr0, hm0] at hbad
      simp at hbad
    · push_neg at hnY
      have hE : err53 X ε B n ≤ Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 5)) :=
        le_of_not_gt (fun hh => hA' ⟨hn, hh⟩)
      have hS : c / Real.log (Real.log X ^ B) ≤ ‖series2 n (Real.log X ^ B)‖ :=
        le_of_not_gt (fun hh => hC' ⟨hn, hh⟩)
      have hr : Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 3)) ≤
          integerMain X (windowY X ε) n :=
        le_of_not_gt (fun hh => hD' ⟨hnY, hh⟩)
      have hI := h54 X hX2' n
      have hs0 : 0 ≤ Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 3)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hLpos.le _)
      have hr0 : 0 ≤ integerMain X (windowY X ε) n := le_trans hs0 hr
      have hE' : err53 X ε B n ≤ Real.sqrt (windowY X ε) * Real.log X ^ (-(A + 3)) *
          Real.log X ^ (-1 : ℝ) * Real.log X ^ (-1 : ℝ) := by
        rw [hsplit] at hE; linarith [hE]
      have hmain : ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ =
          integerMain X (windowY X ε) n * ‖series2 n (Real.log X ^ B)‖ := by
        simp only [main2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg hr0]
      have hdecomp : (roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
          main2 X (windowY X ε) (Real.log X ^ B) n =
          ((roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
            series2 n (Real.log X ^ B) *
              (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)) +
          series2 n (Real.log X ^ B) *
            ((singInt X (windowY X ε) (Real.log X ^ B) n -
              integerMain X (windowY X ε) n : ℝ) : ℂ) := by
        simp only [main2, Complex.ofReal_sub]
        ring
      have htri : ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
          main2 X (windowY X ε) (Real.log X ^ B) n‖ ≤
          err53 X ε B n + ‖series2 n (Real.log X ^ B)‖ *
            |singInt X (windowY X ε) (Real.log X ^ B) n - integerMain X (windowY X ε) n| := by
        rw [hdecomp]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rfl
      rw [hlogP] at hS
      have hfin := htri.trans (eq55_arith hE' hS hr hI hs0 (norm_nonneg _) hupos
        (by linarith) hBpos hucB)
      rw [← hmain] at hfin
      exact (not_lt_of_ge hfin) hbad
  have hcount := le_trans (U1534.cnt_mono sub X H)
    (le_trans (U1534.cnt_or_le badA (fun n => badC n ∨ badD n) X H)
      (Nat.add_le_add_left (U1534.cnt_or_le badC badD X H) _))
  have hcountR : (cntIoc (fun n => InH2 n ∧
      (1 + K1) * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
        (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
      ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
        main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
      (cntIoc badA X H : ℝ) + ((cntIoc badC X H : ℝ) + (cntIoc badD X H : ℝ)) := by
    exact_mod_cast hcount
  have hHnn : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
  have hA1 : (cntIoc badA X H : ℝ) ≤ C1 * H / Real.log X ^ A := by
    refine (h53 X H hX1' hH hHX).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLpos _)
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hC := h48 X H hX3' hH hHX
  have hD := hr2 X H hX4' hH hHX
  calc _ ≤ (cntIoc badA X H : ℝ) + ((cntIoc badC X H : ℝ) + (cntIoc badD X H : ℝ)) := hcountR
    _ ≤ C1 * H / Real.log X ^ A + (C3 * H / Real.log X ^ A + C4 * H / Real.log X ^ A) :=
        add_le_add hA1 (add_le_add hC hD)
    _ = (C1 + C3 + C4) * H / Real.log X ^ A := by ring

/-- LEAF. Proposition 2, pages 16 and 17, applied to the residual of eq. 35.
This includes the parameter reductions and subdivision needed for the full H range.
The published inputs are the prime number theorem, Bombieri Vinogradov and the
Rosser Iwaniec sieve of Lemma 3.7. It remains CITED. -/
theorem residual_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          |residualCount X (windowY X ε) (Real.log X ^ B) n|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

/-- LEAF. Page 16 eq. 55 to eq. 9. The logarithm is absorbed by any positive
power of L. This statement only uses real analysis. -/
theorem log_absorption (δ : ℝ) (hδ : 0 < δ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      L ^ (-1 : ℝ) * Real.log L ≤ L ^ (-1 + δ) := by
  obtain ⟨L0, hL⟩ := Filter.eventually_atTop.mp ((isLittleO_log_rpow_atTop hδ).bound zero_lt_one)
  refine ⟨max L0 1, le_max_right _ _, ?_⟩
  intro L h
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) h
  have hLp : 0 < L := by linarith
  have hb : Real.log L ≤ L ^ δ := by
    have hb := hL L (le_trans (le_max_left _ _) h)
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_pos (Real.rpow_pos_of_pos hLp _)] using hb
  calc L ^ (-1 : ℝ) * Real.log L ≤ L ^ (-1 : ℝ) * L ^ δ :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hLp.le _)
    _ = L ^ (-1 + δ) := (Real.rpow_add hLp _ _).symm

/-- LEAF. Page 16 eq. 55 and Proposition 2. Triangle inequality combines the
circle method error and the residual. -/
theorem combine_errors {R V G : ℂ} {a b : ℝ}
    (hV : ‖V - G‖ ≤ a) (hR : ‖V - R‖ ≤ b) : ‖R - G‖ ≤ a + b := by
  calc ‖R - G‖ ≤ ‖R - V‖ + ‖V - G‖ := norm_sub_le_norm_sub_add_norm_sub R V G
    _ = ‖V - R‖ + ‖V - G‖ := by rw [norm_sub_rev R V]
    _ ≤ b + a := add_le_add hR hV
    _ = a + b := add_comm _ _

/-- Theorem 1 assembled from the analytic leaves and the elementary error bounds.
The assembly has no sorry of its own. Its analytic inputs remain CITED. -/
theorem thm1_from_leaves : kumchev_liu_thm1 := by
  intro A hA
  obtain ⟨Bc, hBc, hc⟩ := circle_input A hA
  obtain ⟨Br, hBr, hr⟩ := residual_input A hA
  let B := max Bc Br
  refine ⟨B, lt_of_lt_of_le hBc (le_max_left _ _), ?_⟩
  intro δ ε hδ hε
  obtain ⟨Cc, Kc, Xc, hCc, hKc, hXc, hc⟩ := hc B (le_max_left _ _) ε hε
  obtain ⟨Cr, Kr, Xr, hCr, hKr, hXr, hr⟩ := hr B (le_max_right _ _) δ ε hδ hε
  obtain ⟨L0, hL0, hL⟩ := log_absorption δ hδ
  refine ⟨Cc + Cr, Kc + Kr, max (max Xc Xr) (Real.exp L0),
    by positivity, by positivity, le_trans hXc (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX
  have hXc' : Xc ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXr' : Xr ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have he : Real.exp L0 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : 0 < X := lt_of_lt_of_le (Real.exp_pos _) he
  have hlog : L0 ≤ Real.log X := by
    rw [← Real.log_exp L0]
    exact Real.log_le_log (Real.exp_pos _) he
  let Y := windowY X ε
  let P := Real.log X ^ B
  let badc := fun n => InH2 n ∧ Kc * ‖main2 X Y P n‖ *
    (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
    ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖
  let badr := fun n => InH2 n ∧ Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
    |residualCount X Y P n|
  have sub : ∀ n, (InH2 n ∧ (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) → badc n ∨ badr n := by
    intro n ⟨hn, hbad⟩
    by_contra h
    have hgood := not_or.mp h
    have hcv : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) := by
      exact le_of_not_gt (fun hh => hgood.1 ⟨hn, hh⟩)
    have hrv : |residualCount X Y P n| ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      exact le_of_not_gt (fun hh => hgood.2 ⟨hn, hh⟩)
    have hcv' : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) :=
      hcv.trans (mul_le_mul_of_nonneg_left (hL _ hlog) (by positivity))
    have hrv' : ‖(roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ)‖ ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      have heq : (roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ) =
          (residualCount X Y P n : ℂ) := by
        simp only [residualCount, Complex.ofReal_sub, Complex.ofReal_natCast]
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact hrv
    have hcombined := combine_errors hcv' hrv'
    have heq : Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) +
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) =
        (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by ring
    rw [heq] at hcombined
    exact (not_lt_of_ge hcombined) hbad
  have hcount := le_trans (U1534.cnt_mono sub X H) (U1534.cnt_or_le badc badr X H)
  have hcountR : (cntIoc (fun n => InH2 n ∧
      (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) X H : ℝ) ≤
      (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := by exact_mod_cast hcount
  have hcb := hc X H hXc' hH hHX
  have hrb := hr X H hXr' hH hHX
  calc _ ≤ (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := hcountR
    _ ≤ Cc * H / Real.log X ^ A + Cr * H / Real.log X ^ A := add_le_add hcb hrb
    _ = (Cc + Cr) * H / Real.log X ^ A := by ring

/-- Page 8 display 35. Every prime pair is counted by the sifted count
when the cutoff is below the lower endpoint of I2, so the residual is nonnegative. -/
theorem residualCount_nonneg (X Y P : ℝ) (n : ℕ)
    (hcut : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Real.sqrt Y / 2) :
    0 ≤ residualCount X Y P n := by
  classical
  have hsub : (windowPairs X Y n).filter (fun v => v.1.Prime ∧ v.2.Prime) ⊆
      (windowPairs X Y n).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ)) := by
    intro v hv
    obtain ⟨hv, hp, hq⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨hv, hp, ?_⟩
    intro p hp hdiv
    have heq : p = v.2 := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv
    rw [heq]
    exact hcut.trans (Finset.mem_filter.mp hv).2.2.2.1
  unfold residualCount
  apply sub_nonneg.mpr
  exact_mod_cast Finset.card_le_card hsub

/-- Page 2 before display 4 and Theorem 1. The nonempty interval range
forces Y below X, which justifies natural integer indices in the windows. -/
theorem windowY_lt_of_range {X H ε : ℝ} (hX : 1 < X)
    (hH : X ^ (7 / 18 + ε) ≤ H) (hHX : H ≤ X) : windowY X ε < X := by
  have hexp : 7 / 18 + ε ≤ 1 :=
    (Real.rpow_le_rpow_left_iff hX).mp (by simpa only [Real.rpow_one] using hH.trans hHX)
  have htheta : 7 / 12 + ε / 2 < 1 := by linarith
  simpa only [windowY, Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hX htheta

end LeanLab.KumchevLiu2007.Task129

#print axioms LeanLab.KumchevLiu2007.Task129.roughCount_eq_repR
#print axioms LeanLab.KumchevLiu2007.Task129.singInt_eq_singIntW
#print axioms LeanLab.KumchevLiu2007.Task129.card_iocNat_le
#print axioms LeanLab.KumchevLiu2007.Task129.prop1_meansq
#print axioms LeanLab.KumchevLiu2007.Task129.prop1_meansq_large
#print axioms LeanLab.KumchevLiu2007.Task129.sum_iocNat_cover
#print axioms LeanLab.KumchevLiu2007.Task129.P_sq_le_rpow
#print axioms LeanLab.KumchevLiu2007.Task129.meansq_from_arcs

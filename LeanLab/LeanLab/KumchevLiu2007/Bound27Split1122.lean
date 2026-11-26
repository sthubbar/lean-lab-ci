/-
ROUTE BURST burst-20261122, unit P1122-0143. SPLIT of the LEAF bound27 in
Prep1121KLMajorArc.lean. Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 7,
the display before 27 and display 27 itself.

Display 27 says that the integral of S1* S2* e(-alpha n) over M0 equals
S2(n, P) I(n) up to O(Y^(1/2) P^(-1)). The paper's three steps are:
1. On M0 the arcs are disjoint and S1*, S2* reduce to the one arc term, so the
   integral is a sum over q, a of mu(q) S(q, a) phi(q)^(-2) times an integral
   of T1 T2 e(-n alpha) over one arc. PROVED here as termA_arc_sum.
2. Shifting each arc to the origin and summing over a gives the Gauss sum
   completion A2(n, q) of page 9 display 45, times the integral of T1 T2 e(-n beta)
   over |beta| at most 1/(q Q0). PROVED here as arc_sum_regroup.
3. Completing each integral to [-1/2, 1/2] gives I(n) = singInt, PROVED
   here as fourier_completion, at the cost of the tail beyond 1/(q Q0), which the
   paper bounds by Y^(1/2) P^(-2), tail_bound. The tail is QUESTION Q2:
   the paper derives it from display 22 for T2, false for beta of order one.
   tail_kernel_identity, PROVED, rewrites the tail as a finite sum of f1 f2
   against the kernel K(k) = delta(k) - sin(2 pi k b)/(pi k), and the one
   remaining LEAF, kernel_sum_bound, HARD, is the discrete bound of that sum;
   the notes sketch its proof.
4. |A2(n, q)| at most one, PROVED here as A2_norm_le_one, and q at most P give
   the stated O(Y^(1/2) P^(-1)), hence the BlockErrorBound with P^(-1/4).

bound27_of_leaves proves the exact type of bound27 with no sorry of its own;
its only open input is the LEAF kernel_sum_bound. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc
import LeanLab.KumchevLiu2007.KernelBound687

namespace LeanLab.KumchevLiu2007.Burst1122B27

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. P0088 page 4 display 15: two arcs around reduced fractions a/q and a'/q'
with q, q' at most P, of widths r1 and r2 in q alpha, can share a point only when
the fractions agree, provided P times r1 plus r2 is below one. -/
theorem arcPairs_unique {P r1 r2 α : ℝ} {v w : ℕ × ℕ} (hv : v ∈ arcPairs P)
    (hw : w ∈ arcPairs P) (h1 : |(v.1 : ℝ) * α - v.2| ≤ r1)
    (h2 : |(w.1 : ℝ) * α - w.2| ≤ r2) (hr : P * (r1 + r2) < 1) : v = w := by
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hv hw
  obtain ⟨⟨⟨hv1, hvP⟩, -⟩, -, hvc⟩ := hv
  obtain ⟨⟨⟨hw1, hwP⟩, -⟩, -, hwc⟩ := hw
  have hP1 : 1 ≤ P := Nat.floor_pos.mp (lt_of_lt_of_le Nat.one_pos (hv1.trans hvP))
  have hvP' : (v.1 : ℝ) ≤ P := (Nat.cast_le.mpr hvP).trans (Nat.floor_le (by linarith))
  have hwP' : (w.1 : ℝ) ≤ P := (Nat.cast_le.mpr hwP).trans (Nat.floor_le (by linarith))
  have hr1 : 0 ≤ r1 := (abs_nonneg _).trans h1
  have hr2 : 0 ≤ r2 := (abs_nonneg _).trans h2
  set d : ℤ := (w.2 : ℤ) * v.1 - (v.2 : ℤ) * w.1 with hd
  have hdr : (d : ℝ) = (w.1 : ℝ) * ((v.1 : ℝ) * α - v.2) - (v.1 : ℝ) * ((w.1 : ℝ) * α - w.2) := by
    rw [hd]; push_cast; ring
  have hdabs : |(d : ℝ)| < 1 := by
    rw [hdr]
    have e1 : |(w.1 : ℝ) * ((v.1 : ℝ) * α - v.2)| ≤ P * r1 := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul hwP' h1 (abs_nonneg _) (by linarith)
    have e2 : |(v.1 : ℝ) * ((w.1 : ℝ) * α - w.2)| ≤ P * r2 := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul hvP' h2 (abs_nonneg _) (by linarith)
    calc _ ≤ |(w.1 : ℝ) * ((v.1 : ℝ) * α - v.2)| + |(v.1 : ℝ) * ((w.1 : ℝ) * α - w.2)| :=
          abs_sub _ _
      _ ≤ P * r1 + P * r2 := add_le_add e1 e2
      _ < 1 := by linarith
  have hd0 : d = 0 := by
    have : |d| < 1 := by exact_mod_cast (Int.cast_abs (R := ℝ) (a := d)) ▸ hdabs
    rw [abs_lt] at this; omega
  have heq : v.2 * w.1 = w.2 * v.1 := by
    have : (v.2 : ℤ) * w.1 = (w.2 : ℤ) * v.1 := by omega
    exact_mod_cast this
  have hd1 : v.1 ∣ w.1 := by
    have : v.1 ∣ v.2 * w.1 := ⟨w.2, by rw [heq, mul_comm]⟩
    exact (Nat.Coprime.symm hvc).dvd_of_dvd_mul_left this
  have hd2 : w.1 ∣ v.1 := by
    have : w.1 ∣ w.2 * v.1 := ⟨v.2, by rw [← heq, mul_comm]⟩
    exact (Nat.Coprime.symm hwc).dvd_of_dvd_mul_left this
  have hq : v.1 = w.1 := Nat.dvd_antisymm hd1 hd2
  have ha : v.2 = w.2 := by
    rw [hq] at heq
    exact Nat.eq_of_mul_eq_mul_right (by omega) heq
  exact Prod.ext hq ha

/-- PROVED. P0088 page 4 display 15 and page 6 display 23: on one period the set M0 of
display 23 is the union of the arcs around a/q with q at most P, 0 at most a at most q,
a coprime to q, once the width P^3/Y is below one. -/
theorem Ioc_inter_majorArcs_eq {R0 P : ℝ} (hP1 : 1 ≤ P) (h1 : (R0 / P)⁻¹ < 1) :
    Set.Ioc (0 : ℝ) 1 ∩ majorArcs R0 P =
      ⋃ v ∈ arcPairs P, Set.Ioc (0 : ℝ) 1 ∩ arc (R0 / P) v := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hα, q, hq1, hqP, a, hcop, habs⟩
    obtain ⟨hα0, hα1⟩ := hα
    have hab := abs_le.mp habs
    have hqα : (q : ℝ) * α ≤ q := by
      have : (0:ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    have hqα0 : 0 ≤ (q : ℝ) * α := by positivity
    have ha0' : (-1 : ℝ) < a := by linarith [hab.1, hab.2]
    have haq' : (a : ℝ) < q + 1 := by linarith [hab.1, hab.2]
    have ha0 : (-1 : ℤ) < a := by exact_mod_cast ha0'
    have haq : a < (q : ℤ) + 1 := by exact_mod_cast haq'
    have hqfl : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
    lift a to ℕ using (by omega)
    refine ⟨(q, a), ?_, ⟨hα0, hα1⟩, ?_⟩
    · simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range]
      refine ⟨⟨⟨hq1, hqfl⟩, by omega⟩, by omega, ?_⟩
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
      simpa [Int.gcd_natCast_natCast] using hg
    · show |((q : ℕ) : ℝ) * α - ((a : ℕ) : ℝ)| ≤ (R0 / P)⁻¹
      simpa using habs
  · rintro ⟨v, hv, hα, harc⟩
    refine ⟨hα, v.1, ?_, ?_, (v.2 : ℤ), ?_, ?_⟩
    · simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hv
      exact hv.1.1.1
    · simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hv
      exact (Nat.cast_le.mpr hv.1.1.2).trans (Nat.floor_le (by linarith))
    · simp only [arcPairs, Finset.mem_filter] at hv
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa [Int.gcd_natCast_natCast] using hv.2.2
    · simpa [arc] using harc

/-- PROVED. P0088 page 5 displays 16 and 17: on M0, inside the arc around a/q, the
models S1* and S2* reduce to the single term of that arc, given P times the two widths
P^3/Y and P/H is below one and P^3/Y is at most P/H. -/
theorem S1star_on_arc {X Y H P R0 α : ℝ} {v : ℕ × ℕ} (hv : v ∈ arcPairs P)
    (hδ : (R0 / P)⁻¹ ≤ (H / P)⁻¹) (hs : P * ((R0 / P)⁻¹ + (H / P)⁻¹) < 1)
    (hα : α ∈ arc (R0 / P) v) :
    S1star X Y H P α = ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
      T1 X Y (α - v.2 / v.1) := by
  unfold S1star
  rw [Finset.sum_eq_single v]
  · exact Set.indicator_of_mem (show α ∈ arc (H / P) v from le_trans hα hδ) _
  · intro w hw hne
    apply Set.indicator_of_notMem
    intro hαw
    exact hne (arcPairs_unique hv hw hα hαw hs).symm
  · intro h; exact absurd hv h

/-- PROVED. P0088 page 5 displays 16 and 17, the same reduction for S2*. -/
theorem S2star_on_arc {Y H P R0 α : ℝ} {v : ℕ × ℕ} (hv : v ∈ arcPairs P)
    (hδ : (R0 / P)⁻¹ ≤ (H / P)⁻¹) (hs : P * ((R0 / P)⁻¹ + (H / P)⁻¹) < 1)
    (hα : α ∈ arc (R0 / P) v) :
    S2star Y H P α = U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
      T2 Y P (α - v.2 / v.1) := by
  unfold S2star
  rw [Finset.sum_eq_single v]
  · exact Set.indicator_of_mem (show α ∈ arc (H / P) v from le_trans hα hδ) _
  · intro w hw hne
    apply Set.indicator_of_notMem
    intro hαw
    exact hne (arcPairs_unique hv hw hα hαw hs).symm
  · intro h; exact absurd hv h

/-- PROVED. P0088 page 7, step to display 27: under the width conditions the integral
termA over M0 splits as the sum over the arcs of the single arc terms. -/
theorem termA_eq_general (X Y H P : ℝ) (n : ℕ) (hP1 : 1 ≤ P)
    (hδ : (Y * P ^ (-2 : ℤ) / P)⁻¹ ≤ (H / P)⁻¹)
    (hs : P * ((Y * P ^ (-2 : ℤ) / P)⁻¹ + (H / P)⁻¹) < 1)
    (hδ0 : 0 ≤ (Y * P ^ (-2 : ℤ) / P)⁻¹) :
    termA X Y H P n =
      ∑ v ∈ arcPairs P,
        ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
          (U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ)) *
        ∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc (Y * P ^ (-2 : ℤ) / P) v,
          fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
            (T1 X Y (α - v.2 / v.1) * T2 Y P (α - v.2 / v.1)) := by
  set R0 := Y * P ^ (-2 : ℤ) with hR0
  have hη0 : 0 ≤ (H / P)⁻¹ := hδ0.trans hδ
  have h1 : (R0 / P)⁻¹ < 1 := by nlinarith
  have hss : P * ((R0 / P)⁻¹ + (R0 / P)⁻¹) < 1 := by nlinarith
  unfold termA
  rw [Ioc_inter_majorArcs_eq hP1 h1]
  have hmeas : ∀ v ∈ arcPairs P, MeasurableSet (Set.Ioc (0 : ℝ) 1 ∩ arc (R0 / P) v) :=
    fun v _ => measurableSet_Ioc.inter (measurableSet_arc _ v)
  have hdisj : Set.Pairwise (↑(arcPairs P))
      (Function.onFun Disjoint fun v => Set.Ioc (0 : ℝ) 1 ∩ arc (R0 / P) v) := by
    intro v hv w hw hne
    rw [Function.onFun, Set.disjoint_left]
    rintro α ⟨-, hαv⟩ ⟨-, hαw⟩
    exact hne (arcPairs_unique hv hw hαv hαw hss)
  have he : MemLp (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))) ⊤ volume := by
    simpa only [sub_zero] using fourier_shift_memLp_top (-(n : ℤ)) 0
  have hf : MemLp (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      (S1star X Y H P α * S2star Y H P α)) ⊤ volume :=
    he.mul (r := ⊤) ((S1star_memLp_top X Y H P).mul (r := ⊤) (S2star_memLp_top Y H P))
  have hper : IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      (S1star X Y H P α * S2star Y H P α)) (Set.Ioc (0 : ℝ) 1) :=
    MemLp.integrable (by simp) (hf.mono_measure Measure.restrict_le_self)
  rw [integral_biUnion_finset _ hmeas hdisj (fun v _ => hper.mono_set Set.inter_subset_left)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (hmeas v hv) (fun α hα => ?_)
  rw [S1star_on_arc hv hδ hs hα.2, S2star_on_arc hv hδ hs hα.2]
  ring

/-- PROVED. P0088 page 4 display 14 and page 6 display 23: in the block range, with
4 P^6 at most K = X^(7/18), K at most Y and K P^(-4) at most H at most Y P^(-4), the M0
width P^3/Y is at most the M width P/H, and P times their sum is below one. -/
theorem widths_small {P H Y K : ℝ} (hP1 : 1 ≤ P) (hK : 4 * P ^ 6 ≤ K) (hKY : K ≤ Y)
    (hHlo : K * P ^ (-4 : ℤ) ≤ H) (hHhi : H ≤ Y * P ^ (-4 : ℤ)) :
    (Y * P ^ (-2 : ℤ) / P)⁻¹ ≤ (H / P)⁻¹ ∧
      P * ((Y * P ^ (-2 : ℤ) / P)⁻¹ + (H / P)⁻¹) < 1 ∧
      0 ≤ (Y * P ^ (-2 : ℤ) / P)⁻¹ := by
  have hP : 0 < P := by linarith
  have hP4 : 0 < P ^ 4 := by positivity
  have hP6 : 0 < P ^ 6 := by positivity
  have hKpos : 0 < K := by linarith
  have hY : 0 < Y := by linarith
  have e4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have e2 : P ^ (-2 : ℤ) = (P ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [e4] at hHlo hHhi
  have hKH : K ≤ H * P ^ 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hP4] at hHlo; exact hHlo
  have hHY : H * P ^ 4 ≤ Y := by
    rw [← div_eq_mul_inv, le_div_iff₀ hP4] at hHhi; exact hHhi
  have hH : 0 < H := by
    by_contra h; push Not at h; nlinarith
  have hδe : (Y * P ^ (-2 : ℤ) / P)⁻¹ = P ^ 3 / Y := by
    rw [e2]; field_simp
  have hηe : (H / P)⁻¹ = P / H := inv_div H P
  rw [hδe, hηe]
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
  have hp42 : P ^ 4 = P ^ 2 * P ^ 2 := by ring
  have hp6 : P ^ 6 = P ^ 2 * P ^ 4 := by ring
  refine ⟨?_, ?_, by positivity⟩
  · rw [div_le_div_iff₀ hY hH]
    have : P ^ 3 * H * P ^ 2 ≤ P * Y := by nlinarith
    nlinarith
  · have a1 : P * (P ^ 3 / Y) ≤ 1 / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ hY]
      have : P * P ^ 3 = P ^ 4 := by ring
      rw [this]; nlinarith
    have a2 : P * (P / H) ≤ 1 / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ hH]
      have : 4 * P ^ 2 * P ^ 4 ≤ H * P ^ 4 := by nlinarith
      have h4 : 4 * P ^ 2 ≤ H := le_of_mul_le_mul_right this hP4
      nlinarith
    rw [mul_add]; linarith

/-- PROVED. P0088 page 7, step to display 27, arc disjointness on M0: for large X in the
block range termA splits as the sum over the arcs of the single arc terms. -/
theorem termA_arc_sum :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) → ∀ n : ℕ,
        termA X (windowY X ε) H (Real.log X ^ B) n =
          ∑ v ∈ arcPairs (Real.log X ^ B),
            ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
              (U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ)) *
            ∫ α in Set.Ioc (0 : ℝ) 1 ∩
                arc (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B) v,
              fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
                (T1 X (windowY X ε) (α - v.2 / v.1) *
                  T2 (windowY X ε) (Real.log X ^ B) (α - v.2 / v.1)) := by
  intro B hB ε hε hε'
  have hlit := (isLittleO_log_rpow_rpow_atTop (B * 6)
    (show (0 : ℝ) < 7 / 18 by norm_num)).bound (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp ((Filter.eventually_ge_atTop (3 : ℝ)).and hlit)
  refine ⟨X0, ?_⟩
  intro X H hX hlo hhi n
  obtain ⟨hX3, hbd⟩ := hX0 X hX
  have hX0' : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0']
    exact Real.exp_one_lt_three.le.trans hX3
  set P := Real.log X ^ B with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP6 : Real.log X ^ (B * 6) = P ^ 6 := by
    rw [Real.rpow_mul (by linarith), ← Real.rpow_natCast]; norm_num [hPdef]
  rw [hP6, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0'.le _)] at hbd
  have hK : 4 * P ^ 6 ≤ X ^ (7 / 18 : ℝ) := by linarith
  have hKY : X ^ (7 / 18 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hKX : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hHlo : X ^ (7 / 18 : ℝ) * P ^ (-4 : ℤ) ≤ H :=
    le_trans (mul_le_mul_of_nonneg_right hKX (zpow_nonneg (by linarith) _)) hlo
  obtain ⟨hδ, hs, hδ0⟩ := widths_small hP1 hK hKY hHlo hhi
  exact termA_eq_general X (windowY X ε) H P n hP1 hδ hs hδ0

/-- PROVED. P0088 page 7 display 27: for large X the M0 arc parameter Y P^(-3) exceeds one,
so each M0 arc has half width below 1/q. -/
theorem R_gt_one (B : ℝ) (_hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      1 < windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (3 * B) (by norm_num : (0:ℝ) < 7 / 12)).bound
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (h1.and (Filter.eventually_ge_atTop (3 : ℝ)))
  refine ⟨X0, fun X hX => ?_⟩
  obtain ⟨hb, hX3⟩ := hX0 X hX
  have hXpos : 0 < X := by linarith
  have hL : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    have := Real.exp_one_lt_d9; linarith
  have hLpos : 0 < Real.log X := by linarith
  have hPpos : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hLpos _
  have hP3 : (Real.log X ^ B) ^ (3 : ℕ) = Real.log X ^ (3 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; ring_nf
  have hY : X ^ (7 / 12 : ℝ) ≤ windowY X ε := by
    unfold windowY
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hXp : 0 < X ^ (7 / 12 : ℝ) := Real.rpow_pos_of_pos hXpos _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _),
    Real.norm_of_nonneg hXp.le] at hb
  have hlt : (Real.log X ^ B) ^ (3 : ℕ) < windowY X ε := by rw [hP3]; linarith
  rw [zpow_neg, zpow_two, div_eq_mul_inv, mul_assoc, ← mul_inv, mul_comm (Real.log X ^ B * Real.log X ^ B), ← div_eq_mul_inv, one_lt_div (by positivity)]
  calc (Real.log X ^ B * (Real.log X ^ B * Real.log X ^ B)) = (Real.log X ^ B) ^ (3 : ℕ) := by ring
    _ < _ := hlt

/-- PROVED. P0088 page 4 display 15: the arc M(q, a) is the closed interval
a/q - r/q to a/q + r/q with r = R^(-1). -/
theorem mem_arc_iff (R : ℝ) (q a : ℕ) (hq : 0 < q) (α : ℝ) :
    α ∈ arc R (q, a) ↔ α ∈ Set.Icc ((a : ℝ) / q - R⁻¹ / q) ((a : ℝ) / q + R⁻¹ / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [arc, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  rw [← sub_div, ← add_div, div_le_iff₀ hq', le_div_iff₀ hq']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- PROVED. P0088 page 7 display 27: shifting alpha by c turns e(-n alpha) into
e(-n c) e(-n beta). -/
theorem shift_integral (n : ℕ) (g : ℝ → ℂ) (l u c : ℝ) :
    (∫ α in l..u, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - c)) =
      fourier (-(n : ℤ)) (c : AddCircle (1 : ℝ)) *
        ∫ β in (l - c)..(u - c), fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
  set F : ℝ → ℂ := fun β => fourier (-(n : ℤ)) (c : AddCircle (1 : ℝ)) *
        (fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β) with hF
  have h : ∀ α : ℝ, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - c) = F (α - c) := by
    intro α
    simp only [hF]
    have : fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) = fourier (-(n : ℤ)) (c : AddCircle (1 : ℝ))
        * fourier (-(n : ℤ)) ((α - c : ℝ) : AddCircle (1 : ℝ)) := by
      rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [this]; ring
  calc (∫ α in l..u, fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - c))
      = ∫ α in l..u, F (α - c) := by congr 1; funext α; exact h α
    _ = ∫ β in (l - c)..(u - c), F β := intervalIntegral.integral_comp_sub_right F c
    _ = _ := by rw [hF]; exact intervalIntegral.integral_const_mul _ _

/-- PROVED. P0088 page 9 display 45: e(-n a/q) on the circle is ee(-an/q). -/
theorem fourier_rat (n a q : ℕ) :
    fourier (-(n : ℤ)) (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      U1534.ee (-((a * n : ℕ) : ℝ) / q) := by
  rw [fourier_coe_apply]
  unfold U1534.ee
  congr 1
  push_cast
  ring

/-- PROVED. P0088 page 7: e(-n) on the circle at one is one. -/
theorem fourier_at_one (n : ℕ) :
    fourier (-(n : ℤ)) (((1 : ℝ)) : AddCircle (1 : ℝ)) = 1 := by
  rw [AddCircle.coe_period]
  simp

/-- PROVED. P0088 page 4 display 8: S(1, a) = 1. -/
theorem gaussS_one (a : ℕ) : U1534.gaussS 1 a = 1 := by
  unfold U1534.gaussS
  have h2 : (Finset.range 1).filter (fun x => Nat.Coprime x 1) = {0} := rfl
  rw [h2, Finset.sum_singleton]
  simp [U1534.ee]

/-- PROVED. P0088 page 7 display 27: for q at least 2 and 1 at most a below q, the arc around
a/q of half width R^(-1)/q with R above one lies inside the period, and shifting by a/q gives
e(-an/q) times the integral over the centred interval. -/
theorem term_ge_two (R : ℝ) (hR : 1 < R) (q a : ℕ) (hq : 2 ≤ q) (ha1 : 1 ≤ a) (ha2 : a < q)
    (n : ℕ) (g : ℝ → ℂ) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R (q, a),
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - (a : ℝ) / q)) =
      U1534.ee (-((a * n : ℕ) : ℝ) / q) *
        ∫ β in -(R⁻¹ / q)..(R⁻¹ / q), fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha2' : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha2
  have hr0 : 0 < R⁻¹ := inv_pos.mpr (by linarith)
  have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hset : Set.Ioc (0 : ℝ) 1 ∩ arc R (q, a) =
      Set.Icc ((a : ℝ) / q - R⁻¹ / q) ((a : ℝ) / q + R⁻¹ / q) := by
    ext α
    rw [Set.mem_inter_iff, mem_arc_iff R q a (by omega)]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨⟨?_, ?_⟩, h⟩
      · have : 0 < (a : ℝ) / q - R⁻¹ / q := by
          rw [← sub_div]; exact div_pos (by linarith) hqpos
        linarith [h.1]
      · have : (a : ℝ) / q + R⁻¹ / q ≤ 1 := by
          rw [← add_div, div_le_one hqpos]; linarith
        linarith [h.2]
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (by have : 0 ≤ R⁻¹ / q := by positivity
        linarith), shift_integral, fourier_rat]
  congr 2 <;> ring

/-- PROVED. P0088 page 7 display 27 at q = 1: the half arcs at 0 and at 1 inside the period
join, after the shift at 1, into one integral over the interval from -R^(-1) to R^(-1). -/
theorem term_one (R : ℝ) (hR : 1 < R) (n : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 0),
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) +
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 1),
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) =
      ∫ β in -(R⁻¹ / ((1 : ℕ) : ℝ))..(R⁻¹ / ((1 : ℕ) : ℝ)),
        fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
  have hr0 : 0 < R⁻¹ := inv_pos.mpr (by linarith)
  have hr1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hs0 : Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 0) = Set.Ioc 0 R⁻¹ := by
    ext α
    rw [Set.mem_inter_iff, mem_arc_iff R 1 0 (by norm_num)]
    simp only [Set.mem_Ioc, Set.mem_Icc, Nat.cast_zero, Nat.cast_one, div_one, zero_sub,
      zero_add]
    constructor
    · rintro ⟨⟨h1, _⟩, _, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, by linarith, h2⟩
  have hs1 : Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 1) = Set.Icc (1 - R⁻¹) 1 := by
    ext α
    rw [Set.mem_inter_iff, mem_arc_iff R 1 1 (by norm_num)]
    simp only [Set.mem_Ioc, Set.mem_Icc, Nat.cast_one, div_one]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, _⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1, by linarith⟩
  have hf : Continuous (fun β : ℝ => fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β) := by
    fun_prop
  have h0 : (∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 0),
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) =
      ∫ β in (0 : ℝ)..R⁻¹, fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
    rw [hs0, intervalIntegral.integral_of_le hr0.le]
    simp
  have h1 : (∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R (1, 1),
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))) =
      ∫ β in -R⁻¹..0, fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
    rw [hs1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have := shift_integral n g (1 - R⁻¹) 1 1
    simp only [Nat.cast_one, div_one]
    rw [this, fourier_at_one, one_mul]
    congr 1 <;> ring
  rw [h0, h1, add_comm, intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  simp

/-- PROVED. P0088 page 7 display 27 with page 9 display 45: the sum over the arc pairs q, a
of mu(q) S(q, a) / phi(q)^2 times the arc integrals regroups by q into A2(n, q) times the
integral over the interval from -R^(-1)/q to R^(-1)/q, for any R above one. -/
theorem regroup_general (P R : ℝ) (hR : 1 < R) (n : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    (∑ v ∈ arcPairs P,
        ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
          (U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ)) *
        ∫ α in Set.Ioc (0 : ℝ) 1 ∩ arc R v,
          fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * g (α - v.2 / v.1)) =
      ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q *
        ∫ β in -(R⁻¹ / q)..(R⁻¹ / q), fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * g β := by
  unfold arcPairs
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [← Finset.sum_filter]
  rw [Finset.mem_Icc] at hq
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have hq1 : q = 1 := by omega
    subst hq1
    have hset : (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ 1 ∧ Nat.Coprime a 1) = {0, 1} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
        Nat.coprime_one_right_eq_true, and_true]
      omega
    rw [hset, Finset.sum_pair (by norm_num), U1534.A2_one, one_mul]
    simp only [ArithmeticFunction.moebius_apply_one, Nat.totient_one, gaussS_one]
    norm_num only [Int.cast_one, Nat.cast_one, div_one, one_mul]
    have := term_one R hR n g hg
    simp only [Nat.cast_one, Nat.cast_zero, div_one] at this
    simpa using this
  · have hset : (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q) =
        (Finset.range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, h2, h3⟩
        refine ⟨lt_of_le_of_ne h2 ?_, h3⟩
        rintro rfl
        rw [Nat.coprime_self] at h3; omega
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1.le, h2⟩
    rw [hset]
    unfold U1534.A2
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; rw [Nat.coprime_zero_left] at ha; omega
      · exact h
    simp only
    rw [term_ge_two R hR q a hq2 ha1 ha.1 n g]
    ring

/-- PROVED. P0088 page 5: T1 times T2 is continuous in beta, a finite trigonometric sum. -/
theorem T1T2_continuous (X Y P : ℝ) : Continuous (fun β => T1 X Y β * T2 Y P β) := by
  unfold T1 T2
  fun_prop

/-- PROVED. P0088 page 7 display 27 with page 9 display 45: regrouping of the M0 arc integrals
by q into A2(n, q) times the centred interval integrals. -/
theorem arc_sum_regroup :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ n : ℕ,
        (∑ v ∈ arcPairs (Real.log X ^ B),
            ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
              (U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ)) *
            ∫ α in Set.Ioc (0 : ℝ) 1 ∩
                arc (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B) v,
              fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
                (T1 X (windowY X ε) (α - v.2 / v.1) *
                  T2 (windowY X ε) (Real.log X ^ B) (α - v.2 / v.1))) =
          ∑ q ∈ Finset.Icc 1 ⌊Real.log X ^ B⌋₊, U1534.A2 n q *
            ∫ β in -((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q)..
                ((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q),
              fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
                (T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β) := by
  intro B hB ε hε _
  obtain ⟨X0, hX0⟩ := R_gt_one B hB ε hε
  refine ⟨X0, fun X hX n => ?_⟩
  exact regroup_general (Real.log X ^ B) _ (hX0 X hX) n
    (fun β => T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β)
    (T1T2_continuous _ _ _)

/-- PROVED. P0088 page 7: e(k beta) integrates to one over [-1/2, 1/2] when k = 0 and to
zero otherwise. -/
theorem fourier_interval_integral (k : ℤ) :
    (∫ β in (-(1 / 2 : ℝ))..(1 / 2), fourier k (β : AddCircle (1 : ℝ))) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp only [fourier_zero, intervalIntegral.integral_const, ite_true]
    norm_num
  · rw [if_neg hk]
    have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have h : (fun β : ℝ => fourier k (β : AddCircle (1 : ℝ))) =
        fun β : ℝ => Complex.exp ((2 * π * Complex.I * k) * β) := by
      funext β
      rw [fourier_coe_apply]; push_cast; rw [div_one]
    rw [h, integral_exp_mul_complex hc]
    have e : Complex.exp (2 * π * Complex.I * k * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * k * ((-(1 / 2 : ℝ) : ℝ) : ℂ)) *
          Complex.exp (k * (2 * π * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]

/-- PROVED. P0088 page 7 after display 27, I(n) as the full integral of T1 T2 e(-beta n)
over [-1/2, 1/2], equal to the sum of f1(m1) f2(m2) over m1 + m2^2 = n, that is singInt.
Orthogonality of e(k beta) on one period, finite sums. -/
theorem fourier_completion (X Y P : ℝ) (n : ℕ) :
    (∫ β in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β)) =
      (singInt X Y P n : ℂ) := by
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)
  set a : ℕ → ℂ := fun m => ((1 / Real.log (m : ℝ) : ℝ) : ℂ)
  set b : ℕ → ℂ := fun m => ((f2Weight z0 (m : ℝ) : ℝ) : ℂ)
  have hexp : ∀ β : ℝ, fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β) =
      ∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
        (a m1 * b m2) * fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))
          (β : AddCircle (1 : ℝ)) := by
    intro β
    unfold T1 T2
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m1 _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m2 _ => ?_)
    rw [fourier_add, fourier_add]
    simp only [a, b, z0]
    ring
  simp_rw [hexp]
  have hint : ∀ k : ℤ, IntervalIntegrable (fun β : ℝ => fourier k (β : AddCircle (1 : ℝ)))
      volume (-(1 / 2 : ℝ)) (1 / 2) := fun k =>
    ((fourier k).continuous.comp (AddCircle.continuous_mk' 1)).intervalIntegrable _ _
  have hc1 : ∀ k : ℤ, Continuous (fun β : ℝ => fourier k (β : AddCircle (1 : ℝ))) := fun k =>
    (fourier k).continuous.comp (AddCircle.continuous_mk' 1)
  have hcont : ∀ m1 : ℕ, Continuous (fun β : ℝ => ∑ m2 ∈ squareWindow Y,
      a m1 * b m2 * fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ))) :=
    fun m1 => continuous_finset_sum _ (fun m2 _ => continuous_const.mul (hc1 _))
  rw [intervalIntegral.integral_finsetSum (fun m1 _ => (hcont m1).intervalIntegrable _ _)]
  have hin : ∀ m1 : ℕ, (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ∑ m2 ∈ squareWindow Y,
      a m1 * b m2 * fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ))) =
      ∑ m2 ∈ squareWindow Y, a m1 * b m2 *
        (if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then 1 else 0) := by
    intro m1
    rw [intervalIntegral.integral_finsetSum (f := fun m2 (β : ℝ) => a m1 * b m2 *
        fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ)))
      (fun m2 _ => (continuous_const.mul (hc1 _)).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun m2 _ => ?_)
    rw [intervalIntegral.integral_const_mul, fourier_interval_integral]
  simp_rw [hin]
  rw [← Finset.sum_product' (primeWindow X Y) (squareWindow Y) (fun m1 m2 => a m1 * b m2 *
    (if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0))]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  unfold singInt windowPairs
  push_cast
  apply Finset.sum_congr
  · ext v
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, primeWindow, squareWindow]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      refine ⟨⟨h1, h3⟩, h2.1, h2.2, h4.1, h4.2, ?_⟩
      have := (Nat.cast_pow v.2 2 : ((v.2 ^ 2 : ℕ) : ℤ) = (v.2 : ℤ) ^ 2)
      omega
    · rintro ⟨⟨h1, h3⟩, h2a, h2b, h4a, h4b, h5⟩
      refine ⟨⟨⟨h1, h2a, h2b⟩, h3, h4a, h4b⟩, ?_⟩
      have := (Nat.cast_pow v.2 2 : ((v.2 ^ 2 : ℕ) : ℤ) = (v.2 : ℤ) ^ 2)
      omega
  · intro v _
    simp only [a, b, z0]
    push_cast
    ring

/-- PROVED. P0088 page 7 display 27: the integral of e(k beta) over [-b, b] is 2b for k = 0
and sin(2 pi k b)/(pi k) otherwise. -/
theorem fourier_symm_integral (k : ℤ) (b : ℝ) :
    (∫ β in (-b)..b, fourier k (β : AddCircle (1 : ℝ))) =
      ((if k = 0 then 2 * b else Real.sin (2 * π * k * b) / (π * k) : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · subst hk
    simp only [fourier_zero, intervalIntegral.integral_const, if_pos]
    simp
    ring
  · rw [if_neg hk]
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      simp [hpi, hk', Complex.I_ne_zero]
    have h : (fun β : ℝ => fourier k (β : AddCircle (1 : ℝ))) =
        fun β : ℝ => Complex.exp ((2 * π * Complex.I * k) * β) := by
      funext β
      rw [fourier_coe_apply]; push_cast; rw [div_one]
    rw [h, integral_exp_mul_complex hc]
    push_cast
    rw [Complex.sin]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- PROVED. P0088 page 7 display 27: the integral of T1 T2 e(-n beta) over any interval
expands into the double sum over the two windows of f1 f2 times the integral of e(k beta),
k = m1 + m2^2 - n. -/
theorem integral_expand (X Y P c d : ℝ) (n : ℕ) :
    (∫ β in c..d, fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β)) =
      ∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
        (((1 / Real.log (m1 : ℝ) : ℝ) : ℂ) *
          ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m2 : ℝ) : ℝ) : ℂ)) *
        ∫ β in c..d, fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ)) := by
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)
  set a : ℕ → ℂ := fun m => ((1 / Real.log (m : ℝ) : ℝ) : ℂ)
  set b : ℕ → ℂ := fun m => ((f2Weight z0 (m : ℝ) : ℝ) : ℂ)
  have hexp : ∀ β : ℝ, fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β) =
      ∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
        (a m1 * b m2) * fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))
          (β : AddCircle (1 : ℝ)) := by
    intro β
    unfold T1 T2
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m1 _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m2 _ => ?_)
    rw [fourier_add, fourier_add]
    simp only [a, b, z0]
    ring
  simp_rw [hexp]
  have hc1 : ∀ k : ℤ, Continuous (fun β : ℝ => fourier k (β : AddCircle (1 : ℝ))) := fun k =>
    (fourier k).continuous.comp (AddCircle.continuous_mk' 1)
  have hcont : ∀ m1 : ℕ, Continuous (fun β : ℝ => ∑ m2 ∈ squareWindow Y,
      a m1 * b m2 * fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ))) :=
    fun m1 => continuous_finset_sum _ (fun m2 _ => continuous_const.mul (hc1 _))
  rw [intervalIntegral.integral_finsetSum (fun m1 _ => (hcont m1).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [intervalIntegral.integral_finsetSum (f := fun m2 (β : ℝ) => a m1 * b m2 *
      fourier (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) (β : AddCircle (1 : ℝ)))
    (fun m2 _ => (continuous_const.mul (hc1 _)).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  rw [intervalIntegral.integral_const_mul]

/-- PROVED. P0088 page 7, the display before 27, in kernel form: the full integral minus the
integral over [-b, b] is the sum of f1(m1) f2(m2) K(m1 + m2^2 - n), with K(k) = 1 - 2b at
k = 0 and K(k) = -sin(2 pi k b)/(pi k) otherwise. -/
theorem tail_kernel_identity (X Y P b : ℝ) (n : ℕ) :
    (∫ β in (-(1 / 2 : ℝ))..(1 / 2),
        fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β)) -
      (∫ β in (-b)..b,
        fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) * (T1 X Y β * T2 Y P β)) =
      ((∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
        1 / Real.log (m1 : ℝ) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m2 : ℝ) *
          ((if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then 1 else 0) -
            (if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then 2 * b else
              Real.sin (2 * π * ((-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * b) /
                (π * ((-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) : ℤ) : ℝ)))) : ℝ) : ℂ) := by
  rw [integral_expand, integral_expand, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  rw [fourier_interval_integral, fourier_symm_integral]
  split_ifs <;> push_cast <;> ring

/-- PROVED from kernel_sum_bound and tail_kernel_identity. P0088 page 7, the display before 27:
the integral of T1 T2 e(-beta n) over 1/(q Q0) at most |beta| at most 1/2 is O(Y^(1/2) P^(-2)),
uniformly in q at most P and in n. -/
theorem tail_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        ‖(∫ β in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
              (T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β)) -
          ∫ β in -((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q)..
              ((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q),
            fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
              (T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β)‖ ≤
          C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, hK⟩ := kernel_sum_bound B hB ε hε hε'
  refine ⟨C, X0, hC, fun X hX q hq1 hqP n => ?_⟩
  rw [tail_kernel_identity, Complex.norm_real, Real.norm_eq_abs]
  exact hK X hX q hq1 hqP n

/-- PROVED. P0088 page 3: e(x) has norm one. -/
theorem ee_norm (x : ℝ) : ‖U1534.ee x‖ = 1 := by
  unfold U1534.ee
  have h : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- PROVED. P0088 page 3 display 8: |S(q, a)| is at most phi(q), the number of
reduced residues in the sum. -/
theorem gaussS_norm_le (q a : ℕ) : ‖U1534.gaussS q a‖ ≤ (Nat.totient q : ℝ) := by
  unfold U1534.gaussS
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
      ‖U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))‖ = 1 := fun x _ => ee_norm _
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.totient]
  have : (Finset.range q).filter (fun x => Nat.Coprime x q) =
      (Finset.range q).filter (Nat.Coprime q) := by
    apply Finset.filter_congr
    intro x _
    exact Nat.coprime_comm
  rw [this]

/-- PROVED. P0088 page 9 display 45: |A2(n, q)| is at most one, from
|mu(q)| at most one, |S(q, a)| at most phi(q) and phi(q) terms in a. -/
theorem A2_norm_le_one (n q : ℕ) : ‖U1534.A2 n q‖ ≤ 1 := by
  unfold U1534.A2
  rw [norm_mul]
  have hmu : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  by_cases hq : Nat.totient q = 0
  · simp [hq]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hsum : ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      U1534.gaussS q a * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ ≤
        (Nat.totient q : ℝ) * (Nat.totient q : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖U1534.gaussS q a * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ ≤ (Nat.totient q : ℝ) := by
      intro a _
      rw [norm_mul]
      have he : ‖U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ = 1 := ee_norm _
      rw [he, mul_one]
      exact gaussS_norm_le q a
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
      rw [Nat.totient]
      congr 1
      apply Finset.filter_congr
      intro x _
      exact Nat.coprime_comm
    rw [hc]
  rw [norm_div, norm_pow, Complex.norm_natCast]
  calc ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ / (Nat.totient q : ℝ) ^ 2 *
        ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖
      ≤ 1 / (Nat.totient q : ℝ) ^ 2 * ((Nat.totient q : ℝ) * (Nat.totient q : ℝ)) := by
        gcongr
    _ = 1 := by field_simp

/-- P0088 page 7 display 27 with the block error O(Y^(1/2) P^(-1/4)): the exact type of
the LEAF bound27 of Prep1121KLMajorArc, from the pieces above. No sorry of its own;
the hypotheses h1 and h2 of bound27 are not needed on this route. -/
theorem bound27_of_leaves (_h1 : T1BoundProp) (_h2 : T2BoundProp) :
    BlockErrorBound (fun X Y H P n => termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)) := by
  intro B hB ε hε hε'
  obtain ⟨X1, hA⟩ := termA_arc_sum B hB ε hε hε'
  obtain ⟨X2, hR⟩ := arc_sum_regroup B hB ε hε hε'
  obtain ⟨C, X3, hC, hT⟩ := tail_bound B hB ε hε hε'
  refine ⟨C, max (max X1 X2) (max X3 3), hC, ?_⟩
  intro X H hX hlo hhi n
  have hX1 : X1 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hX
  have hX4 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hX
  set Y := windowY X ε with hY
  set P := Real.log X ^ B with hP
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX4
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hPpos : 0 < P := by linarith
  set F : ℝ → ℂ := fun β => fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
    (T1 X Y β * T2 Y P β) with hF
  set b : ℕ → ℝ := fun q => (Y * P ^ (-2 : ℤ) / P)⁻¹ / q with hb
  have hfull : (singInt X Y P n : ℂ) = ∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β :=
    (fourier_completion X Y P n).symm
  have hser : series2 n P = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q := rfl
  have hid : termA X Y H P n - series2 n P * (singInt X Y P n : ℂ) =
      -∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q *
        ((∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) - ∫ β in -(b q)..(b q), F β) := by
    rw [hA X H hX1 hlo hhi n, hR X hX2 n, hfull, hser, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  show ‖termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)‖ ≤ _
  rw [hid, norm_neg]
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊, ‖U1534.A2 n q *
      ((∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) - ∫ β in -(b q)..(b q), F β)‖ ≤
        C * Real.sqrt Y * P ^ (-2 : ℤ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq1 : 1 ≤ q := hq.1
    have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hPpos.le)
    rw [norm_mul]
    calc ‖U1534.A2 n q‖ * ‖(∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) -
          ∫ β in -(b q)..(b q), F β‖
        ≤ 1 * (C * Real.sqrt Y * P ^ (-2 : ℤ)) :=
          mul_le_mul (A2_norm_le_one n q) (hT X hX3 q hq1 hqP n) (norm_nonneg _) zero_le_one
      _ = C * Real.sqrt Y * P ^ (-2 : ℤ) := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hfl : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hPpos.le
  have hs : 0 ≤ C * Real.sqrt Y := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hz : P * P ^ (-2 : ℤ) ≤ P ^ (-(1 / 4 : ℝ)) := by
    have e1 : P * P ^ (-2 : ℤ) = P ^ (-1 : ℝ) := by
      rw [show (-1 : ℝ) = ((-2 : ℤ) : ℝ) + 1 by norm_num,
        Real.rpow_add hPpos, Real.rpow_intCast, Real.rpow_one, mul_comm]
    rw [e1]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  have hzpos : 0 ≤ P ^ (-2 : ℤ) := (zpow_pos hPpos _).le
  calc ((⌊P⌋₊ : ℕ) : ℝ) * (C * Real.sqrt Y * P ^ (-2 : ℤ))
      ≤ P * (C * Real.sqrt Y * P ^ (-2 : ℤ)) := by
        gcongr
    _ = C * Real.sqrt Y * (P * P ^ (-2 : ℤ)) := by ring
    _ ≤ C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by gcongr

/-- The theorem above has the exact type of the LEAF bound27. -/
example : type_of% @bound27 := bound27_of_leaves

end LeanLab.KumchevLiu2007.Burst1122B27

#print axioms LeanLab.KumchevLiu2007.Burst1122B27.arcPairs_unique
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.Ioc_inter_majorArcs_eq
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.S1star_on_arc
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.S2star_on_arc
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.termA_eq_general
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.widths_small
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.termA_arc_sum
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.R_gt_one
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.mem_arc_iff
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.shift_integral
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.fourier_rat
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.fourier_at_one
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.gaussS_one
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.term_ge_two
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.term_one
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.regroup_general
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.T1T2_continuous
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.arc_sum_regroup
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.fourier_interval_integral
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.fourier_completion
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.fourier_symm_integral
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.integral_expand
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.tail_kernel_identity
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.kernel_sum_bound
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.tail_bound
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.ee_norm
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.gaussS_norm_le
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.A2_norm_le_one
#print axioms LeanLab.KumchevLiu2007.Burst1122B27.bound27_of_leaves

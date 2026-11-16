/-
Split of theorem leaf_eta_cutoff561 in LeanLab.BHP1997.Decomp561m: the eta
cutoff error of display 2.6 on page 8, the mean square over the even
frequencies of the difference between the truncated eta integral and the
complete period integral.
The cut separates the unit coefficient case with the explicit frequency count
from the two elementary interface estimates (count of even frequencies, sign of
the scale). The u times v scaling is bookkeeping and is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561m
import LeanLab.BHP1997.Route512Eta

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- Both principal models carry one common factor u times v in front of the
modulus sum, and nothing else in them depends on u and v. -/
private theorem principalArc_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N = ((u * v : ℝ) : ℂ) * principalArc512 ε D x 1 1 N := by
  unfold principalArc512
  push_cast
  ring

/-- The complete period model of the same display has the same factor. -/
private theorem completePrincipal_units561 (ε D x u v : ℝ) (N : ℕ) :
    completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) * completePrincipal561 ε D x 1 1 N := by
  unfold completePrincipal561
  push_cast
  ring

/-- The eta cutoff difference at any coefficient pair is the unit coefficient
difference multiplied by the common factor. -/
private theorem etaDiff_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N - completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) *
        (principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N) := by
  rw [principalArc_units561 (u := u) (v := v), completePrincipal_units561 (u := u) (v := v),
    principalArc_units561 (u := 1) (v := 1), completePrincipal_units561 (u := 1) (v := 1)]
  simp only [mul_one, Complex.ofReal_one, one_mul]
  ring

/-- The eta cutoff error is quadratic in the two coefficients. -/
private theorem etaTailError_units561 (ε D x u v : ℝ) :
    etaTailError561 ε D x u v = u ^ 2 * v ^ 2 * etaTailError561 ε D x 1 1 := by
  unfold etaTailError561
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [etaDiff_units561, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- LEAF: Display 2.6 on page 8, the eta cutoff error at unit coefficients, with
the number of even frequencies kept explicit instead of replaced by the
frequency interval length. The two removed eta tails are integrated against the
reciprocal square of the distance to the nearest integer and the modulus average
over q divided by phi of q is taken over the full modulus range. The count factor
is handed to the leaves below, so this leaf is weaker than the target in the
coefficient pair, unit coefficients against arbitrary u and v, the quadratic
scaling being proved above, and in its right hand side, which is larger than the
target scale once the count exceeds the interval length. The polynomial tail
reduction and its mean square transfer are what remains open. -/
theorem leaf_eta_tail_unit_coeff561 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100)
    (A : ℝ) (hA : 0 < A) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      etaTailError561 ε D x 1 1 ≤
        C * ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7) := by
  obtain ⟨K, hK, hw⟩ := Route512.weight_le512
  refine ⟨(A + 7) / 2, fun D hD => ?_⟩
  have hD0 : 0 ≤ D := by linarith
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hθ1 : 11 / 20 + ε < 1 := by linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (Route512.large512 (11 / 20 + ε) 0 D hθ hθ1 (by norm_num) hθ)
  refine ⟨max x₀ (K ^ 2), fun x hx => ?_⟩
  obtain ⟨hL, hL', hY4, _, _, hx1⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  set Y := length512 ε x with hYdef
  set L := Real.log x with hLdef
  set R := L ^ D with hRdef
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hR : 1 ≤ R := Real.one_le_rpow hL hD0
  have hR0 : 0 < R := by linarith
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hlogY : Real.log Y = (11 / 20 + ε) * L := Real.log_rpow hx0 _
  have hP : L ^ (2 * D) = R ^ 2 := by
    rw [hRdef, mul_comm, Real.rpow_mul hL0.le, Real.rpow_two]
  have hM : L ^ (4 * D) = R ^ 4 := by
    rw [hRdef, mul_comm, Real.rpow_mul hL0.le]
    exact_mod_cast Real.rpow_natCast (L ^ D) 4
  have hY4' : 4 * R ^ 4 ≤ Y := by rw [← hM]; exact hY4
  have hLL : 1 ≤ |L| * |Real.log Y| := by
    rw [hlogY, abs_of_pos hL0, abs_of_pos (mul_pos hθ hL0)]
    have h1 : 1 ≤ (11 / 20 + ε) * L := by
      have h2 := (div_le_iff₀ hθ).mp hL'
      linarith
    nlinarith
  have hc : ‖(1 : ℂ) / ((L : ℂ) * (Real.log Y : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    exact div_le_self zero_le_one hLL
  have hfourier : ∀ n : ℤ,
      Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) := fun n =>
    (map_continuous (fourier (T := (1 : ℝ)) n)).comp (AddCircle.continuous_mk' 1)
  have hcont : ∀ N : ℕ, Continuous (integrand512 ε x (fun _ => 1) (fun _ => 1) N) := by
    intro N
    unfold integrand512 polynomial512
    have hp : ∀ S : Finset ℕ, Continuous (fun t : ℝ =>
        ∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) := fun S =>
      continuous_finsetSum S fun k _ =>
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℂ))).mul (hfourier (k : ℤ))
    exact ((hp _).mul (hp _)).mul (hfourier (-(N : ℤ)))
  have hpoint : ∀ N : ℕ,
      ‖principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N‖ ≤ K * Y / R := by
    intro N
    let w : ℕ → ℂ := fun q =>
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N
    let F := integrand512 ε x (fun _ => 1) (fun _ => 1) N
    let I : ℕ → ℂ := fun q => ∫ t in (-(R ^ 4 / (q * Y)))..(R ^ 4 / (q * Y)), F t
    let J : ℂ := ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F t
    have he : principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N =
        (1 / ((L : ℂ) * (Real.log Y : ℂ))) *
          ∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, w q * (I q - J) := by
      unfold principalArc512 completePrincipal561
      simp only [Complex.ofReal_one, one_mul]
      change (1 / ((L : ℂ) * (Real.log Y : ℂ))) *
        (∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, w q *
          ∫ t in (-(L ^ (4 * D) / (q * Y)))..(L ^ (4 * D) / (q * Y)), F t) -
        (1 / ((L : ℂ) * (Real.log Y : ℂ))) *
          (∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, w q * J) = _
      rw [hM, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun q _ => (mul_sub (w q) (I q) J).symm)
    have hperq : ∀ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊,
        ‖w q * (I q - J)‖ ≤ K * R * (Y / (2 * R ^ 4)) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      have hqP : (q : ℝ) ≤ R ^ 2 := by
        rw [← hP]
        exact (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hq).2
      have hη : 0 < R ^ 4 / ((q : ℝ) * Y) := by positivity
      have hη2 : R ^ 4 / ((q : ℝ) * Y) ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have ht := Route512.tail_le512 F (hcont N)
        (fun t ht0 ht => Route512.integrand_norm_le512 _ _ _ _ N t ht0 ht)
        (R ^ 4 / ((q : ℝ) * Y)) hη hη2
      have hend : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      rw [hend] at ht
      have hi : ‖I q - J‖ ≤ (q : ℝ) * (Y / (2 * R ^ 4)) := by
        have he : 1 / (2 * (R ^ 4 / ((q : ℝ) * Y))) =
            (q : ℝ) * (Y / (2 * R ^ 4)) := by field_simp
        rw [he] at ht
        simpa only [I, J, neg_div] using ht
      have hq12 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ R := by
        calc
          _ ≤ (R ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hq0.le hqP (by norm_num)
          _ = R := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hR0.le]
      have hwq : ‖w q‖ * (q : ℝ) ≤ K * (q : ℝ) ^ (1 / 2 : ℝ) := (hw q N hq1).2
      rw [norm_mul]
      calc
        _ ≤ ‖w q‖ * ((q : ℝ) * (Y / (2 * R ^ 4))) :=
          mul_le_mul_of_nonneg_left hi (norm_nonneg _)
        _ = (‖w q‖ * (q : ℝ)) * (Y / (2 * R ^ 4)) := by ring
        _ ≤ (K * (q : ℝ) ^ (1 / 2 : ℝ)) * (Y / (2 * R ^ 4)) := by gcongr
        _ ≤ K * R * (Y / (2 * R ^ 4)) := by gcongr
    have hcard : ((Finset.Icc 1 ⌊L ^ (2 * D)⌋₊).card : ℝ) ≤ R ^ 2 := by
      rw [Nat.card_Icc, Nat.add_sub_cancel, ← hP]
      exact Nat.floor_le (by positivity)
    have hsum : ‖∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, w q * (I q - J)‖ ≤ K * Y / R := by
      calc
        _ ≤ ∑ q ∈ Finset.Icc 1 ⌊L ^ (2 * D)⌋₊, K * R * (Y / (2 * R ^ 4)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hperq)
        _ = ((Finset.Icc 1 ⌊L ^ (2 * D)⌋₊).card : ℝ) * (K * R * (Y / (2 * R ^ 4))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ R ^ 2 * (K * R * (Y / (2 * R ^ 4))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = K * Y / R / 2 := by field_simp
        _ ≤ K * Y / R := by
          have h0 : 0 ≤ K * Y / R := by positivity
          linarith only [h0]
    rw [he, norm_mul]
    exact (mul_le_mul hc hsum (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold etaTailError561
  refine (Finset.sum_le_sum (g := fun _ => (K * Y / R) ^ 2) ?_).trans ?_
  · intro N _
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoint N) 2
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hinv : (R ^ 2)⁻¹ ≤ L ^ (-A - 7) := by
      rw [← hP, ← Real.rpow_neg hL0.le]
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have he : ((frequencies512 ε x).card : ℝ) * (K * Y / R) ^ 2 =
        K ^ 2 * ((frequencies512 ε x).card : ℝ) * Y ^ 2 * (R ^ 2)⁻¹ := by ring
    rw [he]
    calc
      _ ≤ K ^ 2 * ((frequencies512 ε x).card : ℝ) * Y ^ 2 * L ^ (-A - 7) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ max x₀ (K ^ 2) * ((frequencies512 ε x).card : ℝ) * Y ^ 2 * L ^ (-A - 7) := by
        gcongr
        exact le_max_right _ _

/-- LEAF: The number of even frequencies in the closed interval from the
ceiling of x to the floor of x plus the interval length. The interval holds at
most the interval length plus one integers, its even part is at most half of
that, and the length is at least one, so three copies of the length cover the
count. This is the step that replaces the explicit count of the unit
coefficient leaf by the interval length factor of the target scale. -/
theorem leaf_frequencies_card561 (ε x : ℝ) (hε : 0 < ε) (hx : 3 ≤ x) :
    ((frequencies512 ε x).card : ℝ) ≤
      3 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
  have hx1 : 1 ≤ x := by linarith
  have hH1 : 1 ≤ H := Real.one_le_rpow hx1 (by
    apply mul_nonneg
    · linarith
    · norm_num)
  unfold frequencies512
  refine (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans ?_
  rw [Nat.card_Icc]
  have hfloor : (⌊x + H⌋₊ : ℝ) ≤ x + H := Nat.floor_le (by linarith)
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  rcases le_or_gt ⌈x⌉₊ (⌊x + H⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    linarith
  · rw [Nat.sub_eq_zero_of_le h.le]
    simp only [Nat.cast_zero]
    linarith

/-- LEAF: The target scale is nonnegative on the range: the positive power of x,
the square of the interval length and the arbitrary negative power of the
logarithm are each nonnegative. This is the step that lets a bound at the
enlarged constant be multiplied by the scale without turning the inequality
around, including at x where one of the three factors vanishes and including at
zero coefficients. -/
theorem leaf_scale_nonneg561 (ε A x : ℝ) (hx : 3 ≤ x) : 0 ≤ scale512 ε A x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  unfold scale512
  positivity

/-- The assembly: the target statement follows from the unit coefficient leaf,
the frequency count leaf and the sign of the scale, with the constant of the
unit coefficient leaf enlarged by the coefficient square and by the count
factor three. The eta cutoff error at general coefficients is recovered from the
unit coefficient error by the proved quadratic scaling. -/
theorem leaf_eta_cutoff561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaTailError561 ε D x u v ≤ C * scale512 ε A x := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε hε' u v A hA
  obtain ⟨D₀, hD₀⟩ := leaf_eta_tail_unit_coeff561 ε hε hε' A hA
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₀ D hD
  refine ⟨max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3, fun x hx => ?_⟩
  have hCx : C₁ ≤ x := by
    have h : C₁ ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_left C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  have hx3 : 3 ≤ x := by
    have h : (3 : ℝ) ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  set card : ℝ := ((frequencies512 ε x).card : ℝ) with hcard_def
  set Y : ℝ := length512 ε x with hY_def
  set lg : ℝ := Real.log x ^ (-A - 7) with hlg_def
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH_def
  have huv : 0 ≤ u ^ 2 * v ^ 2 := by positivity
  have hcard0 : 0 ≤ card := by
    rw [hcard_def]
    exact Nat.cast_nonneg _
  have hY0 : 0 ≤ Y ^ 2 := by positivity
  have hlg0 : 0 ≤ lg := by
    rw [hlg_def]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hP0 : 0 ≤ card * Y ^ 2 * lg := mul_nonneg (mul_nonneg hcard0 hY0) hlg0
  have hcardH : card ≤ 3 * H := by
    rw [hcard_def, hH_def]
    exact leaf_frequencies_card561 ε x hε hx3
  have hstep : etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := by
    have h := hC₁ x hCx
    rw [hcard_def, hY_def, hlg_def]
    exact h
  have hK : etaTailError561 ε D x 1 1 ≤ max C₁ 0 * card * Y ^ 2 * lg := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (C₁ : ℝ) 0) hP0
    calc etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := hstep
      _ = C₁ * (card * Y ^ 2 * lg) := by ring
      _ ≤ max C₁ 0 * (card * Y ^ 2 * lg) := hm
      _ = max C₁ 0 * card * Y ^ 2 * lg := by ring
  have hKH : max C₁ 0 * card * Y ^ 2 * lg ≤ max C₁ 0 * (3 * H) * Y ^ 2 * lg := by
    have h0 : 0 ≤ max C₁ 0 * (Y ^ 2 * lg) :=
      mul_nonneg (le_max_right (C₁ : ℝ) 0) (mul_nonneg hY0 hlg0)
    have hm := mul_le_mul_of_nonneg_right hcardH h0
    calc max C₁ 0 * card * Y ^ 2 * lg = card * (max C₁ 0 * (Y ^ 2 * lg)) := by ring
      _ ≤ (3 * H) * (max C₁ 0 * (Y ^ 2 * lg)) := hm
      _ = max C₁ 0 * (3 * H) * Y ^ 2 * lg := by ring
  have hmain : etaTailError561 ε D x u v ≤
      u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg) := by
    rw [etaTailError_units561]
    exact (mul_le_mul_of_nonneg_left hK huv).trans (mul_le_mul_of_nonneg_left hKH huv)
  have hscale_eq : H * Y ^ 2 * lg = scale512 ε A x := by
    rw [hH_def, hY_def, hlg_def]
    unfold scale512
    ring
  have hscale0 : 0 ≤ H * Y ^ 2 * lg := by
    rw [hscale_eq]
    exact leaf_scale_nonneg561 ε A x hx3
  have hcoef : 3 * (u ^ 2 * v ^ 2) * max C₁ 0 ≤
      max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
    have hm : max (3 * (u ^ 2 * v ^ 2) * C₁) 0 = 3 * (u ^ 2 * v ^ 2) * max C₁ 0 := by
      rw [mul_max_of_nonneg C₁ 0 (by positivity : (0 : ℝ) ≤ 3 * (u ^ 2 * v ^ 2)), mul_zero]
    rw [← hm]
    refine max_le ?_ ?_
    · linarith [le_max_right C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    · linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
  have hlast : u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg)
      = (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := by ring
  rw [hlast] at hmain
  calc etaTailError561 ε D x u v
      ≤ (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := hmain
    _ ≤ (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * (H * Y ^ 2 * lg) :=
        mul_le_mul_of_nonneg_right hcoef hscale0
    _ = (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * scale512 ε A x := by
        rw [hscale_eq]

end LeanLab.BHP1997.Decomp561m

/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 4 to 7, displays 13 to 28,
the major arc analysis behind `Task556b.major_arc_transference`.

RESULT OF THIS FILE. The conclusion of `Task556b.major_arc_transference` is
refuted here for every A > 4, B ≥ 1 and 0 < ε < 5/18, see
`major_arc_conclusion_fails`. So that leaf is false whenever its two
character hypotheses hold, and no route theorem with its statement is given.
The statement of `Task556b.short_character_major_error` is refuted outright,
see `short_character_major_error_statement_fails`, so the three open leaves
it is derived from are jointly inconsistent. Nothing below uses them.

REASON. The paper takes Y = X^θ1 and H = Y^θ2 with θ2 below one, so that
Q = H / P is at most Q0 = Y / P^3 and the arcs of display 23 lie inside the
arcs of display 15. The Lean statements fix Y = X^(7/12 + ε/2) and let H run
up to X^(1 - ε), which exceeds Y by a power of X when ε < 5/18. For H equal to
X^(1 - ε) the major arcs of display 15 have total length at most 6 P^2 / H, so
the major arc integral of display 28 is at most a negative power of X times
Y^(1/2), while the main term S2(n, P) I(n) is at least Y^(1/2) / (16 (log X)^2)
for some n in every block of 2 P^2 consecutive integers just above X.

Every declaration below is proved in full: the covering and length bound for
the major arcs of display 15, the trivial bound for the major arc integral of
display 28, the block average of the partial singular series of display 7,
the lower bound for the sum I(n) of page 7, and the two refutations.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556b

namespace LeanLab.KumchevLiu2007.Eq33RouteC

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology

/-- P0088 page 4 display 15: on the unit period the major arcs are covered by
the arcs of radius P / (q H) about a / q with 1 ≤ q ≤ P and 0 ≤ a ≤ q + 1. -/
theorem majorArcs_unit_subset (H P : ℝ) (hH : 0 < H) (hPH : P ≤ H) :
    Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P ⊆
      ⋃ q ∈ Finset.Icc 1 ⌊P⌋₊, ⋃ a ∈ Finset.range (q + 2),
        Set.Icc (((a : ℝ) - P / H) / q) (((a : ℝ) + P / H) / q) := by
  rintro α ⟨⟨h0, h1⟩, q, hq1, hqP, a, -, habs⟩
  rw [inv_div] at habs
  have hle : P / H ≤ 1 := (div_le_one hH).mpr hPH
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  obtain ⟨hl, hu⟩ := abs_le.mp habs
  have hqα : 0 < (q : ℝ) * α := mul_pos hq0 h0
  have hqα1 : (q : ℝ) * α ≤ q := by nlinarith
  have ha0 : 0 ≤ a := by
    have h : (-1 : ℝ) < (a : ℝ) := by linarith
    have h' : (-1 : ℤ) < a := by exact_mod_cast h
    omega
  lift a to ℕ using ha0
  have haq : a < q + 2 := by
    have h : (a : ℝ) ≤ (q : ℝ) + 1 := by
      have : ((a : ℤ) : ℝ) = (a : ℝ) := by norm_cast
      rw [this] at hl hu
      linarith
    have h' : a ≤ q + 1 := by exact_mod_cast h
    omega
  have hcast : ((a : ℤ) : ℝ) = (a : ℝ) := by norm_cast
  rw [hcast] at hl hu
  simp only [Set.mem_iUnion, Finset.mem_Icc, Finset.mem_range, exists_prop]
  refine ⟨q, ⟨hq1, Nat.le_floor hqP⟩, a, haq, ?_, ?_⟩
  · rw [div_le_iff₀ hq0]
    linarith
  · rw [le_div_iff₀ hq0]
    linarith

/-- P0088 page 4 display 15 with display 14: on the unit period the major arcs
have total length at most 6 P^2 / H. -/
theorem majorArcs_unit_volume_le (H P : ℝ) (hP : 0 < P) (hH : 0 < H) (hPH : P ≤ H) :
    volume (Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P) ≤ ENNReal.ofReal (6 * P ^ 2 / H) := by
  have hr : 0 ≤ P / H := by positivity
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊, ∀ a ∈ Finset.range (q + 2),
      volume (Set.Icc (((a : ℝ) - P / H) / q) (((a : ℝ) + P / H) / q)) =
        ENNReal.ofReal (2 * (P / H) / q) := by
    intro q _ a _
    rw [Real.volume_Icc]
    congr 1
    ring
  have hinner : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊,
      (∑ _a ∈ Finset.range (q + 2), 2 * (P / H) / (q : ℝ)) ≤ 6 * (P / H) := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    push_cast
    nlinarith
  have hreal : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, ∑ _a ∈ Finset.range (q + 2),
      2 * (P / H) / (q : ℝ)) ≤ 6 * P ^ 2 / H := by
    calc
      _ ≤ ∑ _q ∈ Finset.Icc 1 ⌊P⌋₊, 6 * (P / H) := Finset.sum_le_sum hinner
      _ = (⌊P⌋₊ : ℝ) * (6 * (P / H)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
      _ ≤ P * (6 * (P / H)) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hP.le) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ volume (⋃ q ∈ Finset.Icc 1 ⌊P⌋₊, ⋃ a ∈ Finset.range (q + 2),
        Set.Icc (((a : ℝ) - P / H) / q) (((a : ℝ) + P / H) / q)) :=
      measure_mono (majorArcs_unit_subset H P hH hPH)
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, volume (⋃ a ∈ Finset.range (q + 2),
        Set.Icc (((a : ℝ) - P / H) / q) (((a : ℝ) + P / H) / q)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, ∑ a ∈ Finset.range (q + 2),
        volume (Set.Icc (((a : ℝ) - P / H) / q) (((a : ℝ) + P / H) / q)) :=
      Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, ∑ _a ∈ Finset.range (q + 2),
        ENNReal.ofReal (2 * (P / H) / q) :=
      Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun a ha => hterm q hq a ha
    _ = ENNReal.ofReal (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, ∑ _a ∈ Finset.range (q + 2),
        2 * (P / H) / (q : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro a _
        positivity
      · intro q _
        exact Finset.sum_nonneg fun a _ => by positivity
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- P0088 page 7 display 28, left side: the major arc integral of
S1 S2 e(-αn) is at most the number of pairs of display 12 times the total
length 6 P^2 / H of the major arcs of display 15. -/
theorem major_integral_norm_le (X Y H P : ℝ) (hP : 0 < P) (hH : 0 < H) (hPH : P ≤ H)
    (n : ℕ) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          representationPolynomial X Y P (α : AddCircle (1 : ℝ))‖ ≤
      ((roughPairs X Y P).card : ℝ) * (6 * P ^ 2 / H) := by
  have hv := majorArcs_unit_volume_le H P hP hH hPH
  have hfin : volume (Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P) < ⊤ :=
    lt_of_le_of_lt hv ENNReal.ofReal_lt_top
  have hreal : volume.real (Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P) ≤ 6 * P ^ 2 / H := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hv
  calc
    _ ≤ ((roughPairs X Y P).card : ℝ) *
        volume.real (Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P) := by
      apply norm_setIntegral_le_of_norm_le_const hfin
      intro α _
      rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      exact representationPolynomial_norm_le_card X Y P _
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)

/-- P0088 page 7 display 28 read backwards: the major contribution error is at
least the main term S2(n, P) I(n) minus the trivial bound for the major arc
integral. When H exceeds Y by a power of X the subtracted term is a negative
power of X times Y^(1/2), so display 28 cannot hold there. -/
theorem majorError_norm_ge (X Y H P : ℝ) (hP : 0 < P) (hH : 0 < H) (hPH : P ≤ H)
    (n : ℕ) :
    ‖series2 n P * (singInt X Y P n : ℂ)‖ -
        ((roughPairs X Y P).card : ℝ) * (6 * P ^ 2 / H) ≤
      ‖majorError X Y H P n‖ := by
  rw [majorError_eq_major_integral]
  have h1 := major_integral_norm_le X Y H P hP hH hPH n
  have h2 := norm_sub_norm_le (series2 n P * (singInt X Y P n : ℂ))
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
          representationPolynomial X Y P (α : AddCircle (1 : ℝ)))
  rw [norm_sub_rev] at h2
  linarith

/-- P0088 page 4 display 12 with page 2 display 5: the number of pairs is at
most the product of the two window sizes. -/
theorem roughPairs_card_le (X Y P : ℝ) :
    (roughPairs X Y P).card ≤ (primeWindow X Y).card * (squareWindow Y).card := by
  classical
  rw [roughPairs_eq_product, Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)

/-- P0088 page 7 display 28 against the pointwise conclusion of
`Task556b.major_arc_transference`: any pointwise bound E for the major
contribution error forces the main term S2(n, P) I(n) to be at most E plus the
trivial major arc bound. This is the inequality that the candidate
counterexample violates. -/
theorem main_term_le_of_majorError_le (X Y H P E : ℝ) (hP : 0 < P) (hH : 0 < H)
    (hPH : P ≤ H) (n : ℕ) (hE : ‖majorError X Y H P n‖ ≤ E) :
    ‖series2 n P * (singInt X Y P n : ℂ)‖ ≤
      E + ((primeWindow X Y).card : ℝ) * ((squareWindow Y).card : ℝ) *
        (6 * P ^ 2 / H) := by
  have h1 := majorError_norm_ge X Y H P hP hH hPH n
  have h2 : ((roughPairs X Y P).card : ℝ) ≤
      ((primeWindow X Y).card : ℝ) * ((squareWindow Y).card : ℝ) := by
    exact_mod_cast roughPairs_card_le X Y P
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 6 * P ^ 2 / H by positivity)
  linarith

/-- P0088 page 2 display 7: the additive character e(-an/q) is the n-th power
of e(-a/q). -/
theorem ee_neg_mul_div (a n q : ℕ) :
    U1534.ee (-((a * n : ℕ) : ℝ) / q) = U1534.ee (-(a : ℝ) / q) ^ n := by
  unfold U1534.ee
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- P0088 page 3 notation: e(x) has absolute value one. -/
theorem norm_ee (x : ℝ) : ‖U1534.ee x‖ = 1 := by
  unfold U1534.ee
  have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- P0088 page 2 display 7: e(-a/q) is a q-th root of unity. -/
theorem ee_neg_div_pow (a q : ℕ) (hq : 0 < q) : U1534.ee (-(a : ℝ) / q) ^ q = 1 := by
  unfold U1534.ee
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-(a : ℤ), ?_⟩
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

/-- P0088 page 2 display 7: e(-a/q) is not one when 0 < a < q. -/
theorem ee_neg_div_ne_one (a q : ℕ) (ha : 0 < a) (haq : a < q) :
    U1534.ee (-(a : ℝ) / q) ≠ 1 := by
  intro h
  unfold U1534.ee at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast ha.trans haq
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hx : ((-(a : ℝ) / q : ℝ) : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hk]
    ring
  have hr : -(a : ℝ) / q = (k : ℝ) := by exact_mod_cast hx
  rw [div_eq_iff hq0.ne'] at hr
  have hz : (a : ℤ) = -k * q := by
    have : (a : ℝ) = -(k : ℝ) * q := by linarith
    exact_mod_cast this
  have hd : (q : ℤ) ∣ (a : ℤ) := ⟨-k, by rw [hz]; ring⟩
  have hd' : q ∣ a := Int.natCast_dvd_natCast.mp hd
  exact absurd (Nat.le_of_dvd ha hd') (by omega)

/-- P0088 page 2 display 7: a nontrivial q-th root of unity summed over any
block of consecutive exponents gives at most q in absolute value. -/
theorem root_block_sum_norm_le (w : ℂ) (q : ℕ) (hq0 : 0 < q) (hw : ‖w‖ = 1)
    (hq : w ^ q = 1) (h1 : w ≠ 1) (N0 N : ℕ) :
    ‖∑ n ∈ Finset.Ico N0 (N0 + N), w ^ n‖ ≤ q := by
  have hs : ∑ n ∈ Finset.Ico N0 (N0 + N), w ^ n =
      w ^ N0 * ∑ i ∈ Finset.range N, w ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    simp [pow_add]
  have hr : ∑ i ∈ Finset.range N, w ^ i = ∑ i ∈ Finset.range (N % q), w ^ i := by
    have hne : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    apply mul_right_cancel₀ hne
    rw [geom_sum_mul, geom_sum_mul]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod N q]
    rw [pow_add, pow_mul, hq, one_pow, one_mul]
  rw [hs, hr, norm_mul, norm_pow, hw, one_pow, one_mul]
  calc
    _ ≤ ∑ i ∈ Finset.range (N % q), ‖w ^ i‖ := norm_sum_le _ _
    _ = ((N % q : ℕ) : ℝ) := by simp [norm_pow, hw]
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq0).le

/-- P0088 page 2 display 8: the Gauss sum S(q, a) is at most φ(q) in absolute value. -/
theorem gaussS_norm_le (q a : ℕ) : ‖U1534.gaussS q a‖ ≤ (Nat.totient q : ℝ) := by
  have hc : ((Finset.range q).filter (fun x => Nat.Coprime x q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext x
    simp [Nat.coprime_comm]
  unfold U1534.gaussS
  calc
    _ ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        ‖U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))‖ := norm_sum_le _ _
    _ = (Nat.totient q : ℝ) := by
      simp only [norm_ee, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hc

/-- P0088 page 2 display 7: for a modulus q at least 2 the term A2(n, q) of the
singular series, summed over any block of consecutive n, is at most q in
absolute value. -/
theorem A2_block_sum_norm_le (q : ℕ) (hq : 2 ≤ q) (N0 N : ℕ) :
    ‖∑ n ∈ Finset.Ico N0 (N0 + N), U1534.A2 n q‖ ≤ q := by
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hc : ((Finset.range q).filter (fun x => Nat.Coprime x q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext x
    simp [Nat.coprime_comm]
  have h : ∑ n ∈ Finset.Ico N0 (N0 + N), U1534.A2 n q =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) *
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a *
            ∑ n ∈ Finset.Ico N0 (N0 + N), U1534.ee (-(a : ℝ) / q) ^ n := by
    unfold U1534.A2
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ee_neg_mul_div]
  have hcoef : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2)‖ ≤
      1 / (Nat.totient q : ℝ) ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_intCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hsum : ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      U1534.gaussS q a *
        ∑ n ∈ Finset.Ico N0 (N0 + N), U1534.ee (-(a : ℝ) / q) ^ n‖ ≤
      (Nat.totient q : ℝ) * ((Nat.totient q : ℝ) * q) := by
    calc
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖U1534.gaussS q a *
            ∑ n ∈ Finset.Ico N0 (N0 + N), U1534.ee (-(a : ℝ) / q) ^ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (Nat.totient q : ℝ) * q := by
        refine Finset.sum_le_sum fun a ha => ?_
        obtain ⟨har, hac⟩ := Finset.mem_filter.mp ha
        have haq : a < q := Finset.mem_range.mp har
        have ha0 : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · subst h0
            rw [Nat.coprime_zero_left] at hac
            omega
          · exact h0
        rw [norm_mul]
        exact mul_le_mul (gaussS_norm_le q a)
          (root_block_sum_norm_le _ q (by omega) (norm_ee _)
            (ee_neg_div_pow a q (by omega)) (ee_neg_div_ne_one a q ha0 haq) N0 N)
          (norm_nonneg _) hφ.le
      _ = _ := by
        rw [Finset.sum_const, hc, nsmul_eq_mul]
  rw [h, norm_mul]
  calc
    _ ≤ 1 / (Nat.totient q : ℝ) ^ 2 * ((Nat.totient q : ℝ) * ((Nat.totient q : ℝ) * q)) :=
      mul_le_mul hcoef hsum (norm_nonneg _) (by positivity)
    _ = q := by
      field_simp

/-- P0088 page 2 display 7: over any block of N consecutive integers n the
partial singular series S2(n, P) sums to N up to an error of at most the
square of the integer part of P. -/
theorem series2_block_sum (P : ℝ) (hP : 1 ≤ P) (N0 N : ℕ) :
    ‖(∑ n ∈ Finset.Ico N0 (N0 + N), series2 n P) - (N : ℂ)‖ ≤ ((⌊P⌋₊ : ℝ)) ^ 2 := by
  have hm : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by exact_mod_cast hP)
  unfold series2
  rw [Finset.sum_comm, ← Finset.insert_Icc_add_one_left_eq_Icc hm, Finset.sum_insert (by simp)]
  have h1 : ∑ n ∈ Finset.Ico N0 (N0 + N), U1534.A2 n 1 = (N : ℂ) := by
    simp [U1534.A2_one]
  rw [h1, add_sub_cancel_left]
  calc
    _ ≤ ∑ q ∈ Finset.Icc (1 + 1) ⌊P⌋₊, ‖∑ n ∈ Finset.Ico N0 (N0 + N), U1534.A2 n q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _q ∈ Finset.Icc (1 + 1) ⌊P⌋₊, (⌊P⌋₊ : ℝ) := by
      refine Finset.sum_le_sum fun q hq => ?_
      obtain ⟨hq2, hqm⟩ := Finset.mem_Icc.mp hq
      exact (A2_block_sum_norm_le q hq2 N0 N).trans (by exact_mod_cast hqm)
    _ ≤ (⌊P⌋₊ : ℝ) * (⌊P⌋₊ : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : ⌊P⌋₊ + 1 - (1 + 1) ≤ ⌊P⌋₊)
    _ = _ := by ring

/-- P0088 page 2 display 7: every block of N consecutive integers with N at
least twice the square of the integer part of P contains an n at which the
partial singular series S2(n, P) has absolute value at least one half. -/
theorem exists_series2_ge_half (P : ℝ) (hP : 1 ≤ P) (N0 N : ℕ)
    (hN : 2 * ⌊P⌋₊ ^ 2 ≤ N) :
    ∃ n ∈ Finset.Ico N0 (N0 + N), 1 / 2 ≤ ‖series2 n P‖ := by
  have hm : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by exact_mod_cast hP)
  have hNpos : 0 < N := by nlinarith
  by_contra hcon
  push Not at hcon
  have hne : (Finset.Ico N0 (N0 + N)).Nonempty :=
    ⟨N0, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hlt : ∑ n ∈ Finset.Ico N0 (N0 + N), ‖series2 n P‖ <
      ∑ _n ∈ Finset.Ico N0 (N0 + N), (1 / 2 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne hcon
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hlt
  have hup : ‖∑ n ∈ Finset.Ico N0 (N0 + N), series2 n P‖ < (N : ℝ) / 2 := by
    have h := norm_sum_le (Finset.Ico N0 (N0 + N)) (fun n => series2 n P)
    have hcast : ((N0 + N - N0 : ℕ) : ℝ) = (N : ℝ) := by
      congr 1
      omega
    rw [hcast] at hlt
    linarith
  have hb := series2_block_sum P hP N0 N
  have hlow : (N : ℝ) - ((⌊P⌋₊ : ℝ)) ^ 2 ≤
      ‖∑ n ∈ Finset.Ico N0 (N0 + N), series2 n P‖ := by
    have h := norm_sub_norm_le (N : ℂ) (∑ n ∈ Finset.Ico N0 (N0 + N), series2 n P)
    rw [norm_sub_rev, Complex.norm_natCast] at h
    linarith
  have hN' : 2 * ((⌊P⌋₊ : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

/-- P0088 page 15, the function f2 after display 51: when the lower limit z0
exceeds one and is at most the square root of u, the integral term is
nonnegative, so f2(u) is at least 1 / log u. -/
theorem f2Weight_ge {z0 u : ℝ} (h1 : 1 < z0) (h2 : z0 ^ 2 ≤ u) :
    1 / Real.log u ≤ f2Weight z0 u := by
  have hz0 : 0 < z0 := by linarith
  have hsu : z0 ≤ Real.sqrt u := (Real.le_sqrt' hz0).mpr h2
  have hsu1 : 1 < Real.sqrt u := lt_of_lt_of_le h1 hsu
  have hu0 : 0 ≤ u := le_trans (sq_nonneg z0) h2
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
  unfold f2Weight
  have hint : 0 ≤ ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) := by
    apply intervalIntegral.integral_nonneg hsu
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le h1 ht.1
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos ht1
    have hut : 1 < u / t := by
      rw [one_lt_div ht0]
      nlinarith [ht.2, mul_pos (sub_pos.mpr hsu1) (show (0 : ℝ) < Real.sqrt u by linarith)]
    have hlu : 0 < Real.log (u / t) := Real.log_pos hut
    exact (one_div_pos.mpr (mul_pos (mul_pos ht0 hlt) hlu)).le
  linarith

/-- P0088 page 2 display 5: the members of the square root window and their squares. -/
theorem squareWindow_sq_bounds {Y : ℝ} (hY : 0 ≤ Y) {m : ℕ} (hm : m ∈ squareWindow Y) :
    Real.sqrt Y / 2 ≤ (m : ℝ) ∧ (m : ℝ) < Real.sqrt Y ∧
      Y / 4 ≤ (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 < Y := by
  simp only [squareWindow, Finset.mem_filter] at hm
  obtain ⟨-, hl, hu⟩ := hm
  have hs := Real.sq_sqrt hY
  have hs0 := Real.sqrt_nonneg Y
  refine ⟨hl, hu, ?_, ?_⟩ <;> nlinarith

/-- P0088 page 2 display 5: the square root window has at least Y^(1/2) / 2 - 1 members. -/
theorem squareWindow_card_ge (Y : ℝ) :
    Real.sqrt Y / 2 - 1 ≤ ((squareWindow Y).card : ℝ) := by
  have hs0 := Real.sqrt_nonneg Y
  have hsub : Finset.Ico ⌈Real.sqrt Y / 2⌉₊ ⌈Real.sqrt Y⌉₊ ⊆ squareWindow Y := by
    intro m hm
    simp only [squareWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
      Nat.ceil_le, Nat.lt_ceil] at hm ⊢
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hm.2.le), hm.1, hm.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hc' : ((⌈Real.sqrt Y⌉₊ - ⌈Real.sqrt Y / 2⌉₊ : ℕ) : ℝ) ≤
      ((squareWindow Y).card : ℝ) := by exact_mod_cast hc
  rw [Nat.cast_sub (Nat.ceil_mono (by linarith))] at hc'
  have h1 := Nat.le_ceil (Real.sqrt Y)
  have h2 := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.sqrt Y / 2)
  linarith

/-- P0088 page 2 display 5: the square root window has at most Y^(1/2) + 1 members. -/
theorem squareWindow_card_le (Y : ℝ) :
    ((squareWindow Y).card : ℝ) ≤ Real.sqrt Y + 1 := by
  have h : (squareWindow Y).card ≤ ⌊Real.sqrt Y⌋₊ + 1 := by
    unfold squareWindow
    exact (Finset.card_filter_le _ _).trans (by simp)
  have h' : ((squareWindow Y).card : ℝ) ≤ (⌊Real.sqrt Y⌋₊ : ℝ) + 1 := by exact_mod_cast h
  linarith [Nat.floor_le (Real.sqrt_nonneg Y)]

/-- P0088 page 7, the sum I(n) after display 27 with the page 15 choices of f1
and f2: for X ≤ n ≤ X + Y / 8 every m2 of the square root window gives a pair,
and each term is at least 1 / (log X)^2. -/
theorem singInt_ge (X Y P : ℝ) (n : ℕ) (hY : 16 ≤ Y) (hYX : Y ≤ X - 2)
    (hz1 : 1 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ))
    (hz2 : (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) ^ 2 ≤ Real.sqrt Y / 2)
    (hn1 : X ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ X + Y / 8) :
    (Real.sqrt Y / 2 - 1) * (1 / Real.log X ^ 2) ≤ singInt X Y P n := by
  classical
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsY : 4 ≤ Real.sqrt Y :=
    (Real.le_sqrt' (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num; linarith)
  have hsYY : Real.sqrt Y ≤ Y := by nlinarith [Real.sq_sqrt hY0]
  have hX1 : 1 < X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX1
  have hpt : ∀ v ∈ windowPairs X Y n, 1 / Real.log X ^ 2 ≤
      (1 / Real.log (v.1 : ℝ)) *
        f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ) := by
    intro v hv
    simp only [windowPairs, Finset.mem_filter] at hv
    obtain ⟨-, h1l, h1u, h2l, h2u, -⟩ := hv
    have hv1 : 1 < (v.1 : ℝ) := by linarith
    have hv2 : 1 < (v.2 : ℝ) := by linarith
    have hl1 : 0 < Real.log (v.1 : ℝ) := Real.log_pos hv1
    have hl2 : 0 < Real.log (v.2 : ℝ) := Real.log_pos hv2
    have hl1X : Real.log (v.1 : ℝ) ≤ Real.log X := Real.log_le_log (by linarith) h1u.le
    have hl2X : Real.log (v.2 : ℝ) ≤ Real.log X :=
      Real.log_le_log (by linarith) (by linarith)
    have hf := f2Weight_ge hz1 (hz2.trans h2l)
    have ha : 1 / Real.log X ≤ 1 / Real.log (v.1 : ℝ) := one_div_le_one_div_of_le hl1 hl1X
    have hb : 1 / Real.log X ≤
        f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ) :=
      (one_div_le_one_div_of_le hl2 hl2X).trans hf
    have h0 : 0 ≤ 1 / Real.log X := by positivity
    calc
      1 / Real.log X ^ 2 = (1 / Real.log X) * (1 / Real.log X) := by ring
      _ ≤ _ := mul_le_mul ha hb h0 (h0.trans ha)
  have hcard : (squareWindow Y).card ≤ (windowPairs X Y n).card := by
    apply Finset.card_le_card_of_injOn (fun m => (n - m ^ 2, m))
    · intro m hm
      have hm' : m ∈ squareWindow Y := by simpa using hm
      obtain ⟨hl, hu, hql, hqu⟩ := squareWindow_sq_bounds hY0 hm'
      have hmn : m ^ 2 ≤ n := by
        have : ((m ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
          push_cast
          linarith
        exact_mod_cast this
      have hcast : ((n - m ^ 2 : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) ^ 2 := by
        rw [Nat.cast_sub hmn]
        push_cast
        ring
      have hmr : m < ⌊Real.sqrt Y⌋₊ + 1 := by
        simp only [squareWindow, Finset.mem_filter, Finset.mem_range] at hm'
        exact hm'.1
      show (n - m ^ 2, m) ∈ windowPairs X Y n
      simp only [windowPairs, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, Finset.mem_range]
      refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hmr⟩, ?_, ?_, hl, hu,
        Nat.sub_add_cancel hmn⟩
      · rw [hcast]
        linarith
      · rw [hcast]
        linarith
      · rw [hcast]
        linarith
    · intro a _ b _ h
      simpa using congrArg Prod.snd h
  have hcr : ((squareWindow Y).card : ℝ) ≤ ((windowPairs X Y n).card : ℝ) := by
    exact_mod_cast hcard
  unfold singInt
  calc
    _ ≤ ((windowPairs X Y n).card : ℝ) * (1 / Real.log X ^ 2) :=
      mul_le_mul_of_nonneg_right ((squareWindow_card_ge Y).trans hcr) (by positivity)
    _ = ∑ _v ∈ windowPairs X Y n, 1 / Real.log X ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hpt

/-- P0088 page 4 display 14: a fixed power of log X is eventually below any
positive multiple of any positive power of X. -/
theorem log_rpow_le_eventually (s e c : ℝ) (he : 0 < e) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop, Real.log X ^ s ≤ c * X ^ e := by
  have ht := (isLittleO_log_rpow_rpow_atTop s he).bound hc
  filter_upwards [ht, Filter.eventually_gt_atTop (1 : ℝ)] with X hsmall hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hy : 0 < X ^ e := Real.rpow_pos_of_pos (by linarith) _
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL s), abs_of_pos hy]
    using hsmall

/-- P0088 page 7 display 28 against the conclusion of
`Task556b.major_arc_transference`. With Y = X^(7/12 + ε/2) fixed and
H = X^(1 - ε), which the written range allows and which exceeds Y by a power
of X when ε < 5/18, the pointwise bound C Y / (log X)^A for the squared major
contribution error fails for every A > 4: the major arcs of display 15 are
too short to carry the main term S2(n, P) I(n). No hypothesis on characters
enters. Hence the two character hypotheses of that leaf cannot both hold with
its conclusion in this range, and the leaf is false as soon as they hold. -/
theorem major_arc_conclusion_fails (A B ε : ℝ) (hA : 4 < A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hε1 : ε < 5 / 18) :
    ¬ ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  rintro ⟨C, X0, hC, hX0, hall⟩
  have hθ : (0 : ℝ) < 7 / 12 + ε / 2 := by linarith
  have hκ : (0 : ℝ) < 1 - ε - (7 / 12 + ε / 2) := by linarith
  have e1 := log_rpow_le_eventually (2 * B + 2) ((7 / 12 + ε / 2) * (1 / 4)) (1 / 2)
    (by positivity) (by norm_num)
  have e2 := log_rpow_le_eventually (2 * B + 2) (7 / 12 + ε / 2) (1 / 32) hθ (by norm_num)
  have e3 := log_rpow_le_eventually (2 * B + 2) (1 - ε - (7 / 12 + ε / 2)) (1 / 400) hκ
    (by norm_num)
  have e4 : ∀ᶠ X : ℝ in Filter.atTop, 256 * C ≤ Real.log X ^ (A - 4) :=
    ((tendsto_rpow_atTop (by linarith : 0 < A - 4)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop (256 * C)
  have e5 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have e6 : ∀ᶠ X : ℝ in Filter.atTop, 16 ≤ X ^ (7 / 12 + ε / 2) :=
    (tendsto_rpow_atTop hθ).eventually_ge_atTop 16
  have e7 := Filter.eventually_ge_atTop (max X0 3)
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and e7)))))).exists
  have hXX0 : X0 ≤ X := (le_max_left _ _).trans h7
  have hX3 : 3 ≤ X := (le_max_right _ _).trans h7
  have hXpos : 0 < X := by linarith
  have hYeq : windowY X ε = X ^ (7 / 12 + ε / 2) := rfl
  have hL0 : 0 < Real.log X := by linarith
  -- abbreviations
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = windowY X ε := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = X ^ (1 - ε) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.log X ^ B := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.log X ^ (2 * B + 2) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Y ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hY16 : 16 ≤ Y := by rw [hYdef, hYeq]; exact h6
  have hY0 : 0 < Y := by linarith
  have hHpos : 0 < H := by rw [hHdef]; exact Real.rpow_pos_of_pos hXpos _
  have hP2 : 2 ≤ P := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Real.log X) hB
    rw [Real.rpow_one] at h
    rw [hPdef]
    linarith
  have hPpos : 0 < P := by linarith
  have hPsq : P ^ 2 * Real.log X ^ 2 = T := by
    rw [hTdef, hPdef, show 2 * B + 2 = B + B + 2 by ring, Real.rpow_add hL0,
      Real.rpow_add hL0, Real.rpow_two]
    ring
  have hP4 : 4 ≤ P ^ 2 := by
    have h := mul_le_mul hP2 hP2 (by norm_num) hPpos.le
    rw [sq]
    linarith
  have hT1 : P ^ 2 ≤ T := by
    rw [← hPsq]
    have hL2sq : (1 : ℝ) ≤ Real.log X ^ 2 := by
      have h := mul_le_mul h5 h5 (by norm_num) hL0.le
      rw [sq]
      linarith
    exact le_mul_of_one_le_right (sq_nonneg P) hL2sq
  have hT4 : 4 ≤ T := hP4.trans hT1
  have hTY : T ≤ 1 / 32 * Y := by rw [hTdef, hYdef, hYeq]; exact h2
  have hκeq : X ^ (1 - ε - (7 / 12 + ε / 2)) * Y = H := by
    rw [hYdef, hYeq, hHdef, ← Real.rpow_add hXpos]
    congr 1
    ring
  have hTH : 384 * T * Y < H := by
    have h := mul_le_mul_of_nonneg_right h3 hY0.le
    rw [mul_assoc, hκeq, ← hTdef] at h
    linarith
  have hHX : H ≤ X := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
      (by linarith : 1 - ε ≤ 1)
    rw [Real.rpow_one] at h
    rw [hHdef]
    exact h
  have hYX : Y ≤ X - 2 := by
    have h := mul_le_mul_of_nonneg_right hT4 hY0.le
    linarith
  have hrange1 : X ^ (7 / 18 + ε) ≤ H := by
    rw [hHdef]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hPH : P ≤ H := by
    have h1' : P ≤ P ^ 2 := by
      rw [sq]
      exact le_mul_of_one_le_left hPpos.le (by linarith)
    have h2' := mul_nonneg (show (0 : ℝ) ≤ T by linarith) (show (0 : ℝ) ≤ 384 * Y - 1 by linarith)
    linarith
  have hWeq : W = X ^ ((7 / 12 + ε / 2) * (1 / 4)) := by
    rw [hWdef, hYdef, hYeq, ← Real.rpow_mul hXpos.le]
  have hTW : T ≤ 1 / 2 * W := by rw [hTdef, hWeq]; exact h1
  have hW0 : 0 < W := by linarith
  have hWW : W ^ 2 = Real.sqrt Y := by
    rw [hWdef, Real.sqrt_eq_rpow, sq, ← Real.rpow_add hY0]
    norm_num
  have hzdef : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) = W / P ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, hWdef]
  have hP2pos : 0 < P ^ 2 := by positivity
  have hz1 : 1 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) := by
    rw [hzdef, one_lt_div hP2pos]
    linarith
  have hz2 : (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) ^ 2 ≤ Real.sqrt Y / 2 := by
    rw [hzdef]
    have hle : W / P ^ 2 ≤ W / 4 := by
      rw [div_le_div_iff₀ hP2pos (by norm_num)]
      have h := mul_le_mul_of_nonneg_left hP4 hW0.le
      linarith
    have hq0 : 0 ≤ W / P ^ 2 := by positivity
    have hsq := pow_le_pow_left₀ hq0 hle 2
    have hexp : (W / 4) ^ 2 = W ^ 2 / 16 := by ring
    rw [hexp, hWW] at hsq
    linarith [Real.sqrt_nonneg Y]
  have hsY : 4 ≤ Real.sqrt Y :=
    (Real.le_sqrt' (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num; linarith)
  -- the integer n
  obtain ⟨n, hnmem, hser⟩ := exists_series2_ge_half P (by linarith) ⌈X⌉₊
    (2 * ⌊P⌋₊ ^ 2) le_rfl
  obtain ⟨hnl, hnu⟩ := Finset.mem_Ico.mp hnmem
  have hn1 : X ≤ (n : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hnl)
  have hn2 : (n : ℝ) ≤ X + Y / 8 := by
    have hlt : (n : ℝ) < (⌈X⌉₊ : ℝ) + 2 * (⌊P⌋₊ : ℝ) ^ 2 := by exact_mod_cast hnu
    have hc := Nat.ceil_lt_add_one hXpos.le
    have hf : (⌊P⌋₊ : ℝ) ^ 2 ≤ P ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hPpos.le) 2
    linarith
  have hsing := singInt_ge X Y P n hY16 hYX hz1 hz2 hn1 hn2
  -- the assumed bound
  have hmaj := hall X H hXX0 hrange1 (by rw [hHdef]) n
  rw [← hYdef, ← hPdef] at hmaj
  have hLA : Real.log X ^ A = Real.log X ^ (A - 4) * Real.log X ^ 4 := by
    rw [← Real.rpow_natCast (Real.log X) 4, ← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  have hL4 : 0 < Real.log X ^ 4 := by positivity
  have hLA4 : 0 < Real.log X ^ (A - 4) := Real.rpow_pos_of_pos hL0 _
  have hEsq : C * Y / Real.log X ^ A ≤ (Real.sqrt Y / (16 * Real.log X ^ 2)) ^ 2 := by
    have hexp : (Real.sqrt Y / (16 * Real.log X ^ 2)) ^ 2 = Y / (256 * Real.log X ^ 4) := by
      rw [div_pow, Real.sq_sqrt hY0.le]
      ring
    rw [hexp, hLA, div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ Y * Real.log X ^ 4 * (Real.log X ^ (A - 4) - 256 * C) :=
      mul_nonneg (by positivity) (by linarith)
    linarith [h0]
  have hmajE : ‖majorError X Y H P n‖ ≤ Real.sqrt Y / (16 * Real.log X ^ 2) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hmaj.trans hEsq)
  have hmain := main_term_le_of_majorError_le X Y H P _ hPpos hHpos hPH n hmajE
  have hsing0 : 0 ≤ singInt X Y P n := by
    refine le_trans ?_ hsing
    have : 0 ≤ Real.sqrt Y / 2 - 1 := by linarith
    positivity
  have hprod : 1 / 2 * singInt X Y P n ≤ ‖series2 n P * (singInt X Y P n : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hser (le_abs_self _) hsing0 (norm_nonneg _)
  have hr : 0 < 1 / (16 * Real.log X ^ 2) := by positivity
  have hsl : 2 * (Real.sqrt Y * (1 / (16 * Real.log X ^ 2))) ≤
      1 / 2 * singInt X Y P n := by
    have h : (Real.sqrt Y / 4) * (1 / Real.log X ^ 2) ≤
        (Real.sqrt Y / 2 - 1) * (1 / Real.log X ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hexp : 2 * (Real.sqrt Y * (1 / (16 * Real.log X ^ 2))) =
        1 / 2 * ((Real.sqrt Y / 4) * (1 / Real.log X ^ 2)) := by ring
    rw [hexp]
    linarith
  have hc1 : ((primeWindow X Y).card : ℝ) ≤ 2 * Y :=
    primeWindow_card_le (by linarith) (by linarith)
  have hc2 : ((squareWindow Y).card : ℝ) ≤ 2 * Real.sqrt Y := by
    linarith [squareWindow_card_le Y]
  have hcc : ((primeWindow X Y).card : ℝ) * ((squareWindow Y).card : ℝ) *
      (6 * P ^ 2 / H) ≤ (2 * Y) * (2 * Real.sqrt Y) * (6 * P ^ 2 / H) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul hc1 hc2 (Nat.cast_nonneg _) (by positivity)) (by positivity)
  have hkey : 24 * Y * P ^ 2 / H < 1 / (16 * Real.log X ^ 2) := by
    rw [div_lt_div_iff₀ hHpos (by positivity)]
    have h384 : 24 * Y * P ^ 2 * (16 * Real.log X ^ 2) = 384 * T * Y := by
      rw [← hPsq]
      ring
    rw [h384]
    linarith
  have hfin : (2 * Y) * (2 * Real.sqrt Y) * (6 * P ^ 2 / H) <
      Real.sqrt Y * (1 / (16 * Real.log X ^ 2)) := by
    have hexp : (2 * Y) * (2 * Real.sqrt Y) * (6 * P ^ 2 / H) =
        Real.sqrt Y * (24 * Y * P ^ 2 / H) := by ring
    rw [hexp]
    exact mul_lt_mul_of_pos_left hkey (by linarith)
  have hE : Real.sqrt Y / (16 * Real.log X ^ 2) =
      Real.sqrt Y * (1 / (16 * Real.log X ^ 2)) := by ring
  linarith

/-- P0088 page 7 display 28 against the statement of
`Task556b.short_character_major_error`: that statement, which asks for the
pointwise major arc bound for every A > 0 on the whole written range of H
with Y = X^(7/12 + ε/2) fixed, is false. It fails at A = 5 and ε = 1/10. -/
theorem short_character_major_error_statement_fails :
    ¬ ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
          ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
              C * windowY X ε / Real.log X ^ A := by
  intro hall
  obtain ⟨B0, -, hB⟩ := hall 5 (by norm_num)
  exact major_arc_conclusion_fails 5 (max B0 1) (1 / 10) (by norm_num)
    (le_max_right _ _) (by norm_num) (by norm_num)
    (hB (max B0 1) (le_max_left _ _) (1 / 10) (by norm_num))

end LeanLab.KumchevLiu2007.Eq33RouteC

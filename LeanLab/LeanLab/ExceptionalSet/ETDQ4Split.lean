/-
Unit P1122-0113, burst-20261122, CLOUD S25. Split of the named hypothesis
`DQLemma4.ErdosTuranDQ4`, the Erdős–Turán inequality in the explicit form of L. Kuipers and
H. Niederreiter, Uniform Distribution of Sequences, Wiley 1974, chapter 2, Theorem 2.5,
display (2.33), page 112, copy in `papers/KuipersNiederreiter1974-ch2.pdf`, PDF pages 23 to 27,
read from the page images.

`erdosTuranDQ4_split` proves `ErdosTuranDQ4` itself, the definition unchanged, from the steps
below and the Fejér kernel step of `ETDQ4Fejer.lean`, with no `sorry` anywhere: every step was
first stated as a LEAF and then proved in the same session. The steps follow the paper's
proof, pages 110 and 112 to 114:
1. `leaf_count_eq_discR`, the count over `[a, b)` is `R_N(b) - R_N(a) + N(b - a)`, the
   definition of `R_N` on page 110 and the identity behind (2.40).
2. `leaf_discR_arc`, `R_N` has slope `-N` and jumps that add up to at most `N` over a period,
   the facts behind "For `b < t ≤ b + D*_N` we have `Δ_N(t) ≥ D*_N + b - t`", page 113.
3. `leaf_discR_intervalIntegrable`, `R_N` is integrable, implicit in (2.27) to (2.36).
4. `leaf_discR_fourier`, display (2.29), page 110, in the form (2.35), page 112.
5. `leaf_fejer_expand`, display (2.36), page 113, with the shift of the integration interval
   "because of the periodicity of the integrand".

DECISION, recorded in the notes: the paper first proves the bound for sequences with
`∫ Δ_N = 0`, display (2.34), and then shifts the sequence, display (2.41). Here the same
inequality is proved for `Δ_N - ∫ Δ_N` directly; the count over an interval only sees
differences `Δ_N(b) - Δ_N(a)`, so subtracting the constant replaces the shift. Every other
display is used as printed. The supremum `D*_N` is approached by points `b` with
`|Δ_N(b) - μ| > d` for `d < D`, which replaces the paper's `Δ_N(b + 0) = D*_N`.

PROVED, no hypothesis: `ErdosTuranDQ4` is no longer a citation wall. `lemma4_of_lemma10_split`
gives P0082 Lemma 4 CONDITIONAL ON the cited Karacuba `Lemma10` only.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.ETDQ4Fejer

namespace LeanLab.ExceptionalSet.ETDQ4

open Real Finset Filter MeasureTheory
open scoped Topology
open LeanLab.ExceptionalSet.U1539 (eC norm_eC)

/-- The function `R_N(x) = A([0, x); N) - N x` of Kuipers and Niederreiter, page 110, for the
points `{f n}`, `n ∈ s`, extended with period 1 to `ℝ` as on page 112, line 1 of the proof of
Theorem 2.5. `N` is `s.card`. -/
noncomputable def discR (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  ((s.filter (fun n => Int.fract (f n) < Int.fract x)).card : ℝ) - (s.card : ℝ) * Int.fract x

/-- `R_N` has period 1, as extended on page 112. -/
theorem discR_add_one (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) :
    discR s f (x + 1) = discR s f x := by
  simp [discR, Int.fract_add_one]

lemma count_split (s : Finset ℕ) (g : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    ((s.filter (fun n => a ≤ g n ∧ g n < b)).card : ℝ)
      = ((s.filter (fun n => g n < b)).card : ℝ) - ((s.filter (fun n => g n < a)).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := s.filter (fun n => g n < b))
    (fun n => g n < a)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : s.filter (fun n => g n < b ∧ g n < a) = s.filter (fun n => g n < a) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le h hab, h⟩
  have e2 : s.filter (fun n => g n < b ∧ ¬ g n < a) = s.filter (fun n => a ≤ g n ∧ g n < b) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => ⟨not_lt.mp h.2, h.1⟩
    · exact fun h => ⟨h.2, not_lt.mpr h.1⟩
  rw [e1, e2] at h
  have h' : ((s.filter (fun n => g n < a)).card : ℝ) + ((s.filter (fun n => a ≤ g n ∧ g n < b)).card : ℝ)
      = ((s.filter (fun n => g n < b)).card : ℝ) := by exact_mod_cast h
  linarith

lemma C_mono (s : Finset ℕ) (f : ℕ → ℝ) {x y : ℝ} (h : x ≤ y) :
    ((s.filter (fun n => Int.fract (f n) < x)).card : ℝ)
      ≤ ((s.filter (fun n => Int.fract (f n) < y)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right s
    (fun n _ (hn : Int.fract (f n) < x) => lt_of_lt_of_le hn h))

lemma C_le (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) :
    ((s.filter (fun n => Int.fract (f n) < x)).card : ℝ) ≤ (s.card : ℝ) := by
  exact_mod_cast Finset.card_filter_le _ _

/-- the definition of `A([a, b); N)` and `R_N`, page 110: for `0 ≤ a ≤ b ≤ 1` the number
of points in `[a, b)` minus `(b - a) N` is `R_N(b) - R_N(a)`, the identity behind (2.40); at
`b = 1` it uses `R_N(1) = R_N(0) = 0`. -/
theorem leaf_count_eq_discR (s : Finset ℕ) (f : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    ((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)
        - (b - a) * s.card = discR s f b - discR s f a := by
  rw [count_split s (fun n => Int.fract (f n)) a b hab]
  rcases lt_or_eq_of_le hb with hb1 | hb1
  · have fb : Int.fract b = b := Int.fract_eq_self.mpr ⟨by linarith, hb1⟩
    have fa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha, by linarith⟩
    simp only [discR, fb, fa]
    ring
  · subst hb1
    have e : s.filter (fun n => Int.fract (f n) < 1) = s := by
      apply Finset.filter_true_of_mem
      intro n _
      exact Int.fract_lt_one _
    rw [e]
    rcases lt_or_eq_of_le hab with ha1 | ha1
    · have fa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha, ha1⟩
      have e0 : s.filter (fun n => Int.fract (f n) < 0) = ∅ := by
        apply Finset.filter_false_of_mem
        intro n _
        exact not_lt.mpr (Int.fract_nonneg _)
      simp only [discR, fa, Int.fract_one, e0]
      simp
      ring
    · subst ha1
      rw [e]
      simp [discR]

/-- page 113, "For `b < t ≤ b + D*_N`, we have `Δ_N(t) = D*_N + Δ_N(t) - Δ_N(b + 0) ≥
D*_N + b - t`": `R_N` decreases with slope `N` between its jumps, and its jumps are positive,
so `R_N(t) - R_N(u) + N(t - u)`, the number of points in the arc `[u, t)` mod 1, lies between
`0` and `N` when `u ≤ t ≤ u + 1`. -/
theorem leaf_discR_arc (s : Finset ℕ) (f : ℕ → ℝ) (u t : ℝ) (hut : u ≤ t) (htu : t ≤ u + 1) :
    0 ≤ discR s f t - discR s f u + (s.card : ℝ) * (t - u) ∧
      discR s f t - discR s f u + (s.card : ℝ) * (t - u) ≤ s.card := by
  set d : ℤ := ⌊t⌋ - ⌊u⌋ with hd
  have hdr : (d : ℝ) = (t - u) - (Int.fract t - Int.fract u) := by
    simp only [hd, Int.cast_sub, Int.fract]; ring
  have ft0 := Int.fract_nonneg t
  have ft1 := Int.fract_lt_one t
  have fu0 := Int.fract_nonneg u
  have fu1 := Int.fract_lt_one u
  have hlo : (-1 : ℝ) < d := by rw [hdr]; linarith
  have hhi : (d : ℝ) < 2 := by rw [hdr]; linarith
  have hlo' : -1 < d := by exact_mod_cast hlo
  have hhi' : d < 2 := by exact_mod_cast hhi
  have hC0 := C_le s f (Int.fract t)
  have hC1 := C_le s f (Int.fract u)
  have hN0 : (0 : ℝ) ≤ ((s.filter (fun n => Int.fract (f n) < Int.fract t)).card : ℝ) := by positivity
  have hN1 : (0 : ℝ) ≤ ((s.filter (fun n => Int.fract (f n) < Int.fract u)).card : ℝ) := by positivity
  have key : discR s f t - discR s f u + (s.card : ℝ) * (t - u)
      = ((s.filter (fun n => Int.fract (f n) < Int.fract t)).card : ℝ)
        - ((s.filter (fun n => Int.fract (f n) < Int.fract u)).card : ℝ) + (s.card : ℝ) * d := by
    rw [hdr]; simp only [discR]; ring
  rw [key]
  have hd01 : d = 0 ∨ d = 1 := by omega
  rcases hd01 with h0 | h1
  · have hxy : Int.fract u ≤ Int.fract t := by
      have : (d : ℝ) = 0 := by exact_mod_cast h0
      linarith
    have := C_mono s f hxy
    rw [h0]; simp only [Int.cast_zero, mul_zero, add_zero]
    constructor <;> linarith
  · have hxy : Int.fract t ≤ Int.fract u := by
      have : (d : ℝ) = 1 := by exact_mod_cast h1
      linarith
    have := C_mono s f hxy
    rw [h1]; simp only [Int.cast_one, mul_one]
    constructor <;> linarith

theorem discR_measurable (s : Finset ℕ) (f : ℕ → ℝ) : Measurable (discR s f) := by
  have : discR s f = fun x => (∑ n ∈ s, if Int.fract (f n) < Int.fract x then (1:ℝ) else 0)
      - (s.card : ℝ) * Int.fract x := by
    funext x
    simp [discR, Finset.sum_boole]
  rw [this]
  refine Measurable.sub ?_ (measurable_const.mul measurable_fract)
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt measurable_const measurable_fract

theorem discR_abs_le (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) : |discR s f x| ≤ s.card := by
  have h1 : ((s.filter (fun n => Int.fract (f n) < Int.fract x)).card : ℝ) ≤ s.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have h0 : (0:ℝ) ≤ ((s.filter (fun n => Int.fract (f n) < Int.fract x)).card : ℝ) := by positivity
  have hf0 := Int.fract_nonneg x
  have hf1 := (Int.fract_lt_one x).le
  have hc : (0:ℝ) ≤ s.card := by positivity
  unfold discR
  rw [abs_le]
  constructor <;> nlinarith

/-- `R_N` is a step function minus a sawtooth, so it is integrable on every interval, as
the integrals (2.27) to (2.36) use. -/
theorem leaf_discR_intervalIntegrable (s : Finset ℕ) (f : ℕ → ℝ) (u v : ℝ) :
    IntervalIntegrable (discR s f) volume u v := by
  have hm := discR_measurable s f
  have key : ∀ a b : ℝ, IntegrableOn (discR s f) (Set.Ioc a b) volume := fun a b =>
    Measure.integrableOn_of_bounded (M := (s.card : ℝ)) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs]; exact discR_abs_le s f x))
  exact ⟨key u v, key v u⟩

lemma eC_mul' (h : ℕ) (x : ℝ) :
    eC ((h : ℝ) * x) = Complex.exp ((2 * (π : ℂ) * Complex.I * (h : ℂ)) * (x : ℂ)) := by
  unfold eC; congr 1; push_cast; ring

lemma hasDerivAt_expc (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (x : ℂ)) * c) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * (x : ℂ)) * c) (x : ℂ) := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul c).cexp
    simpa using this
  exact h1.comp_ofReal

lemma cont_expc (c : ℂ) : Continuous (fun y : ℝ => Complex.exp (c * (y : ℂ))) := by
  fun_prop

lemma integral_expc (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Complex.exp (c * (x : ℂ)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c)
      (Complex.exp (c * (x : ℂ))) x := by
    intro x _
    have := (hasDerivAt_expc c x).div_const c
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((cont_expc c).intervalIntegrable _ _)]
  ring

lemma integral_x_expc (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, (x : ℂ) * Complex.exp (c * (x : ℂ)) =
      (Complex.exp c) / c - (Complex.exp c - 1) / c ^ 2 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun y : ℝ => (y : ℂ) * Complex.exp (c * (y : ℂ)) / c - Complex.exp (c * (y : ℂ)) / c ^ 2)
      ((x : ℂ) * Complex.exp (c * (x : ℂ))) x := by
    intro x _
    have h1 := (((hasDerivAt_id x).ofReal_comp).mul (hasDerivAt_expc c x)).div_const c
    have h2 := (hasDerivAt_expc c x).div_const (c ^ 2)
    refine (h1.sub h2).congr_deriv ?_
    simp only [id, Complex.ofReal_one]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

/-- display (2.29), page 110, in the form (2.35), page 112: for an integer `h ≠ 0`,
`∫_0^1 R_N(x) e(hx) dx = -(1/(2πih)) Σ_n e(h x_n)`, here with `x_n = {f n}` and
`e(h {f n}) = e(h f n)`. -/
theorem leaf_discR_fourier (s : Finset ℕ) (f : ℕ → ℝ) (h : ℕ) (hh : 1 ≤ h) :
    ∫ x in (0 : ℝ)..1, (discR s f x : ℂ) * eC ((h : ℝ) * x) =
      -(1 / (2 * (π : ℂ) * Complex.I * (h : ℂ))) * ∑ n ∈ s, eC ((h : ℝ) * f n) := by
  set c : ℂ := 2 * (π : ℂ) * Complex.I * (h : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have : (h : ℂ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
    simp [hcdef, Real.pi_ne_zero, Complex.I_ne_zero, this]
  have hc1 : Complex.exp c = 1 := by
    have := Complex.exp_nat_mul_two_pi_mul_I h
    rw [← this]; congr 1; rw [hcdef]; ring
  set E : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ)) with hE
  have hEc : Continuous E := cont_expc c
  let y : ℕ → ℝ := fun n => Int.fract (f n)
  -- ae rewrite
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) 1 →
      (discR s f x : ℂ) * eC ((h : ℝ) * x) =
        (∑ n ∈ s, (Set.Ioi (y n)).indicator E x) - (s.card : ℂ) * ((x : ℂ) * E x) := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      have : (volume : Measure ℝ) {(1:ℝ)} = 0 := Real.volume_singleton
      exact measure_eq_zero_iff_ae_notMem.mp this |>.mono (fun x hx => by simpa using hx)
    filter_upwards [hne] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hfx : Int.fract x = x := by
      rw [Int.fract_eq_self]; exact ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    rw [eC_mul']
    simp only [discR, hfx, Finset.card_filter, Set.indicator_apply, Set.mem_Ioi]
    push_cast
    rw [sub_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl; intro n _; split_ifs <;> simp [hE, hcdef]
    · simp [hE]; ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hint : ∀ n ∈ s, IntervalIntegrable ((Set.Ioi (y n)).indicator E) volume 0 1 := by
    intro n _
    rw [intervalIntegrable_iff]
    exact (hEc.continuousOn.integrableOn_compact isCompact_uIcc |>.mono_set Set.uIoc_subset_uIcc).indicator
      measurableSet_Ioi
  have hind : ∀ n ∈ s, ∫ x in (0:ℝ)..1, (Set.Ioi (y n)).indicator E x = (1 - E (y n)) / c := by
    intro n _
    have hy0 : 0 ≤ y n := Int.fract_nonneg _
    have hy1 : y n ≤ 1 := (Int.fract_lt_one _).le
    rw [intervalIntegral.integral_of_le zero_le_one, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi]
    have : Set.Ioi (y n) ∩ Set.Ioc 0 1 = Set.Ioc (y n) 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
    rw [this, ← intervalIntegral.integral_of_le hy1, integral_expc c hc]
    simp [hE, hc1]
  have hsum : IntervalIntegrable (fun x => ∑ n ∈ s, (Set.Ioi (y n)).indicator E x) volume 0 1 := by
    have := IntervalIntegrable.sum s hint
    convert this using 1
    ext x; simp [Finset.sum_apply]
  rw [intervalIntegral.integral_sub hsum (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_finsetSum hint, intervalIntegral.integral_const_mul,
    Finset.sum_congr rfl hind, integral_x_expc c hc, hc1]
  have hEy : ∀ n ∈ s, E (y n) = eC ((h : ℝ) * f n) := by
    intro n _
    rw [eC_mul', hE]
    simp only [y, Int.fract]
    push_cast
    rw [mul_sub, Complex.exp_sub]
    have : Complex.exp (c * ((⌊f n⌋ : ℤ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (h * ⌊f n⌋)]
      congr 1; rw [hcdef]; push_cast; ring
    rw [this, div_one, hcdef]
  rw [← Finset.sum_congr rfl hEy, ← Finset.sum_div, Finset.sum_sub_distrib]
  simp
  field_simp
  ring

lemma ofReal_mul_eC_ii (g : ℝ → ℝ) (u v c : ℝ) (hg : IntervalIntegrable g volume u v) :
    IntervalIntegrable (fun t => (g t : ℂ) * eC (c * t)) volume u v := by
  have : IntervalIntegrable (fun t => (g t : ℂ)) volume u v := by
    rw [intervalIntegrable_iff] at hg ⊢
    exact hg.ofReal
  exact this.mul_continuousOn (by unfold eC; fun_prop)

lemma integral_cos_period (h : ℕ) (hh : 1 ≤ h) (c : ℝ) :
    ∫ t in (0:ℝ)..1, cos (2 * π * ((h : ℝ) * (t - c))) = 0 := by
  have hpos : (0 : ℝ) < 2 * π * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    positivity
  have := intervalIntegral.integral_comp_mul_sub (fun x => cos x) (c := 2 * π * h) (a := 0)
    (b := 1) hpos.ne' (2 * π * h * c)
  simp only [integral_cos] at this
  have e1 : ∀ t, 2 * π * ((h : ℝ) * (t - c)) = 2 * π * h * t - 2 * π * h * c := fun t => by ring
  simp only [e1]
  rw [this]
  have e2 : 2 * π * (h : ℝ) * 1 - 2 * π * h * c = (2 * π * (h : ℝ) * 0 - 2 * π * h * c)
      + (h : ℕ) * (2 * π) := by ring
  rw [e2, Real.sin_add_nat_mul_two_pi]
  simp

lemma re_term (r x : ℝ) (h : ℝ) (a : ℝ) :
    (eC (-(h * a)) * ((r : ℂ) * eC (h * x))).re = r * cos (2 * π * (h * (x - a))) := by
  have : eC (-(h * a)) * ((r : ℂ) * eC (h * x)) =
      (r : ℂ) * Complex.exp (((2 * π * (h * (x - a)) : ℝ) : ℂ) * Complex.I) := by
    unfold eC
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem fejer_expand_aux (s : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) (a : ℝ)
    (hI : ∀ u v : ℝ, IntervalIntegrable (discR s f) volume u v) :
    ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        (discR s f (x + a) - ∫ y in (0 : ℝ)..1, discR s f y) * fejK m x =
      2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) *
        (eC (-((h : ℝ) * a)) *
          ∫ x in (0 : ℝ)..1, (discR s f x : ℂ) * eC ((h : ℝ) * x)).re := by
  set μ : ℝ := ∫ y in (0 : ℝ)..1, discR s f y with hμ
  set F : ℝ → ℝ := fun t => (discR s f t - μ) * fejK m (t - a) with hF
  -- shift
  have h1 : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), (discR s f (x + a) - μ) * fejK m x =
      ∫ t in (-(1 / 2) + a : ℝ)..(1 / 2 + a), F t := by
    rw [← intervalIntegral.integral_comp_add_right F a]
    simp only [hF, add_sub_cancel_right]
  -- periodicity
  have hper : Function.Periodic F 1 := by
    intro x
    simp only [hF, discR_add_one]
    congr 1
    unfold fejK
    congr 2
    refine Finset.sum_congr rfl fun h _ => ?_
    congr 1
    rw [show 2 * π * ((h : ℝ) * (x + 1 - a)) = 2 * π * ((h : ℝ) * (x - a)) + (h : ℕ) * (2 * π)
      by ring, Real.cos_add_nat_mul_two_pi]
  have h2 : ∫ t in (-(1 / 2) + a : ℝ)..(1 / 2 + a), F t = ∫ t in (0 : ℝ)..1, F t := by
    have := hper.intervalIntegral_add_eq (-(1 / 2) + a) 0
    rw [show (-(1 / 2) + a : ℝ) + 1 = 1 / 2 + a by ring, zero_add] at this
    exact this
  rw [h1, h2]
  -- integrability
  have hc : ∀ h : ℕ, Continuous fun t : ℝ => cos (2 * π * ((h : ℝ) * (t - a))) := fun h => by
    fun_prop
  have hG : IntervalIntegrable (fun t => discR s f t - μ) volume 0 1 :=
    (hI 0 1).sub intervalIntegrable_const
  have hGc : ∀ h : ℕ, IntervalIntegrable
      (fun t => (discR s f t - μ) * cos (2 * π * ((h : ℝ) * (t - a)))) volume 0 1 :=
    fun h => hG.mul_continuousOn (hc h).continuousOn
  have hRc : ∀ h : ℕ, IntervalIntegrable
      (fun t => discR s f t * cos (2 * π * ((h : ℝ) * (t - a)))) volume 0 1 :=
    fun h => (hI 0 1).mul_continuousOn (hc h).continuousOn
  have hexp : ∀ t, F t = ((m : ℝ) + 1) * (discR s f t - μ) +
      2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) *
        ((discR s f t - μ) * cos (2 * π * ((h : ℝ) * (t - a)))) := by
    intro t
    simp only [hF, fejK, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · congr 1; ext h; ring
  simp only [hexp]
  have hsum : IntervalIntegrable (fun t => 2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) *
      ((discR s f t - μ) * cos (2 * π * ((h : ℝ) * (t - a))))) volume 0 1 := by
    refine IntervalIntegrable.const_mul ?_ _
    have := IntervalIntegrable.sum (Icc 1 m) (fun h _ => (hGc h).const_mul (((m : ℝ) + 1) - (h : ℝ)))
    convert this using 1
    ext t; simp
  rw [intervalIntegral.integral_add (hG.const_mul _) hsum, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  swap
  · intro h _; exact (hGc h).const_mul _
  have hmean : ∫ t in (0 : ℝ)..1, (discR s f t - μ) = 0 := by
    rw [intervalIntegral.integral_sub (hI 0 1) intervalIntegrable_const]
    simp [hμ]
  rw [hmean, mul_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
  -- per-h identity
  have hL : ∫ t in (0 : ℝ)..1, (discR s f t - μ) * cos (2 * π * ((h : ℝ) * (t - a))) =
      ∫ t in (0 : ℝ)..1, discR s f t * cos (2 * π * ((h : ℝ) * (t - a))) := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub (hRc h) (((hc h).intervalIntegrable _ _).const_mul μ),
      intervalIntegral.integral_const_mul, integral_cos_period h hh1, mul_zero, sub_zero]
  rw [hL, ← intervalIntegral.integral_const_mul]
  have := Complex.reCLM.intervalIntegral_comp_comm
      ((ofReal_mul_eC_ii (discR s f) 0 1 h (hI 0 1)).const_mul (eC (-((h : ℝ) * a))))
  simp only [Complex.reCLM_apply] at this
  rw [← this]
  simp only [re_term]

/-- display (2.36), page 113, for `Δ_N - μ` with `μ = ∫_0^1 R_N`: the integral of
`(R_N(x + a) - μ)` against the Fejér kernel over `[-1/2, 1/2]` equals, after the shift of the
interval "because of the periodicity of the integrand", the sum over `1 ≤ |h| ≤ m` of
`(m + 1 - |h|) e(-ha) ∫_0^1 R_N(x) e(hx) dx`, the terms `h` and `-h` paired into twice a real
part; the term `h = 0` vanishes since `R_N - μ` has mean zero, which is (2.34). -/
theorem leaf_fejer_expand (s : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) (a : ℝ) :
    ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        (discR s f (x + a) - ∫ y in (0 : ℝ)..1, discR s f y) * fejK m x =
      2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) *
        (eC (-((h : ℝ) * a)) *
          ∫ x in (0 : ℝ)..1, (discR s f x : ℂ) * eC ((h : ℝ) * x)).re := by
  exact fejer_expand_aux s f m a (leaf_discR_intervalIntegrable s f)

theorem discR_fract (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) :
    discR s f x = discR s f (Int.fract x) := by
  simp [discR, Int.fract_fract]

theorem dev_le_helper (s : Finset ℕ) (f : ℕ → ℝ)
    (harc : ∀ u t : ℝ, u ≤ t → t ≤ u + 1 →
      0 ≤ discR s f t - discR s f u + (s.card : ℝ) * (t - u) ∧
        discR s f t - discR s f u + (s.card : ℝ) * (t - u) ≤ s.card)
    (hint : ∀ u v : ℝ, IntervalIntegrable (discR s f) volume u v)
    (x : ℝ) :
    |discR s f x - ∫ y in (0 : ℝ)..1, discR s f y| ≤ s.card := by
  rw [discR_fract]
  set z := Int.fract x with hz
  have hz0 : 0 ≤ z := Int.fract_nonneg x
  have hz1 : z < 1 := Int.fract_lt_one x
  have hc : (0:ℝ) ≤ s.card := by positivity
  have hpt : ∀ t ∈ Set.uIoc (0:ℝ) 1, ‖discR s f t - discR s f z‖ ≤ s.card := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [Real.norm_eq_abs, abs_le]
    rcases le_total z t with h | h
    · obtain ⟨a, b⟩ := harc z t h (by linarith)
      constructor <;> nlinarith
    · obtain ⟨a, b⟩ := harc t z h (by linarith)
      constructor <;> nlinarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub (hint 0 1) intervalIntegrable_const] at hb
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul, abs_one,
    mul_one, Real.norm_eq_abs] at hb
  rw [abs_sub_comm]; exact hb

/-- `0 ≤ D*_N ≤ 1`, used on page 113 when `t` runs over `b < t ≤ b + D*_N` inside one
period, here for `Δ_N - μ`: by `leaf_discR_arc` the oscillation of `R_N` over a period is at
most `N`, and `R_N - μ` has mean zero, so `|R_N(x) - μ| ≤ N`. -/
theorem leaf_discR_dev_le (s : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) :
    |discR s f x - ∫ y in (0 : ℝ)..1, discR s f y| ≤ s.card := by
  exact dev_le_helper s f (leaf_discR_arc s f) (leaf_discR_intervalIntegrable s f) x

/-! ### Assembly -/

/-- The norm of `-(1/(2πih)) S` is `‖S‖/(2πh)`. -/
theorem norm_fourier_coeff (h : ℕ) (hh : 1 ≤ h) (S : ℂ) :
    ‖-(1 / (2 * (π : ℂ) * Complex.I * (h : ℂ))) * S‖ = ‖S‖ / (2 * π * h) := by
  have hpos : (0 : ℝ) < 2 * π * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    positivity
  rw [norm_mul, norm_neg, norm_div, norm_one]
  have : ‖2 * (π : ℂ) * Complex.I * (h : ℂ)‖ = 2 * π * h := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [this]; field_simp

/-- Display (2.38), page 113: the smoothed function is bounded by
`(1/π) Σ_{h=1}^m (m + 1 - h) |S_h| / h`, unnormalized. From `leaf_fejer_expand` and
`leaf_discR_fourier`. -/
theorem smoothed_le (s : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) (a : ℝ) :
    |∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        (discR s f (x + a) - ∫ y in (0 : ℝ)..1, discR s f y) * fejK m x| ≤
      1 / π * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) / h *
        ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
  rw [leaf_fejer_expand]
  have hterm : ∀ h ∈ Icc 1 m,
      |(((m : ℝ) + 1) - (h : ℝ)) * (eC (-((h : ℝ) * a)) *
          ∫ x in (0 : ℝ)..1, (discR s f x : ℂ) * eC ((h : ℝ) * x)).re| ≤
        (((m : ℝ) + 1) - (h : ℝ)) * (‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ / (2 * π * h)) := by
    intro h hh
    obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
    have hc : (0 : ℝ) ≤ ((m : ℝ) + 1) - (h : ℝ) := by
      have : (h : ℝ) ≤ m := by exact_mod_cast hh2
      linarith
    rw [abs_mul, abs_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_eC, one_mul, leaf_discR_fourier s f h hh1, norm_fourier_coeff h hh1]
  calc |2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) * (eC (-((h : ℝ) * a)) *
          ∫ x in (0 : ℝ)..1, (discR s f x : ℂ) * eC ((h : ℝ) * x)).re|
      ≤ 2 * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) *
          (‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ / (2 * π * h)) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 1 / π * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) / h *
          ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h hh => ?_
        have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
        have : (h : ℝ) ≠ 0 := by linarith
        field_simp

/-- The peak bound, pages 113 and 114: `|R_N(x) - μ| ≤ 3N/(m+1) + (2/π) Σ (1/h - 1/(m+1)) |S_h|`
for every `x`, the inequality before (2.40), unnormalized, for `Δ_N - μ`. -/
theorem dev_le (s : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    |discR s f x - ∫ y in (0 : ℝ)..1, discR s f y| ≤
      3 * s.card / ((m : ℝ) + 1) +
        2 / π * ∑ h ∈ Icc 1 m,
          (1 / (h : ℝ) - 1 / ((m : ℝ) + 1)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
  set μ : ℝ := ∫ y in (0 : ℝ)..1, discR s f y with hμ
  set G : ℝ → ℝ := fun x => discR s f x - μ with hG
  set M : ℝ := (s.card : ℝ) with hM
  set T : ℝ := 1 / π * ∑ h ∈ Icc 1 m, (((m : ℝ) + 1) - (h : ℝ)) / h *
        ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ with hT
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcoef : ∀ h ∈ Icc 1 m, (0 : ℝ) ≤ 1 / (h : ℝ) - 1 / ((m : ℝ) + 1) := by
    intro h hh
    obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
    have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have h2 : (h : ℝ) ≤ m := by exact_mod_cast hh2
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hsum0 : 0 ≤ ∑ h ∈ Icc 1 m,
      (1 / (h : ℝ) - 1 / ((m : ℝ) + 1)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ :=
    Finset.sum_nonneg fun h hh => mul_nonneg (hcoef h hh) (norm_nonneg _)
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hB0 : 0 ≤ 3 * M / ((m : ℝ) + 1) + 2 / π * ∑ h ∈ Icc 1 m,
      (1 / (h : ℝ) - 1 / ((m : ℝ) + 1)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
    have : 0 ≤ 2 / π := by positivity
    positivity
  -- `2T/(m+1)` is the paper's sum
  have hT2 : 2 * T / ((m : ℝ) + 1) = 2 / π * ∑ h ∈ Icc 1 m,
      (1 / (h : ℝ) - 1 / ((m : ℝ) + 1)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
    rw [hT, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
    have : (h : ℝ) ≠ 0 := by linarith
    field_simp
  -- the bounds `|G| ≤ M`
  have hGle : ∀ y, |G y| ≤ M := fun y => leaf_discR_dev_le s f y
  rcases eq_or_lt_of_le hM0 with hM00 | hMpos
  · -- no points
    have := hGle x
    rw [← hM00] at this
    show |G x| ≤ _
    have hB := hB0
    rw [← hM00] at hB ⊢
    linarith [abs_nonneg (G x)]
  have hbdd : BddAbove (Set.range fun y => |G y|) := ⟨M, by
    rintro _ ⟨y, rfl⟩; exact hGle y⟩
  set D : ℝ := ⨆ y, |G y| with hD
  have hGD : ∀ y, |G y| ≤ D := fun y => le_ciSup hbdd y
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hGD 0)
  have hDM : D ≤ M := ciSup_le hGle
  have hint : ∀ c : ℝ, IntervalIntegrable (fun x => discR s f (x + c)) volume (-(1 / 2)) (1 / 2) :=
    fun c => by
      simpa only [add_sub_cancel_right] using
        (leaf_discR_intervalIntegrable s f (-(1 / 2) + c) (1 / 2 + c)).comp_add_right c
  have hsm := smoothed_le s f m
  -- the main inequality for every `d < D/M`
  have hmain : ∀ d, 0 < d → d < D / M →
      d * (((m : ℝ) + 1) / 2) - 3 * (D / M) / (2 * d) ≤ T / M := by
    intro d hd hdD
    have hD1 : D / M ≤ 1 := by rw [div_le_one hMpos]; exact hDM
    have hd1 : d ≤ 1 := by linarith
    obtain ⟨b, hb⟩ : ∃ b, d * M < |G b| := by
      have : d * M < D := by rwa [lt_div_iff₀ hMpos] at hdD
      exact exists_lt_of_lt_ciSup this
    rcases lt_abs.mp hb with hpos | hneg
    · -- `Δ_N(b) > d`: the paper's second alternative
      set a : ℝ := b + d / 2 with ha
      have hgint : IntervalIntegrable (fun x => G (x + a) / M) volume (-(1 / 2)) (1 / 2) :=
        ((hint a).sub intervalIntegrable_const).div_const M
      have hpk : ∀ x, |x| < d / 2 → d / 2 - x ≤ G (x + a) / M := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
        have harc := (leaf_discR_arc s f b (x + a) (by rw [ha]; linarith)
          (by rw [ha]; linarith)).1
        rw [le_div_iff₀ hMpos]
        simp only [hG]
        rw [ha] at harc ⊢
        nlinarith
      have hlw : ∀ x, -(1 / 2) ≤ x → x ≤ 1 / 2 → -(D / M) ≤ G (x + a) / M := by
        intro x _ _
        rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hMpos]
        have := hGD (x + a)
        linarith [neg_abs_le (G (x + a))]
      have hF := fejer_peak_lower m (fun x => G (x + a) / M) d (D / M) hd hdD.le hd1 hgint hpk hlw
      have heq : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (x + a) / M * fejK m x =
          (∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (x + a) * fejK m x) / M := by
        rw [← intervalIntegral.integral_div]
        exact intervalIntegral.integral_congr fun x _ => by ring
      rw [heq] at hF
      have := (le_abs_self _).trans (hsm a)
      calc _ ≤ _ := hF
        _ ≤ T / M := div_le_div_of_nonneg_right this hMpos.le
    · -- `Δ_N(b) < -d`: the paper's first alternative, "completely similar"
      set a : ℝ := b - d / 2 with ha
      have hint' : IntervalIntegrable (fun x => discR s f (a - x)) volume (-(1 / 2)) (1 / 2) :=
        by simpa only [sub_sub_cancel] using
          (leaf_discR_intervalIntegrable s f (a - -(1 / 2)) (a - 1 / 2)).comp_sub_left a
      have hgint : IntervalIntegrable (fun x => -G (a - x) / M) volume (-(1 / 2)) (1 / 2) :=
        ((hint'.sub intervalIntegrable_const).neg).div_const M
      have hpk : ∀ x, |x| < d / 2 → d / 2 - x ≤ -G (a - x) / M := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
        have harc := (leaf_discR_arc s f (a - x) b (by rw [ha]; linarith)
          (by rw [ha]; linarith)).1
        rw [le_div_iff₀ hMpos]
        simp only [hG]
        rw [ha] at harc ⊢
        nlinarith
      have hlw : ∀ x, -(1 / 2) ≤ x → x ≤ 1 / 2 → -(D / M) ≤ -G (a - x) / M := by
        intro x _ _
        rw [neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right hMpos]
        have := hGD (a - x)
        linarith [le_abs_self (G (a - x))]
      have hF := fejer_peak_lower m (fun x => -G (a - x) / M) d (D / M) hd hdD.le hd1 hgint
        hpk hlw
      have heq : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), -G (a - x) / M * fejK m x =
          -(∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (x + a) * fejK m x) / M := by
        have h1 : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), -G (a - x) / M * fejK m x =
            -(∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (a - x) * fejK m x) / M := by
          rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_div]
          exact intervalIntegral.integral_congr fun x _ => by ring
        have h2 : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (a - x) * fejK m x =
            ∫ x in (-(1 / 2) : ℝ)..(1 / 2), G (x + a) * fejK m x := by
          have := intervalIntegral.integral_comp_neg
            (a := -(1 / 2)) (b := 1 / 2) (fun x => G (x + a) * fejK m x)
          simp only [neg_neg, fejK_neg] at this
          rw [← this]
          exact intervalIntegral.integral_congr fun x _ => by
            show G (a - x) * fejK m x = G (-x + a) * fejK m x
            rw [neg_add_eq_sub]
        rw [h1, h2]
      rw [heq] at hF
      have := (neg_le_abs _).trans (hsm a)
      calc _ ≤ _ := hF
        _ ≤ T / M := div_le_div_of_nonneg_right this hMpos.le
  -- let `d → D/M`
  have hDle : D ≤ 3 * M / ((m : ℝ) + 1) + 2 * T / ((m : ℝ) + 1) := by
    rcases eq_or_lt_of_le hD0 with hD00 | hDpos
    · rw [← hD00]
      have hT0 : 0 ≤ T := by
        rw [hT]
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun h hh => ?_)
        have hh2 : (h : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hh).2
        have : 0 ≤ ((m : ℝ) + 1) - (h : ℝ) := by linarith
        positivity
      exact add_nonneg (div_nonneg (by linarith) hm1.le) (div_nonneg (by linarith) hm1.le)
    set E : ℝ := D / M with hE
    have hE0 : 0 < E := div_pos hDpos hMpos
    have hlim : Tendsto (fun d => d * (((m : ℝ) + 1) / 2) - 3 * E / (2 * d))
        (𝓝[<] E) (𝓝 (E * (((m : ℝ) + 1) / 2) - 3 * E / (2 * E))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have hc : ContinuousAt (fun d => d * (((m : ℝ) + 1) / 2) - 3 * E / (2 * d)) E := by
        refine (continuousAt_id.mul continuousAt_const).sub
          (continuousAt_const.div (continuousAt_const.mul continuousAt_id) ?_)
        show (2 : ℝ) * E ≠ 0
        positivity
      exact hc.tendsto
    have hev : ∀ᶠ d in 𝓝[<] E, d * (((m : ℝ) + 1) / 2) - 3 * E / (2 * d) ≤ T / M := by
      have h1 : ∀ᶠ d in 𝓝[<] E, 0 < d :=
        nhdsWithin_le_nhds (lt_mem_nhds hE0)
      have h2 : ∀ᶠ d in 𝓝[<] E, d < E := self_mem_nhdsWithin
      filter_upwards [h1, h2] with d hd1 hd2
      exact hmain d hd1 hd2
    have hle := le_of_tendsto hlim hev
    have h3 : 3 * E / (2 * E) = 3 / 2 := by field_simp
    rw [h3] at hle
    have hEM : E * M = D := by rw [hE]; field_simp
    have : E * ((m : ℝ) + 1) ≤ 3 + 2 * (T / M) := by linarith
    rw [← hEM]
    rw [← add_div, le_div_iff₀ hm1]
    have h4 : E * M * ((m : ℝ) + 1) = (E * ((m : ℝ) + 1)) * M := by ring
    rw [h4]
    have h5 : (3 + 2 * (T / M)) * M = 3 * M + 2 * T := by field_simp
    nlinarith
  calc |G x| ≤ D := hGD x
    _ ≤ _ := hDle
    _ = _ := by rw [← hT2, hM]

/-- `ErdosTuranDQ4`, the named hypothesis of `DQLemma4Decisions.lean`, definition unchanged,
from the steps of this file and `ETDQ4Fejer.lean`. Display (2.40), page 114: an interval
count is a difference of two values of `R_N - μ`, each bounded by `dev_le`. No `sorry` here. -/
theorem erdosTuranDQ4_split : DQLemma4.ErdosTuranDQ4 := by
  intro s f a b ha hab hb m _hm
  rw [leaf_count_eq_discR s f a b ha hab hb]
  set μ : ℝ := ∫ y in (0 : ℝ)..1, discR s f y
  have h1 := dev_le s f m b
  have h2 := dev_le s f m a
  have htri : |discR s f b - discR s f a| ≤
      |discR s f b - μ| + |discR s f a - μ| := by
    have := abs_sub (discR s f b - μ) (discR s f a - μ)
    simpa using this
  calc |discR s f b - discR s f a| ≤ _ := htri
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- Wiring: P0082 Lemma 4, page 359, the sealed `U1539.Lemma4`, CONDITIONAL ON the sealed cited
Karacuba `Lemma10` only; the named hypothesis
`ErdosTuranDQ4` is discharged by `erdosTuranDQ4_split`. -/
theorem lemma4_of_lemma10_split (h10 : LeanLab.ExceptionalSet.U1539.Lemma10) :
    LeanLab.ExceptionalSet.U1539.Lemma4 :=
  DQLemma4.lemma4_of_erdosTuran_lemma10 erdosTuranDQ4_split h10

end LeanLab.ExceptionalSet.ETDQ4

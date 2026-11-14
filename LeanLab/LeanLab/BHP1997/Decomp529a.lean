/-
P0069 pages 11, 24 to 27 and 41 to 42. CODEX task529.
Smooth taper, finite Buchstab algebra and exact simplex volumes.
The selected-region family and its uniform mean value remain OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.Rough308
import LeanLab.BHP1997.Decomp312c
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace LeanLab.BHP1997.Decomp529a
open Decomp312c DecompC165b Task308 Classical
open MeasureTheory Set
open scoped BigOperators ContDiff

/-- Supporting cutoff for P0069 page 24 display 4.1 and pages 41 to 42.
It vanishes outside the long interval and has a plateau around I and I1.
This is the lab endpoint repair, not a printed paper formula. -/
noncomputable def upperTaper (x t : ℝ) : ℝ :=
  Real.smoothTransition (4 * (t / x) - 2) *
    Real.smoothTransition (4 - 2 * (t / x))

/-- Supporting endpoint repair for P0069 page 24 display 4.1 and pages 41 to 42. -/
theorem upperTaper_mem_Icc (x t : ℝ) : upperTaper x t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)

/-- Supporting endpoint repair for P0069 page 24 display 4.1 and pages 41 to 42. -/
theorem upperTaper_contDiff (x : ℝ) (n : ℕ∞) : ContDiff ℝ n (upperTaper x) := by
  unfold upperTaper
  fun_prop

/-- Supporting endpoint repair for P0069 page 24 display 4.1 and pages 41 to 42. -/
theorem upperTaper_zero_left {x t : ℝ} (hx : 0 < x) (ht : t ≤ x / 2) : upperTaper x t = 0 := by
  unfold upperTaper
  rw [Real.smoothTransition.zero_of_nonpos ?_, zero_mul]
  have : t / x ≤ (1 / 2 : ℝ) := (div_le_iff₀ hx).mpr (by linarith)
  linarith

/-- Supporting endpoint repair for P0069 page 24 display 4.1 and pages 41 to 42. -/
theorem upperTaper_zero_right {x t : ℝ} (hx : 0 < x) (ht : 2 * x ≤ t) : upperTaper x t = 0 := by
  unfold upperTaper
  rw [Real.smoothTransition.zero_of_nonpos (show 4 - 2 * (t / x) ≤ 0 from ?_), mul_zero]
  have : (2 : ℝ) ≤ t / x := (le_div_iff₀ hx).mpr ht
  linarith

/-- Supporting endpoint repair for P0069 page 24 display 4.1 and pages 41 to 42. -/
theorem upperTaper_one {x t : ℝ} (hx : 0 < x) (ht : 3 * x / 4 ≤ t) (ht' : t ≤ 3 * x / 2) :
    upperTaper x t = 1 := by
  have hlo : (3 / 4 : ℝ) ≤ t / x := (le_div_iff₀ hx).mpr (by linarith)
  have hhi : t / x ≤ (3 / 2 : ℝ) := (div_le_iff₀ hx).mpr (by linarith)
  unfold upperTaper
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- Supporting auxiliary family for P0069 page 24 display 4.1 and pages 41 to 42. -/
noncomputable def taperedFamily (a : ℝ → ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  upperTaper x k * a x k

/-- Supporting divisor bound for the endpoint repair of P0069 page 24 display 4.1. -/
theorem taperedFamily_divisor_bound (a : ℝ → ℕ → ℝ) (B C : ℝ)
    (ha : ∀ x k, |a x k| ≤ C * (k.divisors.card : ℝ) ^ B) :
    ∀ x k, |taperedFamily a x k| ≤ C * (k.divisors.card : ℝ) ^ B := by
  intro x k
  have hw : |upperTaper x k| ≤ 1 := by
    unfold upperTaper
    rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))]
    exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)).trans (by simpa using Real.smoothTransition.le_one _)
  calc
    |taperedFamily a x k| = |upperTaper x k| * |a x k| := abs_mul _ _
    _ ≤ 1 * |a x k| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ = |a x k| := one_mul _
    _ ≤ _ := ha x k

/-- Supporting placement of I1 for P0069 page 24 below display 4.2. -/
theorem referenceWidth_lt_quarter {x : ℝ} (hx : 3 ≤ x) :
    referenceWidth x < x / 4 := by
  change x * Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) < x / 4
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr
    (Real.exp_one_lt_d9.le.trans ((by norm_num : (2.7182818286 : ℝ) ≤ 3).trans hx))
  have hr : 1 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.one_le_rpow hl (by norm_num)
  have he2 : 2 < Real.exp 1 := (by norm_num : (2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have he3 : 4 < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have hen : Real.exp (-3) < 1 / 4 := by
    rw [Real.exp_neg]
    simpa only [one_div] using (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 4)).mpr he3
  have hh : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) < 1 / 4 :=
    (Real.exp_le_exp.mpr (by linarith)).trans_lt hen
  nlinarith [mul_lt_mul_of_pos_left hh hx0]

/-- Supporting taper geometry for P0069 page 24 displays 4.1 and 4.2. -/
theorem upperTaper_hasCompactSupport {x : ℝ} (hx : 0 < x) : HasCompactSupport (upperTaper x) := by
  apply HasCompactSupport.intro (K := Set.Icc (x / 2) (2 * x)) isCompact_Icc
  intro t ht
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact upperTaper_zero_left hx ht.le
  · exact upperTaper_zero_right hx ht.le

/-- Supporting taper geometry for P0069 page 24 displays 4.1 and 4.2. -/
theorem upperTaper_on_reference {x : ℝ} (hx : 3 ≤ x)
    {k : ℕ} (hk : k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊) :
    upperTaper x k = 1 := by
  obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hkr : x - referenceWidth x < (k : ℝ) := (Nat.floor_lt' hk0).mp hkl
  have hxr : (k : ℝ) ≤ x := (by exact_mod_cast hku : (k : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ x))
  have hw := referenceWidth_lt_quarter hx
  exact upperTaper_one (by linarith) (by linarith) (by linarith)

/-- Supporting taper geometry for P0069 page 24 displays 4.1 and 4.2. -/
theorem short_width_lt_quarter_eventually {ε : ℝ} (hε : ε < 1 / 10) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * x ^ (11 / 20 + ε) ≤ x / 4 := by
  have hδ : 0 < 1 - (11 / 20 + ε) := by linarith
  have hg := (tendsto_rpow_atTop hδ).eventually (Filter.eventually_ge_atTop (8 : ℝ))
  filter_upwards [hg, Filter.eventually_gt_atTop (0 : ℝ)] with x hg hx
  have he : x ^ (11 / 20 + ε) * x ^ (1 - (11 / 20 + ε)) = x := by
    rw [← Real.rpow_add hx]
    ring_nf
    exact Real.rpow_one x
  have hp : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx.le _
  nlinarith [mul_le_mul_of_nonneg_left hg hp]

/-- Supporting exact local transport for P0069 page 24 display 4.2 and pages 41 to 42. -/
theorem upperTaper_on_left {ε : ℝ} (hε : ε < 1 / 10) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k ∈ leftInterval ε x, upperTaper x k = 1 := by
  filter_upwards [short_width_lt_quarter_eventually hε,
    Filter.eventually_ge_atTop (3 : ℝ)] with x hw hx
  intro k hk
  obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hlo : x - 2 * x ^ (11 / 20 + ε) < (k : ℝ) := (Nat.floor_lt' hk0).mp hkl
  have hhi : (k : ℝ) ≤ x := (by exact_mod_cast hku : (k : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ x))
  exact upperTaper_one (by linarith) (by linarith) (by linarith)

/-- Supporting exact local transport for P0069 page 24 display 4.2 and pages 41 to 42. -/
theorem referenceAverage_tapered (a : ℝ → ℕ → ℝ) {x : ℝ} (hx : 3 ≤ x) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    referenceAverage (taperedFamily a) x χ = referenceAverage a x χ := by
  unfold referenceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [taperedFamily, upperTaper_on_reference hx hk, one_mul]

/-- Supporting exact local transport for P0069 page 24 display 4.2 and pages 41 to 42. -/
theorem referenceDensity_tapered_iff (u : ℝ) (a : ℝ → ℕ → ℝ) :
    ReferenceDensity u (taperedFamily a) ↔ ReferenceDensity u a := by
  constructor <;> intro h A hA
  all_goals
    obtain ⟨C, X, hC⟩ := h A hA
    refine ⟨C, max X 3, ?_⟩
    intro x hx q hq hqx χ
    have hxX : X ≤ x := (le_max_left _ _).trans hx
    have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
    have hh := hC x hxX q hq hqx χ
    simpa only [referenceAverage_tapered a hx3 χ] using hh

/-- Supporting exact preservation of P0069 pages 26 to 27 displays 4.11 and 4.12. -/
theorem shortApproximation_tapered_iff {ε : ℝ} (hε : ε < 1 / 10) (a b : ℝ → ℕ → ℝ) :
    ShortApproximation ε a (taperedFamily b) ↔ ShortApproximation ε a b := by
  obtain ⟨Xw, hXw⟩ := Filter.eventually_atTop.mp (upperTaper_on_left hε)
  constructor <;> intro h A hA
  all_goals
    obtain ⟨C, X, hC⟩ := h A hA
    refine ⟨C, max X Xw, ?_⟩
    intro x hx
    have he : (∑ k ∈ leftInterval ε x, |a x k - taperedFamily b x k|) =
        ∑ k ∈ leftInterval ε x, |a x k - b x k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [taperedFamily, hXw x ((le_max_right _ _).trans hx) k hk, one_mul]
    have hh := hC x ((le_max_left _ _).trans hx)
    simpa only [he] using hh

/-- Supporting smooth scaling for the endpoint repair of P0069 page 24 display 4.1. -/
theorem upperTaper_rescale (x t : ℝ) : upperTaper x t = upperTaper 1 (t / x) := by
  simp only [upperTaper, div_one]

/-- Supporting smooth scaling for the endpoint repair of P0069 page 24 display 4.1. -/
theorem upperTaper_iteratedDeriv (x : ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (upperTaper x) t =
      (x⁻¹) ^ n * iteratedDeriv n (upperTaper 1) (t / x) := by
  have he : upperTaper x = fun t : ℝ => upperTaper 1 (x⁻¹ * t) := by
    funext t
    simp only [upperTaper, div_eq_mul_inv, inv_one, mul_one, mul_comm x⁻¹ t]
  rw [he, iteratedDeriv_comp_const_mul (upperTaper_contDiff 1 n)]
  simp only [div_eq_mul_inv, mul_comm x⁻¹ t]

/-- Supporting smooth scaling for the endpoint repair of P0069 page 24 display 4.1. -/
theorem upperTaper_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ i : ℕ, i ≤ m → ∀ t : ℝ,
      |iteratedDeriv i (upperTaper x) t| ≤ C / x ^ i := by
  obtain ⟨C, hC, hbound⟩ := (upperTaper_hasCompactSupport (show (0 : ℝ) < 1 by norm_num)).exists_bound_iteratedFDeriv
    (upperTaper_contDiff 1 ⊤) m
  refine ⟨C, hC, ?_⟩
  intro x hx i hi t
  have hb := hbound i hi (t / x)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
  have he : upperTaper x = fun t : ℝ => upperTaper 1 (x⁻¹ * t) := by
    funext t
    simp only [upperTaper, div_eq_mul_inv, inv_one, mul_one, mul_comm x⁻¹ t]
  rw [he, iteratedDeriv_comp_const_mul (upperTaper_contDiff 1 i)]
  simp only [mul_comm x⁻¹ t, ← div_eq_mul_inv t x]
  rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hx.le) _)]
  calc
    _ ≤ (x⁻¹) ^ i * C := mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr hx.le) _)
    _ = C / x ^ i := by simp only [div_eq_mul_inv, inv_pow, mul_comm]

/-- Supporting endpoint repair for P0069 page 24 displays 4.1 and 4.2 and pages 41 to 42.
CONDITIONAL ON the three explicit analytic estimates. The taper does not supply them. -/
theorem tapered_auxiliary_data {ε B u : ℝ} (hε : ε < 1 / 10) (c a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * (k.divisors.card : ℝ) ^ B)
    (hm : MeanValue41 ε (taperedFamily a)) (hd : ReferenceDensity u a)
    (happ : ShortApproximation ε (section4SiftedFamily c) a) :
    ∃ b : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * (k.divisors.card : ℝ) ^ B) ∧
      MeanValue41 ε b ∧ ReferenceDensity u b ∧
      ShortApproximation ε (section4SiftedFamily c) b := by
  obtain ⟨C, hC⟩ := ha
  exact ⟨taperedFamily a, ⟨C, taperedFamily_divisor_bound a B C hC⟩, hm,
    (referenceDensity_tapered_iff u a).mpr hd,
    (shortApproximation_tapered_iff hε (section4SiftedFamily c) a).mpr happ⟩

/-- Supporting endpoint repair for P0069 page 24 displays 4.1 and 4.2 and pages 41 to 42. -/
theorem upperTaper_nonzero_instance : upperTaper 4 2 = 0 ∧ upperTaper 4 4 = 1 ∧ upperTaper 4 8 = 0 ∧
    taperedFamily (fun _ _ => 1) 4 4 = 1 := by
  have hmid : upperTaper 4 4 = 1 := upperTaper_one (by norm_num) (by norm_num) (by norm_num)
  exact ⟨upperTaper_zero_left (by norm_num) (by norm_num), hmid,
    upperTaper_zero_right (by norm_num) (by norm_num), by simp [taperedFamily, hmid]⟩

/-- Supporting uniform-cutoff recursion from P0069 page 27 display 4.14.
This is the raw algebra before the selected C5 and C7 region decisions on page 41. -/
noncomputable def buchstabLayer : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, n, w, _ => roughIndicator n w
  | j + 1, n, w, z => ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n),
      buchstabLayer j (n / p) w p

/-- Supporting uniform-cutoff remainder from P0069 page 27 display 4.14.
The terminal rough cutoff is the last prime. No discarded domain is selected here. -/
noncomputable def buchstabRemainder: ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, n, _, z => roughIndicator n z
  | j + 1, n, w, z => ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n),
      buchstabRemainder j (n / p) w p

/-- Supporting finite Buchstab algebra for P0069 page 27 display 4.14 and page 41. -/
theorem buchstab_layer_remainder (j n w z : ℕ) (hwz : w ≤ z) :
    buchstabLayer j n w z = buchstabRemainder j n w z + buchstabRemainder (j + 1) n w z := by
  induction j generalizing n z with
  | zero =>
    simp only [buchstabLayer, buchstabRemainder]
    have h := rough_buchstab_finite n w z hwz
    linarith
  | succ j ih =>
    simp only [buchstabLayer, buchstabRemainder]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    exact ih (n / p) p (Finset.mem_filter.mp hp).2.1

/-- Supporting finite Buchstab algebra for P0069 page 27 display 4.14 and page 41. -/
theorem buchstab_remainder_nonneg (j n w z : ℕ) : 0 ≤ buchstabRemainder j n w z := by
  induction j generalizing n z with
  | zero => simp only [buchstabRemainder, roughIndicator]; split_ifs <;> norm_num
  | succ j ih =>
    exact Finset.sum_nonneg (fun p hp => ih (n / p) p)

/-- Supporting finite Buchstab algebra for P0069 page 27 display 4.14 and page 41. -/
theorem buchstab_expansion (j n w z : ℕ) (hwz : w ≤ z) :
    roughIndicator n z =
      (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * buchstabLayer i n w z) +
      (-1 : ℝ) ^ j * buchstabRemainder j n w z := by
  have hs : (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * buchstabLayer i n w z) =
      buchstabRemainder 0 n w z - (-1 : ℝ) ^ j * buchstabRemainder j n w z := by
    calc
      _ = ∑ i ∈ Finset.range j,
          ((-1 : ℝ) ^ i * buchstabRemainder i n w z -
            (-1 : ℝ) ^ (i + 1) * buchstabRemainder (i + 1) n w z) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [buchstab_layer_remainder i n w z hwz, pow_succ]
        ring
      _ = _ := by
        simpa only [pow_zero, one_mul] using
          Finset.sum_range_sub' (fun i => (-1 : ℝ) ^ i * buchstabRemainder i n w z) j
  simp only [buchstabRemainder] at hs
  linarith

/-- Supporting finite Buchstab algebra for P0069 page 27 display 4.14 and page 41. -/
theorem buchstab_seven_upper (n w z : ℕ) (hwz : w ≤ z) :
    roughIndicator n z ≤ ∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i * buchstabLayer i n w z := by
  have h := buchstab_expansion 7 n w z hwz
  have hpos := buchstab_remainder_nonneg 7 n w z
  norm_num only [show (-1 : ℝ) ^ 7 = -1 by norm_num, neg_one_mul] at h
  linarith

/-- Supporting elementary divisor bound for P0069 page 11 display 3.1 and page 41. -/
theorem buchstab_layer_abs_le (j n w z : ℕ) (hn : n ≠ 0) :
    |buchstabLayer j n w z| ≤ (n.divisors.card : ℝ) ^ j := by
  induction j generalizing n z with
  | zero => simp only [buchstabLayer, pow_zero, roughIndicator]; split_ifs <;> norm_num
  | succ j ih =>
    let S := z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n)
    have hS : S ⊆ n.divisors := by
      intro p hp
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hp).2.2, hn⟩
    have hcard : (S.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hS
    calc
      |buchstabLayer (j + 1) n w z| ≤ ∑ p ∈ S, |buchstabLayer j (n / p) w p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S, (n.divisors.card : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro p hp
        have hpd := (Finset.mem_filter.mp hp).2.2
        have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
        have hnq : n / p ≠ 0 := by
          exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpd) hpprime.pos)
        have hc : ((n / p).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn (Nat.div_dvd_of_dvd hpd))
        exact (ih (n / p) p hnq).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hc j)
      _ = (S.card : ℝ) * (n.divisors.card : ℝ) ^ j := by simp
      _ ≤ (n.divisors.card : ℝ) * (n.divisors.card : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hcard (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (n.divisors.card : ℝ) ^ (j + 1) := by rw [pow_succ]; ring

/-- Supporting elementary divisor bound for P0069 page 11 display 3.1 and page 41. -/
theorem buchstab_seven_abs_le (n w z : ℕ) (hn : n ≠ 0) :
    |∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i * buchstabLayer i n w z| ≤
      7 * (n.divisors.card : ℝ) ^ 6 := by
  have hcard : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  calc
    _ ≤ ∑ i ∈ Finset.range 7, |(-1 : ℝ) ^ i * buchstabLayer i n w z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range 7, (n.divisors.card : ℝ) ^ 6 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact (buchstab_layer_abs_le i n w z hn).trans
        (pow_le_pow_right₀ hcard (by have := Finset.mem_range.mp hi; omega))
    _ = _ := by simp

/-- Supporting elementary divisor bound for P0069 page 11 display 3.1 and page 41. -/
theorem tapered_seven_upper_divisor_bound (w z : ℝ → ℕ) (x : ℝ) (k : ℕ) :
    |upperTaper x k * (∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i * buchstabLayer i k (w x) (z x))| ≤
      7 * (k.divisors.card : ℝ) ^ (6 : ℝ) := by
  by_cases hk : k = 0
  · subst k
    have hw : upperTaper x 0 = 0 := by
      unfold upperTaper
      simp only [zero_div, mul_zero, zero_sub]
      rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), zero_mul]
    simp [hw]
  · calc
      _ = upperTaper x k * |∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i * buchstabLayer i k (w x) (z x)| := by
        rw [abs_mul, abs_of_nonneg (upperTaper_mem_Icc x k).1]
      _ ≤ 1 * |∑ i ∈ Finset.range 7, (-1 : ℝ) ^ i * buchstabLayer i k (w x) (z x)| :=
        mul_le_mul_of_nonneg_right (upperTaper_mem_Icc x k).2 (abs_nonneg _)
      _ ≤ 7 * (k.divisors.card : ℝ) ^ (6 : ℕ) := by
        simpa only [one_mul] using buchstab_seven_abs_le k (w x) (z x) hk
      _ = _ := by simp only [Real.rpow_ofNat]

/-- Supporting finite discarded-term accounting for P0069 page 41. -/
theorem discarded_negative_identity {ι : Type*} [DecidableEq ι] (S T : Finset ι) (hST : S ⊆ T)
    (a : ℝ) (f : ι → ℝ) :
    a - ∑ i ∈ S, f i = (a - ∑ i ∈ T, f i) + ∑ i ∈ T \ S, f i := by
  have h := Finset.sum_sdiff hST (f := f)
  linarith

/-- Supporting finite discarded-term accounting for P0069 page 41. -/
theorem discarded_negative_majorant {ι : Type*} [DecidableEq ι] (S T : Finset ι) (hST : S ⊆ T)
    (a : ℝ) (f : ι → ℝ) (hf : ∀ i ∈ T \ S, 0 ≤ f i) :
    a - ∑ i ∈ T, f i ≤ a - ∑ i ∈ S, f i := by
  have h := Finset.sum_sdiff hST (f := f)
  have hn := Finset.sum_nonneg hf
  linarith

/-- P0069 page 24 display 4.1, supporting bounded scalar normalization.
CONDITIONAL ON MeanValue41 for the original family. The factor depends only on x,
not on the coefficient index. No general multiplication by a cutoff is asserted. -/
theorem meanValue41_bounded_scale {ε : ℝ} {a : ℝ → ℕ → ℝ} (ha : MeanValue41 ε a)
    (r : ℝ → ℝ) (M : ℝ)
    (hr : ∀ᶠ x : ℝ in Filter.atTop, |r x| ≤ M) :
    MeanValue41 ε (fun x k => r x * a x k) := by
  obtain ⟨Xr, hXr⟩ := Filter.eventually_atTop.mp hr
  intro A hA
  obtain ⟨C, X, hC⟩ := ha A hA
  refine ⟨M * |C|, max X (max Xr 1), ?_⟩
  intro x hx q hq hqx χ σ hσ
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxR : Xr ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ x := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  have hR : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have he (t : ℝ) :
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (((r x * a x k : ℝ) : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t))‖ =
        |r x| * ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖ := by
    have hh : (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (((r x * a x k : ℝ) : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t))) =
        (r x : ℂ) * ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    rw [hh, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hh := hC x hxX q hq hqx χ σ hσ
  calc
    _ ≤ |r x| * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ ≤ |r x| * (|C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) hR) hL) (abs_nonneg _)
    _ ≤ M * (|C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_right (hXr x hxR) (mul_nonneg (mul_nonneg (abs_nonneg C) hR) hL)
    _ = _ := by ring

/-- Supporting exact measure calculation for the P0069 page 42 five-dimensional region. -/
theorem abs_map_volume : Measure.map (fun x : ℝ => |x|) volume =
    (2 : ENNReal) • (volume.restrict (Ici (0 : ℝ))) := by
  have hp : Measure.map (fun x : ℝ => |x|) (volume.restrict (Ici 0)) = volume.restrict (Ici 0) := by
    calc
      _ = Measure.map id (volume.restrict (Ici (0 : ℝ))) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact abs_of_nonneg hx
      _ = _ := Measure.map_id
  have hn : Measure.map (fun x : ℝ => |x|) (volume.restrict (Iio 0)) = volume.restrict (Ici 0) := by
    calc
      _ = Measure.map (fun x : ℝ => -x) (volume.restrict (Iio 0)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
        exact abs_of_neg hx
      _ = (Measure.map (fun x : ℝ => -x) volume).restrict (Ioi 0) := by
        rw [Measure.restrict_map measurable_neg measurableSet_Ioi]
        congr 1
        ext x
        simp
      _ = _ := by rw [Measure.map_neg_eq_self, restrict_Ioi_eq_restrict_Ici]
  calc
    _ = Measure.map (fun x : ℝ => |x|) (volume.restrict (Ici 0) + volume.restrict (Iio 0)) := by
      rw [← compl_Ici, Measure.restrict_add_restrict_compl measurableSet_Ici]
    _ = volume.restrict (Ici 0) + volume.restrict (Ici 0) := by
      rw [Measure.map_add _ _ measurable_abs, hp, hn]
    _ = _ := by norm_num [← two_smul ENNReal (volume.restrict (Ici (0 : ℝ)))]

/-- Supporting exact measure calculation for the P0069 page 42 five-dimensional region. -/
theorem pi_two_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    Measure.pi (fun i => (2 : ENNReal) • μ i) =
      (2 : ENNReal) ^ Fintype.card ι • Measure.pi μ := by
  have (i : ι) : SigmaFinite ((2 : ENNReal) • μ i) := by
    change SigmaFinite ((2 : NNReal) • μ i)
    infer_instance
  refine (Measure.pi_eq (μ := fun i => (2 : ENNReal) • μ i) (fun s hs => ?_))
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

/-- Supporting exact measure calculation for the P0069 page 42 five-dimensional region. -/
theorem abs_pi5_map_volume : Measure.map (fun x : Fin 5 → ℝ => fun i => |x i|) volume =
    (32 : ENNReal) • volume.restrict (Set.pi Set.univ (fun _ : Fin 5 => Ici (0 : ℝ))) := by
  have : SigmaFinite (Measure.map (fun x : ℝ => |x|) volume) := by
    rw [abs_map_volume]
    change SigmaFinite ((2 : NNReal) • (volume.restrict (Ici (0 : ℝ))))
    infer_instance
  have hp := Measure.pi_map_pi (μ := fun _ : Fin 5 => (volume : Measure ℝ))
    (f := fun _ : Fin 5 => fun x : ℝ => |x|) (fun _ => measurable_abs.aemeasurable)
  change Measure.map (fun x : Fin 5 → ℝ => fun i => |x i|) (Measure.pi fun _ => volume) = _
  rw [hp]
  simp_rw [abs_map_volume]
  rw [pi_two_smul, ← Measure.restrict_pi_pi]
  norm_num
  rfl

/-- Supporting exact measure calculation for the P0069 page 42 five-dimensional region. -/
theorem nonnegative_simplex_five_volume (r : ℝ) (hr : 0 ≤ r) :
    volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r} =
      ENNReal.ofReal (r ^ 5 / 120) := by
  have hm : Measurable (fun x : Fin 5 → ℝ => fun i => |x i|) := by fun_prop
  have hS : MeasurableSet {g : Fin 5 → ℝ | (∑ i, g i) ≤ r} := by
    apply measurableSet_le <;> fun_prop
  have he : volume {g : Fin 5 → ℝ | (∑ i, |g i|) ≤ r} =
      (32 : ENNReal) * volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r} := by
    calc
      _ = (Measure.map (fun x : Fin 5 → ℝ => fun i => |x i|) volume)
          {g : Fin 5 → ℝ | (∑ i, g i) ≤ r} := by
        rw [Measure.map_apply hm hS]
        rfl
      _ = _ := by
        rw [abs_pi5_map_volume, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
        congr 1
        congr 1
        ext g
        simp [Pi.le_def, and_comm]
  have hg2 : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have hg6 : Real.Gamma (6 : ℝ) = 120 := by
    convert Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  have hb := volume_sum_rpow_le (Fin 5) (p := 1) (by norm_num) r
  simp only [Real.rpow_one, Fintype.card_fin, div_one] at hb
  norm_num only [mul_one] at hb
  rw [hg2, hg6] at hb
  calc
    _ = (1 / 32 : ENNReal) * ((32 : ENNReal) *
        volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r}) := by
      rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ = (1 / 32 : ENNReal) * volume {g : Fin 5 → ℝ | (∑ i, |g i|) ≤ r} := by rw [he]
    _ = _ := by
      rw [hb, ← ENNReal.ofReal_pow hr]
      rw [show (1 / 32 : ENNReal) = ENNReal.ofReal (1 / 32 : ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
noncomputable def upperFiveRegion : Set (Fin 5 → ℝ) :=
 {a | a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧ a 3 ≤ a 4 ∧
   a 4 ≤ 1 - ∑ i, a i ∧ 1 - ∑ i, a i < 0.18 ∧
   0.46 ≤ a 0 + a 1 + a 2 ∧ a 0 + a 1 + a 2 ≤ 0.5}

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
noncomputable def upperFiveIntegral : ℝ :=
 ∫ a in upperFiveRegion, (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
noncomputable def upperFiveGaps (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
 ![6 * ((∑ i, a i) - 0.82),
   5 * (1 - (∑ i, a i) - a 4),
   4 * (a 4 - a 3), 3 * (a 3 - a 2), 2 * (a 2 - a 1)]

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
noncomputable def upperFiveGapMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
 !![6, 6, 6, 6, 6; -5, -5, -5, -5, -10; 0, 0, 0, -4, 4;
    0, 0, -3, 3, 0; 0, -2, 2, 0, 0]

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
theorem upper_five_gap_det : upperFiveGapMatrix.det = 720 := by
 norm_num [upperFiveGapMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
theorem upper_five_gap_affine (a : Fin 5 → ℝ) :
 upperFiveGaps a = upperFiveGapMatrix.mulVec a + ![-4.92, 5, 0, 0, 0] := by
 ext i
 fin_cases i <;> simp [upperFiveGaps, upperFiveGapMatrix, dotProduct,
  Fin.sum_univ_succ] <;> ring

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
theorem upper_five_geometry {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
 (∀ i, 0 ≤ upperFiveGaps a i) ∧ (∑ i, upperFiveGaps a i) ≤ 0.08 ∧
 (∀ i, 0.1 ≤ a i ∧ a i ≤ 0.18) ∧ 0.1 ≤ 1 - ∑ i, a i := by
 rcases ha with ⟨h01,h12,h23,h34,h45,h5,h3,h3'⟩
 have hs : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 := by
  simp [Fin.sum_univ_succ]; ring
 refine ⟨?_, ?_, ?_, ?_⟩
 · intro i
   fin_cases i <;> simp [upperFiveGaps] <;> linarith
 · simp [upperFiveGaps, Fin.sum_univ_succ]
   linarith
 · intro i
   fin_cases i <;> dsimp <;> constructor <;> linarith
 · linarith

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
theorem upper_five_gap_map :
    Measure.map upperFiveGaps volume = ENNReal.ofReal (1 / 720 : ℝ) • volume := by
  have hm : Measurable (Matrix.toLin' upperFiveGapMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  have he : upperFiveGaps = (fun x : Fin 5 → ℝ => x + ![-4.92, 5, 0, 0, 0]) ∘
      Matrix.toLin' upperFiveGapMatrix := by
    ext a i
    exact congrFun (upper_five_gap_affine a) i
  rw [he, ← Measure.map_map (by fun_prop) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [upper_five_gap_det]; norm_num),
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]
  norm_num [upper_five_gap_det]

/-- Copied elementary page 42 coordinates in an independent namespace.
The target and its consumers are not imported. -/
theorem upper_five_geometry_converse (a : Fin 5 → ℝ)
    (h0 : ∀ i, 0 ≤ upperFiveGaps a i) (hs : ∑ i, upperFiveGaps a i ≤ 0.08)
    (hp : 0 < upperFiveGaps a 0) : a ∈ upperFiveRegion := by
  have h1 := h0 1
  have h2 := h0 2
  have h3 := h0 3
  have h4 := h0 4
  have hsum : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 := by
    simp [Fin.sum_univ_succ]; ring
  simp [upperFiveGaps, Fin.sum_univ_succ] at hs hp h1 h2 h3 h4
  change a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧ a 3 ≤ a 4 ∧
    a 4 ≤ 1 - ∑ i, a i ∧ 1 - ∑ i, a i < 0.18 ∧
    0.46 ≤ a 0 + a 1 + a 2 ∧ a 0 + a 1 + a 2 ≤ 0.5
  repeat' constructor
  all_goals linarith

/-- Exact geometric support for the literal five-dimensional integral on P0069 page 42. -/
theorem five_coordinate_zero_volume : volume {g : Fin 5 → ℝ | g 0 = 0} = 0 := by
  have he : {g : Fin 5 → ℝ | g 0 = 0} =
      Set.pi Set.univ (fun i : Fin 5 => if i = 0 then ({0} : Set ℝ) else Set.univ) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : i = 0 <;> simp [hi, h]
    · intro h
      simpa using h 0
  rw [he, volume_pi_pi]
  simp [Fin.prod_univ_succ]

/-- Exact geometric support for the literal five-dimensional integral on P0069 page 42. -/
theorem positive_simplex_five_volume : volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08 ∧ 0 < g 0} =
    ENNReal.ofReal ((0.08 : ℝ) ^ 5 / 120) := by
  have hz := five_coordinate_zero_volume
  calc
    _ = volume {g : Fin 5 → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08} := by
      apply measure_congr
      filter_upwards [show ∀ᵐ g : Fin 5 → ℝ, g 0 ≠ 0 from ae_iff.mpr (by simpa only [not_not] using hz)] with g hg
      apply propext
      constructor
      · exact fun h => ⟨h.1, h.2.1⟩
      · exact fun h => ⟨h.1, h.2, lt_of_le_of_ne (h.1 0) (Ne.symm hg)⟩
    _ = _ := nonnegative_simplex_five_volume _ (by norm_num)

/-- Exact geometric support for the literal five-dimensional integral on P0069 page 42. -/
theorem upper_five_region_volume_exact : volume upperFiveRegion = ENNReal.ofReal ((0.08 : ℝ) ^ 5 / 86400) := by
  let S : Set (Fin 5 → ℝ) := {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.08 ∧ 0 < g 0}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
      (measurable_pi_apply i)).inter ((measurableSet_le
        (show Measurable (fun g : Fin 5 → ℝ => ∑ i, g i) by fun_prop) measurable_const).inter
          (measurableSet_lt measurable_const (measurable_pi_apply 0)))
  have he : upperFiveRegion = upperFiveGaps ⁻¹' S := by
    ext a
    constructor
    · intro ha
      have hg := upper_five_geometry ha
      refine ⟨hg.1, hg.2.1, ?_⟩
      have hc : 1 - ∑ i, a i < 0.18 := ha.2.2.2.2.2.1
      simp only [upperFiveGaps, Matrix.cons_val_zero]
      linarith
    · intro ha
      exact upper_five_geometry_converse a ha.1 ha.2.1 ha.2.2
  have hm : Measurable upperFiveGaps := by unfold upperFiveGaps; fun_prop
  rw [he, ← Measure.map_apply hm hS, upper_five_gap_map, Measure.smul_apply, smul_eq_mul]
  have hv : volume S = ENNReal.ofReal ((0.08 : ℝ) ^ 5 / 120) := positive_simplex_five_volume
  rw [hv, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hp := Finset.prod_le_one₀ h0s h1s
    have hpa := mul_nonneg (sub_nonneg.mpr (h1 a (Finset.mem_insert_self _ _))) (sub_nonneg.mpr hp)
    have hi := ih h0s h1s
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem upper_five_product_bound (a : Fin 6 → ℝ)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 0.18) (hs : ∑ i, a i = 1) :
    0.1 * 0.18 ^ 5 ≤ ∏ i, a i := by
  have h := one_sub_sum_le_prod Finset.univ (fun i => a i / 0.18)
    (fun i _ => div_nonneg (h0 i) (by norm_num)) (fun i _ => (div_le_one (by norm_num)).mpr (h1 i))
  have hsum : (∑ i : Fin 6, (1 - a i / 0.18)) = 6 - 1 / 0.18 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    norm_num
  rw [hsum, Finset.prod_div_distrib] at h
  norm_num at h
  linarith

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem upper_five_integrand_bound {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
    ‖(∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹‖ ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ := by
  obtain ⟨_, _, harange, hr⟩ := upper_five_geometry ha
  let b : Fin 6 → ℝ := Fin.snoc (α := fun _ => ℝ) a (1 - ∑ i, a i)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (show (0 : ℝ) ≤ 1 - ∑ j, a j by linarith)
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (show (0 : ℝ) ≤ a j by linarith [(harange j).1])
  have hb1 : ∀ i, b i ≤ 0.18 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using le_of_lt ha.2.2.2.2.2.1
    · simpa only [b, Fin.snoc_castSucc, Fin.snoc_last] using (harange j).2
  have hsum : ∑ i, b i = 1 := by rw [Fin.sum_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hprod := upper_five_product_bound b hb hb1 hsum
  have he : (∏ i, b i) = (∏ i, a i) * (1 - ∑ i, a i) := by
    rw [Fin.prod_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
  rw [he] at hprod
  rw [← mul_inv, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hprod))]
  exact inv_anti₀ (by norm_num) hprod

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem upper_five_integrable :
    IntegrableOn (fun a : Fin 5 → ℝ => (∏ i, a i)⁻¹ * (1 - ∑ i, a i)⁻¹) upperFiveRegion := by
  have hf : volume upperFiveRegion ≠ ⊤ :=
    by rw [upper_five_region_volume_exact]; exact ENNReal.ofReal_ne_top
  have hm : MeasurableSet upperFiveRegion := by
    unfold upperFiveRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals first | apply measurableSet_le | apply measurableSet_lt
    all_goals fun_prop
  have hc : IntegrableOn (fun _ : Fin 5 → ℝ => (0.1 * 0.18 ^ 5 : ℝ)⁻¹) upperFiveRegion :=
    integrableOn_const hf
  apply hc.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem hm] with a ha
  exact upper_five_integrand_bound ha

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem six_product_le_sixth (b : Fin 6 → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, b i = 1) :
    (∏ i, b i) ≤ (1/6:ℝ)^6 := by
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin 6 => (1:ℝ)) b
    (fun _ _ => by norm_num) (by norm_num) (fun i _ => hb i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hs] at h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hb i)) _) h 6
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hb i)) (by norm_num : (6:ℕ) ≠ 0)] at hh
  exact hh

/-- Copied elementary denominator support for the literal page 42 integral. -/
theorem upper_five_integrand_lower_amgm {a : Fin 5 → ℝ} (ha : a ∈ upperFiveRegion) :
    (46656:ℝ) ≤ (∏ i, a i)⁻¹ * (1-∑ i, a i)⁻¹ := by
  have hg := upper_five_geometry ha
  let b : Fin 6 → ℝ := Fin.snoc (α:=fun _ => ℝ) a (1-∑ i, a i)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [b, Fin.snoc_last] using (show (0:ℝ) ≤ 1-∑ i, a i by linarith [hg.2.2.2])
    · simpa only [b, Fin.snoc_castSucc] using (show (0:ℝ) ≤ a j by linarith [(hg.2.2.1 j).1])
  have hs : ∑ i, b i = 1 := by
    rw [Fin.sum_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hp := six_product_le_sixth b hb hs
  have he : (∏ i, b i) = (∏ i, a i)*(1-∑ i, a i) := by
    rw [Fin.prod_univ_castSucc]; simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
  rw [he] at hp
  have hpos : 0 < (∏ i, a i)*(1-∑ i, a i) := by
    apply mul_pos
    · exact Finset.prod_pos (fun i _ => by linarith [(hg.2.2.1 i).1])
    · linarith [hg.2.2.2]
  have hi := inv_anti₀ hpos hp
  norm_num at hi
  simpa [mul_inv, mul_comm] using hi

/-- P0069 page 42, a rational enclosure using exact region volume and elementary product bounds.
The inherited discrepancy with the printed value remains a QUESTION. -/
theorem upper_five_integral_exact_volume_bounds : (432 / 244140625 : ℝ) ≤ upperFiveIntegral ∧
    upperFiveIntegral ≤ (16 / 7971615 : ℝ) := by
  have hv : volume.real upperFiveRegion = (0.08 : ℝ) ^ 5 / 86400 := by
    rw [measureReal_def, upper_five_region_volume_exact, ENNReal.toReal_ofReal (by norm_num)]
  have hf : volume upperFiveRegion ≠ ⊤ := by
    rw [upper_five_region_volume_exact]
    exact ENNReal.ofReal_ne_top
  have hm : MeasurableSet upperFiveRegion := by
    unfold upperFiveRegion
    simp only [Set.ofPred_and]
    repeat' apply MeasurableSet.inter
    all_goals first | apply measurableSet_le | apply measurableSet_lt
    all_goals fun_prop
  constructor
  · have hc : IntegrableOn (fun _ : Fin 5 → ℝ => (46656 : ℝ)) upperFiveRegion :=
      integrableOn_const hf
    have hi := setIntegral_mono_on hc upper_five_integrable hm
      (fun a ha => upper_five_integrand_lower_amgm ha)
    have hh : (46656 : ℝ) * volume.real upperFiveRegion ≤ upperFiveIntegral := by
      simpa [upperFiveIntegral, integral_const, smul_eq_mul, mul_comm] using hi
    rw [hv] at hh
    norm_num at hh ⊢
    exact hh
  · have hi := norm_setIntegral_le_of_norm_le_const
      (show volume upperFiveRegion < ⊤ by rw [upper_five_region_volume_exact]; exact ENNReal.ofReal_lt_top)
      (fun a ha => upper_five_integrand_bound ha)
    have hh : upperFiveIntegral ≤ (0.1 * 0.18 ^ 5 : ℝ)⁻¹ * volume.real upperFiveRegion :=
      (le_abs_self _).trans hi
    rw [hv] at hh
    norm_num at hh ⊢
    exact hh

/-- P0069 page 42, numeric budget for twelve copies of the literal five-dimensional integral.
This supplies no actual decomposition count and no seven-dimensional loss estimate. -/
theorem upper_five_twelve_budget : (12 : ℝ) * upperFiveIntegral < 0.000025 := by
  have h := mul_le_mul_of_nonneg_left upper_five_integral_exact_volume_bounds.2
    (show (0 : ℝ) ≤ 12 by norm_num)
  exact h.trans_lt (by norm_num)

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem abs_pi_map_volume (ι : Type*) [Fintype ι] :
    Measure.map (fun x : ι → ℝ => fun i => |x i|) volume =
      (2 : ENNReal) ^ Fintype.card ι • volume.restrict (Set.pi Set.univ (fun _ : ι => Ici (0 : ℝ))) := by
  have : SigmaFinite (Measure.map (fun x : ℝ => |x|) volume) := by
    rw [abs_map_volume]
    change SigmaFinite ((2 : NNReal) • (volume.restrict (Ici (0 : ℝ))))
    infer_instance
  have hp := Measure.pi_map_pi (μ := fun _ : ι => (volume : Measure ℝ))
    (f := fun _ : ι => fun x : ℝ => |x|) (fun _ => measurable_abs.aemeasurable)
  change Measure.map (fun x : ι → ℝ => fun i => |x i|) (Measure.pi fun _ => volume) = _
  rw [hp]
  simp_rw [abs_map_volume]
  rw [pi_two_smul, ← Measure.restrict_pi_pi]
  rfl

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem nonnegative_simplex_volume (ι : Type*) [Fintype ι] [Nonempty ι]
    (r : ℝ) (hr : 0 ≤ r) :
    volume {g : ι → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r} =
      ENNReal.ofReal (r ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  let n := Fintype.card ι
  have hm : Measurable (fun x : ι → ℝ => fun i => |x i|) := by fun_prop
  have hS : MeasurableSet {g : ι → ℝ | (∑ i, g i) ≤ r} := by
    apply measurableSet_le <;> fun_prop
  have he : volume {g : ι → ℝ | (∑ i, |g i|) ≤ r} =
      (2 : ENNReal) ^ n * volume {g : ι → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r} := by
    calc
      _ = (Measure.map (fun x : ι → ℝ => fun i => |x i|) volume)
          {g : ι → ℝ | (∑ i, g i) ≤ r} := by
        rw [Measure.map_apply hm hS]
        rfl
      _ = _ := by
        rw [abs_pi_map_volume, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
        congr 1
        congr 1
        ext g
        simp [Pi.le_def, and_comm]
  have hg2 : Real.Gamma (2 : ℝ) = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  have hb := volume_sum_rpow_le ι (p := 1) (by norm_num) r
  simp only [Real.rpow_one, div_one] at hb
  norm_num only [one_div_one] at hb
  rw [hg2, Real.Gamma_nat_eq_factorial] at hb
  simp only [mul_one] at hb
  have hc0 : (2 : ENNReal) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hct : (2 : ENNReal) ^ n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  calc
    _ = ((2 : ENNReal) ^ n)⁻¹ * ((2 : ENNReal) ^ n *
        volume {g : ι → ℝ | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ r}) := by
      rw [ENNReal.inv_mul_cancel_left hc0 hct]
    _ = ((2 : ENNReal) ^ n)⁻¹ * volume {g : ι → ℝ | (∑ i, |g i|) ≤ r} := by rw [he]
    _ = _ := by
      rw [hb]
      change ((2 : ENNReal) ^ n)⁻¹ * (ENNReal.ofReal r ^ n *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ))) = _
      have hc : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num
      rw [hc, ← ENNReal.ofReal_inv_of_pos (show 0 < (2 : ℝ) ^ n by positivity),
        ← ENNReal.ofReal_pow hr]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = r ^ n * (((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n) / (n.factorial : ℝ) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), mul_one]

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
noncomputable def orderedSevenRegion : Set (Fin 7 → ℝ) :=
 {a | 0.1 ≤ a 0 ∧ a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧
    a 3 ≤ a 4 ∧ a 4 ≤ a 5 ∧ a 5 ≤ a 6 ∧ a 6 ≤ 1 - ∑ i, a i}

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
noncomputable def orderedSevenGaps (a : Fin 7 → ℝ) : Fin 7 → ℝ :=
 ![8 * (a 0 - 0.1), 7 * (a 1 - a 0), 6 * (a 2 - a 1),
   5 * (a 3 - a 2), 4 * (a 4 - a 3), 3 * (a 5 - a 4), 2 * (a 6 - a 5)]

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
noncomputable def orderedSevenGapMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
 !![8,0,0,0,0,0,0; -7,7,0,0,0,0,0; 0,-6,6,0,0,0,0;
    0,0,-5,5,0,0,0; 0,0,0,-4,4,0,0; 0,0,0,0,-3,3,0; 0,0,0,0,0,-2,2]

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem ordered_seven_gap_det : orderedSevenGapMatrix.det = 40320 := by
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    have hlt : i < j := hij
    fin_cases i <;> fin_cases j <;> norm_num [orderedSevenGapMatrix] at * )]
  norm_num [orderedSevenGapMatrix, Fin.prod_univ_succ]

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem ordered_seven_gap_affine (a : Fin 7 → ℝ) :
    orderedSevenGaps a = orderedSevenGapMatrix.mulVec a + ![-0.8,0,0,0,0,0,0] := by
  ext i
  fin_cases i <;> simp [orderedSevenGaps,orderedSevenGapMatrix,dotProduct,Fin.sum_univ_succ] <;> ring

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem ordered_seven_gap_map :
    Measure.map orderedSevenGaps volume = ENNReal.ofReal (1 / 40320 : ℝ) • volume := by
  have hm : Measurable (Matrix.toLin' orderedSevenGapMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  have he : orderedSevenGaps = (fun x : Fin 7 → ℝ => x + ![-0.8,0,0,0,0,0,0]) ∘
      Matrix.toLin' orderedSevenGapMatrix := by
    ext a i
    exact congrFun (ordered_seven_gap_affine a) i
  rw [he, ← Measure.map_map (by fun_prop) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [ordered_seven_gap_det]; norm_num),
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]
  norm_num [ordered_seven_gap_det]

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem ordered_seven_region_iff_gaps (a : Fin 7 → ℝ) :
    a ∈ orderedSevenRegion ↔
      (∀ i, 0 ≤ orderedSevenGaps a i) ∧ (∑ i, orderedSevenGaps a i) ≤ 0.2 := by
  have hsum : (∑ i, a i) = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 := by
    simp [Fin.sum_univ_succ]
    ring
  constructor
  · rintro ⟨h0,h01,h12,h23,h34,h45,h56,h6⟩
    constructor
    · intro i
      fin_cases i <;> simp [orderedSevenGaps] <;> linarith
    · simp [orderedSevenGaps, Fin.sum_univ_succ]
      linarith
  · rintro ⟨hg,hs⟩
    have h0 := hg 0
    have h1 := hg 1
    have h2 := hg 2
    have h3 := hg 3
    have h4 := hg 4
    have h5 := hg 5
    have h6 := hg 6
    simp [orderedSevenGaps, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 hs
    change 0.1 ≤ a 0 ∧ a 0 ≤ a 1 ∧ a 1 ≤ a 2 ∧ a 2 ≤ a 3 ∧
      a 3 ≤ a 4 ∧ a 4 ≤ a 5 ∧ a 5 ≤ a 6 ∧ a 6 ≤ 1 - ∑ i, a i
    repeat' constructor
    all_goals linarith

/-- Supporting exact simplex geometry for P0069 page 42.
The ordered seven-dimensional statements concern one auxiliary envelope only. -/
theorem ordered_seven_region_volume_exact :
    volume orderedSevenRegion = ENNReal.ofReal ((0.2 : ℝ) ^ 7 / 203212800) := by
  let S : Set (Fin 7 → ℝ) := {g | (∀ i, 0 ≤ g i) ∧ (∑ i, g i) ≤ 0.2}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const
      (measurable_pi_apply i)).inter (measurableSet_le
        (show Measurable (fun g : Fin 7 → ℝ => ∑ i, g i) by fun_prop) measurable_const)
  have he : orderedSevenRegion = orderedSevenGaps ⁻¹' S := by
    ext a
    exact ordered_seven_region_iff_gaps a
  have hm : Measurable orderedSevenGaps := by unfold orderedSevenGaps; fun_prop
  have hv : volume S = ENNReal.ofReal ((0.2 : ℝ) ^ 7 / 5040) := by
    simpa [Fintype.card_fin, Nat.factorial] using
      nonnegative_simplex_volume (Fin 7) (0.2 : ℝ) (by norm_num)
  rw [he, ← Measure.map_apply hm hS, ordered_seven_gap_map, Measure.smul_apply, smul_eq_mul,
    hv, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end LeanLab.BHP1997.Decomp529a

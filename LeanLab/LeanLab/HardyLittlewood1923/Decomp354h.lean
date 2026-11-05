import LeanLab.HardyLittlewood1923.Decomp296Farey
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
AI wrote this Lean code for CODEX task354.
P0004 pages 5 and 6 section 1.4 and page 23 equation 3.123.
Dirichlet approximation proves the upper width without a determinant formula.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354h

open Real
open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
Distinct rationals are separated by at least the reciprocal denominator product. -/
theorem rational_gap {r s : ℚ} (hrs : r < s) :
    1 / ((r.den : ℝ) * s.den) ≤ (s : ℝ) - r := by
  have hn : (1 : ℝ) ≤ ((s - r).num : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ (s-r).num by have := Rat.num_pos.mpr (sub_pos.mpr hrs); omega)
  have hd : (s-r).den ≤ r.den * s.den := by
    simpa [Nat.mul_comm] using Nat.le_of_dvd (by positivity : 0 < s.den * r.den) (Rat.sub_den_dvd s r)
  have hpos : (0 : ℝ) < (s-r).den := by exact_mod_cast (s-r).pos
  calc
    _ ≤ 1 / ((s-r).den : ℝ) := one_div_le_one_div_of_le hpos (by exact_mod_cast hd)
    _ ≤ ((s-r).num : ℝ) / (s-r).den := div_le_div_of_nonneg_right hn hpos.le
    _ = _ := by rw [← Rat.cast_def, Rat.cast_sub]

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
A sufficiently close rational approximation must lie to the right of the endpoint. -/
theorem approximation_right {N : ℕ} (hN : 0 < N) {r t : ℚ} {x : ℝ}
    (hr : r.den ≤ N) (hap : |x - t| < 1 / ((N : ℝ) * t.den))
    (hx : 1 / ((r.den : ℝ) * N) < x - r) : r < t := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have htR : (0 : ℝ) < t.den := by exact_mod_cast t.pos
  by_contra h
  have htr : t ≤ r := le_of_not_gt h
  rcases lt_or_eq_of_le htr with hlt | rfl
  · have hgap := rational_gap hlt
    have hlow : 1 / ((N : ℝ) * t.den) ≤ 1 / ((t.den : ℝ) * r.den) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hrR : (r.den : ℝ) ≤ N := by exact_mod_cast hr
      nlinarith
    have htrR : (t : ℝ) < r := by exact_mod_cast hlt
    have hxR : (r : ℝ) < x := by
      have : 0 < 1 / ((r.den : ℝ) * N) := by positivity
      linarith
    rw [abs_of_pos (by linarith : 0 < x - (t : ℝ))] at hap
    linarith
  · rw [mul_comm] at hx
    have := le_abs_self (x - (t : ℝ))
    linarith

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
Dirichlet approximation supplies an intermediate rational when both endpoint distances exceed their denominator bounds. -/
theorem rational_between {N : ℕ} (hN : 0 < N) {r s : ℚ} {x : ℝ}
    (hr : r.den ≤ N) (hs : s.den ≤ N)
    (hL : 1 / ((r.den : ℝ) * N) < x - r)
    (hR : 1 / ((s.den : ℝ) * N) < s - x) :
    ∃ t : ℚ, r < t ∧ t < s ∧ t.den ≤ N := by
  obtain ⟨t, hap, ht⟩ := Real.exists_rat_abs_sub_le_and_den_le x hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have htR : (0 : ℝ) < t.den := by exact_mod_cast t.pos
  have hap' : |x - t| < 1 / ((N : ℝ) * t.den) := hap.trans_lt
    (one_div_lt_one_div_of_lt (by positivity) (by nlinarith))
  have hleft : r < t := approximation_right hN hr hap' hL
  have hright : -s < -t := approximation_right (r := -s) (t := -t) (x := -x)
    hN (by simpa using hs) (by simpa only [Rat.cast_neg, Rat.neg_den, neg_sub_neg, abs_sub_comm] using hap')
    (by simpa only [Rat.neg_den, Rat.cast_neg, neg_sub_neg] using hR)
  exact ⟨t, hleft, neg_lt_neg_iff.mp hright, ht⟩

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
The mediant divides the gap in inverse proportion to the endpoint denominators. -/
theorem mediant_balance (r s : ℚ) :
    (r.den : ℝ) * ((mediant r s : ℝ) - r) =
      (s.den : ℝ) * ((s : ℝ) - mediant r s) := by
  have hr : (r : ℝ) = (r.num : ℝ) / r.den := Rat.cast_def r
  have hs : (s : ℝ) = (s.num : ℝ) / s.den := Rat.cast_def s
  rw [hr, hs]
  simp only [mediant, Rat.cast_div, Rat.cast_natCast, Int.cast_add]
  have hr0 : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hs0 : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.pos.ne'
  push_cast
  field_simp
  ring

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
No intermediate rational of bounded denominator implies the upper mediant width bounds. -/
theorem mediant_upper {N : ℕ} (hN : 0 < N) {r s : ℚ}
    (hr : r.den ≤ N) (hs : s.den ≤ N)
    (hno : ∀ t : ℚ, t.den ≤ N → r < t → t < s → False) :
    (mediant r s : ℝ) - r ≤ 1 / ((r.den : ℝ) * N) ∧
      (s : ℝ) - mediant r s ≤ 1 / ((s.den : ℝ) * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hsR : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hb := mediant_balance r s
  have hbN := congrArg (fun y : ℝ => y * N) hb
  constructor
  · by_contra h
    have hL : 1 / ((r.den : ℝ) * N) < (mediant r s : ℝ) - r := lt_of_not_ge h
    have hR : 1 / ((s.den : ℝ) * N) < (s : ℝ) - mediant r s := by
      apply (div_lt_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ (by positivity : 0 < (r.den : ℝ) * N)).mp hL
      nlinarith only [hh, hbN]
    obtain ⟨t, htL, htR, htd⟩ := rational_between hN hr hs hL hR
    exact hno t htd htL htR
  · by_contra h
    have hR : 1 / ((s.den : ℝ) * N) < (s : ℝ) - mediant r s := lt_of_not_ge h
    have hL : 1 / ((r.den : ℝ) * N) < (mediant r s : ℝ) - r := by
      apply (div_lt_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ (by positivity : 0 < (s.den : ℝ) * N)).mp hR
      nlinarith only [hh, hbN]
    obtain ⟨t, htL, htR, htd⟩ := rational_between hN hr hs hL hR
    exact hno t htd htL htR

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
Every rational between minus one and two with bounded reduced denominator belongs to the translated Farey set. -/
theorem farey_mem_of_den {N : ℕ} {r : ℚ} (hd : r.den ≤ N)
    (hr0 : -1 ≤ r) (hr2 : r ≤ 2) : r ∈ fareyPoints N := by
  have hdQ : (0 : ℚ) < r.den := by exact_mod_cast r.pos
  have hlow := (le_div_iff₀ hdQ).mp
    (show (-1 : ℚ) ≤ (r.num : ℚ) / r.den by rw [r.num_div_den]; exact hr0)
  have hhigh := (div_le_iff₀ hdQ).mp
    (show (r.num : ℚ) / r.den ≤ 2 by rw [r.num_div_den]; exact hr2)
  have hl : -(r.den : ℤ) ≤ r.num := by exact_mod_cast (by simpa using hlow : -(r.den : ℚ) ≤ r.num)
  have hh : r.num ≤ 2 * (r.den : ℤ) := by exact_mod_cast hhigh
  apply Finset.mem_biUnion.mpr
  refine ⟨r.den, Finset.mem_Icc.mpr ⟨r.pos, hd⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨r.num, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hh⟩, r.reduced⟩, ?_⟩
  exact r.num_div_den

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
A selected point to the left of r is at most the selected predecessor. -/
theorem farey_prev_max {N : ℕ} {r t : ℚ} (ht : t ∈ fareyPoints N) (htr : t < r) :
    t ≤ fareyPrev N r := by
  have hm : t ∈ (fareyPoints N).filter (fun v => v < r) := Finset.mem_filter.mpr ⟨ht, htr⟩
  have he : ((fareyPoints N).filter (fun v => v < r)).Nonempty := ⟨t, hm⟩
  rw [fareyPrev, dite_eq_left he]
  exact Finset.le_max' _ t hm

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
A selected point to the right of r is at least the selected successor. -/
theorem farey_next_min {N : ℕ} {r t : ℚ} (ht : t ∈ fareyPoints N) (hrt : r < t) :
    fareyNext N r ≤ t := by
  have hm : t ∈ (fareyPoints N).filter (fun v => r < v) := Finset.mem_filter.mpr ⟨ht, hrt⟩
  have he : ((fareyPoints N).filter (fun v => r < v)).Nonempty := ⟨t, hm⟩
  rw [fareyNext, dite_eq_left he]
  exact Finset.min'_le _ t hm

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
No rational with denominator at most N lies strictly between a point and either selected neighbor. -/
theorem farey_no_between {N : ℕ} (hN : 1 ≤ N) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∀ t : ℚ, t.den ≤ N → fareyPrev N r < t → t < r → False) ∧
      (∀ t : ℚ, t.den ≤ N → r < t → t < fareyNext N r → False) := by
  have hplo : -1 ≤ fareyPrev N r := farey_prev_max
    (LeanLab.HardyLittlewood1923.Decomp296Farey.fareyPoints_extremes hN).1 (by linarith)
  have hnhi : fareyNext N r ≤ 2 := farey_next_min
    (LeanLab.HardyLittlewood1923.Decomp296Farey.fareyPoints_extremes hN).2 (by linarith)
  constructor
  · intro t ht hpt htr
    have hm := farey_mem_of_den ht (hplo.trans hpt.le) (by linarith : t ≤ 2)
    exact (not_lt_of_ge (farey_prev_max hm htr)) hpt
  · intro t ht hrt htn
    have hm := farey_mem_of_den ht (by linarith : -1 ≤ t) (htn.le.trans hnhi)
    exact (not_lt_of_ge (farey_next_min hm hrt)) htn

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
Both actual angular endpoint distances are at most two pi over q N. -/
theorem arc_upper_widths {N p q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N)
    (hp : p < q) (hpq : p.Coprime q) :
    -arcLeft N p q ≤ 2 * π / ((q : ℝ) * N) ∧
      arcRight N p q ≤ 2 * π / ((q : ℝ) * N) := by
  let r : ℚ := (p : ℚ) / q
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    exact (div_le_one hqQ).mpr (by exact_mod_cast hp.le)
  have hrd : r.den = q := by
    have hd := Rat.den_div_eq_of_coprime (a := (p : ℤ))
      (show (0 : ℤ) < q by exact_mod_cast (by omega : 0 < q)) (by simpa using hpq)
    apply Int.natCast_inj.mp
    simpa only [r, Int.cast_natCast] using hd
  obtain ⟨hprev, hnext, hpden, hsden⟩ :=
    LeanLab.HardyLittlewood1923.Decomp296Farey.farey_neighbors hN hr0 hr1
  obtain ⟨hnop, hnon⟩ := farey_no_between hN hr0 hr1
  have hL := (mediant_upper (by omega : 0 < N) hpden (hrd ▸ hqN) hnop).2
  have hR := (mediant_upper (by omega : 0 < N) (hrd ▸ hqN) hsden hnon).1
  rw [hrd] at hL hR
  have heL : -arcLeft N p q = 2 * π * ((r : ℝ) - mediant (fareyPrev N r) r) := by
    change -(2 * π * ((mediant (fareyPrev N r) r - r : ℚ) : ℝ)) = _
    push_cast
    ring
  have heR : arcRight N p q = 2 * π * ((mediant r (fareyNext N r) : ℝ) - r) := by
    change 2 * π * ((mediant r (fareyNext N r) - r : ℚ) : ℝ) = _
    push_cast
    rfl
  rw [heL, heR]
  constructor
  · calc
      _ ≤ 2 * π * (1 / ((q : ℝ) * N)) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ 2 * π * (1 / ((q : ℝ) * N)) := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring

/-- P0004 pages 5 and 6 section 1.4, used on page 23 in equation 3.123.
The upper angular width gives the square root saving n to minus one quarter. -/
theorem farey_upper_width :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        |θ| ≤ 2 * π ∧ Real.sqrt q * Real.sqrt |θ| ≤ D * (n : ℝ) ^ (-1 / 4 : ℝ) := by
  refine ⟨Real.sqrt (4 * π), Real.sqrt_nonneg _, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  let N := Nat.sqrt n
  have hN : 1 ≤ N := Nat.le_sqrt.mpr (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNq : (1 : ℝ) ≤ q * N := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  obtain ⟨hL, hR⟩ := arc_upper_widths hN hq hqN hp hpq
  have ht : |θ| ≤ 2 * π / ((q : ℝ) * N) := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have htheta : |θ| ≤ 2 * π := ht.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_pos]))
  refine ⟨htheta, ?_⟩
  have htprod : (q : ℝ) * |θ| * N ≤ 2 * π := by
    have hh := (le_div_iff₀ (by positivity : 0 < (q : ℝ) * N)).mp ht
    nlinarith only [hh]
  have hNsq : Real.sqrt n ≤ 2 * (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlt : (n : ℝ) < ((N : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
    have hs := Real.sq_sqrt hnR.le
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have htfinal : (q : ℝ) * |θ| * Real.sqrt n ≤ 4 * π := by
    have hh := mul_le_mul_of_nonneg_left hNsq (show 0 ≤ (q : ℝ) * |θ| by positivity)
    nlinarith only [hh, htprod]
  let s : ℝ := Real.sqrt (Real.sqrt n)
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsq : (Real.sqrt q * Real.sqrt |θ| * s) ^ 2 = (q : ℝ) * |θ| * Real.sqrt n := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q),
      Real.sq_sqrt (abs_nonneg θ), Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))]
  have hh : Real.sqrt q * Real.sqrt |θ| * s ≤ Real.sqrt (4 * π) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hsq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * π)]
    exact htfinal
  have hs : s = (n : ℝ) ^ (1 / 4 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnR.le]
    norm_num
  calc
    _ ≤ Real.sqrt (4 * π) / s := (le_div_iff₀ hspos).mpr hh
    _ = _ := by
      rw [hs, div_eq_mul_inv, show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hnR.le]

#print axioms rational_gap
#print axioms approximation_right
#print axioms rational_between
#print axioms mediant_balance
#print axioms mediant_upper
#print axioms farey_mem_of_den
#print axioms farey_prev_max
#print axioms farey_next_min
#print axioms farey_no_between
#print axioms arc_upper_widths
#print axioms farey_upper_width

end LeanLab.HardyLittlewood1923.Decomp354h

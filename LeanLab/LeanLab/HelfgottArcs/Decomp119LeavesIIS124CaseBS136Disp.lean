/-
Split of the HARD leaf caseB_display536 of Decomp119LeavesIIS124CaseB, burst S136.
P0013 page 62 display 5.36 is stated as a cited leaf with r standing for q/φ(q) and t for |δq|,
then page 68 display 5.55 gives q/φ(q) ≤ ̥(y), and the evaluation leaf bounds the right side
of 5.36 by caseBDisplay on the case b range 8y < t ≤ U, q ≤ y.
An mpmath check at 30 digits, 401 log spaced points in t: the maximum of the right side of 5.36
with r = ̥(y), q = y is at t = 8y, with ratio 0.2269576 at x = 2.16e20 against 0.2495513 for
caseBDisplay; 0.2280412 against 0.2455632 at 1e25; 0.2258799 against 0.2400937 at 1e30.
The comparison is not term by term: the last term of caseBDisplay, with the factor
√(2 / log(8e²/3)) ≈ 0.819, is below the last term of 5.36 at every t.
Grid checks only, not proofs. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBS136Disp
open LeanLab.HelfgottArcs.Decomp119 LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB

/-- P0013 page 62 display 5.36, the right side, with θ = e², Q = x/U, ρ = q/Q,
t standing for |δq| and r for q/φ(q), so that 2x/√(|δ|φ(q)) = 2x√r/√t.
The constants κ2, κ6, κ7, κ9 are the paper's upper bounds as in caseBDisplay. -/
noncomputable def rhs536 (x q t r : ℝ) : ℝ :=
  let θ := Real.exp 2
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  2 * x * Real.sqrt r / Real.sqrt t *
      Real.sqrt ((Real.log (x / (U x * θ * t)) +
          Real.log (3 * t / 8) * Real.log (Real.log (8 * x / (3 * U x * t)) /
            Real.log (8 * θ / 3))) *
        (κ6 * Real.log (x / (U x * θ * t)) + 2 * κ7)) +
    2 * κ2 / 3 * (x / Real.sqrt (2 * t) + x / (4 * Real.sqrt (Q - q))) *
      (Real.log (θ * t) ^ ((3 : ℝ) / 2) - Real.log (V x) ^ ((3 : ℝ) / 2)) +
    (κ2 / Real.sqrt (2 * (1 - q / Q)) *
        (Real.sqrt (Real.log (V x)) + Real.sqrt (1 / Real.log (V x))) + κ9) *
      (x / Real.sqrt (V x)) +
    κ2 * Real.sqrt r * Real.sqrt (Real.log (θ * t)) * (x / Real.sqrt (U x))

/-- LEAF: P0013 page 62 display 5.36, the Type II bound for |δ| ≥ 8 and |δq| > V/θ with θ = e²,
proved on pages 55 to 62 from Proposition 5.2 and Lemmas 5.3 to 5.6 of the paper,
for 2α = a/q + δ/x with q ≤ Q = x/U and |δ/x| ≤ 1/(qQ). Class HARD. -/
theorem display536 (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hQ : (q' : ℝ) ≤ x / U x) (hb1 : 8 ≤ |δ'|) (hV : V x / Real.exp 2 < |δ'| * q') :
    ‖II α x‖ ≤ rhs536 x q' (|δ'| * q') ((q' : ℝ) / (Nat.totient q' : ℝ)) := by
  sorry

/-- LEAF: P0013 page 68 display 5.55 with Rosser and Schoenfeld 1962 Theorem 15,
q/φ(q) < ̥(q), and ̥ increasing, so q/φ(q) ≤ ̥(y) for 1 ≤ q ≤ y = x^{1/3}/6, used on page 72.
Class MEDIUM; the inequality for q ≥ 3 is a cited theorem, q = 1, 2 are direct. -/
theorem qphi_le_frakF (x : ℝ) (hx : 2.16e20 ≤ x) (q : ℕ) (hq1 : 1 ≤ q)
    (hy : (q : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    (q : ℝ) / (Nat.totient q : ℝ) ≤ frakF (x ^ ((1 : ℝ) / 3) / 6) := by
  sorry

/-- LEAF: P0013 page 72, case b evaluation: the right side of 5.36 with r = ̥(y), q ≤ y and
8y < t ≤ U is at most the page 72 display. Class HARD; not term by term, the float maximum
over t is at t = 8y, ratio 0.2269576 against 0.2495513 at x = 2.16e20. -/
theorem eval536_caseB (x : ℝ) (hx : 2.16e20 ≤ x) (q t : ℝ) (hq1 : 1 ≤ q)
    (hy : q ≤ x ^ ((1 : ℝ) / 3) / 6) (ht1 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < t) (ht2 : t ≤ U x) :
    rhs536 x q t (frakF (x ^ ((1 : ℝ) / 3) / 6)) ≤ caseBDisplay x := by
  sorry

/-- The right side of 5.36 is monotone in r = q/φ(q), for x ≥ 0. -/
theorem rhs536_mono (x q t r r' : ℝ) (hx : 0 ≤ x) (hr : r ≤ r') :
    rhs536 x q t r ≤ rhs536 x q t r' := by
  have hs : Real.sqrt r ≤ Real.sqrt r' := Real.sqrt_le_sqrt hr
  unfold rhs536
  simp only
  have h1 : 2 * x * Real.sqrt r / Real.sqrt t ≤ 2 * x * Real.sqrt r' / Real.sqrt t := by
    gcongr
  have h4 : (1.93768 : ℝ) * Real.sqrt r ≤ 1.93768 * Real.sqrt r' := by gcongr
  have hA := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg
      ((Real.log (x / (U x * Real.exp 2 * t)) +
          Real.log (3 * t / 8) * Real.log (Real.log (8 * x / (3 * U x * t)) /
            Real.log (8 * Real.exp 2 / 3))) *
        (0.60428 * Real.log (x / (U x * Real.exp 2 * t)) + 2 * 0.1281)))
  have hB := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (Real.log (Real.exp 2 * t))))
    (div_nonneg hx (Real.sqrt_nonneg (U x)))
  linarith

/-- In case b, the hypotheses give q ≤ Q = x/U, |δq| ≤ U and |δq| > V/e². -/
theorem caseB_ranges (x : ℝ) (hx : 2.16e20 ≤ x) (q' : ℕ) (δ' : ℝ) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hb2 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')
    (hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    (q' : ℝ) ≤ x / U x ∧ |δ'| * q' ≤ U x ∧ V x / Real.exp 2 < |δ'| * q' := by
  have hx0 : 0 < x := by linarith
  set c := x ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hx0 _
  have hc3 : c ^ 3 = x := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hc2 : x ^ ((2 : ℝ) / 3) = c ^ 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hc6 : 6e6 ≤ c := by
    by_contra h
    rw [not_le] at h
    have : c ^ 3 < (6e6 : ℝ) ^ 3 := by
      exact pow_lt_pow_left₀ h hc0.le (by norm_num)
    norm_num at this
    linarith
  have hs6 : 0 < Real.sqrt 6 := by positivity
  have hs6' : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hU : U x = 500 * Real.sqrt 6 * c := rfl
  have hUpos : 0 < U x := by rw [hU]; positivity
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hUpos, hU, ← hc3]
    have : (q' : ℝ) * (500 * Real.sqrt 6 * c) ≤ c / 6 * (1500 * c) := by
      have h1 : (500 * Real.sqrt 6 * c) ≤ 1500 * c := by nlinarith
      calc (q' : ℝ) * (500 * Real.sqrt 6 * c) ≤ (q' : ℝ) * (1500 * c) := by gcongr
        _ ≤ c / 6 * (1500 * c) := by gcongr
    nlinarith
  · rw [hc2] at hδ
    rw [abs_div, abs_of_pos hx0] at hδ
    have hQ : 0 < c ^ 2 / (500 * Real.sqrt 6) := by positivity
    rw [div_le_div_iff₀ hx0 (by positivity), one_mul] at hδ
    rw [hU]
    have key : |δ'| * q' * (c ^ 2 / (500 * Real.sqrt 6)) ≤ 500 * Real.sqrt 6 * c *
        (c ^ 2 / (500 * Real.sqrt 6)) := by
      have : 500 * Real.sqrt 6 * c * (c ^ 2 / (500 * Real.sqrt 6)) = x := by
        rw [← hc3]; field_simp
      rw [this]; linarith
    exact le_of_mul_le_mul_right key hQ
  · have he : 1 < Real.exp 2 := by
      have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num); linarith
    have hVx : V x = c / 3 := rfl
    rw [hVx, div_lt_iff₀ (by linarith)]
    nlinarith

/-- Assembly of caseB_display536 from the three leaves, exact statement of the parent LEAF. -/
theorem caseB_display536_of_leaves (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hb1 : 8 < |δ'|) (hb2 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')
    (hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    ‖II α x‖ ≤ caseBDisplay x := by
  obtain ⟨hQ, hU, hV⟩ := caseB_ranges x hx q' δ' hq1 hδ hb2 hy
  have h1 := display536 x α hx a' q' δ' h2α hg hq1 hδ hQ hb1.le hV
  have h2 := rhs536_mono x q' (|δ'| * q') _ _ (by linarith) (qphi_le_frakF x hx q' hq1 hy)
  have h3 := eval536_caseB x hx q' (|δ'| * q') (by exact_mod_cast hq1) hy hb2 hU
  linarith

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBS136Disp

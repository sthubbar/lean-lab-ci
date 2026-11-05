/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Tail113
import LeanLab.Tchudakov1938.Decomp362d
namespace LeanLab.Tchudakov1938.Decomp362e

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open Finset
open LeanLab.Tchudakov1938.Tail113 LeanLab.Tchudakov1938.Euler113
open LeanLab.Tchudakov1938.Lemma4Abs113 LeanLab.Tchudakov1938.Decomp113b

/-- LEAF. P0064, page 29, inequality 5. Express an integer tail as an indicator series. -/
theorem tail_indicator (f : ℕ → ℝ) (Q : ℕ) :
    (∑' k : ℕ, f (k + (Q + 1))) = ∑' q : ℕ, if Q < q then f q else 0 := by
  have hi : Function.Injective (fun k : ℕ => k + (Q + 1)) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hs : Function.support (fun q : ℕ => if Q < q then f q else 0) ⊆
      Set.range (fun k : ℕ => k + (Q + 1)) := by
    intro q hq
    have hq' : Q < q := by
      by_contra hn
      simp [Function.mem_support, hn] at hq
    exact ⟨q - (Q + 1), by dsimp; omega⟩
  simpa only [show ∀ k : ℕ, Q < k + (Q + 1) by omega, ite_true] using hi.tsum_eq hs

/-- LEAF. P0064, page 29, inequality 5. Reindex the multiples of a positive divisor above the cutoff. -/
theorem multiple_indicator (f : ℕ → ℝ) (d Q : ℕ) (hd : 0 < d) :
    (∑' q : ℕ, if d ∣ q ∧ Q < q then f q else 0) =
      ∑' k : ℕ, f (d * (k + (Q / d + 1))) := by
  have hi : Function.Injective (fun k : ℕ => d * (k + (Q / d + 1))) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hd hab)
  have hs : Function.support (fun q : ℕ => if d ∣ q ∧ Q < q then f q else 0) ⊆
      Set.range (fun k : ℕ => d * (k + (Q / d + 1))) := by
    intro q hq
    have hh : d ∣ q ∧ Q < q := by
      by_contra hn
      simp [Function.mem_support, hn] at hq
    have hdiv : Q / d < q / d := by
      rw [Nat.div_lt_iff_lt_mul hd]
      rw [Nat.div_mul_cancel hh.1]
      exact hh.2
    refine ⟨q / d - (Q / d + 1), ?_⟩
    dsimp
    rw [Nat.sub_add_cancel (by omega), Nat.mul_div_cancel' hh.1]
  have hcond (k : ℕ) : d ∣ d * (k + (Q / d + 1)) ∧ Q < d * (k + (Q / d + 1)) := by
    refine ⟨dvd_mul_right _ _, ?_⟩
    exact (Nat.lt_mul_div_succ Q hd).trans_le (Nat.mul_le_mul_left d (by omega))
  simpa [hcond] using (hi.tsum_eq hs).symm



/-- LEAF. P0064, page 29, inequality 5, first two bounds. Keep the gcd in the logarithmic coefficient estimate. -/
theorem coefficient_log_gcd (m q : ℕ) (hq : 2 ≤ q) :
    ‖coefficientNat m q‖ ≤ (1 / (Real.log 2 / 2)^2) *
      ((Nat.gcd q m : ℝ) * (Real.log q)^2 / (q : ℝ)^2) := by
  have hc : 0 < Real.log 2 / 2 := by positivity
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have ht := totient_log_lower q hq
  have hs : (Real.log 2 / 2)^2 * (q : ℝ)^2 ≤
      (q.totient : ℝ)^2 * (Real.log q)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) ht 2
  rw [coefficientNat, dite_eq_right (by omega : q ≠ 0)]
  calc ‖LeanLab.Tchudakov1938.Decomp113.coefficient m ⟨q, hq0⟩‖ ≤
        (Nat.gcd q m : ℝ) / (q.totient : ℝ)^2 := coefficient_norm_le m ⟨q, hq0⟩
    _ ≤ ((Nat.gcd q m : ℝ) * (Real.log q)^2) / ((Real.log 2 / 2)^2 * (q : ℝ)^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have H := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ Nat.gcd q m by positivity)
      nlinarith
    _ = _ := by ring

/-- LEAF. P0064, page 29, inequality 5. The gcd is bounded by the sum of common divisors. -/
theorem gcd_le_divisor_sum (m q : ℕ) (hm : 0 < m) :
    (Nat.gcd q m : ℝ) ≤ ∑ d ∈ m.divisors, if d ∣ q then (d : ℝ) else 0 := by
  have hg : Nat.gcd q m ∈ m.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q m, by omega⟩
  have h := Finset.single_le_sum (s := m.divisors)
    (f := fun d => if d ∣ q then (d : ℝ) else 0) (fun d _ => by split_ifs <;> positivity) hg
  simpa only [Nat.gcd_dvd_left, ite_true] using h


/-- LEAF. P0064, page 29, inequality 5, large divisor range. The full inner series is bounded by twice its logarithmic polynomial. -/
theorem full_series_bound (d : ℝ) (hd : Real.exp 1 ≤ d) :
    (1 / d) * (∑' k : ℕ, (Real.log (d * (k + 1 : ℕ)))^2 / ((k + 1 : ℕ) : ℝ)^2) ≤
      2 * (((Real.log d)^2 + Real.log d + 1) / d) := by
  have hd0 : 0 < d := (Real.exp_pos 1).trans_le hd
  have hderiv : ∀ t ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ => -((Real.log (d * t))^2 + 2 * Real.log (d * t) + 2) / t)
        ((Real.log (d * t))^2 / t^2) t := by
    intro t ht
    exact LeanLab.Tchudakov1938.Decomp362d.primitive_derivative d hd0 t (by have : (1 : ℝ) ≤ t := ht; linarith)
  have hnonneg : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ (Real.log (d * t))^2 / t^2 := by
    intro t ht
    positivity
  have hint := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg
    (LeanLab.Tchudakov1938.Decomp362d.primitive_tendsto d hd0)
  have hsum : Summable (fun k : ℕ => (Real.log (d * (k : ℝ)))^2 / (k : ℝ)^2) := by
    apply AntitoneOn.summable_of_integrableOn_Ioi (N := 1)
      (f := fun t : ℝ => (Real.log (d * t))^2 / t^2)
    · simpa only [Nat.cast_one] using
        LeanLab.Tchudakov1938.Decomp362d.scaled_log_sq_antitone d 1 hd0 (by norm_num) (by simpa using hd)
    · simpa only [Nat.cast_one] using hint
    · simpa only [Nat.cast_one] using hnonneg
  have hg : Summable (fun k : ℕ => (Real.log (d * (k + 1 : ℕ)))^2 / ((k + 1 : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff 1).mpr hsum
  have heq := hg.tsum_eq_zero_add
  have ht := LeanLab.Tchudakov1938.Decomp362d.shifted_sum_bound d hd0 1 (by norm_num) (by simpa using hd)
  simp only [Nat.zero_add, Nat.cast_one, mul_one, one_pow, div_one, Nat.add_assoc] at heq ht
  rw [heq]
  have hscaled := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1 / d by positivity)
  calc
    _ ≤ (1 / d) * ((Real.log d)^2 + ((Real.log d)^2 + 2 * Real.log d + 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ht) (by positivity)
    _ = _ := by ring



/-- LEAF. P0064, page 29, inequality 5, divisor regrouping. Summable indicator reindexing gives the divisor series. -/
theorem tail_le_divisor_series (m Q : ℕ) (hm : 0 < m) (hQ : 1 ≤ Q) :
    ‖tailSeries m Q‖ ≤ (1 / (Real.log 2 / 2)^2) *
      ∑ d ∈ m.divisors, (1 / (d : ℝ)) *
        ∑' k : ℕ, (Real.log ((d : ℝ) * (k + (Q / d + 1) : ℕ)))^2 /
          ((k + (Q / d + 1) : ℕ) : ℝ)^2 := by
  classical
  let f : ℕ → ℝ := fun q => (Real.log q)^2 / (q : ℝ)^2
  let g : ℕ → ℕ → ℝ := fun d q => if d ∣ q ∧ Q < q then (d : ℝ) * f q else 0
  let K : ℝ := 1 / (Real.log 2 / 2)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsf : Summable f := summable_log_sq_div_sq
  have hsg (d : ℕ) : Summable (g d) := by
    apply ((hsf.mul_left (d : ℝ)).indicator {q : ℕ | d ∣ q ∧ Q < q}).congr
    intro q
    simp only [g, Set.indicator_apply, Set.mem_ofPred_eq]
  have hsn : Summable (fun q : ℕ => if Q < q then ‖coefficientNat m q‖ else 0) := by
    apply ((summable_norm_coefficientNat m hm).indicator {q : ℕ | Q < q}).congr
    intro q
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hpt (q : ℕ) : (if Q < q then ‖coefficientNat m q‖ else 0) ≤ K * ∑ d ∈ m.divisors, g d q := by
    by_cases hq : Q < q
    · rw [ite_eq_left hq]
      have hc := coefficient_log_gcd m q (by omega)
      have hd := mul_le_mul_of_nonneg_right (gcd_le_divisor_sum m q hm)
        (show 0 ≤ f q by dsimp [f]; positivity)
      calc
        ‖coefficientNat m q‖ ≤ K * ((Nat.gcd q m : ℝ) * f q) := by
          simpa only [K, f, mul_div_assoc] using hc
        _ ≤ K * ((∑ d ∈ m.divisors, if d ∣ q then (d : ℝ) else 0) * f q) :=
          mul_le_mul_of_nonneg_left hd hK
        _ = K * ∑ d ∈ m.divisors, g d q := by
          rw [Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro d _
          simp only [g, hq, and_true]
          split_ifs <;> simp
    · simp [hq, g]
  have hsum := Summable.tsum_le_tsum hpt hsn ((summable_sum (fun d _ => hsg d)).mul_left K)
  have hnorm : ‖tailSeries m Q‖ ≤ ∑' k : ℕ, ‖coefficientNat m (k + (Q + 1))‖ := by
    apply norm_tsum_le_tsum_norm
    exact (summable_nat_add_iff (Q + 1)).mpr (summable_norm_coefficientNat m hm)
  rw [tail_indicator (fun q => ‖coefficientNat m q‖) Q] at hnorm
  refine hnorm.trans (hsum.trans_eq ?_)
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun d _ => hsg d)]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have heq : (∑' q : ℕ, g d q) = (d : ℝ) * ∑' k : ℕ, f (d * (k + (Q / d + 1))) := by
    calc
      (∑' q : ℕ, g d q) = (d : ℝ) * ∑' q : ℕ, if d ∣ q ∧ Q < q then f q else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro q
        dsimp [g]
        split_ifs <;> simp
      _ = _ := congrArg (fun v : ℝ => (d : ℝ) * v) (multiple_indicator f d Q hd0)
  rw [heq, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [f]
  push_cast
  field_simp

/-- P0064, page 29, inequality 5. Split at d equal to xi and bound the full large-divisor series. This proves the divisor regrouping input. -/
theorem divisor_split :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ xi : ℝ, Real.exp 2 ≤ xi →
      ‖tailSeries m ⌊xi⌋₊‖ ≤ C *
        ((∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), (1 / (d : ℝ)) *
          ∑' k : ℕ, (Real.log ((d : ℝ) * (k + (⌊xi / d⌋₊ + 1) : ℕ)))^2 /
            ((k + (⌊xi / d⌋₊ + 1) : ℕ) : ℝ)^2) +
        ∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)),
          ((Real.log d)^2 + Real.log d + 1) / (d : ℝ)) := by
  let K : ℝ := 1 / (Real.log 2 / 2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2 * K, by positivity, fun m hm xi hxi => ?_⟩
  have hxi0 : 0 < xi := (Real.exp_pos 2).trans_le hxi
  have hxi1 : 1 ≤ xi := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hxi
  have ht := tail_le_divisor_series m ⌊xi⌋₊ hm ((Nat.one_le_floor_iff _).mpr hxi1)
  let F : ℕ → ℝ := fun d => (1 / (d : ℝ)) *
    ∑' k : ℕ, (Real.log ((d : ℝ) * (k + (⌊xi / d⌋₊ + 1) : ℕ)))^2 /
      ((k + (⌊xi / d⌋₊ + 1) : ℕ) : ℝ)^2
  let G : ℕ → ℝ := fun d => ((Real.log d)^2 + Real.log d + 1) / (d : ℝ)
  have hF0 (d : ℕ) : 0 ≤ F d := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun k => by positivity)
  have hlarge (d : ℕ) (hd : d ∈ m.divisors) (hdx : xi < (d : ℝ)) : F d ≤ 2 * G d := by
    have hd0 : (0 : ℝ) < d := hxi0.trans hdx
    have hfloor : ⌊xi / d⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hd0).mpr hdx)
    have he : Real.exp 1 ≤ (d : ℝ) := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans (hxi.trans hdx.le)
    simpa only [F, G, hfloor, Nat.zero_add] using full_series_bound d he
  have hsum : (∑ d ∈ m.divisors, F d) ≤
      (∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), F d) +
      2 * ∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)), G d := by
    calc
      (∑ d ∈ m.divisors, F d) ≤ ∑ d ∈ m.divisors, if (d : ℝ) ≤ xi then F d else 2 * G d := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs with hdx
        · exact le_rfl
        · exact hlarge d hd (lt_of_not_ge hdx)
      _ = _ := by rw [Finset.sum_ite]; simp only [not_le, Finset.mul_sum]
  have hsmall0 : 0 ≤ ∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), F d :=
    Finset.sum_nonneg (fun d _ => hF0 d)
  have ht' : ‖tailSeries m ⌊xi⌋₊‖ ≤ K * ∑ d ∈ m.divisors, F d := by
    simpa only [K, F, Nat.floor_div_natCast] using ht
  change ‖tailSeries m ⌊xi⌋₊‖ ≤ (2 * K) *
    ((∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), F d) +
      ∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)), G d)
  calc
    _ ≤ K * ((∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ xi), F d) +
        2 * ∑ d ∈ m.divisors.filter (fun d : ℕ => xi < (d : ℝ)), G d) :=
      ht'.trans (mul_le_mul_of_nonneg_left hsum hK.le)
    _ ≤ _ := by nlinarith

end LeanLab.Tchudakov1938.Decomp362e

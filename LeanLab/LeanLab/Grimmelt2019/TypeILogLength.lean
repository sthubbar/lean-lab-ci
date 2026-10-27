/-
AI wrote this Lean code for CODEX task51.
P0074 page 11, the unscaled Type I bound with the interval logarithmic scale.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.RationalTypeI

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- An interval of length below one contains at most one integer. -/
theorem shortInterval_exp_le_one {t H θ : ℝ} (hH : 0 ≤ H) (hH1 : H < 1) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ ≤ 1 := by
  have hc := (abs_le.mp (shortInterval_card_error (t := t) hH)).2
  have hc2 : ((shortInterval t H).card : ℝ) < 2 := by linarith
  have hcNat : (shortInterval t H).card < 2 := by exact_mod_cast hc2
  calc
    _ ≤ ∑ n ∈ shortInterval t H, ‖LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ := norm_sum_le _ _
    _ = ((shortInterval t H).card : ℝ) := by simp only [norm_e, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by exact_mod_cast (show (shortInterval t H).card ≤ 1 by omega)

/-- Divisors above H cost at most D, while smaller divisors admit the rational G estimate. -/
theorem divisor_interval_split (D : ℕ) (t H α : ℝ) (hH : 0 ≤ H) :
    (∑ d ∈ Finset.Icc 1 D,
      ‖∑ k ∈ shortInterval (t / d) (H / d),
        LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * ((d : ℝ) * α))‖) ≤
      (∑ d ∈ Finset.Icc 1 (min D ⌊H⌋₊),
        LeanLab.PNTPort.Vinogradov.G (2 * H / d) (α * d)) + D := by
  let F : ℕ → ℝ := fun d => ‖∑ k ∈ shortInterval (t / d) (H / d),
    LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * ((d : ℝ) * α))‖
  let N : ℕ := min D ⌊H⌋₊
  have hsmall : (Finset.Icc 1 D).filter (fun d => d ≤ N) = Finset.Icc 1 N := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, N]
    omega
  have hs : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ≤ N), F d ≤
      ∑ d ∈ Finset.Icc 1 N, LeanLab.PNTPort.Vinogradov.G (2 * H / d) (α * d) := by
    rw [hsmall]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdH : (d : ℝ) ≤ H := by
      have hdfl : d ≤ ⌊H⌋₊ := (Finset.mem_Icc.mp hd).2.trans (min_le_right _ _)
      exact (show (d : ℝ) ≤ ⌊H⌋₊ by exact_mod_cast hdfl).trans (Nat.floor_le hH)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    apply (shortInterval_exp_cap_le (t := t / d) (div_nonneg hH hdR.le)).trans
    rw [geomCap_eq_G, mul_comm (d : ℝ) α]
    apply LeanLab.PNTPort.Vinogradov.G_mono
    rw [le_div_iff₀ hdR]
    have he : (H / (d : ℝ) + 1) * d = H + d := by field_simp
    rw [he]
    linarith
  have hl : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬d ≤ N), F d ≤ (D : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ (Finset.Icc 1 D).filter (fun d => ¬d ≤ N), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd, hdN⟩ := Finset.mem_filter.mp hd
        have hdD := Finset.mem_Icc.mp hd
        have hfl : ⌊H⌋₊ < d := by dsimp [N] at hdN; omega
        have hHd : H < (d : ℝ) := Nat.lt_of_floor_lt hfl
        have hdR : (0 : ℝ) < d := by exact_mod_cast hdD.1
        exact shortInterval_exp_le_one (div_nonneg hH hdR.le)
          ((div_lt_one hdR).mpr hHd)
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by norm_num)
      _ = (D : ℝ) := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D) (fun d => d ≤ N) F
  change ∑ d ∈ Finset.Icc 1 D, F d ≤ _
  rw [← hsplit]
  exact add_le_add hs hl

/-- The unscaled rational Type I estimate uses log H rather than log D for H at least one. -/
theorem divisorWeight_logLength_le {q : ℕ} (hq : 0 < q) {r : ℤ}
    (hr : Int.gcd r q = 1) {α : ℝ}
    (hα : |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) (weights : ℕ → ℝ) (t H : ℝ) (hH : 1 ≤ H)
    (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      25 * (H / q + D + q) * (1 + Real.log q + Real.log H) := by
  let N : ℕ := min D ⌊H⌋₊
  have hN : N ≤ D := min_le_left _ _
  have hNR : (N : ℝ) ≤ H := by
    exact (show (N : ℝ) ≤ ⌊H⌋₊ by exact_mod_cast min_le_right D ⌊H⌋₊).trans
      (Nat.floor_le (by linarith))
  have hlogN : Real.log N ≤ Real.log H := by
    rcases Nat.eq_zero_or_pos N with hz | hn
    · rw [hz, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hH
    · exact Real.log_le_log (by exact_mod_cast hn) hNR
  have hNRD : (N : ℝ) ≤ D := by exact_mod_cast hN
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hH0 : 0 ≤ H := by linarith
  have hR : 0 ≤ H / (q : ℝ) + D + q := by positivity
  have hL : 1 ≤ 1 + Real.log q + Real.log H := by linarith
  have hG := LeanLab.PNTPort.Vinogradov.sum_G_div_le hq
    (Int.isCoprime_iff_gcd_eq_one.mpr hr) hα N (X := 2 * H) (by positivity)
  have hb := (divisorWeight_fourier_le D weights t H α hw).trans
    (divisor_interval_split D t H α hH0)
  apply hb.trans
  have hfirst : 12 * (2 * H / (q : ℝ) + N + q) *
      (1 + Real.log q + Real.log N) ≤
      24 * (H / q + D + q) * (1 + Real.log q + Real.log H) := by
    have hin : 2 * H / (q : ℝ) + N + q ≤ 2 * (H / q + D + q) := by
      have : (0 : ℝ) ≤ D := by positivity
      rw [mul_div_assoc]
      linarith
    calc
      _ ≤ (12 * (2 * (H / q + D + q))) * (1 + Real.log q + Real.log H) := by
        apply mul_le_mul
        · linarith
        · linarith
        · linarith
        · positivity
      _ = _ := by ring
  have hD : (D : ℝ) ≤ (H / q + D + q) * (1 + Real.log q + Real.log H) := by
    have hRD : (D : ℝ) ≤ H / (q : ℝ) + D + q := by
      have hx : 0 ≤ H / (q : ℝ) + q := by positivity
      linarith
    exact hRD.trans (by simpa using mul_le_mul_of_nonneg_left hL hR)
  change (∑ d ∈ Finset.Icc 1 N, LeanLab.PNTPort.Vinogradov.G (2 * H / d) (α * d)) +
    (D : ℝ) ≤ _
  calc
    _ ≤ 12 * (2 * H / (q : ℝ) + N + q) *
        (1 + Real.log q + Real.log N) + D := add_le_add hG le_rfl
    _ ≤ 24 * (H / (q : ℝ) + D + q) *
        (1 + Real.log q + Real.log H) + D := add_le_add hfirst le_rfl
    _ ≤ _ := by linarith only [hD]

#print axioms shortInterval_exp_le_one
#print axioms divisor_interval_split
#print axioms divisorWeight_logLength_le
end LeanLab.Grimmelt2019.MainTerm

/-
Finite partial summation inputs for P0013 pages 22 and 23, equation 3.40.
These are derived tools for the logarithmic Type I weight.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119

namespace LeanLab.HelfgottArcs.Decomp119
open Finset

/-- Finite Abel bound for the weighted phases in P0013 page 23.
The endpoint weight and the discrete total variation are retained. -/
theorem partial_summation_bound325 (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ B) :
    ‖∑ i ∈ range N, w i • z i‖ ≤
      B * (|w (N - 1)| + ∑ i ∈ range (N - 1), |w (i + 1) - w i|) := by
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖w (N - 1) • ∑ i ∈ range N, z i‖ +
        ‖∑ i ∈ range (N - 1), (w (i + 1) - w i) • ∑ j ∈ range (i + 1), z j‖ :=
      norm_sub_le _ _
    _ ≤ |w (N - 1)| * B +
        ∑ i ∈ range (N - 1), |w (i + 1) - w i| * B := by
      apply add_le_add
      · simpa only [norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hz N le_rfl) (abs_nonneg (w (N - 1)))
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i hi
        have hiN : i + 1 ≤ N := by have := mem_range.mp hi; omega
        simpa only [norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hz (i + 1) hiN) (abs_nonneg (w (i + 1) - w i))
    _ = _ := by rw [← sum_mul]; ring

/-- A nonnegative unimodal weight has endpoint plus variation at most twice its peak.
This is the finite form of the first derivative norm used on P0013 pages 7 and 23. -/
theorem unimodal_variation_bound325 (w : ℕ → ℝ) (N p : ℕ) (hp : p < N)
    (hw : ∀ i < N, 0 ≤ w i)
    (hleft : ∀ i < p, w i ≤ w (i + 1))
    (hright : ∀ i ∈ Ico p (N - 1), w (i + 1) ≤ w i) :
    |w (N - 1)| + ∑ i ∈ range (N - 1), |w (i + 1) - w i| ≤ 2 * w p := by
  have hpN : p ≤ N - 1 := by omega
  have hN : N - 1 < N := by omega
  have hl : ∑ i ∈ range p, |w (i + 1) - w i| = w p - w 0 := by
    rw [← sum_range_sub w p]
    apply sum_congr rfl
    intro i hi
    exact abs_of_nonneg (sub_nonneg.mpr (hleft i (mem_range.mp hi)))
  have hr : ∑ i ∈ Ico p (N - 1), |w (i + 1) - w i| = w p - w (N - 1) := by
    calc
      _ = ∑ i ∈ Ico p (N - 1), -(w (i + 1) - w i) := by
        apply sum_congr rfl
        intro i hi
        exact abs_of_nonpos (sub_nonpos.mpr (hright i hi))
      _ = _ := by rw [sum_neg_distrib, sum_Ico_sub w hpN]; ring
  rw [← sum_range_add_sum_Ico _ hpN, hl, hr, abs_of_nonneg (hw _ hN)]
  have hw0 := hw 0 (by omega)
  linarith

/-- Abel summation for a nonnegative unimodal smoothing weight.
Source: P0013 page 23, a derived finite version of the weighted phase estimate. -/
theorem unimodal_partial_sum_bound325 (w : ℕ → ℝ) (z : ℕ → ℂ) (N p : ℕ)
    (hp : p < N) (B : ℝ) (hB : 0 ≤ B)
    (hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ B)
    (hw : ∀ i < N, 0 ≤ w i)
    (hleft : ∀ i < p, w i ≤ w (i + 1))
    (hright : ∀ i ∈ Ico p (N - 1), w (i + 1) ≤ w i) :
    ‖∑ i ∈ range N, w i • z i‖ ≤ 2 * B * w p := by
  calc
    _ ≤ B * (|w (N - 1)| + ∑ i ∈ range (N - 1), |w (i + 1) - w i|) :=
      partial_summation_bound325 w z N B hz
    _ ≤ B * (2 * w p) := mul_le_mul_of_nonneg_left
      (unimodal_variation_bound325 w N p hp hw hleft hright) hB
    _ = _ := by ring

/-- Weighted interval phases with their exact discrete variation.
Source: P0013 pages 10 and 23, derived by finite Abel summation. -/
theorem weighted_phase_variation325 (w : ℕ → ℝ) (α : ℝ) (M N : ℕ)
    (hα : 0 < |α - round α|) :
    ‖∑ i ∈ range N, w i • e (α * (M + i))‖ ≤
      min (N : ℝ) (1 / (2 * |α - round α|)) *
        (|w (N - 1)| + ∑ i ∈ range (N - 1), |w (i + 1) - w i|) := by
  apply partial_summation_bound325
  intro k hk
  exact (interval_phase_min252 α M k hα).trans
    (min_le_min_right _ (by exact_mod_cast hk))

/-- A unimodal weight costs at most twice its peak in the geometric phase bound.
Source: P0013 pages 10 and 23, derived finite smoothing bound. -/
theorem unimodal_phase_bound325 (w : ℕ → ℝ) (α : ℝ) (M N p : ℕ)
    (hα : 0 < |α - round α|) (hp : p < N)
    (hw : ∀ i < N, 0 ≤ w i)
    (hleft : ∀ i < p, w i ≤ w (i + 1))
    (hright : ∀ i ∈ Ico p (N - 1), w (i + 1) ≤ w i) :
    ‖∑ i ∈ range N, w i • e (α * (M + i))‖ ≤
      2 * min (N : ℝ) (1 / (2 * |α - round α|)) * w p := by
  apply unimodal_partial_sum_bound325 w _ N p hp
  · exact le_min (Nat.cast_nonneg _) (by positivity)
  · intro k hk
    exact (interval_phase_min252 α M k hα).trans
      (min_le_min_right _ (by exact_mod_cast hk))
  · exact hw
  · exact hleft
  · exact hright

/-- The smoothing weight increases up to one half, including its zero extension.
Source: P0013 page 3 equation 1.4. -/
theorem eta2_monotone_left325 : MonotoneOn eta2 (Set.Iic (1 / 2)) := by
  intro a ha b hb hab
  by_cases ha4 : a < 1 / 4
  · rw [eta2_of_lt ha4]
    exact eta2_nonneg b
  · have ha4' : 1 / 4 ≤ a := le_of_not_gt ha4
    rw [eta2_of_mem_left ha4' ha, eta2_of_mem_left (ha4'.trans hab) hb]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) (by norm_num)

/-- The smoothing weight decreases after one half, including its zero extension.
Source: P0013 page 3 equation 1.4. -/
theorem eta2_antitone_right325 : AntitoneOn eta2 (Set.Ici (1 / 2)) := by
  intro a ha b hb hab
  change 1 / 2 ≤ a at ha
  change 1 / 2 ≤ b at hb
  by_cases hb1 : 1 < b
  · rw [eta2_of_gt hb1]
    exact eta2_nonneg a
  · have hb1' : b ≤ 1 := le_of_not_gt hb1
    rw [eta2_of_mem_right hb hb1', eta2_of_mem_right ha (hab.trans hb1')]
    exact mul_le_mul_of_nonpos_left
      (Real.log_le_log (by linarith) hab) (by norm_num)

/-- Between two points eta2 is at least the smaller endpoint value.
Source: P0013 page 3 equation 1.4, derived from its two monotone pieces. -/
theorem eta2_between325 (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    min (eta2 a) (eta2 c) ≤ eta2 b := by
  by_cases hb : b ≤ 1 / 2
  · exact (min_le_left _ _).trans
      (eta2_monotone_left325 (hab.trans hb) hb hab)
  · have hb' : 1 / 2 ≤ b := le_of_not_ge hb
    exact (min_le_right _ _).trans
      (eta2_antitone_right325 hb' (hb'.trans hbc) hbc)

/-- Ordered samples of a nonnegative single peak weight preserve the Abel bound.
Source: P0013 page 23, derived finite smoothing tool. -/
theorem sampled_weight_phase_bound325 (w : ℝ → ℝ) (t : ℕ → ℝ) (ht : Monotone t)
    (H : ℝ) (hw : ∀ t, 0 ≤ w t) (hpeak : ∀ t, w t ≤ H)
    (hbetween : ∀ a b c, a ≤ b → b ≤ c → min (w a) (w c) ≤ w b)
    (α : ℝ) (M N : ℕ) (hα : 0 < |α - round α|) :
    ‖∑ i ∈ range N, w (t i) • e (α * (M + i))‖ ≤
      2 * H * min (N : ℝ) (1 / (2 * |α - round α|)) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hN0 : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨p, hp, hmax⟩ := (range N).exists_max_image (fun i => w (t i))
      ⟨0, mem_range.mpr hN0⟩
    have hpN : p < N := mem_range.mp hp
    have hl : ∀ i < p, w (t i) ≤ w (t (i + 1)) := by
      intro i hi
      have hiN : i < N := hi.trans hpN
      have hh := hbetween (t i) (t (i + 1)) (t p) (ht (by omega)) (ht (by omega))
      rwa [min_eq_left (hmax i (mem_range.mpr hiN))] at hh
    have hr : ∀ i ∈ Ico p (N - 1), w (t (i + 1)) ≤ w (t i) := by
      intro i hi
      obtain ⟨hpi, hiN⟩ := mem_Ico.mp hi
      have hiN' : i + 1 < N := by omega
      have hh := hbetween (t p) (t i) (t (i + 1)) (ht hpi) (ht (by omega))
      rwa [min_eq_right (hmax (i + 1) (mem_range.mpr hiN'))] at hh
    calc
      _ ≤ 2 * min (N : ℝ) (1 / (2 * |α - round α|)) * w (t p) :=
        unimodal_phase_bound325 (fun i => w (t i)) α M N p hα hpN
          (fun i _ => hw (t i)) hl hr
      _ ≤ 2 * min (N : ℝ) (1 / (2 * |α - round α|)) * H :=
        mul_le_mul_of_nonneg_left (hpeak _) (by positivity)
      _ = _ := by ring

/-- Geometric cancellation survives monotone sampling of eta2.
Source: P0013 pages 7, 10 and 23, derived using the peak 4 log 2. -/
theorem eta2_sampled_phase_bound325 (t : ℕ → ℝ) (ht : Monotone t)
    (α : ℝ) (M N : ℕ) (hα : 0 < |α - round α|) :
    ‖∑ i ∈ range N, eta2 (t i) • e (α * (M + i))‖ ≤
      8 * Real.log 2 * min (N : ℝ) (1 / (2 * |α - round α|)) := by
  simpa only [show (2 : ℝ) * (4 * Real.log 2) = 8 * Real.log 2 by ring] using
    sampled_weight_phase_bound325 eta2 t ht (4 * Real.log 2)
      eta2_nonneg eta2_le eta2_between325 α M N hα

/-- The logarithmic smoothing weight increases up to one half for rho at least four.
Source: P0013 page 7 equation 2.6 and page 23. -/
theorem eta2rho_monotone_left325 {ρ : ℝ} (hρ : 4 ≤ ρ) :
    MonotoneOn (eta2rho ρ) (Set.Iic (1 / 2)) := by
  intro a ha b hb hab
  change a ≤ 1 / 2 at ha
  change b ≤ 1 / 2 at hb
  by_cases ha4 : a < 1 / 4
  · simp only [eta2rho, eta2_of_lt ha4, mul_zero]
    exact eta2rho_nonneg hρ b
  · have ha4' : 1 / 4 ≤ a := le_of_not_gt ha4
    have hρa : 1 ≤ ρ * a := by nlinarith
    have hρb : 1 ≤ ρ * b := by nlinarith
    exact mul_le_mul
      (Real.log_le_log (by linarith) (mul_le_mul_of_nonneg_left hab (by linarith)))
      (eta2_monotone_left325 ha hb hab) (eta2_nonneg a) (Real.log_nonneg hρb)

/-- The logarithmic smoothing weight decreases after one half for rho at least four.
Source: P0013 page 7 equation 2.6 and page 23. -/
theorem eta2rho_antitone_right325 {ρ : ℝ} (hρ : 4 ≤ ρ) :
    AntitoneOn (eta2rho ρ) (Set.Ici (1 / 2)) := by
  intro a ha b hb hab
  change 1 / 2 ≤ a at ha
  change 1 / 2 ≤ b at hb
  by_cases hb1 : 1 < b
  · simp only [eta2rho, eta2_of_gt hb1, mul_zero]
    exact eta2rho_nonneg hρ a
  · have hb1' : b ≤ 1 := le_of_not_gt hb1
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hρ0 : 0 < ρ := by linarith
    have hl2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    have hla : -Real.log 2 ≤ Real.log a := by
      rw [← hl2]
      exact Real.log_le_log (by norm_num) ha
    have hlb : -Real.log 2 ≤ Real.log b := hla.trans (Real.log_le_log ha0 hab)
    have hlρ : 2 * Real.log 2 ≤ Real.log ρ := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hρ
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hh
      norm_num at hh
      exact hh
    have hh := mul_nonneg
      (sub_nonneg.mpr (Real.log_le_log ha0 hab))
      (show 0 ≤ Real.log ρ + Real.log a + Real.log b by linarith)
    simp only [eta2rho, Real.log_mul hρ0.ne' hb0.ne', Real.log_mul hρ0.ne' ha0.ne',
      eta2_of_mem_right hb hb1', eta2_of_mem_right ha (hab.trans hb1')]
    nlinarith

/-- Between two points the logarithmic weight is at least the smaller endpoint value.
Source: P0013 page 7 equation 2.6, a derived shape property. -/
theorem eta2rho_between325 {ρ : ℝ} (hρ : 4 ≤ ρ)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    min (eta2rho ρ a) (eta2rho ρ c) ≤ eta2rho ρ b := by
  by_cases hb : b ≤ 1 / 2
  · exact (min_le_left _ _).trans
      (eta2rho_monotone_left325 hρ (hab.trans hb) hb hab)
  · have hb' : 1 / 2 ≤ b := le_of_not_ge hb
    exact (min_le_right _ _).trans
      (eta2rho_antitone_right325 hρ hb' (hb'.trans hbc) hbc)

/-- Geometric cancellation for the logarithmic Type I smoothing weight.
Source: P0013 pages 7 and 23, derived finite version with the 8 log 2 factor. -/
theorem eta2rho_sampled_phase_bound325 {ρ : ℝ} (hρ : 4 ≤ ρ)
    (t : ℕ → ℝ) (ht : Monotone t) (α : ℝ) (M N : ℕ)
    (hα : 0 < |α - round α|) :
    ‖∑ i ∈ range N, eta2rho ρ (t i) • e (α * (M + i))‖ ≤
      8 * Real.log 2 * Real.log ρ * min (N : ℝ) (1 / (2 * |α - round α|)) := by
  have hpeak (t : ℝ) : eta2rho ρ t ≤ Real.log ρ * (4 * Real.log 2) :=
    (eta2rho_le_log_mul hρ t).trans
      (mul_le_mul_of_nonneg_left (eta2_le t) (Real.log_nonneg (by linarith)))
  convert sampled_weight_phase_bound325 (eta2rho ρ) t ht
    (Real.log ρ * (4 * Real.log 2)) (eta2rho_nonneg hρ) hpeak
    (eta2rho_between325 hρ) α M N hα using 1; ring

/-- Removing the constant phase leaves the norm of the odd progression unchanged.
Source: P0013 page 21 equation 3.35 and its change of variable. -/
theorem odd_phase_norm325 (w : ℕ → ℝ) (α : ℝ) (N : ℕ) :
    ‖∑ i ∈ range N, w i • e (α * (2 * i + 1))‖ =
      ‖∑ i ∈ range N, w i • e ((2 * α) * (0 + i))‖ := by
  have he (i : ℕ) : e (α * (2 * i + 1)) = e α * e ((2 * α) * (0 + i)) := by
    unfold e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum : ∑ i ∈ range N, w i • e (α * (2 * i + 1)) =
      e α * ∑ i ∈ range N, w i • e ((2 * α) * (0 + i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [he, mul_smul_comm]
  rw [hsum, norm_mul, show ‖e α‖ = 1 by simp [e, Complex.norm_exp], one_mul]

/-- Finite odd eta2 sums retain the doubled frequency cancellation.
Source: P0013 page 21 equation 3.35, a derived Abel bound. -/
theorem odd_eta2_phase_bound325 (s α : ℝ) (hs : 0 ≤ s) (N : ℕ)
    (hα : 0 < |2 * α - round (2 * α)|) :
    ‖∑ i ∈ range N, eta2 (s * (2 * i + 1)) • e (α * (2 * i + 1))‖ ≤
      8 * Real.log 2 * min (N : ℝ) (1 / (2 * |2 * α - round (2 * α)|)) := by
  rw [odd_phase_norm325]
  have ht : Monotone (fun i : ℕ => s * (2 * (i : ℝ) + 1)) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : 2 * i + 1 ≤ 2 * j + 1)) hs
  simpa only [Nat.cast_zero] using
    eta2_sampled_phase_bound325 (fun i : ℕ => s * (2 * (i : ℝ) + 1)) ht (2 * α) 0 N hα

/-- Finite odd sums with the logarithmic weight used by Type I.
Source: P0013 page 23, the displayed estimate for T with the logarithmic weight. -/
theorem odd_log_eta2_phase_bound325 (x m α : ℝ) (hm : 0 < m) (hx : 4 * m ≤ x)
    (N : ℕ) (hα : 0 < |2 * (α * m) - round (2 * (α * m))|) :
    ‖∑ i ∈ range N, (Real.log (2 * i + 1) * eta2 (m * (2 * i + 1) / x)) •
      e ((α * m) * (2 * i + 1))‖ ≤
      8 * Real.log 2 * Real.log (x / m) *
        min (N : ℝ) (1 / (2 * |2 * (α * m) - round (2 * (α * m))|)) := by
  have hx0 : 0 < x := by linarith
  have hρ : 4 ≤ x / m := (le_div_iff₀ hm).mpr hx
  have hw (i : ℕ) : Real.log (2 * i + 1) * eta2 (m * (2 * i + 1) / x) =
      eta2rho (x / m) (m * (2 * i + 1) / x) := by
    unfold eta2rho
    congr 2
    field_simp
  simp_rw [hw]
  rw [odd_phase_norm325]
  have ht : Monotone (fun i : ℕ => m * (2 * (i : ℝ) + 1) / x) := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hx0.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : 2 * i + 1 ≤ 2 * j + 1)) hm.le
  simpa only [Nat.cast_zero] using eta2rho_sampled_phase_bound325 hρ
    (fun i : ℕ => m * (2 * (i : ℝ) + 1) / x) ht (2 * (α * m)) 0 N hα

/-- The elementary length bound for any finite samples of eta2.
Source: P0013 pages 3 and 21, used at integral frequencies. -/
theorem eta2_sampled_length_bound325 (t : ℕ → ℝ) (α : ℝ) (M N : ℕ) :
    ‖∑ i ∈ range N, eta2 (t i) • e (α * (M + i))‖ ≤ 4 * Real.log 2 * N := by
  calc
    _ ≤ ∑ i ∈ range N, ‖eta2 (t i) • e (α * (M + i))‖ := norm_sum_le _ _
    _ = ∑ i ∈ range N, eta2 (t i) := by
      apply sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (eta2_nonneg _),
        show ‖e (α * (M + i))‖ = 1 by simp [e, Complex.norm_exp], mul_one]
    _ ≤ ∑ _i ∈ range N, 4 * Real.log 2 := sum_le_sum (fun i _ => eta2_le _)
    _ = _ := by simp [mul_comm]

/-- A full short block of odd smoothed phase sums, including the exceptional residue.
Source: P0013 pages 10 to 13 and 21, a derived weighted residue bound. -/
theorem minor_odd_eta2_block325 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (s : Finset ℕ) (M : ℕ)
    (hs : s ⊆ Ico M (M + q))
    (hn : ∀ n ∈ s, (n : ℝ) ≤ (3 / 4 * x ^ ((2 : ℝ) / 3)) / 2) (N : ℕ) :
    ∑ n ∈ s, ‖∑ i ∈ range N,
      eta2 ((n : ℝ) / x * (2 * i + 1)) • e ((α * n) * (2 * i + 1))‖ ≤
      8 * Real.log 2 * min ((s.card : ℝ) * N) ((N : ℝ) + 2 * q * (1 + Real.log q)) := by
  have hx : 0 < x := by have := h.1; linarith
  calc
    _ ≤ ∑ n ∈ s, 8 * Real.log 2 *
        (if |2 * α * n - round (2 * α * n)| = 0 then (N : ℝ)
          else min (N : ℝ) (1 / (2 * |2 * α * n - round (2 * α * n)|))) := by
      apply sum_le_sum
      intro n _
      by_cases hd : |2 * α * n - round (2 * α * n)| = 0
      · rw [ite_eq_left hd, odd_phase_norm325]
        have hlen := eta2_sampled_length_bound325
          (fun i : ℕ => (n : ℝ) / x * (2 * (i : ℝ) + 1)) (2 * (α * n)) 0 N
        simp only [Nat.cast_zero] at hlen
        apply hlen.trans
        have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have hN := Nat.cast_nonneg (α := ℝ) N
        nlinarith
      · rw [ite_eq_right hd]
        simpa only [mul_assoc] using odd_eta2_phase_bound325 ((n : ℝ) / x) (α * n)
          (by positivity) N (by simpa only [← mul_assoc] using
            (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)))
    _ = 8 * Real.log 2 * ∑ n ∈ s,
        (if |2 * α * n - round (2 * α * n)| = 0 then (N : ℝ)
          else min (N : ℝ) (1 / (2 * |2 * α * n - round (2 * α * n)|))) := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (minor_clipped_reciprocal_sum252 x α a q δ h s M hs hn N (Nat.cast_nonneg N))
      (by positivity)

end LeanLab.HelfgottArcs.Decomp119

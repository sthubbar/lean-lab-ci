/-
Gallagher1970 page 331 displays 12 and 13 for a fixed modulus.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.LargeSieve.Multiplicative
import LeanLab.RieselVaughan1983.Lemma11Char
import LeanLab.BHP1997.Gallagher605

namespace LeanLab.BHP1997.Decomp513a
open Finset

/-- Gallagher 1970 page 331 display 12, the finite residue class step.
A bound H for the count in each residue class gives phi q times H
as the coefficient energy multiplier. No coefficient size bound is needed. -/
theorem character_square_sum_of_fiber_card {q : ℕ} [NeZero q]
    (S : Finset ℕ) (a : ℕ → ℂ) {H : ℝ} (hH : 0 ≤ H)
    (hcard : ∀ b : ZMod q,
      ((S.filter (fun n : ℕ => (n : ZMod q) = b)).card : ℝ) ≤ H) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ n‖ ^ 2) ≤
      (q.totient : ℝ) * H * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  let A (b : ZMod q) : ℂ := ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), a n
  have heq (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ S, a n * χ n) = ∑ b : ZMod q, χ b * A b := by
    rw [← Finset.sum_fiberwise S (fun n => (n : ZMod q)) (fun n => a n * χ n)]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [A]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [(Finset.mem_filter.mp hn).2, mul_comm]
  have hA (b : ZMod q) : ‖A b‖ ^ 2 ≤
      H * ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), ‖a n‖ ^ 2 := by
    let P := S.filter (fun n : ℕ => (n : ZMod q) = b)
    have hnorm : ‖A b‖ ≤ ∑ n ∈ P, ‖a n‖ := norm_sum_le _ _
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := P)
      (f := fun _ : ℕ => (1 : ℝ)) (g := fun n => ‖a n‖)
    have hcs' : (∑ n ∈ P, ‖a n‖) ^ 2 ≤
        (P.card : ℝ) * ∑ n ∈ P, ‖a n‖ ^ 2 := by simpa using hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (hcs'.trans (mul_le_mul_of_nonneg_right (hcard b)
        (Finset.sum_nonneg (fun n _ => sq_nonneg _))))
  simp_rw [heq]
  rw [LeanLab.PNTPort.LargeSieve.sum_chars_normSq]
  calc
    _ ≤ (q.totient : ℝ) * ∑ b : ZMod q,
        H * ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = b), ‖a n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro b hb
      split_ifs
      · exact hA b
      · exact mul_nonneg hH (Finset.sum_nonneg (fun n _ => sq_nonneg _))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]
      ring

/-- Gallagher 1970 page 331 Lemma 2 display 12.
For arbitrary coefficients supported in a real interval of length z,
character orthogonality costs at most q plus z. -/
theorem character_square_sum_interval {q : ℕ} [NeZero q]
    (S : Finset ℕ) (a : ℕ → ℂ) (y z : ℝ) (hz : 0 ≤ z)
    (hS : ∀ n ∈ S, y < n ∧ (n : ℝ) ≤ y + z) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ n‖ ^ 2) ≤
      ((q : ℝ) + z) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hH : 0 ≤ z / (q : ℝ) + 1 := by positivity
  have h := character_square_sum_of_fiber_card S a hH
    (LeanLab.RieselVaughan1983.L11.card_class_le_real S y z hz hS)
  apply h.trans
  have hphi : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hfactor : (q.totient : ℝ) * (z / (q : ℝ) + 1) ≤ (q : ℝ) + z := by
    calc
      _ ≤ (q : ℝ) * (z / (q : ℝ) + 1) := mul_le_mul_of_nonneg_right hphi hH
      _ = _ := by field_simp; ring
  exact mul_le_mul_of_nonneg_right hfactor (Finset.sum_nonneg (fun n _ => sq_nonneg _))

end LeanLab.BHP1997.Decomp513a

namespace LeanLab.BHP1997.Decomp513a
open Finset MeasureTheory
open LeanLab.BHP1997.Gallagher605

/-- Gallagher1970 page 331 display 12 on a logarithmic frequency window.
The extra two cover the closed lower endpoint of the finite window. -/
theorem fixed_modulus_mellin_window (a : ℕ → ℂ) (q N : ℕ) [NeZero q]
    {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
        (fun n => Real.log n) δ u‖ ^ 2) ≤
      (Real.exp (u + δ) - Real.exp u + 2 + (q : ℝ)) *
        ∑ n ∈ Finset.Icc 1 N,
          (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
  classical
  let S := (Finset.Icc 1 N).filter
    (fun n : ℕ => u ∈ Set.Icc (Real.log n - δ) (Real.log n))
  have heq (χ : DirichletCharacter ℂ q) :
      frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
        (fun n => Real.log n) δ u = ∑ n ∈ S, a n * χ n := by
    simp only [frequencyWindow, S, sum_filter, Set.indicator]
  have hnorm : (∑ n ∈ S, ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N,
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
    simp only [S, sum_filter, Set.indicator]
  have hdiff : 0 ≤ Real.exp (u + δ) - Real.exp u :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hs : ∀ n ∈ S, Real.exp u - 1 < n ∧
      (n : ℝ) ≤ (Real.exp u - 1) +
        (Real.exp (u + δ) - Real.exp u + 1) := by
    intro n hn
    obtain ⟨hnN, hnu⟩ := mem_filter.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnN).1
    have hlo : Real.exp u ≤ n := by
      simpa only [Real.exp_log hnpos] using Real.exp_le_exp.mpr hnu.2
    have hhi : (n : ℝ) ≤ Real.exp (u + δ) := by
      rw [← Real.exp_log hnpos]
      exact Real.exp_le_exp.mpr (by linarith [hnu.1])
    constructor <;> linarith
  simp_rw [heq]
  rw [← hnorm]
  have h := character_square_sum_interval (q := q) S a (Real.exp u - 1)
    (Real.exp (u + δ) - Real.exp u + 1) (by linarith) hs
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun n _ => sq_nonneg _))
  linarith

/-- Gallagher1970 page 331 proof of Theorem 2 display 13.
Integrate the logarithmic windows before estimating their scalar weights. -/
theorem fixed_modulus_integrated_mellin_window (a : ℕ → ℂ)
    (q N : ℕ) [NeZero q] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ χ : DirichletCharacter ℂ q, ∫ u : ℝ,
      ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
        (fun n => Real.log n) δ u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, (δ * ((q : ℝ) + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 := by
  classical
  let K : ℝ → ℝ := fun u => Real.exp (u + δ) - Real.exp u + 2 + (q : ℝ)
  let W (χ : DirichletCharacter ℂ q) (u : ℝ) :=
    ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n) (fun n => Real.log n) δ u‖ ^ 2
  have hiW (χ : DirichletCharacter ℂ q) : Integrable (W χ) :=
    integrable_frequencyWindow_energy _ _ _ _
  have hiR (n : ℕ) : Integrable (fun u => K u *
      (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u) := by
    have heq : (fun u => K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
        (fun _ => ‖a n‖ ^ 2) u) =
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun u => K u * ‖a n‖ ^ 2) := by
      ext u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n) <;> simp [hu]
    rw [heq]
    exact (by dsimp [K]; fun_prop : Continuous (fun u => K u * ‖a n‖ ^ 2)).integrableOn_Icc.integrable_indicator measurableSet_Icc
  change (∑ χ : DirichletCharacter ℂ q, ∫ u, W χ u) ≤ _
  rw [← integral_finsetSum _ (fun χ _ => hiW χ)]
  calc
    _ ≤ ∫ u, ∑ n ∈ Finset.Icc 1 N, K u *
        (Set.Icc (Real.log n - δ) (Real.log n)).indicator (fun _ => ‖a n‖ ^ 2) u := by
      apply integral_mono (integrable_finsetSum _ (fun χ _ => hiW χ))
        (integrable_finsetSum _ (fun n _ => hiR n))
      intro u
      dsimp only [W, K]
      rw [← mul_sum]
      exact fixed_modulus_mellin_window a q N hδ.le u
    _ = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 *
        ∫ u : ℝ, K u * (Set.Icc (Real.log n - δ) (Real.log n)).indicator
          (fun _ => (1 : ℝ)) u := by
      rw [integral_finsetSum _ (fun n _ => hiR n)]
      apply sum_congr rfl
      intro n _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Icc (Real.log n - δ) (Real.log n)
      · simp [hu]; ring
      · simp [hu]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hb := mellin_window_weight_bound (Real.log n) (q : ℝ) hδ.le hδ1
      rw [Real.exp_log hnpos] at hb
      dsimp [K]
      have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a n‖)
      nlinarith

/-- Gallagher1970 page 331 Theorem 2 display 13 with an explicit constant.
The estimate includes all characters of one positive modulus and arbitrary coefficients. -/
theorem fixed_modulus_hybrid_mean_value (q N : ℕ) [NeZero q]
    (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
      (2 * Real.pi ^ 3) * ∑ n ∈ Finset.Icc 1 N,
        ((q : ℝ) * T + n) * ‖a n‖ ^ 2 := by
  classical
  let δ : ℝ := 1 / T
  have hTpos : 0 < T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_one hTpos]; exact hT
  let C : ℝ := Real.pi ^ 3 / (2 * δ ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let W (χ : DirichletCharacter ℂ q) :=
    ∫ u : ℝ, ‖frequencyWindow (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) δ u‖ ^ 2
  have htime (χ : DirichletCharacter ℂ q) :
      (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) ≤ C * W χ := by
    rw [characterPolynomial_time_integral]
    have hnear : δ * (T / (2 * Real.pi)) ≤ 1 / 2 := by
      dsimp [δ]
      have he : (1 / T) * (T / (2 * Real.pi)) = 1 / (2 * Real.pi) := by field_simp
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Real.pi_gt_three]
    have hh := gallagher_window_smoothing (Finset.Icc 1 N) (fun n => a n * χ n)
      (fun n => Real.log n) hδ (div_nonneg hTpos.le (by positivity)) hnear
    apply (mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).trans_eq
    dsimp [C, W]
    ring
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, C * W χ := sum_le_sum (fun χ _ => htime χ)
    _ = C * (∑ χ : DirichletCharacter ℂ q, W χ) := by rw [mul_sum]
    _ ≤ C * ∑ n ∈ Finset.Icc 1 N,
        (δ * ((q : ℝ) + 2) + 2 * δ ^ 2 * n) * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (fixed_modulus_integrated_mellin_window a q N hδ hδ1) hC
    _ ≤ _ := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro n _
      rw [← mul_assoc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hqr : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      have he : C * (δ * ((q : ℝ) + 2) + 2 * δ ^ 2 * n) =
          (Real.pi ^ 3 / 2) * T * ((q : ℝ) + 2) + Real.pi ^ 3 * n := by
        dsimp [C, δ]
        field_simp
      rw [he]
      have hmult := mul_le_mul_of_nonneg_left
        (show (q : ℝ) + 2 ≤ 3 * (q : ℝ) by linarith)
        (show 0 ≤ (Real.pi ^ 3 / 2) * T by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hrest : 0 ≤ Real.pi ^ 3 * ((q : ℝ) * T) := by positivity
      have hrest2 : 0 ≤ Real.pi ^ 3 * n := by positivity
      nlinarith

end LeanLab.BHP1997.Decomp513a

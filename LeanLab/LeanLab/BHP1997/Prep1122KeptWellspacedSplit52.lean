/-
P0069 Baker Harman Pintz 1997, pages 11, 12, 20, 48 and 53, read from papers/P0069-original.pdf.
Burst burst-20261122, WAVE 3 unit on the LEAF kept52_wellspaced of the branch
claude/BHP1997-upD_kept_52, file Prep1122KeptLemma33Pieces52.lean.

That LEAF is the end of the proof of Lemma 33 on page 48, "||LMN||_2^2 << Y L^-A if t is in
[T, T + T2]", read for the kept part of k_m on page 53 and the principal character. Its own
hypotheses, Theorem 4 and Lemma 9, do not give it: the paper also uses Lemma 5 on page 20 for
(3.2) of the prime polynomials, and Lemma 1, display 3.3 on page 11, for the discrete mean value
bound. This file splits it once into four LEAFs, each a cited step of the paper:
1. kept52_lemma33_block, HARD, CONDITIONAL on Theorem 4: Lemma 33 on page 48 for one product
   LMN with (beta1, beta2) in R, P1 or P2, on one block of length T2.
2. kept52_prime_32, HARD, CITED: Lemma 5 on page 20, (3.2) for a prime polynomial at the
   principal character for T0 <= |t| <= Y.
3. kept52_mvt_lemma1, HARD, CITED: Lemma 1, display 3.3 on page 11, the mean value bound.
4. kept52_box_reduce, HARD: page 53, the reduction of the kept part of k_m to products to
   which Lemma 33 applies, from the three statements above as hypotheses.
kept52_wellspaced_split has the exact statement of kept52_wellspaced and is PROVED from them.

New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves
import LeanLab.BHP1997.HybridWindow605
import LeanLab.BHP1997.CriticalLine605
import LeanLab.BHP1997.Decomp513b

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

section MvtLemma1Helpers
open Finset MeanSquareC165 LeanLab.BHP1997.Gallagher605

/-- P0069 page 11, the energy of display 3.3 for the logarithmic derivative coefficients, with the
range hypothesis weakened from `2 ≤ F` to `1 ≤ F` (only `2 ≤ x` is needed). This is
`Decomp513b.log_weight_energy_le` with that one hypothesis weakened. -/
private theorem mvt_log_weight_energy_le (a : ℕ → ℂ) {c₁ c₂ F x : ℝ}
    (hlo : 0 < c₁ * F) (hc₂ : 0 < c₂) (hF : 1 ≤ F) (hFx : F ≤ x) (hx : 2 ≤ x) :
    energy (fun n => (Real.log n : ℂ) * a n) c₁ c₂ F ≤
      ((1 + |Real.log c₂| / Real.log 2) * Real.log x) ^ 2 * energy a c₁ c₂ F := by
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogF : Real.log F ≤ Real.log x := Real.log_le_log hF0 hFx
  have hscale : |Real.log c₂| ≤ (|Real.log c₂| / Real.log 2) * Real.log x := by
    calc
      _ = (|Real.log c₂| / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlx (by positivity)
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨_, hnlo, hnhi⟩ := Finset.mem_filter.mp hn
  have hnpos : 0 < (n : ℝ) := hlo.trans hnlo
  have hnN : 0 < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hupper : Real.log (n : ℝ) ≤ |Real.log c₂| + Real.log x := by
    have hh := Real.log_le_log hnpos hnhi.le
    rw [Real.log_mul hc₂.ne' hF0.ne'] at hh
    linarith [le_abs_self (Real.log c₂)]
  have hbound : Real.log (n : ℝ) ≤ (1 + |Real.log c₂| / Real.log 2) * Real.log x := by
    nlinarith
  have hnorm : ‖(Real.log (n : ℝ) : ℂ) * a n‖ ^ 2 ≤
      ((1 + |Real.log c₂| / Real.log 2) * Real.log x) ^ 2 * ‖a n‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlogn hbound 2) (sq_nonneg _)
  calc
    _ ≤ (((1 + |Real.log c₂| / Real.log 2) * Real.log x) ^ 2 * ‖a n‖ ^ 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right hnorm hnpos.le
    _ = _ := by ring

/-- P0069 page 11 display 3.3, the continuous critical line input, as
`Decomp513a.dirPoly_integral_square_sum` states it: Gallagher 1970 page 331 display 13 over all
characters of one modulus. -/
private theorem mvt_dirPoly_integral_square_sum (a : ℕ → ℂ) {c₁ c₂ F T : ℝ}
    {q : ℕ} [NeZero q] (hlo : 0 < c₁ * F) (hT : 1 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..T, ‖Thm4.dirPoly a c₁ c₂ F χ (Thm4.half t)‖ ^ 2) ≤
      (2 * Real.pi ^ 3) * ((q : ℝ) * T + c₂ * F) * energy a c₁ c₂ F := by
  classical
  let N := ⌊c₂ * F⌋₊
  let S := (Finset.range (N + 1)).filter
    (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F)
  let b (n : ℕ) : ℂ := if n ∈ S then a n / (n : ℂ) ^ (1 / 2 : ℂ) else 0
  have hnpos (n : ℕ) (hn : n ∈ S) : 0 < (n : ℝ) :=
    hlo.trans (mem_filter.mp hn).2.1
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn0 : 0 < n := by exact_mod_cast hnpos n hn
    exact mem_Icc.mpr ⟨by omega, by
      have := mem_range.mp (mem_filter.mp hn).1
      omega⟩
  have hpoly (χ : DirichletCharacter ℂ q) (t : ℝ) :
      characterPolynomial χ b N t = Thm4.dirPoly a c₁ c₂ F χ (Thm4.half t) := by
    unfold characterPolynomial Thm4.dirPoly
    change (∑ n ∈ Finset.Icc 1 N, b n * χ n *
      Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)) =
      ∑ n ∈ S, a n * χ n / (n : ℂ) ^ Thm4.half t
    rw [← Finset.sum_subset hsub (by
      intro n hn hnS
      simp [b, hnS])]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [b]
    rw [if_pos hn]
    exact Decomp513a.critical_line_term n (hnpos n hn) (a n) (χ n) t
  have hbn (n : ℕ) (hn : n ∈ S) : ‖b n‖ ^ 2 = ‖a n‖ ^ 2 / (n : ℝ) := by
    simp only [b, if_pos hn]
    exact Decomp513a.critical_line_coefficient_norm_sq n (hnpos n hn) (a n)
  have henergy : (∑ n ∈ Finset.Icc 1 N,
      ((q : ℝ) * T + n) * ‖b n‖ ^ 2) ≤
      ((q : ℝ) * T + c₂ * F) * energy a c₁ c₂ F := by
    rw [← Finset.sum_subset hsub (by intro n hn hnS; simp [b, hnS])]
    change _ ≤ ((q : ℝ) * T + c₂ * F) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ)
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [hbn n hn]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    linarith [(mem_filter.mp hn).2.2]
  have h := Decomp513a.fixed_modulus_hybrid_mean_value q N b hT
  simp_rw [hpoly] at h
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergy
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 3))

/-- P0069 page 11, Lemma 1 and display 3.3: the discrete mean value bound for a well-spaced set of
pairs `(t, χ)` with `|t| ≤ T`, for arbitrary coefficients (no divisor bound is needed). This is
`DecompC165c.hybrid_mean_square` with the coefficient hypothesis dropped and the range hypotheses
weakened to `1 ≤ F`, `2 ≤ T`, `T ≤ x`. -/
private theorem mvt_mean_square_pairs (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : c₁ < c₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      2 ≤ x → 1 ≤ F → F ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∑ p ∈ S, ‖Thm4.dirPoly a c₁ c₂ F p.2 (Thm4.half p.1)‖ ^ 2) ≤
        C * Real.log x * ((q : ℝ) * T + F) * energy a c₁ c₂ F := by
  classical
  have hc₂pos : 0 < c₂ := hc₁.trans hc₂
  let K : ℝ := 2 * Real.pi ^ 3
  let D : ℝ := 1 + |Real.log c₂| / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (2 + c₂) * (1 / Real.log 2 + 2 * D), by positivity, ?_⟩
  intro x F T q S a hx hF hFx hT hTx hq hqx hspace htimes
  letI : NeZero q := ⟨by omega⟩
  have hFpos : 0 < F := by linarith
  have hlo : 0 < c₁ * F := mul_pos hc₁ hFpos
  have hTpos : 0 < T := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  let L : ℝ := D * Real.log x
  have hL : 0 < L := mul_pos hD hlogx
  let H : ℝ := K * ((q : ℝ) * (T + 1) + c₂ * F)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hE : 0 ≤ energy a c₁ c₂ F := by
    unfold energy
    exact Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hmoment (b : ℕ → ℂ) :
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..(T + 1),
        ‖Thm4.dirPoly b c₁ c₂ F χ (Thm4.half t)‖ ^ 2) ≤
        H * energy b c₁ c₂ F := by
    apply le_trans _ (mvt_dirPoly_integral_square_sum (q := q) b hlo (by linarith : 1 ≤ T + 1))
    apply Finset.sum_le_sum
    intro χ hχ
    have hc := (Decomp513b.dirPoly_contDiff b c₁ c₂ F χ hlo).continuous.norm.pow 2
    apply intervalIntegral.integral_mono_interval
      (by linarith : -(T + 1) ≤ -T) (by linarith : -T ≤ T + 1) le_rfl
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hc.intervalIntegrable _ _)
  let f (χ : DirichletCharacter ℂ q) (t : ℝ) := Thm4.dirPoly a c₁ c₂ F χ (Thm4.half t)
  let g (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
    -Complex.I * Thm4.dirPoly (fun n => (Real.log n : ℂ) * a n) c₁ c₂ F χ (Thm4.half t)
  have hf (χ : DirichletCharacter ℂ q) (t : ℝ) : HasDerivAt (f χ) (g χ t) t :=
    Decomp513b.dirPoly_hasDerivAt a c₁ c₂ F χ hlo t
  have hg (χ : DirichletCharacter ℂ q) : Continuous (g χ) := by
    exact continuous_const.mul
      (Decomp513b.dirPoly_contDiff (fun n => (Real.log n : ℂ) * a n) c₁ c₂ F χ hlo).continuous
  have hs := Decomp513a.character_square_sampling_scaled S f g hf hg hspace hTpos.le hL htimes
  have hA : (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..(T + 1), ‖f χ t‖ ^ 2) ≤ H * energy a c₁ c₂ F := hmoment a
  have hB : (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..(T + 1), ‖g χ t‖ ^ 2) ≤ H * (L ^ 2 * energy a c₁ c₂ F) := by
    simp only [g, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact (hmoment (fun n => (Real.log n : ℂ) * a n)).trans
      (mul_le_mul_of_nonneg_left (mvt_log_weight_energy_le a hlo hc₂pos hF hFx hx) hH)
  have htotal : (∑ p ∈ S, ‖f p.2 p.1‖ ^ 2) ≤ (1 + 2 * L) * H * energy a c₁ c₂ F := by
    apply hs.trans
    calc
      _ ≤ (1 + L) * (H * energy a c₁ c₂ F) + L⁻¹ * (H * (L ^ 2 * energy a c₁ c₂ F)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hL.le))
      _ = _ := by field_simp [hL.ne']; ring
  have hlogfactor : 1 + 2 * L ≤ (1 / Real.log 2 + 2 * D) * Real.log x := by
    have h1 : 1 ≤ Real.log x / Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlogle)
    calc
      _ ≤ Real.log x / Real.log 2 + 2 * L := by linarith only [h1]
      _ = _ := by dsimp [L]; ring
  have hqT : 0 ≤ (q : ℝ) * T := by positivity
  have hbracket : (q : ℝ) * (T + 1) + c₂ * F ≤ (2 + c₂) * ((q : ℝ) * T + F) := by
    have hqt : (q : ℝ) ≤ (q : ℝ) * T := by
      simpa using mul_le_mul_of_nonneg_left (show 1 ≤ T by linarith) (Nat.cast_nonneg q)
    nlinarith [mul_nonneg hc₂pos.le hqT]
  have hHbound : H ≤ K * (2 + c₂) * ((q : ℝ) * T + F) := by
    dsimp [H]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbracket hK.le
  apply htotal.trans
  calc
    _ ≤ ((1 / Real.log 2 + 2 * D) * Real.log x) *
        (K * (2 + c₂) * ((q : ℝ) * T + F)) * energy a c₁ c₂ F := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hlogfactor hHbound hH (by positivity)) hE
    _ = _ := by ring

end MvtLemma1Helpers

section Lemma33BlockHelpers
open Finset MeanSquareC165

/-- Convolution support bounds for a product of two finite Dirichlet convolutions. -/
private theorem support_mul_bounds (p r : MonoidAlgebra ℂ ℕ) {lo₁ hi₁ lo₂ hi₂ : ℝ}
    (hp : ∀ n ∈ p.coeff.support, lo₁ < n ∧ (n : ℝ) < hi₁)
    (hr : ∀ n ∈ r.coeff.support, lo₂ < n ∧ (n : ℝ) < hi₂)
    (hlo₁ : 0 < lo₁) (hlo₂ : 0 < lo₂) :
    ∀ n ∈ (p * r).coeff.support, lo₁ * lo₂ < n ∧ (n : ℝ) < hi₁ * hi₂ := by
  intro n hn
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset p r hn)
  obtain ⟨hu1, hu2⟩ := hp u hu
  obtain ⟨hv1, hv2⟩ := hr v hv
  have hu0 : (0 : ℝ) < (u : ℝ) := hlo₁.trans hu1
  have hv0 : (0 : ℝ) < (v : ℝ) := hlo₂.trans hv1
  have hcast : ((u * v : ℕ) : ℝ) = (u : ℝ) * (v : ℝ) := by push_cast; ring
  rw [hcast]
  exact ⟨mul_lt_mul'' hu1 hv1 hlo₁.le hlo₂.le, mul_lt_mul'' hu2 hv2 hu0.le hv0.le⟩

/-- `(Y^p)^2 = Y^(2p)` for a positive base. -/
private theorem rpow_sq_rpow {Y p : ℝ} (hY : 0 < Y) : (Y ^ p) ^ 2 = Y ^ (2 * p) := by
  rw [← Real.rpow_natCast (Y ^ p) 2, ← Real.rpow_mul hY.le]
  congr 1
  ring

/-- P0069 page 48, region `R` with the arrangement `N²L, LM, M`: the two large factors differ by at
most `θ₂ - ε` in `Y`-exponents. -/
private theorem region_R_pair {ε β₁ β₂ t2 : ℝ} (ht2 : t2 = 2 * (1 / 16 - 1 / 10 ^ 5))
    (hε8 : ε ≤ 1 / 10 ^ 8) (hm : β₁ ≤ (36 * t2 - 2) / 11 - ε)
    (hn : (1 + 7 * t2) / 15 - ε ≤ β₂) (hR : 2 * β₂ - t2 + ε ≤ β₁) :
    |2 * β₂ - β₁| ≤ t2 - ε := by
  have h1 : 2 * β₂ - β₁ ≤ t2 - ε := by linarith
  have h2 : β₁ - 2 * β₂ ≤ t2 - ε := by
    rw [ht2] at *
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 48, region `P1` with the arrangement `M²N, L², N`. -/
private theorem region_P1_pair {β₁ β₂ t2 ε : ℝ} (ht2 : t2 = 2 * (1 / 16 - 1 / 10 ^ 5))
    (hε8 : ε ≤ 1 / 10 ^ 8) (hP : |4 * β₁ + 3 * β₂ - 2| ≤ t2 - ε) :
    |2 * β₁ + 3 / 2 * β₂ - 1| ≤ (t2 - ε) / 2 := by
  have h : (4 * β₁ + 3 * β₂ - 2) / 2 = 2 * β₁ + 3 / 2 * β₂ - 1 := by ring
  rw [← h, abs_div]
  norm_num
  linarith

/-- P0069 page 48, region `P2` with the arrangement `L²N, M², N`. -/
private theorem region_P2_pair {β₁ β₂ t2 ε : ℝ} (ht2 : t2 = 2 * (1 / 16 - 1 / 10 ^ 5))
    (hε8 : ε ≤ 1 / 10 ^ 8) (hP : |4 * β₁ + β₂ - 2| ≤ t2 - ε) :
    |1 - 2 * β₁ - β₂ / 2| ≤ (t2 - ε) / 2 := by
  have h : (4 * β₁ + β₂ - 2) / 2 = 2 * β₁ + β₂ / 2 - 1 := by ring
  have h' : 1 - 2 * β₁ - β₂ / 2 = -(2 * β₁ + β₂ / 2 - 1) := by ring
  rw [h', abs_neg, ← h, abs_div]
  norm_num
  linarith

/-- P0069 display (3.8) at the exponent `θ` of the block, `θ = 1/2 + θ₂/4 - δ`. -/
private theorem gam_theta_ge {ε δ t2 : ℝ} (ht2 : t2 = 2 * (1 / 16 - 1 / 10 ^ 5))
    (hδ : δ = ε / 144) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    (18 * t2 - 1) / 11 - 72 * δ / 11 ≤ Thm4.gam (1 / 2 + t2 / 4 - δ) := by
  rw [Thm4.gam, ht2, hδ]
  refine le_min ?_ (le_min ?_ ?_) <;> norm_num <;> linarith

end Lemma33BlockHelpers

/-- `(Y^(2:ℝ))^((2β₂+l)/2) = Y^(β₂+β₂+l)`. -/
private theorem rpow_half_pair {Y β₂ l : ℝ} (hY : 0 < Y) :
    (Y ^ (2 : ℝ)) ^ ((2 * β₂ + l) / 2) = Y ^ (β₂ + β₂ + l) := by
  rw [← Real.rpow_mul hY.le]
  congr 1
  ring

/-- `(Y^(2:ℝ))^((2β₁+β₂)/2) = Y^(β₁+β₁+β₂)`. -/
private theorem rpow_half_pair' {Y β₁ β₂ : ℝ} (hY : 0 < Y) :
    (Y ^ (2 : ℝ)) ^ ((2 * β₁ + β₂) / 2) = Y ^ (β₁ + β₁ + β₂) := by
  rw [← Real.rpow_mul hY.le]
  congr 1
  ring

/-- `(Y^(2:ℝ))^((l+l)/2) = Y^(l+l)`. -/
private theorem rpow_half_two {Y l : ℝ} (hY : 0 < Y) :
    (Y ^ (2 : ℝ)) ^ ((l + l) / 2) = Y ^ (l + l) := by
  rw [← Real.rpow_mul hY.le]
  congr 1
  ring

/-- `(Y^(2:ℝ))^(β/2) = Y^β`. -/
private theorem rpow_half_single {Y β : ℝ} (hY : 0 < Y) :
    (Y ^ (2 : ℝ)) ^ (β / 2) = Y ^ β := by
  rw [← Real.rpow_mul hY.le]
  congr 1
  ring

/-- `(Y^(2:ℝ))^(1/2) = Y`. -/
private theorem rpow_sqrt_sq {Y : ℝ} (hY : 0 ≤ Y) : (Y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = Y := by
  rw [← Real.rpow_mul hY]
  norm_num

/-- A positive power of a large base is at least two once the exponent is at least `1/8`. -/
private theorem rpow_ge_two {Y e : ℝ} (hY : 2 ^ (8 : ℝ) ≤ Y) (he : 1 / 8 ≤ e) : 2 ≤ Y ^ e := by
  have h8e : (1 : ℝ) ≤ 8 * e := by linarith
  have step1 : (2 : ℝ) ^ (1 : ℝ) ≤ 2 ^ (8 * e) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h8e
  have step2 : (2 : ℝ) ^ (8 * e) = (2 ^ (8 : ℝ)) ^ e := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have step3 : (2 ^ (8 : ℝ)) ^ e ≤ Y ^ e :=
    Real.rpow_le_rpow (by positivity) hY (by linarith)
  rw [Real.rpow_one] at step1
  linarith

/-- A power of a base at least one does not exceed the base once the exponent is at most one. -/
private theorem rpow_le_self {X a : ℝ} (hX : 1 ≤ X) (ha : a ≤ 1) : X ^ a ≤ X := by
  calc X ^ a ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX ha
    _ = X := Real.rpow_one X

/-- `(Y^(2:ℝ))^θ` is monotone in nothing; this records the two powers of `X = Y²` used below. -/
private theorem rpow_two_mul {Y a : ℝ} (hY : 0 < Y) : (Y ^ (2 : ℝ)) ^ a = Y ^ (2 * a) := by
  rw [← Real.rpow_mul hY.le]

/-- P0069 page 48, the step "if t is in [T, T + T2]" of the proof of Lemma 33: the block is
moved into [-T, T] by the twist of the coefficients by `n^(-iT)`, since the polynomial at
1/2 + i(t + T) equals the twisted polynomial at 1/2 + it. The twist is multiplicative, so it is
the same for every factor of a product. PROVED. -/
private theorem blk_dirPoly_shift {q : ℕ} (a : ℕ → ℂ) (c₁ c₂ F : ℝ) (χ : DirichletCharacter ℂ q)
    (t T : ℝ) :
    Thm4.dirPoly a c₁ c₂ F χ (Thm4.half (t + T)) =
      Thm4.dirPoly (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) c₁ c₂ F χ (Thm4.half t) := by
  unfold Thm4.dirPoly Thm4.half
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : (1 / 2 + ((t + T : ℝ) : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h2 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow h1, Complex.zero_cpow h2, div_zero, div_zero]
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsplit : (n : ℂ) ^ (1 / 2 + ((t + T : ℝ) : ℂ) * I) =
        (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) * (n : ℂ) ^ ((T : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn']; congr 1; push_cast; ring
    have hne1 : (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hne2 : (n : ℂ) ^ ((T : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    simp only []
    rw [hsplit, Complex.cpow_neg]
    field_simp

/-- P0069 page 11, display 3.1 is kept by the twist of kept52_dirPoly_shift, since
|n^(-iT)| is at most 1 for every natural n. PROVED. -/
private theorem blk_coeffBound_shift {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B) (T : ℝ) :
    Thm4.CoeffBound (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) B := by
  intro n
  have h1 : ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ ≤ 1 := by
    rcases eq_or_ne n 0 with rfl | hn
    · by_cases hT : T = 0
      · simp [hT]
      · have : -((T : ℂ) * I) ≠ 0 := by
          intro h; apply hT; have := congrArg Complex.im h; simpa using this
        simp [Complex.zero_cpow this]
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
  calc ‖a n * (n : ℂ) ^ (-((T : ℂ) * I))‖ = ‖a n‖ * ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ := norm_mul _ _
    _ ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact ha n

/-- `Thm4.dirPoly` as a sum over its own window. -/
private theorem dirPoly_eq_sum_filter {q : ℕ} (a : ℕ → ℂ) (c₁ c₂ F : ℝ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Thm4.dirPoly a c₁ c₂ F χ s =
      ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), a n * χ (n : ZMod q) / (n : ℂ) ^ s := rfl

/-- P0069 page 48: the product of two Dirichlet polynomials over one window, reindexed by the
product of the summation indices. This is the step "|LMN|² = |(LMN)²|" at the level of
coefficients: every factor of the square is a Dirichlet polynomial of a convolution. PROVED. -/
private theorem dirPoly_mul_conv {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a b : ℕ → ℂ)
    {c₁ c₂ Fa Fb : ℝ} (hc₁ : 0 < c₁) (hFa : 0 < Fa) (hFb : 0 < Fb) :
    Thm4.dirPoly a c₁ c₂ Fa χ s * Thm4.dirPoly b c₁ c₂ Fb χ s =
      ∑ k ∈ ((Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa) ×ˢ (Finset.range (⌊c₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fb < n ∧ (n : ℝ) < c₂ * Fb)).image (fun p : ℕ × ℕ => p.1 * p.2),
        (∑ p ∈ ((Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa) ×ˢ (Finset.range (⌊c₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fb < n ∧ (n : ℝ) < c₂ * Fb)).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
            a p.1 * b p.2) * χ (k : ZMod q) / (k : ℂ) ^ s := by
  classical
  set A := (Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa) with hA
  set B := (Finset.range (⌊c₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fb < n ∧ (n : ℝ) < c₂ * Fb) with hB
  have hW : ∀ n : ℕ, n ∈ A → c₁ * Fa < (n : ℝ) := fun n hn => (Finset.mem_filter.mp hn).2.1
  have hW' : ∀ n : ℕ, n ∈ B → c₁ * Fb < (n : ℝ) := fun n hn => (Finset.mem_filter.mp hn).2.1
  have hposA : ∀ n ∈ A, 0 < n := by
    intro n hn
    have h : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (mul_pos hc₁ hFa) (hW n hn).le
    exact_mod_cast h
  have hposB : ∀ n ∈ B, 0 < n := by
    intro n hn
    have h : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (mul_pos hc₁ hFb) (hW' n hn).le
    exact_mod_cast h
  have hχ : ∀ x y : ℕ, χ ((x : ZMod q) * (y : ZMod q)) = χ (x : ZMod q) * χ (y : ZMod q) :=
    fun x y => map_mul χ (x : ZMod q) (y : ZMod q)
  have hcp : ∀ x y : ℕ, ((x : ℂ) * (y : ℂ)) ^ s = (x : ℂ) ^ s * (y : ℂ) ^ s :=
    fun x y => Complex.natCast_mul_natCast_cpow x y s
  have hterm : ∀ p ∈ A ×ˢ B,
      (a p.1 * χ (p.1 : ZMod q) / (p.1 : ℂ) ^ s) * (b p.2 * χ (p.2 : ZMod q) / (p.2 : ℂ) ^ s) =
      (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have h1 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (hposA p.1 hp1).ne'
    have h2 : (p.2 : ℂ) ≠ 0 := by exact_mod_cast (hposB p.2 hp2).ne'
    rw [hχ p.1 p.2, hcp p.1 p.2]
    field_simp
  calc Thm4.dirPoly a c₁ c₂ Fa χ s * Thm4.dirPoly b c₁ c₂ Fb χ s
      = ∑ x ∈ A, ∑ y ∈ B,
          (a x * χ (x : ZMod q) / (x : ℂ) ^ s) * (b y * χ (y : ZMod q) / (y : ℂ) ^ s) := by
        rw [dirPoly_eq_sum_filter, dirPoly_eq_sum_filter, Finset.sum_mul_sum]
    _ = ∑ p ∈ A ×ˢ B,
          (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s := by
        rw [← Finset.sum_product']
        exact Finset.sum_congr rfl hterm
    _ = ∑ k ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2),
          (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) *
            χ (k : ZMod q) / (k : ℂ) ^ s := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := A ×ˢ B) (t := (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2))
          (g := fun p : ℕ × ℕ => p.1 * p.2)
          (f := fun p : ℕ × ℕ =>
            (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s)
          (fun p hp => Finset.mem_image_of_mem _ hp)]
        apply Finset.sum_congr rfl
        intro k hk
        have hcongr : (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
              (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s) =
            ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
              (a p.1 * b p.2) * χ (k : ZMod q) / (k : ℂ) ^ s := by
          apply Finset.sum_congr rfl
          intro p hp
          have h : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
          simp only [← Nat.cast_mul]
          rw [h]
        rw [hcongr]
        refine (Finset.sum_congr rfl (fun p _ => mul_div_assoc _ _ _)).trans ?_
        exact ((Finset.sum_mul _ (fun p : ℕ × ℕ => a p.1 * b p.2)
          (χ (k : ZMod q) / (k : ℂ) ^ s)).symm).trans (mul_div_assoc _ _ _).symm

/-- A window sum over a subset of the window is a Dirichlet polynomial with the coefficients cut
off outside the subset. PROVED. -/
private theorem sum_win_eq_dirPoly {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (f : ℕ → ℂ)
    {c₁ c₂ F : ℝ} {K : Finset ℕ} (hK : K ⊆ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F)) :
    (∑ k ∈ K, f k * χ (k : ZMod q) / (k : ℂ) ^ s) =
      Thm4.dirPoly (fun k => if k ∈ K then f k else 0) c₁ c₂ F χ s := by
  rw [dirPoly_eq_sum_filter]
  simp only [ite_mul, zero_mul, ite_div, zero_div]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hK]

/-- The products of two windowed indices stay inside the correspondingly widened window. PROVED. -/
private theorem win_mul_subset {c₁ c₂ Fa Fb : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₁ < c₂)
    (hFa : 0 < Fa) (hFb : 0 < Fb) :
    ((Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa) ×ˢ (Finset.range (⌊c₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fb < n ∧ (n : ℝ) < c₂ * Fb)).image (fun p : ℕ × ℕ => p.1 * p.2) ⊆
      (Finset.range (⌊c₂ * c₂ * Fa * Fb⌋₊ + 1)).filter (fun n : ℕ => c₁ * c₁ * Fa * Fb < n ∧ (n : ℝ) < c₂ * c₂ * Fa * Fb) := by
  classical
  intro k hk
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hlo1, hhi1⟩ := (Finset.mem_filter.mp hp1).2
  obtain ⟨hlo2, hhi2⟩ := (Finset.mem_filter.mp hp2).2
  have h1 : (0 : ℝ) < (p.1 : ℝ) := lt_trans (mul_pos hc₁ hFa) hlo1
  have h2 : (0 : ℝ) < (p.2 : ℝ) := lt_trans (mul_pos hc₁ hFb) hlo2
  have hcast : ((p.1 * p.2 : ℕ) : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; ring
  have hlt : (p.1 : ℝ) * (p.2 : ℝ) < c₂ * c₂ * Fa * Fb := by
    have h := mul_lt_mul'' hhi1 hhi2 h1.le h2.le
    rw [show c₂ * c₂ * Fa * Fb = (c₂ * Fa) * (c₂ * Fb) by ring]
    exact h
  have hgt : c₁ * c₁ * Fa * Fb < (p.1 : ℝ) * (p.2 : ℝ) := by
    have h := mul_lt_mul'' hlo1 hlo2 (mul_pos hc₁ hFa).le (mul_pos hc₁ hFb).le
    rw [show c₁ * c₁ * Fa * Fb = (c₁ * Fa) * (c₁ * Fb) by ring]
    exact h
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_floor (by rw [hcast]; exact hlt.le))
  · rw [hcast]; exact hgt
  · rw [hcast]; exact hlt

/-- Membership in the window of `Thm4.dirPoly`. -/
private theorem mem_dirPoly_win {c₁ c₂ F : ℝ} (h : 0 ≤ c₂ * F) (k : ℕ) :
    k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F) ↔
      c₁ * F < (k : ℝ) ∧ (k : ℝ) < c₂ * F := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by have := Nat.le_floor h2.le; omega, h1, h2⟩

/-- A Dirichlet polynomial over one window is a Dirichlet polynomial over any larger window, with
its coefficients cut off outside the smaller one. -/
private theorem dirPoly_widen {q : ℕ} (a : ℕ → ℂ) {c₁ c₂ C₁ C₂ F : ℝ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (h1 : C₁ ≤ c₁) (h2 : c₂ ≤ C₂)
    (hc₂ : 0 < c₂) (hF : 0 < F) :
    Thm4.dirPoly a c₁ c₂ F χ s =
      Thm4.dirPoly (fun n => if c₁ * F < (n : ℝ) ∧ (n : ℝ) < c₂ * F then a n else 0)
        C₁ C₂ F χ s := by
  have hc2F : 0 ≤ c₂ * F := (mul_pos hc₂ hF).le
  have hC2F : 0 ≤ C₂ * F := by nlinarith
  rw [dirPoly_eq_sum_filter, dirPoly_eq_sum_filter]
  have hsub : ((Finset.range (⌊c₂ * F⌋₊ + 1)).filter
        (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F)) ⊆
      ((Finset.range (⌊C₂ * F⌋₊ + 1)).filter
        (fun n : ℕ => C₁ * F < n ∧ (n : ℝ) < C₂ * F)) := by
    intro k hk
    rw [mem_dirPoly_win hc2F k] at hk
    obtain ⟨hk1, hk2⟩ := hk
    rw [mem_dirPoly_win hC2F k]
    exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hF.le) hk1,
      lt_of_lt_of_le hk2 (mul_le_mul_of_nonneg_right h2 hF.le)⟩
  have hpt : ∀ k : ℕ,
      (if c₁ * F < (k : ℝ) ∧ (k : ℝ) < c₂ * F then a k else 0) =
        (if k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
          (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F) then a k else 0) := by
    intro k
    have hiff := mem_dirPoly_win (c₁ := c₁) hc2F k
    by_cases h : c₁ * F < (k : ℝ) ∧ (k : ℝ) < c₂ * F
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]
  have hrhs : (∑ k ∈ (Finset.range (⌊C₂ * F⌋₊ + 1)).filter
        (fun n : ℕ => C₁ * F < n ∧ (n : ℝ) < C₂ * F),
        (if c₁ * F < (k : ℝ) ∧ (k : ℝ) < c₂ * F then a k else 0) * χ (k : ZMod q) /
          (k : ℂ) ^ s) =
      ∑ k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
        (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), a k * χ (k : ZMod q) / (k : ℂ) ^ s := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hpt k])]
    have hterm : ∀ k : ℕ,
        (if k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
            (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F) then a k else 0) *
            χ (k : ZMod q) / (k : ℂ) ^ s =
          (if k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
            (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F) then
              a k * χ (k : ZMod q) / (k : ℂ) ^ s else 0) := by
      intro k
      by_cases h : k ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
          (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F) <;> simp [h]
    simp only [hterm]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  exact hrhs.symm

/-- Support bounds for a product of two windowed sets whose windows may differ. -/
private theorem win_mul_subset_gen {c₁ c₂ d₁ d₂ Fa Fb : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hFa : 0 < Fa) (hFb : 0 < Fb) :
    (((Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa)) ×ˢ
        ((Finset.range (⌊d₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => d₁ * Fb < n ∧ (n : ℝ) < d₂ * Fb))).image
        (fun p : ℕ × ℕ => p.1 * p.2) ⊆
      (Finset.range (⌊(c₂ * d₂) * (Fa * Fb)⌋₊ + 1)).filter
        (fun n : ℕ => (c₁ * d₁) * (Fa * Fb) < n ∧ (n : ℝ) < (c₂ * d₂) * (Fa * Fb)) := by
  classical
  intro k hk
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hlo1, hhi1⟩ := (Finset.mem_filter.mp hp1).2
  obtain ⟨hlo2, hhi2⟩ := (Finset.mem_filter.mp hp2).2
  have hpa : (0 : ℝ) < (p.1 : ℝ) := lt_trans (mul_pos hc₁ hFa) hlo1
  have hpb : (0 : ℝ) < (p.2 : ℝ) := lt_trans (mul_pos hd₁ hFb) hlo2
  have hcast : ((p.1 * p.2 : ℕ) : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; ring
  have hlo : (c₁ * d₁) * (Fa * Fb) < (p.1 : ℝ) * (p.2 : ℝ) := by
    have h := mul_lt_mul'' hlo1 hlo2 (mul_pos hc₁ hFa).le (mul_pos hd₁ hFb).le
    rw [show (c₁ * d₁) * (Fa * Fb) = (c₁ * Fa) * (d₁ * Fb) by ring]
    exact h
  have hhi : (p.1 : ℝ) * (p.2 : ℝ) < (c₂ * d₂) * (Fa * Fb) := by
    have h := mul_lt_mul'' hhi1 hhi2 hpa.le hpb.le
    rw [show (c₂ * d₂) * (Fa * Fb) = (c₂ * Fa) * (d₂ * Fb) by ring]
    exact h
  rw [mem_dirPoly_win (by positivity) (p.1 * p.2)]
  rw [hcast]
  exact ⟨hlo, hhi⟩

/-- P0069 page 48: the product of two Dirichlet polynomials over possibly different windows, with
the resulting polynomial over the product window. `|LMN|² = |(LMN)²|` at the level of
coefficients. PROVED. -/
private theorem dirPoly_mul_conv_gen {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a b : ℕ → ℂ)
    {c₁ c₂ d₁ d₂ Fa Fb : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hFa : 0 < Fa) (hFb : 0 < Fb) :
    Thm4.dirPoly a c₁ c₂ Fa χ s * Thm4.dirPoly b d₁ d₂ Fb χ s =
      Thm4.dirPoly (fun k => ∑ p ∈
          (((Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa)) ×ˢ
            ((Finset.range (⌊d₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => d₁ * Fb < n ∧ (n : ℝ) < d₂ * Fb))).filter
            (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2)
        (c₁ * d₁) (c₂ * d₂) (Fa * Fb) χ s := by
  classical
  set A := (Finset.range (⌊c₂ * Fa⌋₊ + 1)).filter (fun n : ℕ => c₁ * Fa < n ∧ (n : ℝ) < c₂ * Fa) with hA
  set B := (Finset.range (⌊d₂ * Fb⌋₊ + 1)).filter (fun n : ℕ => d₁ * Fb < n ∧ (n : ℝ) < d₂ * Fb) with hB
  have hposA : ∀ n ∈ A, 0 < n := by
    intro n hn
    have h : (0 : ℝ) < (n : ℝ) :=
      lt_of_lt_of_le (mul_pos hc₁ hFa) (Finset.mem_filter.mp hn).2.1.le
    exact_mod_cast h
  have hposB : ∀ n ∈ B, 0 < n := by
    intro n hn
    have h : (0 : ℝ) < (n : ℝ) :=
      lt_of_lt_of_le (mul_pos hd₁ hFb) (Finset.mem_filter.mp hn).2.1.le
    exact_mod_cast h
  have hterm : ∀ p ∈ A ×ˢ B,
      (a p.1 * χ (p.1 : ZMod q) / (p.1 : ℂ) ^ s) * (b p.2 * χ (p.2 : ZMod q) / (p.2 : ℂ) ^ s) =
      (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have h1 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (hposA p.1 hp1).ne'
    have h2 : (p.2 : ℂ) ≠ 0 := by exact_mod_cast (hposB p.2 hp2).ne'
    rw [map_mul χ (p.1 : ZMod q) (p.2 : ZMod q), Complex.natCast_mul_natCast_cpow]
    field_simp
  have hfib : (∑ p ∈ A ×ˢ B,
        (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s) =
      ∑ k ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2),
        (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) *
          χ (k : ZMod q) / (k : ℂ) ^ s := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := A ×ˢ B) (t := (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2))
      (g := fun p : ℕ × ℕ => p.1 * p.2)
      (f := fun p : ℕ × ℕ =>
        (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_congr rfl
    intro k hk
    have hcongr : (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
          (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s) =
        ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
          (a p.1 * b p.2) * χ (k : ZMod q) / (k : ℂ) ^ s := by
      apply Finset.sum_congr rfl
      intro p hp
      have h : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
      simp only [← Nat.cast_mul]
      rw [h]
    rw [hcongr]
    refine (Finset.sum_congr rfl (fun p _ => mul_div_assoc _ _ _)).trans ?_
    exact ((Finset.sum_mul _ (fun p : ℕ × ℕ => a p.1 * b p.2)
      (χ (k : ZMod q) / (k : ℂ) ^ s)).symm).trans (mul_div_assoc _ _ _).symm
  have hsub := win_mul_subset_gen hc₁ hc₂ hd₁ hd₂ hFa hFb
  have hfib0 : ∀ k, k ∉ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2) →
      (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) = 0 := by
    intro k hk
    apply Finset.sum_eq_zero
    intro p hp
    have h : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
    refine absurd (h ▸ Finset.mem_image_of_mem (fun p : ℕ × ℕ => p.1 * p.2)
      (Finset.mem_filter.mp hp).1) hk
  have hfun : (fun k => if k ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2) then
        ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2 else 0) =
      (fun k => ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) := by
    funext k
    by_cases hk : k ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2)
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact (hfib0 k hk).symm
  calc Thm4.dirPoly a c₁ c₂ Fa χ s * Thm4.dirPoly b d₁ d₂ Fb χ s
      = ∑ x ∈ A, ∑ y ∈ B,
          (a x * χ (x : ZMod q) / (x : ℂ) ^ s) * (b y * χ (y : ZMod q) / (y : ℂ) ^ s) := by
        rw [dirPoly_eq_sum_filter, dirPoly_eq_sum_filter, Finset.sum_mul_sum, ← hA, ← hB]
    _ = ∑ p ∈ A ×ˢ B,
          (a p.1 * χ (p.1 : ZMod q) / (p.1 : ℂ) ^ s) * (b p.2 * χ (p.2 : ZMod q) / (p.2 : ℂ) ^ s) := by
        rw [← Finset.sum_product']
    _ = ∑ p ∈ A ×ˢ B,
          (a p.1 * b p.2) * χ ((p.1 * p.2) : ZMod q) / ((p.1 * p.2) : ℂ) ^ s :=
        Finset.sum_congr rfl hterm
    _ = ∑ k ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2),
          (∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) *
            χ (k : ZMod q) / (k : ℂ) ^ s := hfib
    _ = Thm4.dirPoly (fun k => ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
          a p.1 * b p.2) (c₁ * d₁) (c₂ * d₂) (Fa * Fb) χ s := by
        rw [sum_win_eq_dirPoly (K := (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2))
          (c₁ := c₁ * d₁) (c₂ := c₂ * d₂) (F := Fa * Fb) χ s
          (fun k => ∑ p ∈ (A ×ˢ B).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), a p.1 * b p.2) hsub]
        rw [hfun]

/-- The number of pairs `(u, v)` in two sets of positive integers with `u * v = k` is at most the
number of divisors of `k`. -/
private theorem fiber_card_le {s t : Finset ℕ} (hs : ∀ n ∈ s, 0 < n)
    (ht : ∀ n ∈ t, 0 < n) (k : ℕ) :
    ((s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k)).card ≤ k.divisors.card := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hempty : (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have h1 := hs p.1 hp1
      have h2 := ht p.2 hp2
      have h3 : p.1 * p.2 = 0 := (Finset.mem_filter.mp hp).2
      rcases Nat.mul_eq_zero.mp h3 with h | h <;> omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · set S := (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k) with hS
    have hpos : ∀ p ∈ S, 0 < p.1 := by
      intro p hp
      exact hs p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1) ↑S := by
      intro p hp q hq heq
      simp only at heq
      have hp2 : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
      have hq2 : q.1 * q.2 = k := (Finset.mem_filter.mp hq).2
      have hmul : p.1 * p.2 = p.1 * q.2 := by
        rw [hp2, heq]
        exact hq2.symm
      exact Prod.ext heq (Nat.eq_of_mul_eq_mul_left (hpos p hp) hmul)
    have hsub : S.image (fun p : ℕ × ℕ => p.1) ⊆ k.divisors := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      have hp2 : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
      exact Nat.mem_divisors.mpr ⟨⟨p.2, hp2.symm⟩, hk.ne'⟩
    calc S.card = (S.image (fun p : ℕ × ℕ => p.1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ k.divisors.card := Finset.card_le_card hsub

/-- The coefficients of the product of two Dirichlet polynomials, with the divisor bound (3.1) of
the factors, satisfy (3.1) with any exponent at least `2B + 1`. -/
private theorem fiber_coeffBound {a b : ℕ → ℂ} {Ba Bb B' : ℝ} (hBa : 0 ≤ Ba) (hBb : 0 ≤ Bb)
    (hBB : Ba + Bb + 1 ≤ B')
    (hB'0 : 0 < B')
    (ha : Thm4.CoeffBound a Ba) (hb : Thm4.CoeffBound b Bb)
    {s t : Finset ℕ} (hs : ∀ n ∈ s, 0 < n) (ht : ∀ n ∈ t, 0 < n) :
    Thm4.CoeffBound (fun k => ∑ p ∈ (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
        a p.1 * b p.2) B' := by
  classical
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have h0 : (fun k => ∑ p ∈ (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
        a p.1 * b p.2) 0 = 0 := by
      simp only
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have h1 := hs p.1 hp1
      have h2 := ht p.2 hp2
      have h3 : p.1 * p.2 = 0 := (Finset.mem_filter.mp hp).2
      rcases Nat.mul_eq_zero.mp h3 with h | h <;> omega
    rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hk0 : k ≠ 0 := hk.ne'
    set S := (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k) with hS
    have hτ1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
      have hpos : 0 < k.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk0⟩
      exact_mod_cast hpos
    have hτ0 : (0 : ℝ) < (k.divisors.card : ℝ) := by linarith
    have hcard : (S.card : ℝ) ≤ (k.divisors.card : ℝ) := by
      exact_mod_cast fiber_card_le hs ht k
    have hterm : ∀ p ∈ S, ‖a p.1 * b p.2‖ ≤ (k.divisors.card : ℝ) ^ (Ba + Bb) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hp2eq : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
      have hdiv1 : p.1 ∣ k := ⟨p.2, hp2eq.symm⟩
      have hdiv2 : p.2 ∣ k := ⟨p.1, by rw [mul_comm]; exact hp2eq.symm⟩
      have hle1 : p.1.divisors.card ≤ k.divisors.card :=
        Finset.card_le_card (Nat.divisors_subset_of_dvd hk0 hdiv1)
      have hle2 : p.2.divisors.card ≤ k.divisors.card :=
        Finset.card_le_card (Nat.divisors_subset_of_dvd hk0 hdiv2)
      have hb1 : ((p.1.divisors.card : ℝ)) ^ Ba ≤ ((k.divisors.card : ℝ)) ^ Ba :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle1) hBa
      have hb2 : ((p.2.divisors.card : ℝ)) ^ Bb ≤ ((k.divisors.card : ℝ)) ^ Bb :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle2) hBb
      have hnn : (0 : ℝ) ≤ ((k.divisors.card : ℝ)) ^ Ba := Real.rpow_nonneg hτ0.le _
      have hnn2 : (0 : ℝ) ≤ ((k.divisors.card : ℝ)) ^ Bb := Real.rpow_nonneg hτ0.le _
      rw [norm_mul]
      calc ‖a p.1‖ * ‖b p.2‖ ≤ ((p.1.divisors.card : ℝ) ^ Ba) * ((p.2.divisors.card : ℝ) ^ Bb) :=
            mul_le_mul (ha p.1) (hb p.2) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
        _ ≤ ((k.divisors.card : ℝ) ^ Ba) * ((k.divisors.card : ℝ) ^ Bb) :=
            mul_le_mul hb1 hb2 (Real.rpow_nonneg (by positivity) _) hnn
        _ = (k.divisors.card : ℝ) ^ (Ba + Bb) := by
            rw [← Real.rpow_add hτ0]
    have hsum : ‖∑ p ∈ S, a p.1 * b p.2‖ ≤ (S.card : ℝ) * (k.divisors.card : ℝ) ^ (Ba + Bb) := by
      calc ‖∑ p ∈ S, a p.1 * b p.2‖ ≤ ∑ p ∈ S, ‖a p.1 * b p.2‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ S, (k.divisors.card : ℝ) ^ (Ba + Bb) := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (k.divisors.card : ℝ) ^ (Ba + Bb) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hstep : (k.divisors.card : ℝ) ^ (Ba + Bb + 1) =
        (k.divisors.card : ℝ) ^ (Ba + Bb) * (k.divisors.card : ℝ) := by
      rw [Real.rpow_add hτ0, Real.rpow_one]
    have hmid : (S.card : ℝ) * (k.divisors.card : ℝ) ^ (Ba + Bb) ≤
        (k.divisors.card : ℝ) ^ (Ba + Bb + 1) := by
      rw [hstep]
      calc (S.card : ℝ) * (k.divisors.card : ℝ) ^ (Ba + Bb)
          ≤ (k.divisors.card : ℝ) * (k.divisors.card : ℝ) ^ (Ba + Bb) :=
            mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hτ0.le _)
        _ = (k.divisors.card : ℝ) ^ (Ba + Bb) * (k.divisors.card : ℝ) := by ring
    have hmono : (k.divisors.card : ℝ) ^ (Ba + Bb + 1) ≤ (k.divisors.card : ℝ) ^ B' :=
      Real.rpow_le_rpow_of_exponent_le hτ1 hBB
    have hgoal : ‖(∑ p ∈ S, a p.1 * b p.2)‖ ≤ (k.divisors.card : ℝ) ^ B' := by
      exact hsum.trans (hmid.trans hmono)
    have hbeta : (fun k => ∑ p ∈ (s ×ˢ t).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
        a p.1 * b p.2) k = ∑ p ∈ S, a p.1 * b p.2 := by
      simp only [hS]
    rw [hbeta]
    exact hgoal

/-- `2 ≤ Y ^ e` for `Y ≥ 2^16` and `1/16 ≤ e`. -/
private theorem rpow_two_le {Y e : ℝ} (hY : (2 : ℝ) ^ (16 : ℕ) ≤ Y) (he : 1 / 16 ≤ e) :
    (2 : ℝ) ≤ Y ^ e := by
  have h2d : ((2 : ℝ) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← h2d]
  calc ((2 : ℝ) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) ≤ Y ^ (1 / 16 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hY (by norm_num)
    _ ≤ Y ^ e := Real.rpow_le_rpow_of_exponent_le (by linarith) he

/-- `(Y^2)^e ≤ Y^2` for `Y ≥ 1` and `e ≤ 1`. -/
private theorem rpow_sq_le {Y e : ℝ} (hY : (1 : ℝ) ≤ Y) (he : e ≤ 1) :
    (Y ^ (2 : ℝ)) ^ e ≤ Y ^ (2 : ℝ) := by
  have h1 : (1 : ℝ) ≤ Y ^ (2 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hY (by norm_num : (0 : ℝ) ≤ 2)
    simpa using h
  calc (Y ^ (2 : ℝ)) ^ e ≤ (Y ^ (2 : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 he
    _ = Y ^ (2 : ℝ) := Real.rpow_one _

/-- `2 ≤ (Y^2)^e` for `Y ≥ 2^16` and `1/32 ≤ e` (assuming `Y > 0`). -/
private theorem rpow_sq_two_le {Y e : ℝ} (hY0 : 0 < Y) (hY : (2 : ℝ) ^ (16 : ℕ) ≤ Y)
    (he : 1 / 32 ≤ e) : (2 : ℝ) ≤ (Y ^ (2 : ℝ)) ^ e := by
  rw [rpow_two_mul hY0]
  exact rpow_two_le hY (by linarith)

/-- Theorem 4 applied to a block: the `L²` bound for one product of three Dirichlet polynomials
over the window `(C₁, C₂)` with `X = Y²`. The constant does not depend on the exponents. -/
private theorem t4_block_bound {ε' B' : ℝ} (h4 : Thm4.Theorem4 ε' B')
    {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₁C₂ : C₁ < C₂)
    {K : ℝ → ℝ} {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 0 < Y → (2 : ℝ) ^ (16 : ℕ) ≤ Y →
      ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ Y ^ (2 : ℝ) →
      ∀ (S : Finset (ℝ × DirichletCharacter ℂ q)), Thm4.WellSpaced S →
      ∀ (θ α₁ α₂ T : ℝ), 1 / 2 + ε' < θ → θ < 7 / 12 →
      |α₁ - α₂| < 2 * θ - 1 - ε' → 1 - (α₁ + α₂) < Thm4.gam θ - ε' →
      1 / 32 ≤ α₁ → α₁ ≤ 1 → 1 / 32 ≤ α₂ → α₂ ≤ 1 →
      1 / 32 ≤ 1 - α₁ - α₂ → 1 - α₁ - α₂ ≤ 1 →
      (q : ℝ) * T = (Y ^ (2 : ℝ)) ^ (1 - θ) → 2 < T → T ≤ (Y ^ (2 : ℝ)) / 4 →
      (∀ p ∈ S, |p.1| ≤ T) →
      ∀ (a b e : ℕ → ℂ), Thm4.CoeffBound a B' → Thm4.CoeffBound b B' →
      Thm4.CoeffBound e B' →
      (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
        ‖Thm4.dirPoly e C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) p.2 (Thm4.half p.1)‖ ≤
          K A' * ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) *
            Real.log (Y ^ (2 : ℝ)) ^ (-A')) →
      ∑ p ∈ S, ‖Thm4.dirPoly a C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₁) p.2 (Thm4.half p.1) *
              Thm4.dirPoly b C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₂) p.2 (Thm4.half p.1) *
              Thm4.dirPoly e C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) p.2 (Thm4.half p.1)‖ ≤
        C * Y * Real.log (Y ^ (2 : ℝ)) ^ (-A) := by
  obtain ⟨C, hC⟩ := h4 C₁ C₂ hC₁ hC₁C₂ K A hA
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Y hY0 hY16 q hq hqY S hS θ α₁ α₂ T hθ1 hθ2 hαd hα3 hα1lo hα1hi hα2lo hα2hi
    hα3lo hα3hi hTeq hT2 hTx hSt a b e ha hb he he32
  have hY1 : (1 : ℝ) ≤ Y := by linarith [hY16]
  have hYsq1 : (1 : ℝ) ≤ Y ^ (2 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hY1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa using h
  have hX2 : (2 : ℝ) ≤ Y ^ (2 : ℝ) := by
    have h2 : (2 : ℝ) ≤ Y := by
      have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
      rw [h16] at hY16
      linarith
    have h3 : (2 : ℝ) * 2 ≤ Y * Y := mul_le_mul h2 h2 (by norm_num) hY0.le
    calc (2 : ℝ) ≤ 2 * 2 := by norm_num
      _ ≤ Y * Y := h3
      _ = Y ^ (2 : ℝ) := by rw [Real.rpow_two, pow_two]
  have hXα1lo : (2 : ℝ) ≤ (Y ^ (2 : ℝ)) ^ α₁ := by
    rw [← Real.rpow_mul hY0.le]
    exact rpow_two_le hY16 (by linarith)
  have hXα1hi : (Y ^ (2 : ℝ)) ^ α₁ ≤ Y ^ (2 : ℝ) := rpow_sq_le hY1 hα1hi
  have hXα2lo : (2 : ℝ) ≤ (Y ^ (2 : ℝ)) ^ α₂ := by
    rw [← Real.rpow_mul hY0.le]
    exact rpow_two_le hY16 (by linarith)
  have hXα2hi : (Y ^ (2 : ℝ)) ^ α₂ ≤ Y ^ (2 : ℝ) := rpow_sq_le hY1 hα2hi
  have hXα3lo : (2 : ℝ) ≤ (Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂) := by
    rw [← Real.rpow_mul hY0.le]
    exact rpow_two_le hY16 (by linarith)
  have hXα3hi : (Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂) ≤ Y ^ (2 : ℝ) := rpow_sq_le hY1 hα3hi
  have happ := hC θ α₁ α₂ (Y ^ (2 : ℝ)) (Y ^ (2 : ℝ)) T q S a b e
    hθ1 hθ2 hαd hα3 hX2 (Or.inl rfl) hq hqY hT2 hTx hTeq
    hXα1lo hXα1hi hXα2lo hXα2hi hXα3lo hXα3hi hS hSt ha hb he he32
  have hsqrt : (Y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = Y := rpow_sqrt_sq hY0.le
  rw [hsqrt] at happ
  refine happ.trans (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (Real.log_nonneg hYsq1) _))
  exact mul_le_mul_of_nonneg_right (le_max_left C 1) hY0.le

/-- `A ≤ Y ^ e` from `log A ≤ e * log Y`. -/
private theorem le_rpow_of_log_le {A Y e : ℝ} (hA : 0 < A) (hY : 0 < Y)
    (hlog : Real.log A ≤ e * Real.log Y) : A ≤ Y ^ e := by
  rw [← Real.log_le_log_iff hA (Real.rpow_pos_of_pos hY e), Real.log_rpow hY]
  exact hlog

/-- `2 ^ 16 ≤ Y` from `16 * log 2 ≤ log Y`. -/
private theorem rpow_two16_le {Y : ℝ} (hY : 0 < Y) (h : 16 * Real.log 2 ≤ Real.log Y) :
    (2 : ℝ) ^ (16 : ℕ) ≤ Y := by
  rw [← Real.log_le_log_iff (by positivity) hY, Real.log_pow]
  push_cast
  exact h

/-- The two bounds for `sieveQ` at the prime window: it is the floor of `Y^(t2/2)/2`. -/
private theorem sieveQ_bounds {ε x Y t2 : ℝ} (hxpos : 0 < x) (hY : Y = x ^ (11 / 20 + ε))
    (ht2 : t2 = 2 * (1 / 16 - 1 / 10 ^ 5)) (h4 : (4 : ℝ) ≤ Y ^ (t2 / 2)) :
    ((sieveQ ε x : ℕ) : ℝ) ≤ Y ^ (t2 / 2) / 2 ∧
      Y ^ (t2 / 2) / 4 ≤ ((sieveQ ε x : ℕ) : ℝ) := by
  have hYpos : 0 < Y := by rw [hY]; exact Real.rpow_pos_of_pos hxpos _
  have harg : ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2
      = Y ^ (t2 / 2) / 2 := by
    rw [← hY, ← ht2, ← Real.rpow_mul hYpos.le]
    congr 2
    ring
  constructor
  · have h := Nat.floor_le (show (0 : ℝ) ≤ Y ^ (t2 / 2) / 2 by positivity)
    unfold sieveQ
    rw [harg]
    exact h
  · have h := Nat.lt_floor_add_one (Y ^ (t2 / 2) / 2)
    have h' : Y ^ (t2 / 2) / 2 - 1 < ((⌊Y ^ (t2 / 2) / 2⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    unfold sieveQ
    rw [harg]
    linarith

/-- The block `T = Y^(1 - t2/2 + 2δ)/q` exceeds `2`. -/
private theorem T_gt_two {Y q t2 δ : ℝ} (hY : 1 < Y) (hq : 0 < q)
    (hqle : q ≤ Y ^ (t2 / 2) / 2) (ht2 : t2 < 1) (hδ : 0 < δ) :
    (2 : ℝ) < Y ^ (1 - t2 / 2 + 2 * δ) / q := by
  have hp1 : (0 : ℝ) < Y ^ (1 - t2 / 2 + 2 * δ) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : Y ^ (1 - t2 / 2 + 2 * δ) / (Y ^ (t2 / 2) / 2) ≤
      Y ^ (1 - t2 / 2 + 2 * δ) / q := div_le_div_of_nonneg_left hp1.le hq hqle
  have hp2 : (0 : ℝ) < Y ^ (t2 / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hfac : Y ^ (1 - t2 / 2 + 2 * δ) = Y ^ (1 - t2 + 2 * δ) * Y ^ (t2 / 2) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  have h2 : Y ^ (1 - t2 / 2 + 2 * δ) / (Y ^ (t2 / 2) / 2) = 2 * Y ^ (1 - t2 + 2 * δ) := by
    rw [hfac]
    field_simp
  rw [h2] at h1
  have h3 : (0 : ℝ) < 1 - t2 + 2 * δ := by linarith
  have h4 : (1 : ℝ) < Y ^ (1 - t2 + 2 * δ) := by
    have h5 : Y ^ (0 : ℝ) < Y ^ (1 - t2 + 2 * δ) :=
      Real.rpow_lt_rpow_of_exponent_lt hY h3
    rwa [Real.rpow_zero] at h5
  linarith

/-- The block `T = Y^(1 - t2/2 + 2δ)/q` is at most `Y^2/4`. -/
private theorem T_le_quarter {Y q t2 δ : ℝ} (hY : 1 ≤ Y) (hq : 1 ≤ q)
    (h4 : (4 : ℝ) ≤ Y ^ (2 * δ)) (h2δ : 4 * δ ≤ 1) (ht2 : 0 < t2) (hδ : 0 < δ) :
    Y ^ (1 - t2 / 2 + 2 * δ) / q ≤ (Y ^ (2 : ℝ)) / 4 := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hp := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < Y) (1 - t2 / 2 + 2 * δ)
  have h1 : Y ^ (1 - t2 / 2 + 2 * δ) / q ≤ Y ^ (1 - t2 / 2 + 2 * δ) := by
    rw [div_le_iff₀ hqpos]
    nlinarith
  have h2 : Y ^ (1 - t2 / 2 + 2 * δ) ≤ Y ^ (2 - 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hp2 := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < Y) (2 - 2 * δ)
  have hfac : Y ^ (2 - 2 * δ) * Y ^ (2 * δ) = Y ^ (2 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  have h3 : Y ^ (2 - 2 * δ) ≤ Y ^ (2 : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    rw [← hfac]
    nlinarith
  linarith

/-- The block length `Y/(q Q)` is at most `T`. -/
private theorem block_le {Y q Q T blk t2 δ : ℝ} (hY : 0 < Y) (hq : 0 < q) (hQ : 0 < Q)
    (hstep : blk ≤ Y / (q * Q)) (hQlow : Y ^ (t2 / 2) / 4 ≤ Q)
    (h4 : (4 : ℝ) ≤ Y ^ (2 * δ)) (hδ : 0 < δ) (hT : T = Y ^ (1 - t2 / 2 + 2 * δ) / q) :
    blk ≤ T := by
  have hp := Real.rpow_pos_of_pos hY (t2 / 2)
  have hYp := Real.rpow_pos_of_pos hY (1 - t2 / 2)
  have h1 : Y / (q * Q) ≤ 4 * Y ^ (1 - t2 / 2) / q := by
    have hstep2 : Y / (q * Q) ≤ Y / (q * (Y ^ (t2 / 2) / 4)) := by
      apply div_le_div_of_nonneg_left hY.le (by positivity) (by nlinarith)
    have heq : Y / (q * (Y ^ (t2 / 2) / 4)) = 4 * Y ^ (1 - t2 / 2) / q := by
      have hdiv : Y / Y ^ (t2 / 2) = Y ^ (1 - t2 / 2) := by
        rw [Real.rpow_sub hY, Real.rpow_one]
      calc Y / (q * (Y ^ (t2 / 2) / 4)) = (Y / Y ^ (t2 / 2)) * 4 / q := by
            field_simp
        _ = Y ^ (1 - t2 / 2) * 4 / q := by rw [hdiv]
        _ = 4 * Y ^ (1 - t2 / 2) / q := by ring
    rw [heq] at hstep2
    exact hstep2
  have h2 : 4 * Y ^ (1 - t2 / 2) ≤ Y ^ (1 - t2 / 2 + 2 * δ) := by
    have hfac : Y ^ (1 - t2 / 2) * Y ^ (2 * δ) = Y ^ (1 - t2 / 2 + 2 * δ) := by
      rw [← Real.rpow_add hY]
    nlinarith
  have h3 : 4 * Y ^ (1 - t2 / 2) / q ≤ Y ^ (1 - t2 / 2 + 2 * δ) / q :=
    div_le_div_of_nonneg_right h2 hq.le
  rw [hT]
  linarith

/-- The divisor bound (3.1) survives cutting the coefficients off outside a window that avoids zero. -/
private theorem coeffBound_cutoff {a : ℕ → ℂ} {B B' lo hi : ℝ} (hlo : 0 < lo) (hBB : B ≤ B')
    (ha : Thm4.CoeffBound a B) :
    Thm4.CoeffBound (fun n => if lo < (n : ℝ) ∧ (n : ℝ) < hi then a n else 0) B' := by
  intro n
  simp only
  by_cases h : lo < (n : ℝ) ∧ (n : ℝ) < hi
  · rw [if_pos h]
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hlo h.1
    have hn0 : n ≠ 0 := by intro hh; rw [hh] at hnpos; simp at hnpos
    have hτ : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
      have hpos : 0 < n.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      exact_mod_cast hpos
    exact le_trans (ha n) (Real.rpow_le_rpow_of_exponent_le hτ hBB)
  · rw [if_neg h, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The divisor bound (3.1) at a nonnegative exponent. -/
private theorem coeffBound_max_zero {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B) :
    Thm4.CoeffBound a (max B 0) := by
  by_cases hB : (0:ℝ) ≤ B
  · rwa [max_eq_left hB]
  · intro n
    have hBlt : B < 0 := by linarith
    have hmax : max B 0 = 0 := max_eq_right hBlt.le
    rw [hmax, Real.rpow_zero]
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have h := ha 0
      rw [Nat.divisors_zero, Finset.card_empty] at h
      simp only [Nat.cast_zero, Real.zero_rpow (ne_of_lt hBlt)] at h
      refine le_trans h ?_
      norm_num
    · have h := ha n
      have hτ : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
        have hpos : 0 < n.divisors.card :=
          Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
        exact_mod_cast hpos
      have h1 : (n.divisors.card : ℝ) ^ B ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hτ hBlt.le
      linarith

/-- `log (Y²) = 2(11/20+ε) log x`, so powers of `log x` convert into powers of `log (Y²)`. -/
private theorem log_x_pow_eq {ε x Y : ℝ} (hx1 : 1 ≤ x) (hYpos : 0 < Y) (hε : 0 < ε)
    (hlogY : Real.log Y = (11 / 20 + ε) * Real.log x) (a : ℝ) :
    Real.log x ^ (-a) = (2 * (11 / 20 + ε)) ^ a * Real.log (Y ^ (2 : ℝ)) ^ (-a) := by
  have hc : (0 : ℝ) < 2 * (11 / 20 + ε) := by linarith
  have h1 : Real.log (Y ^ (2 : ℝ)) = (2 * (11 / 20 + ε)) * Real.log x := by
    rw [Real.log_rpow hYpos, hlogY]
    ring
  rw [h1, Real.mul_rpow hc.le (Real.log_nonneg hx1)]
  rw [← mul_assoc, ← Real.rpow_add hc, show a + -a = 0 from by ring, Real.rpow_zero, one_mul]

/-- The same conversion in the other direction. -/
private theorem log_sq_pow_eq {ε x Y : ℝ} (hx1 : 1 ≤ x) (hYpos : 0 < Y) (hε : 0 < ε)
    (hlogY : Real.log Y = (11 / 20 + ε) * Real.log x) (a : ℝ) :
    Real.log (Y ^ (2 : ℝ)) ^ (-a) = 2 ^ (-a) * (11 / 20 + ε) ^ (-a) * Real.log x ^ (-a) := by
  have hc : (0 : ℝ) < 2 * (11 / 20 + ε) := by linarith
  have h1 : Real.log (Y ^ (2 : ℝ)) = (2 * (11 / 20 + ε)) * Real.log x := by
    rw [Real.log_rpow hYpos, hlogY]
    ring
  rw [h1, Real.mul_rpow hc.le (Real.log_nonneg hx1)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ 11 / 20 + ε)]

set_option maxHeartbeats 800000 in
/-- LEAF: P0069 page 48, Lemma 33 and its proof, "for (beta1, beta2) in R we apply Theorem 4
with N^2 L, LM, M, T2 in place of M, N, L, T. Thus (3.5) holds with X = Y^2", and for P1 with
M^2 N, L^2, N, and P2 by beta1 to 1 - beta1 - beta2, ending "||LMN||_2^2 << Y L^-A if t is in
[T, T + T2]", for the principal character. M and N have lengths Y^beta1 and Y^beta2, satisfy
(3.1) and (3.2) on the block, L has length Y^(1 - beta1 - beta2) and satisfies (3.1), and
(beta1, beta2) lies in R, P1 or P2 as in upperPairRegion. Paper's proof: |LMN|^2 = |(LMN)^2|,
the block is moved into [-T, T] by kept52_dirPoly_shift, and Theorem 4 is applied with its own
x equal to Y^2 and X = x, theta just below 1/2 + theta2/4, and a smaller eps, see the notes.
CONDITIONAL on Theorem 4. HARD. -/
theorem kept52_lemma33_block (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro B c₁ c₂ hc₁ hc₂ K A hA
  set t2 : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5) with ht2def
  have ht2pos : 0 < t2 := by rw [ht2def]; norm_num
  have ht2lt : t2 < 1 := by rw [ht2def]; norm_num
  set δ : ℝ := ε / 144 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : 4 * δ ≤ 1 := by rw [hδdef]; nlinarith [hε8]
  set Bm : ℝ := max B 0 with hBmdef
  have hBm0 : 0 ≤ Bm := le_max_right B 0
  have hBmB : B ≤ Bm := le_max_left B 0
  set Bq : ℝ := 2 * Bm + 1 with hBqdef
  have hBq0 : 0 < Bq := by rw [hBqdef]; linarith
  set Bz : ℝ := 2 * Bq + 1 with hBzdef
  have hBz0 : 0 < Bz := by rw [hBzdef]; linarith
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := h4 Bz
  set ep : ℝ := min (ε₀ / 2) (ε / 288) with hepdef
  have heppos : 0 < ep := lt_min (by linarith) (by positivity)
  have heplt : ep < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heple : ep ≤ ε / 288 := min_le_right _ _
  have hT4 : Thm4.Theorem4 ep Bz := hε₀ ep heppos heplt
  set C₁ : ℝ := min c₁ (min (c₁ * c₁) (c₁ * c₁ * c₁)) with hC1def
  set C₂ : ℝ := max c₂ (max (c₂ * c₂) (c₂ * c₂ * c₂)) with hC2def
  have hC1pos : 0 < C₁ := lt_min hc₁ (lt_min (by positivity) (by positivity))
  have hC1c1 : C₁ ≤ c₁ := min_le_left _ _
  have hC1c2 : C₁ ≤ c₁ * c₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hC1c3 : C₁ ≤ c₁ * c₁ * c₁ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hc2C2 : c₂ ≤ C₂ := le_max_left _ _
  have hc2C2b : c₂ * c₂ ≤ C₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hc2C2c : c₂ * c₂ * c₂ ≤ C₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hc2pos : (0 : ℝ) < c₂ := lt_trans hc₁ hc₂
  have hC12 : C₁ < C₂ := lt_of_lt_of_le (lt_of_le_of_lt hC1c1 hc₂) hc2C2
  set θ : ℝ := 1 / 2 + t2 / 4 - δ with hθdef
  set Λ : ℝ := max (max (16 * Real.log 2) (Real.log 4 / (2 * δ)))
    (max (Real.log 4 / (t2 / 2)) 1) with hΛdef
  have hAΛ : max (16 * Real.log 2) (Real.log 4 / (2 * δ)) ≤ Λ := le_max_left _ _
  have hBΛ : max (Real.log 4 / (t2 / 2)) 1 ≤ Λ := le_max_right _ _
  have h161 : 16 * Real.log 2 ≤ Λ :=
    le_trans (le_max_left _ _) hAΛ
  have hδ1 : Real.log 4 / (2 * δ) ≤ Λ := le_trans (le_max_right _ _) hAΛ
  have hq1 : Real.log 4 / (t2 / 2) ≤ Λ := le_trans (le_max_left _ _) hBΛ
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hBΛ)
  set K' : ℝ → ℝ := fun A' => K A' * (2 * (11 / 20 + ε)) ^ A' with hK'def
  obtain ⟨C4, hC4pos, hC4⟩ := t4_block_bound (K := K') (A := A) hT4 hC1pos hC12 hA
  set Cfin : ℝ := C4 * 2 ^ (-A) * (11 / 20 + ε) ^ (-A) with hCfindef
  have hCfinpos : 0 < Cfin := by
    rw [hCfindef]
    exact mul_pos (mul_pos hC4pos (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨max (Real.exp (2 * Λ / (11 / 20 + ε)) + 2) Cfin, ?_⟩
  intro x hx q hq hqx a b hab hblk S hS hspace β₁ β₂ hreg eL eM eN hLc hMc hNc hM32 hN32
  have hxe : Real.exp (2 * Λ / (11 / 20 + ε)) ≤ x := by
    linarith [le_max_left (Real.exp (2 * Λ / (11 / 20 + ε)) + 2) Cfin]
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hx1 : (1 : ℝ) ≤ x := by
    have h3 : (1 : ℝ) ≤ Real.exp (2 * Λ / (11 / 20 + ε)) := Real.one_le_exp (by positivity)
    linarith only [hxe, h3]
  have hden : 0 < 11 / 20 + ε := by linarith
  have hlogx : 2 * Λ / (11 / 20 + ε) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at h
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos _
  have hlogY : (11 / 20 + ε) * Real.log x = Real.log Y := by
    rw [hYdef, Real.log_rpow hxpos]
  have hlogYbig : Λ ≤ Real.log Y := by
    have h2 : (11 / 20 + ε) * (2 * Λ / (11 / 20 + ε)) = 2 * Λ := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have h3 := mul_le_mul_of_nonneg_left hlogx hden.le
    rw [h2] at h3
    rw [← hlogY]
    linarith
  have h16log : 16 * Real.log 2 ≤ Real.log Y := le_trans h161 hlogYbig
  have hlog4δ : Real.log 4 ≤ 2 * δ * Real.log Y := by
    have hpos : (0 : ℝ) < 2 * δ := by positivity
    have h1' : Real.log 4 ≤ Λ * (2 * δ) := (div_le_iff₀ hpos).mp hδ1
    have h3 : Λ * (2 * δ) ≤ Real.log Y * (2 * δ) :=
      mul_le_mul_of_nonneg_right hlogYbig hpos.le
    linarith
  have hlog4t : Real.log 4 ≤ t2 / 2 * Real.log Y := by
    have hpos : (0 : ℝ) < t2 / 2 := by positivity
    have h1' : Real.log 4 ≤ Λ * (t2 / 2) := (div_le_iff₀ hpos).mp hq1
    have h3 : Λ * (t2 / 2) ≤ Real.log Y * (t2 / 2) :=
      mul_le_mul_of_nonneg_right hlogYbig hpos.le
    linarith
  have hY16 : (2 : ℝ) ^ (16 : ℕ) ≤ Y := rpow_two16_le hYpos h16log
  have hYsq4 : (4 : ℝ) ≤ Y ^ (2 * δ) := le_rpow_of_log_le (by norm_num) hYpos hlog4δ
  have hYQ4 : (4 : ℝ) ≤ Y ^ (t2 / 2) := le_rpow_of_log_le (by norm_num) hYpos hlog4t
  have hY2 : (2 : ℝ) ≤ Y := by
    have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
    rw [h16] at hY16
    linarith
  have hYone : (1 : ℝ) ≤ Y := by linarith
  have hYgt1 : (1 : ℝ) < Y := by linarith
  obtain ⟨hQup, hQlow⟩ := sieveQ_bounds hxpos hYdef ht2def hYQ4
  have hqx' : (q : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hqx
  have hqQ : (q : ℝ) ≤ Y ^ (t2 / 2) / 2 := le_trans hqx' hQup
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQpos : (0 : ℝ) < (sieveQ ε x : ℝ) := by
    have : 0 < sieveQ ε x := by
      have := hq
      have := hqx
      omega
    exact_mod_cast this
  set T : ℝ := Y ^ (1 - t2 / 2 + 2 * δ) / (q : ℝ) with hTdef
  have hTeq : (q : ℝ) * T = (Y ^ (2 : ℝ)) ^ (1 - θ) := by
    rw [hTdef, rpow_two_mul hYpos]
    have he : 2 * (1 - θ) = 1 - t2 / 2 + 2 * δ := by rw [hθdef]; ring
    rw [he]
    field_simp
  have hT2 : 2 < T := T_gt_two hYgt1 hqpos hqQ ht2lt hδpos
  have hTx : T ≤ (Y ^ (2 : ℝ)) / 4 := by
    rw [hTdef]
    exact T_le_quarter (q := (q : ℝ)) hYone (by exact_mod_cast hq) hYsq4 hδsmall ht2pos hδpos
  have hblkT : b - a ≤ T := by
    have hcast : ((q * sieveQ ε x : ℕ) : ℝ) = (q : ℝ) * (sieveQ ε x : ℝ) := by push_cast; ring
    have hstep : b - a ≤ Y / ((q : ℝ) * (sieveQ ε x : ℝ)) := hblk
    exact block_le hYpos hqpos hQpos hstep hQlow hYsq4 hδpos (by rw [hTdef])
  set S' : Finset (ℝ × DirichletCharacter ℂ q) :=
    S.image (fun t => (t - a, (1 : DirichletCharacter ℂ q))) with hS'def
  have hS'space : Thm4.WellSpaced S' := by
    intro p hp p' hp' hne hχ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hp'
    have h1 : t - a - (t' - a) = t - t' := by ring
    have h2 : 1 ≤ |t - t'| := hspace t ht t' ht' (fun h => hne (by rw [h]))
    rwa [h1]
  have hS't : ∀ p ∈ S', |p.1| ≤ T := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have h1 : a ≤ t ∧ t ≤ b := hS t ht
    have h2 : |t - a| = t - a := abs_of_nonneg (by linarith)
    rw [h2]
    linarith
  have hinjS : Set.InjOn (fun t : ℝ => (t - a, (1 : DirichletCharacter ℂ q))) ↑S := by
    intro t _ t' _ h
    have h1 := congrArg Prod.fst h
    simp only at h1
    linarith
  have hsum_reindex : ∀ FL : ℝ, ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ FL
        (1 : DirichletCharacter ℂ q) (Thm4.half t) *
      Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
      Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2
      = ∑ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ FL
        (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
      Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
      Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2 := by
    intro FL
    rw [hS'def, Finset.sum_image hinjS]
    apply Finset.sum_congr rfl
    intro t _
    simp only [sub_add_cancel]

  -- CASE B: |4β₁ + 3β₂ - 2| ≤ t2 - ε  (arrangement M²N, L², N)
  have hcaseB (hP : |4 * β₁ + 3 * β₂ - 2| ≤ t2 - ε) :
      ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ (Y ^ (1 - β₁ - β₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half t) *
        Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
        Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
        Cfin * Y * Real.log x ^ (-A) := by
    set Fl : ℝ := Y ^ (1 - β₁ - β₂) with hFldef
    set Fm : ℝ := Y ^ β₁ with hFmdef
    set Fn : ℝ := Y ^ β₂ with hFndef
    have hFlpos : 0 < Fl := by rw [hFldef]; exact Real.rpow_pos_of_pos hYpos _
    have hFmpos : 0 < Fm := by rw [hFmdef]; exact Real.rpow_pos_of_pos hYpos _
    have hFnpos : 0 < Fn := by rw [hFndef]; exact Real.rpow_pos_of_pos hYpos _
    set tL : ℕ → ℂ := fun n => eL n * (n : ℂ) ^ (-((a : ℂ) * I)) with htLdef
    set tM : ℕ → ℂ := fun n => eM n * (n : ℂ) ^ (-((a : ℂ) * I)) with htMdef
    set tN : ℕ → ℂ := fun n => eN n * (n : ℂ) ^ (-((a : ℂ) * I)) with htNdef
    have hLc2 : Thm4.CoeffBound tL Bm := coeffBound_max_zero (blk_coeffBound_shift hLc a)
    have hMc2 : Thm4.CoeffBound tM Bm := coeffBound_max_zero (blk_coeffBound_shift hMc a)
    have hNc2 : Thm4.CoeffBound tN Bm := coeffBound_max_zero (blk_coeffBound_shift hNc a)
    have hBmBq : Bm + Bm + 1 ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBqBz : Bq ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBmBz : Bm ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    set Wm : Finset ℕ := (Finset.range (⌊c₂ * Fm⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fm < n ∧ (n : ℝ) < c₂ * Fm) with hWm
    set Wl : Finset ℕ := (Finset.range (⌊c₂ * Fl⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fl < n ∧ (n : ℝ) < c₂ * Fl) with hWl
    set Wn : Finset ℕ := (Finset.range (⌊c₂ * Fn⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fn < n ∧ (n : ℝ) < c₂ * Fn) with hWn
    set WMM : Finset ℕ := (Finset.range (⌊(c₂ * c₂) * (Fm * Fm)⌋₊ + 1)).filter
      (fun n : ℕ => (c₁ * c₁) * (Fm * Fm) < n ∧ (n : ℝ) < (c₂ * c₂) * (Fm * Fm)) with hWMM
    have hWmpos : ∀ n ∈ Wm, 0 < n := by
      intro n hn
      rw [hWm] at hn
      have h : c₁ * Fm < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFmpos) h
      exact_mod_cast h2
    have hWlpos : ∀ n ∈ Wl, 0 < n := by
      intro n hn
      rw [hWl] at hn
      have h : c₁ * Fl < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFlpos) h
      exact_mod_cast h2
    have hWnpos : ∀ n ∈ Wn, 0 < n := by
      intro n hn
      rw [hWn] at hn
      have h : c₁ * Fn < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFnpos) h
      exact_mod_cast h2
    have hWMMpos : ∀ n ∈ WMM, 0 < n := by
      intro n hn
      rw [hWMM] at hn
      have h : (c₁ * c₁) * (Fm * Fm) < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) h
      exact_mod_cast h2
    set gMM : ℕ → ℂ := fun k => ∑ p ∈ (Wm ×ˢ Wm).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tM p.1 * tM p.2 with hgMM
    set g3 : ℕ → ℂ := fun k =>
      ∑ p ∈ (WMM ×ˢ Wn).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), gMM p.1 * tN p.2 with hg3
    set g3w : ℕ → ℂ := fun n =>
      if ((c₁ * c₁) * c₁) * (Fm * Fm * Fn) < (n : ℝ) ∧
        (n : ℝ) < ((c₂ * c₂) * c₂) * (Fm * Fm * Fn) then g3 n else 0 with hg3w
    set gLL : ℕ → ℂ := fun k => ∑ p ∈ (Wl ×ˢ Wl).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tL p.1 * tL p.2 with hgLL
    set gLLw : ℕ → ℂ := fun n =>
      if (c₁ * c₁) * (Fl * Fl) < (n : ℝ) ∧ (n : ℝ) < (c₂ * c₂) * (Fl * Fl) then gLL n else 0
      with hgLLw
    set g1 : ℕ → ℂ := fun n =>
      if c₁ * Fn < (n : ℝ) ∧ (n : ℝ) < c₂ * Fn then tN n else 0 with hg1
    have hgMMc : Thm4.CoeffBound gMM (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hMc2 hMc2 hWmpos hWmpos
    have hg3c : Thm4.CoeffBound g3 (Bm + Bm + 1 + Bm + 1) :=
      fiber_coeffBound (by linarith) hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1 + Bm + 1) hgMMc hNc2 hWMMpos hWnpos
    have hg3wc : Thm4.CoeffBound g3w Bz :=
      coeffBound_cutoff (lo := ((c₁ * c₁) * c₁) * (Fm * Fm * Fn)) (hi := ((c₂ * c₂) * c₂) * (Fm * Fm * Fn))
        (by positivity) (by rw [hBzdef]; linarith) hg3c
    have hgLLc : Thm4.CoeffBound gLL (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hLc2 hLc2 hWlpos hWlpos
    have hgLLwc : Thm4.CoeffBound gLLw Bz :=
      coeffBound_cutoff (lo := (c₁ * c₁) * (Fl * Fl)) (hi := (c₂ * c₂) * (Fl * Fl))
        (by positivity) hBmBq hgLLc
    have hg1c : Thm4.CoeffBound g1 Bz :=
      coeffBound_cutoff (lo := c₁ * Fn) (hi := c₂ * Fn) (by positivity) hBmBz hNc2
    -- the convolution identities at a general point s
    have hconvMM : ∀ s : ℂ, Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s * Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gMM (c₁ * c₁) (c₂ * c₂) (Fm * Fm) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tM tM
        (d₁ := c₁) (d₂ := c₂) (Fa := Fm) (Fb := Fm) hc₁ hc2pos hc₁ hc2pos hFmpos hFmpos
      simp only [← hWm] at h
      simpa only [← hgMM] using h
    have hconvMMn : ∀ s : ℂ, Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s * Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gMM (c₁ * c₁) (c₂ * c₂) (Fm * Fm) (1 : DirichletCharacter ℂ q) s := hconvMM
    have hconv3 : ∀ s : ℂ, Thm4.dirPoly gMM (c₁ * c₁) (c₂ * c₂) (Fm * Fm) (1 : DirichletCharacter ℂ q) s *
        Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s = Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂)
          (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gMM tN
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (d₁ := c₁) (d₂ := c₂) (Fa := Fm * Fm) (Fb := Fn)
        (by positivity) (by positivity) hc₁ hc2pos (by positivity) hFnpos
      simp only [← hWMM, ← hWn] at h
      simpa only [← hg3] using h
    have hconv3w : ∀ s : ℂ, Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂)
        (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q) s = Thm4.dirPoly g3w C₁ C₂ (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) g3
        (c₁ := (c₁ * c₁) * c₁) (c₂ := (c₂ * c₂) * c₂) (C₁ := C₁) (C₂ := C₂)
        (F := Fm * Fm * Fn) hC1c3 hc2C2c (by positivity) (by positivity)
      simpa only [← hg3w] using h
    have hconvLL : ∀ s : ℂ, Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s * Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gLL (c₁ * c₁) (c₂ * c₂) (Fl * Fl) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tL tL
        (d₁ := c₁) (d₂ := c₂) (Fa := Fl) (Fb := Fl) hc₁ hc2pos hc₁ hc2pos hFlpos hFlpos
      simp only [← hWl] at h
      simpa only [← hgLL] using h
    have hconvLLw : ∀ s : ℂ, Thm4.dirPoly gLL (c₁ * c₁) (c₂ * c₂) (Fl * Fl) (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gLLw C₁ C₂ (Fl * Fl) (1 : DirichletCharacter ℂ q) s := by
      intro s
      exact dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gLL
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (C₁ := C₁) (C₂ := C₂) (F := Fl * Fl)
        hC1c2 hc2C2b (by positivity) (by positivity)
    have hconv1 : ∀ s : ℂ, Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s = Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) s := by
      intro s
      exact dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tN
        (c₁ := c₁) (c₂ := c₂) (C₁ := C₁) (C₂ := C₂) (F := Fn) hC1c1 hc2C2
        (by positivity) hFnpos
    -- the pointwise identity
    have hid : ∀ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2
        = ‖Thm4.dirPoly g3w C₁ C₂ (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly gLLw C₁ C₂ (Fl * Fl) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ := by
      intro u _
      have hPL : Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) u.1 a
      have hPM : Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) u.1 a
      have hPN : Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) u.1 a
      have hA : Thm4.dirPoly g3w C₁ C₂ (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconv3w (Thm4.half u.1), ← hconv3 (Thm4.half u.1), ← hconvMM (Thm4.half u.1)]
      have hB : Thm4.dirPoly gLLw C₁ C₂ (Fl * Fl) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconvLLw (Thm4.half u.1), ← hconvLL (Thm4.half u.1)]
      have hE : Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        (hconv1 (Thm4.half u.1)).symm
      rw [hPL, hPM, hPN, hA, hB, hE, ← norm_pow]
      congr 1
      ring
    -- the exponent data of the arrangement M²N, L², N
    set α₁ : ℝ := β₁ + β₂ / 2 with hα1def
    set α₂ : ℝ := 1 - β₁ - β₂ with hα2def
    have hlen1 : (Y ^ (2 : ℝ)) ^ α₁ = Fm * Fm * Fn := by
      rw [rpow_two_mul hYpos, hα1def, hFmdef, hFndef, ← Real.rpow_add hYpos,
        ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen2 : (Y ^ (2 : ℝ)) ^ α₂ = Fl * Fl := by
      rw [rpow_two_mul hYpos, hα2def, hFldef, ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen3 : (Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂) = Fn := by
      have h3 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h3, rpow_two_mul hYpos, hFndef]
      congr 1
      ring
    -- (3.2) for the third factor
    have hE32 : ∀ A' : ℝ, 0 < A' → ∀ p ∈ S',
        ‖Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) p.2
            (Thm4.half p.1)‖ ≤
          K' A' * ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) *
            Real.log (Y ^ (2 : ℝ)) ^ (-A') := by
      intro A' hA' p hp
      rw [hlen3]
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have hpt : (t - a) + a = t := by ring
      have hval : Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (t - a)) =
          Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half t) := by
        rw [(hconv1 (Thm4.half (t - a))).symm, ← blk_dirPoly_shift eN c₁ c₂ Fn
          (1 : DirichletCharacter ℂ q) (t - a) a, hpt]
      rw [hval]
      have h1 := hN32 A' hA' t ht
      have hFnp : (Y ^ β₂) ^ (1 / 2 : ℝ) = Fn ^ (1 / 2 : ℝ) := by rw [hFndef]
      rw [hFnp] at h1
      refine h1.trans (le_of_eq ?_)
      rw [hK'def, log_x_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A']
      ring
    -- the region arithmetic
    obtain ⟨hb2b1, hb1half, hlow, hup, -⟩ := hreg
    have hβ2le : β₂ ≤ 1 / 2 := le_trans hb2b1 hb1half
    have hP' : |2 * β₁ + 3 / 2 * β₂ - 1| ≤ (t2 - ε) / 2 :=
      region_P1_pair ht2def hε8 hP
    have hαd : |α₁ - α₂| < 2 * θ - 1 - ep := by
      have h1 : α₁ - α₂ = 2 * β₁ + 3 / 2 * β₂ - 1 := by rw [hα1def, hα2def]; ring
      rw [h1, hθdef]
      have h2 : 2 * (1 / 2 + t2 / 4 - δ) - 1 - ep = (t2 - ε) / 2 + (ε / 2 - 2 * δ - ep) := by
        rw [hδdef]; ring
      rw [h2]
      have h3 : (0 : ℝ) < ε / 2 - 2 * δ - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [hP', h3]
    have hα3 : 1 - (α₁ + α₂) < Thm4.gam θ - ep := by
      have h1 : 1 - (α₁ + α₂) = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h2 : β₂ / 2 ≤ ((36 * t2 - 2) / 11 - ε) / 2 := by linarith only [hup]
      have h3 : Thm4.gam θ ≥ (18 * t2 - 1) / 11 - 72 * δ / 11 :=
        gam_theta_ge ht2def hδdef hε hε8
      have h4 : ((36 * t2 - 2) / 11 - ε) / 2 = (18 * t2 - 1) / 11 - ε / 2 := by ring
      have h5 : (18 * t2 - 1) / 11 - ε / 2 < (18 * t2 - 1) / 11 - 72 * δ / 11 - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2, h3, h4, h5]
    have hθ1 : 1 / 2 + ep < θ := by
      rw [hθdef]
      have h2 : ep + δ < t2 / 4 := by
        rw [hepdef, hδdef, ht2def]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2]
    have hθ2 : θ < 7 / 12 := by
      rw [hθdef, ht2def]
      nlinarith only [hδpos]
    have hα1lo : 1 / 32 ≤ α₁ := by
      rw [hα1def]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      have h8 : (0 : ℝ) ≤ β₁ - β₂ := by linarith
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7, h8]
    have hα1hi : α₁ ≤ 1 := by
      rw [hα1def]
      linarith only [hb1half, hβ2le]
    have hα2lo : 1 / 32 ≤ α₂ := by
      rw [hα2def]
      have h7 : β₂ ≤ (36 * t2 - 2) / 11 - ε := hup
      rw [ht2def] at h7
      nlinarith only [hε, hε8, hb1half, h7]
    have hα2hi : α₂ ≤ 1 := by rw [hα2def]; linarith only [hε, hε8, hlow, hb2b1]
    have hα3lo : 1 / 32 ≤ 1 - α₁ - α₂ := by
      have h1 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7]
    have hα3hi : 1 - α₁ - α₂ ≤ 1 := by
      have h1 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      linarith only [hβ2le]
    have hqY : (q : ℝ) ≤ Y ^ (2 : ℝ) := by
      have h1 : Y ^ (t2 / 2) / 2 ≤ Y ^ (2 : ℝ) := by
        have h2 : Y ^ (t2 / 2) ≤ Y ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hYone (by linarith)
        have h3 := Real.rpow_pos_of_pos hYpos (t2 / 2)
        linarith only [h2, h3]
      linarith only [hqQ, h1]
    -- Theorem 4 for the block
    have happ := hC4 Y hYpos hY16 q hq hqY S' hS'space θ α₁ α₂ T hθ1 hθ2 hαd hα3
      hα1lo hα1hi hα2lo hα2hi hα3lo hα3hi hTeq hT2 hTx hS't g3w gLLw g1 hg3wc hgLLwc hg1c hE32
    have happ1 : (∑ p ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₁)
          (1 : DirichletCharacter ℂ q) (Thm4.half p.1) *
        Thm4.dirPoly gLLw C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₂) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1) *
        Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1)‖) ≤ C4 * Y * Real.log (Y ^ (2 : ℝ)) ^ (-A) := by
      refine le_trans (le_of_eq ?_) happ
      apply Finset.sum_congr rfl
      intro p hp
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      rfl
    rw [hlen1, hlen2, hlen3] at happ1
    rw [hsum_reindex Fl]
    have hsum_eq : (∑ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2)
        = ∑ u ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ (Fm * Fm * Fn) (1 : DirichletCharacter ℂ q)
            (Thm4.half u.1) *
          Thm4.dirPoly gLLw C₁ C₂ (Fl * Fl) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
          Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ :=
      Finset.sum_congr rfl hid
    rw [hsum_eq]
    refine happ1.trans ?_
    have hlog := log_sq_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A
    rw [hCfindef, hlog]
    refine le_of_eq ?_
    ring

  -- CASE C: |4β₁ + β₂ - 2| ≤ t2 - ε  (arrangement L²N, M², N)
  have hcaseC (hP : |4 * β₁ + β₂ - 2| ≤ t2 - ε) :
      ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ (Y ^ (1 - β₁ - β₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half t) *
        Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
        Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
        Cfin * Y * Real.log x ^ (-A) := by
    set Fl : ℝ := Y ^ (1 - β₁ - β₂) with hFldef
    set Fm : ℝ := Y ^ β₁ with hFmdef
    set Fn : ℝ := Y ^ β₂ with hFndef
    have hFlpos : 0 < Fl := by rw [hFldef]; exact Real.rpow_pos_of_pos hYpos _
    have hFmpos : 0 < Fm := by rw [hFmdef]; exact Real.rpow_pos_of_pos hYpos _
    have hFnpos : 0 < Fn := by rw [hFndef]; exact Real.rpow_pos_of_pos hYpos _
    set tL : ℕ → ℂ := fun n => eL n * (n : ℂ) ^ (-((a : ℂ) * I)) with htLdef
    set tM : ℕ → ℂ := fun n => eM n * (n : ℂ) ^ (-((a : ℂ) * I)) with htMdef
    set tN : ℕ → ℂ := fun n => eN n * (n : ℂ) ^ (-((a : ℂ) * I)) with htNdef
    have hLc2 : Thm4.CoeffBound tL Bm := coeffBound_max_zero (blk_coeffBound_shift hLc a)
    have hMc2 : Thm4.CoeffBound tM Bm := coeffBound_max_zero (blk_coeffBound_shift hMc a)
    have hNc2 : Thm4.CoeffBound tN Bm := coeffBound_max_zero (blk_coeffBound_shift hNc a)
    have hBmBq : Bm + Bm + 1 ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBqBz : Bq ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBmBzc : Bm ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    set Wm : Finset ℕ := (Finset.range (⌊c₂ * Fm⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fm < n ∧ (n : ℝ) < c₂ * Fm) with hWm
    set Wl : Finset ℕ := (Finset.range (⌊c₂ * Fl⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fl < n ∧ (n : ℝ) < c₂ * Fl) with hWl
    set Wn : Finset ℕ := (Finset.range (⌊c₂ * Fn⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fn < n ∧ (n : ℝ) < c₂ * Fn) with hWn
    set WLL : Finset ℕ := (Finset.range (⌊(c₂ * c₂) * (Fl * Fl)⌋₊ + 1)).filter
      (fun n : ℕ => (c₁ * c₁) * (Fl * Fl) < n ∧ (n : ℝ) < (c₂ * c₂) * (Fl * Fl)) with hWLL
    have hWmpos : ∀ n ∈ Wm, 0 < n := by
      intro n hn
      rw [hWm] at hn
      have h : c₁ * Fm < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFmpos) h
      exact_mod_cast h2
    have hWlpos : ∀ n ∈ Wl, 0 < n := by
      intro n hn
      rw [hWl] at hn
      have h : c₁ * Fl < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFlpos) h
      exact_mod_cast h2
    have hWnpos : ∀ n ∈ Wn, 0 < n := by
      intro n hn
      rw [hWn] at hn
      have h : c₁ * Fn < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFnpos) h
      exact_mod_cast h2
    have hWLLpos : ∀ n ∈ WLL, 0 < n := by
      intro n hn
      rw [hWLL] at hn
      have h : (c₁ * c₁) * (Fl * Fl) < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) h
      exact_mod_cast h2
    set gLL : ℕ → ℂ := fun k => ∑ p ∈ (Wl ×ˢ Wl).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tL p.1 * tL p.2 with hgLL
    set g3 : ℕ → ℂ := fun k =>
      ∑ p ∈ (WLL ×ˢ Wn).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), gLL p.1 * tN p.2 with hg3
    set g3w : ℕ → ℂ := fun n =>
      if ((c₁ * c₁) * c₁) * (Fl * Fl * Fn) < (n : ℝ) ∧
        (n : ℝ) < ((c₂ * c₂) * c₂) * (Fl * Fl * Fn) then g3 n else 0 with hg3w
    set gMM : ℕ → ℂ := fun k => ∑ p ∈ (Wm ×ˢ Wm).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tM p.1 * tM p.2 with hgMM
    set gMMw : ℕ → ℂ := fun n =>
      if (c₁ * c₁) * (Fm * Fm) < (n : ℝ) ∧ (n : ℝ) < (c₂ * c₂) * (Fm * Fm) then gMM n else 0
      with hgMMw
    set g1 : ℕ → ℂ := fun n =>
      if c₁ * Fn < (n : ℝ) ∧ (n : ℝ) < c₂ * Fn then tN n else 0 with hg1
    have hgLLc : Thm4.CoeffBound gLL (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hLc2 hLc2 hWlpos hWlpos
    have hg3c : Thm4.CoeffBound g3 (Bm + Bm + 1 + Bm + 1) :=
      fiber_coeffBound (by linarith) hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1 + Bm + 1) hgLLc hNc2 hWLLpos hWnpos
    have hg3wc : Thm4.CoeffBound g3w Bz :=
      coeffBound_cutoff (lo := ((c₁ * c₁) * c₁) * (Fl * Fl * Fn)) (hi := ((c₂ * c₂) * c₂) * (Fl * Fl * Fn))
        (by positivity) (by rw [hBzdef]; linarith) hg3c
    have hgMMc : Thm4.CoeffBound gMM (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hMc2 hMc2 hWmpos hWmpos
    have hgMMwc : Thm4.CoeffBound gMMw Bz :=
      coeffBound_cutoff (lo := (c₁ * c₁) * (Fm * Fm)) (hi := (c₂ * c₂) * (Fm * Fm))
        (by positivity) hBmBq hgMMc
    have hg1c : Thm4.CoeffBound g1 Bz :=
      coeffBound_cutoff (lo := c₁ * Fn) (hi := c₂ * Fn) (by positivity) hBmBzc hNc2
    have hconvLL : ∀ s : ℂ, Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s *
        Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gLL (c₁ * c₁) (c₂ * c₂) (Fl * Fl) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tL tL
        (d₁ := c₁) (d₂ := c₂) (Fa := Fl) (Fb := Fl) hc₁ hc2pos hc₁ hc2pos hFlpos hFlpos
      simp only [← hWl] at h
      simpa only [← hgLL] using h
    have hconv3 : ∀ s : ℂ, Thm4.dirPoly gLL (c₁ * c₁) (c₂ * c₂) (Fl * Fl)
        (1 : DirichletCharacter ℂ q) s * Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂) (Fl * Fl * Fn)
          (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gLL tN
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (d₁ := c₁) (d₂ := c₂) (Fa := Fl * Fl) (Fb := Fn)
        (by positivity) (by positivity) hc₁ hc2pos (by positivity) hFnpos
      simp only [← hWLL, ← hWn] at h
      simpa only [← hg3] using h
    have hconv3w : ∀ s : ℂ, Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂)
        (Fl * Fl * Fn) (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g3w C₁ C₂ (Fl * Fl * Fn) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) g3
        (c₁ := (c₁ * c₁) * c₁) (c₂ := (c₂ * c₂) * c₂) (C₁ := C₁) (C₂ := C₂)
        (F := Fl * Fl * Fn) hC1c3 hc2C2c (by positivity) (by positivity)
      simpa only [← hg3w] using h
    have hconvMM : ∀ s : ℂ, Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s *
        Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gMM (c₁ * c₁) (c₂ * c₂) (Fm * Fm) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tM tM
        (d₁ := c₁) (d₂ := c₂) (Fa := Fm) (Fb := Fm) hc₁ hc2pos hc₁ hc2pos hFmpos hFmpos
      simp only [← hWm] at h
      simpa only [← hgMM] using h
    have hconvMMw : ∀ s : ℂ, Thm4.dirPoly gMM (c₁ * c₁) (c₂ * c₂) (Fm * Fm)
        (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gMMw C₁ C₂ (Fm * Fm) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gMM
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (C₁ := C₁) (C₂ := C₂) (F := Fm * Fm)
        hC1c2 hc2C2b (by positivity) (by positivity)
      simpa only [← hgMMw] using h
    have hconv1 : ∀ s : ℂ, Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) s := by
      intro s
      exact dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tN
        (c₁ := c₁) (c₂ := c₂) (C₁ := C₁) (C₂ := C₂) (F := Fn) hC1c1 hc2C2
        (by positivity) hFnpos
    have hid : ∀ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2
        = ‖Thm4.dirPoly g3w C₁ C₂ (Fl * Fl * Fn) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly gMMw C₁ C₂ (Fm * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ := by
      intro u _
      have hPL : Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) u.1 a
      have hPM : Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) u.1 a
      have hPN : Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) u.1 a
      have hA : Thm4.dirPoly g3w C₁ C₂ (Fl * Fl * Fn) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconv3w (Thm4.half u.1), ← hconv3 (Thm4.half u.1), ← hconvLL (Thm4.half u.1)]
      have hB : Thm4.dirPoly gMMw C₁ C₂ (Fm * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconvMMw (Thm4.half u.1), ← hconvMM (Thm4.half u.1)]
      have hE : Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        (hconv1 (Thm4.half u.1)).symm
      rw [hPL, hPM, hPN, hA, hB, hE, ← norm_pow]
      congr 1
      ring
    set α₁ : ℝ := 1 - β₁ - β₂ + β₂ / 2 with hα1def
    set α₂ : ℝ := β₁ with hα2def
    have hlen1 : (Y ^ (2 : ℝ)) ^ α₁ = Fl * Fl * Fn := by
      rw [rpow_two_mul hYpos, hα1def, hFldef, hFndef, ← Real.rpow_add hYpos,
        ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen2 : (Y ^ (2 : ℝ)) ^ α₂ = Fm * Fm := by
      rw [rpow_two_mul hYpos, hα2def, hFmdef, ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen3 : (Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂) = Fn := by
      have h3 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h3, rpow_two_mul hYpos, hFndef]
      congr 1
      ring
    have hE32 : ∀ A' : ℝ, 0 < A' → ∀ p ∈ S',
        ‖Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) p.2
            (Thm4.half p.1)‖ ≤
          K' A' * ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) *
            Real.log (Y ^ (2 : ℝ)) ^ (-A') := by
      intro A' hA' p hp
      rw [hlen3]
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have hpt : (t - a) + a = t := by ring
      have hval : Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (t - a)) =
          Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half t) := by
        rw [(hconv1 (Thm4.half (t - a))).symm, ← blk_dirPoly_shift eN c₁ c₂ Fn
          (1 : DirichletCharacter ℂ q) (t - a) a, hpt]
      rw [hval]
      have h1 := hN32 A' hA' t ht
      have hFnp : (Y ^ β₂) ^ (1 / 2 : ℝ) = Fn ^ (1 / 2 : ℝ) := by rw [hFndef]
      rw [hFnp] at h1
      refine h1.trans (le_of_eq ?_)
      rw [hK'def, log_x_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A']
      ring
    obtain ⟨hb2b1, hb1half, hlow, hup, -⟩ := hreg
    have hb1halfX : β₁ ≤ 1 / 2 := hb1half
    have hβ2le : β₂ ≤ 1 / 2 := le_trans hb2b1 hb1halfX
    have hP' : |1 - 2 * β₁ - β₂ / 2| ≤ (t2 - ε) / 2 := region_P2_pair ht2def hε8 hP
    have hαd : |α₁ - α₂| < 2 * θ - 1 - ep := by
      have h1 : α₁ - α₂ = 1 - 2 * β₁ - β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1, hθdef]
      have h2 : 2 * (1 / 2 + t2 / 4 - δ) - 1 - ep = (t2 - ε) / 2 + (ε / 2 - 2 * δ - ep) := by
        rw [hδdef]; ring
      rw [h2]
      have h3 : (0 : ℝ) < ε / 2 - 2 * δ - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [hP', h3]
    have hα3 : 1 - (α₁ + α₂) < Thm4.gam θ - ep := by
      have h1 : 1 - (α₁ + α₂) = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h2 : β₂ / 2 ≤ ((36 * t2 - 2) / 11 - ε) / 2 := by linarith only [hup]
      have h3 : Thm4.gam θ ≥ (18 * t2 - 1) / 11 - 72 * δ / 11 :=
        gam_theta_ge ht2def hδdef hε hε8
      have h4 : ((36 * t2 - 2) / 11 - ε) / 2 = (18 * t2 - 1) / 11 - ε / 2 := by ring
      have h5 : (18 * t2 - 1) / 11 - ε / 2 < (18 * t2 - 1) / 11 - 72 * δ / 11 - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2, h3, h4, h5]
    have hθ1 : 1 / 2 + ep < θ := by
      rw [hθdef]
      have h2 : ep + δ < t2 / 4 := by
        rw [hepdef, hδdef, ht2def]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2]
    have hθ2 : θ < 7 / 12 := by
      rw [hθdef, ht2def]
      nlinarith only [hδpos]
    have hα1lo : 1 / 32 ≤ α₁ := by
      rw [hα1def]
      have h7 : β₂ ≤ (36 * t2 - 2) / 11 - ε := hup
      rw [ht2def] at h7
      nlinarith only [hε, hε8, hb1halfX, h7]
    have hα1hi : α₁ ≤ 1 := by
      rw [hα1def]
      linarith only [hε, hε8, hlow, hb2b1]
    have hα2lo : 1 / 32 ≤ α₂ := by
      rw [hα2def]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7, hb2b1]
    have hα2hi : α₂ ≤ 1 := le_trans hb1halfX (by norm_num)
    have hα3lo : 1 / 32 ≤ 1 - α₁ - α₂ := by
      have h1 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7]
    have hα3hi : 1 - α₁ - α₂ ≤ 1 := by
      have h1 : 1 - α₁ - α₂ = β₂ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      linarith only [hβ2le]
    have hqY : (q : ℝ) ≤ Y ^ (2 : ℝ) := by
      have h1 : Y ^ (t2 / 2) / 2 ≤ Y ^ (2 : ℝ) := by
        have h2 : Y ^ (t2 / 2) ≤ Y ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hYone (by linarith)
        have h3 := Real.rpow_pos_of_pos hYpos (t2 / 2)
        linarith only [h2, h3]
      linarith only [hqQ, h1]
    have happ := hC4 Y hYpos hY16 q hq hqY S' hS'space θ α₁ α₂ T hθ1 hθ2 hαd hα3
      hα1lo hα1hi hα2lo hα2hi hα3lo hα3hi hTeq hT2 hTx hS't g3w gMMw g1 hg3wc hgMMwc hg1c hE32
    have happ1 : (∑ p ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₁)
          (1 : DirichletCharacter ℂ q) (Thm4.half p.1) *
        Thm4.dirPoly gMMw C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₂) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1) *
        Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1)‖) ≤ C4 * Y * Real.log (Y ^ (2 : ℝ)) ^ (-A) := by
      refine le_trans (le_of_eq ?_) happ
      apply Finset.sum_congr rfl
      intro p hp
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      rfl
    rw [hlen1, hlen2, hlen3] at happ1
    rw [hsum_reindex Fl]
    have hsum_eq : (∑ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2)
        = ∑ u ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ (Fl * Fl * Fn) (1 : DirichletCharacter ℂ q)
            (Thm4.half u.1) *
          Thm4.dirPoly gMMw C₁ C₂ (Fm * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
          Thm4.dirPoly g1 C₁ C₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ :=
      Finset.sum_congr rfl hid
    rw [hsum_eq]
    refine happ1.trans ?_
    have hlog := log_sq_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A
    rw [hCfindef, hlog]
    refine le_of_eq ?_
    ring

  -- CASE A: 2β₂ - t2 + ε ≤ β₁ and β₁ ≤ (36t2-2)/11 - ε  (arrangement N²L, LM, M)
  have hcaseA (hPa : 2 * β₂ - t2 + ε ≤ β₁) (hPb : β₁ ≤ (36 * t2 - 2) / 11 - ε) :
      ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ (Y ^ (1 - β₁ - β₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half t) *
        Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
        Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
        Cfin * Y * Real.log x ^ (-A) := by
    set Fl : ℝ := Y ^ (1 - β₁ - β₂) with hFldef
    set Fm : ℝ := Y ^ β₁ with hFmdef
    set Fn : ℝ := Y ^ β₂ with hFndef
    have hFlpos : 0 < Fl := by rw [hFldef]; exact Real.rpow_pos_of_pos hYpos _
    have hFmpos : 0 < Fm := by rw [hFmdef]; exact Real.rpow_pos_of_pos hYpos _
    have hFnpos : 0 < Fn := by rw [hFndef]; exact Real.rpow_pos_of_pos hYpos _
    set tL : ℕ → ℂ := fun n => eL n * (n : ℂ) ^ (-((a : ℂ) * I)) with htLdef
    set tM : ℕ → ℂ := fun n => eM n * (n : ℂ) ^ (-((a : ℂ) * I)) with htMdef
    set tN : ℕ → ℂ := fun n => eN n * (n : ℂ) ^ (-((a : ℂ) * I)) with htNdef
    have hLc2 : Thm4.CoeffBound tL Bm := coeffBound_max_zero (blk_coeffBound_shift hLc a)
    have hMc2 : Thm4.CoeffBound tM Bm := coeffBound_max_zero (blk_coeffBound_shift hMc a)
    have hNc2 : Thm4.CoeffBound tN Bm := coeffBound_max_zero (blk_coeffBound_shift hNc a)
    have hBmBq : Bm + Bm + 1 ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBqBz : Bq ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    have hBmBzc : Bm ≤ Bz := by rw [hBzdef, hBqdef]; linarith
    set Wm : Finset ℕ := (Finset.range (⌊c₂ * Fm⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fm < n ∧ (n : ℝ) < c₂ * Fm) with hWm
    set Wl : Finset ℕ := (Finset.range (⌊c₂ * Fl⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fl < n ∧ (n : ℝ) < c₂ * Fl) with hWl
    set Wn : Finset ℕ := (Finset.range (⌊c₂ * Fn⌋₊ + 1)).filter
      (fun n : ℕ => c₁ * Fn < n ∧ (n : ℝ) < c₂ * Fn) with hWn
    set WNN : Finset ℕ := (Finset.range (⌊(c₂ * c₂) * (Fn * Fn)⌋₊ + 1)).filter
      (fun n : ℕ => (c₁ * c₁) * (Fn * Fn) < n ∧ (n : ℝ) < (c₂ * c₂) * (Fn * Fn)) with hWNN
    have hWmpos : ∀ n ∈ Wm, 0 < n := by
      intro n hn
      rw [hWm] at hn
      have h : c₁ * Fm < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFmpos) h
      exact_mod_cast h2
    have hWlpos : ∀ n ∈ Wl, 0 < n := by
      intro n hn
      rw [hWl] at hn
      have h : c₁ * Fl < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFlpos) h
      exact_mod_cast h2
    have hWnpos : ∀ n ∈ Wn, 0 < n := by
      intro n hn
      rw [hWn] at hn
      have h : c₁ * Fn < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (mul_pos hc₁ hFnpos) h
      exact_mod_cast h2
    have hWNNpos : ∀ n ∈ WNN, 0 < n := by
      intro n hn
      rw [hWNN] at hn
      have h : (c₁ * c₁) * (Fn * Fn) < (n : ℝ) := (Finset.mem_filter.mp hn).2.1
      have h2 : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) h
      exact_mod_cast h2
    set gNN : ℕ → ℂ := fun k => ∑ p ∈ (Wn ×ˢ Wn).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tN p.1 * tN p.2 with hgNN
    set g3 : ℕ → ℂ := fun k =>
      ∑ p ∈ (WNN ×ˢ Wl).filter (fun p : ℕ × ℕ => p.1 * p.2 = k), gNN p.1 * tL p.2 with hg3
    set g3w : ℕ → ℂ := fun n =>
      if ((c₁ * c₁) * c₁) * (Fn * Fn * Fl) < (n : ℝ) ∧
        (n : ℝ) < ((c₂ * c₂) * c₂) * (Fn * Fn * Fl) then g3 n else 0 with hg3w
    set gLM : ℕ → ℂ := fun k => ∑ p ∈ (Wl ×ˢ Wm).filter (fun p : ℕ × ℕ => p.1 * p.2 = k),
      tL p.1 * tM p.2 with hgLM
    set gLMw : ℕ → ℂ := fun n =>
      if (c₁ * c₁) * (Fl * Fm) < (n : ℝ) ∧ (n : ℝ) < (c₂ * c₂) * (Fl * Fm) then gLM n else 0
      with hgLMw
    set g1 : ℕ → ℂ := fun n =>
      if c₁ * Fm < (n : ℝ) ∧ (n : ℝ) < c₂ * Fm then tM n else 0 with hg1
    have hgNNc : Thm4.CoeffBound gNN (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hNc2 hNc2 hWnpos hWnpos
    have hg3c : Thm4.CoeffBound g3 (Bm + Bm + 1 + Bm + 1) :=
      fiber_coeffBound (by linarith) hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1 + Bm + 1) hgNNc hLc2 hWNNpos hWlpos
    have hg3wc : Thm4.CoeffBound g3w Bz :=
      coeffBound_cutoff (lo := ((c₁ * c₁) * c₁) * (Fn * Fn * Fl)) (hi := ((c₂ * c₂) * c₂) * (Fn * Fn * Fl))
        (by positivity) (by rw [hBzdef]; linarith) hg3c
    have hgLMc : Thm4.CoeffBound gLM (Bm + Bm + 1) :=
      fiber_coeffBound hBm0 hBm0 (le_refl _) (by linarith : (0:ℝ) < Bm + Bm + 1) hLc2 hMc2 hWlpos hWmpos
    have hgLMwc : Thm4.CoeffBound gLMw Bz :=
      coeffBound_cutoff (lo := (c₁ * c₁) * (Fl * Fm)) (hi := (c₂ * c₂) * (Fl * Fm))
        (by positivity) hBmBq hgLMc
    have hg1c : Thm4.CoeffBound g1 Bz :=
      coeffBound_cutoff (lo := c₁ * Fm) (hi := c₂ * Fm) (by positivity) hBmBzc hMc2
    have hconvNN : ∀ s : ℂ, Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s *
        Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gNN (c₁ * c₁) (c₂ * c₂) (Fn * Fn) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tN tN
        (d₁ := c₁) (d₂ := c₂) (Fa := Fn) (Fb := Fn) hc₁ hc2pos hc₁ hc2pos hFnpos hFnpos
      simp only [← hWn] at h
      simpa only [← hgNN] using h
    have hconv3 : ∀ s : ℂ, Thm4.dirPoly gNN (c₁ * c₁) (c₂ * c₂) (Fn * Fn)
        (1 : DirichletCharacter ℂ q) s * Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂) (Fn * Fn * Fl)
          (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gNN tL
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (d₁ := c₁) (d₂ := c₂) (Fa := Fn * Fn) (Fb := Fl)
        (by positivity) (by positivity) hc₁ hc2pos (by positivity) hFlpos
      simp only [← hWNN, ← hWl] at h
      simpa only [← hg3] using h
    have hconv3w : ∀ s : ℂ, Thm4.dirPoly g3 ((c₁ * c₁) * c₁) ((c₂ * c₂) * c₂)
        (Fn * Fn * Fl) (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g3w C₁ C₂ (Fn * Fn * Fl) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) g3
        (c₁ := (c₁ * c₁) * c₁) (c₂ := (c₂ * c₂) * c₂) (C₁ := C₁) (C₂ := C₂)
        (F := Fn * Fn * Fl) hC1c3 hc2C2c (by positivity) (by positivity)
      simpa only [← hg3w] using h
    have hconvLM : ∀ s : ℂ, Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) s *
        Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gLM (c₁ * c₁) (c₂ * c₂) (Fl * Fm) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_mul_conv_gen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tL tM
        (d₁ := c₁) (d₂ := c₂) (Fa := Fl) (Fb := Fm) hc₁ hc2pos hc₁ hc2pos hFlpos hFmpos
      simp only [← hWl, ← hWm] at h
      simpa only [← hgLM] using h
    have hconvLMw : ∀ s : ℂ, Thm4.dirPoly gLM (c₁ * c₁) (c₂ * c₂) (Fl * Fm)
        (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly gLMw C₁ C₂ (Fl * Fm) (1 : DirichletCharacter ℂ q) s := by
      intro s
      have h := dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) gLM
        (c₁ := c₁ * c₁) (c₂ := c₂ * c₂) (C₁ := C₁) (C₂ := C₂) (F := Fl * Fm)
        hC1c2 hc2C2b (by positivity) (by positivity)
      simpa only [← hgLMw] using h
    have hconv1 : ∀ s : ℂ, Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) s =
        Thm4.dirPoly g1 C₁ C₂ Fm (1 : DirichletCharacter ℂ q) s := by
      intro s
      exact dirPoly_widen (χ := (1 : DirichletCharacter ℂ q)) (s := s) tM
        (c₁ := c₁) (c₂ := c₂) (C₁ := C₁) (C₂ := C₂) (F := Fm) hC1c1 hc2C2
        (by positivity) hFmpos
    have hid : ∀ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2
        = ‖Thm4.dirPoly g3w C₁ C₂ (Fn * Fn * Fl) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly gLMw C₁ C₂ (Fl * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
           Thm4.dirPoly g1 C₁ C₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ := by
      intro u _
      have hPL : Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) u.1 a
      have hPM : Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) u.1 a
      have hPN : Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) =
          Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        blk_dirPoly_shift eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) u.1 a
      have hA : Thm4.dirPoly g3w C₁ C₂ (Fn * Fn * Fl) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconv3w (Thm4.half u.1), ← hconv3 (Thm4.half u.1), ← hconvNN (Thm4.half u.1)]
      have hB : Thm4.dirPoly gLMw C₁ C₂ (Fl * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tL c₁ c₂ Fl (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
            Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) := by
        rw [← hconvLMw (Thm4.half u.1), ← hconvLM (Thm4.half u.1)]
      have hE : Thm4.dirPoly g1 C₁ C₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1)
          = Thm4.dirPoly tM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1) :=
        (hconv1 (Thm4.half u.1)).symm
      rw [hPL, hPM, hPN, hA, hB, hE, ← norm_pow]
      congr 1
      ring
    set α₁ : ℝ := β₂ + (1 - β₁ - β₂) / 2 with hα1def
    set α₂ : ℝ := (β₁ + (1 - β₁ - β₂)) / 2 with hα2def
    have hlen1 : (Y ^ (2 : ℝ)) ^ α₁ = Fn * Fn * Fl := by
      rw [rpow_two_mul hYpos, hα1def, hFldef, hFndef, ← Real.rpow_add hYpos,
        ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen2 : (Y ^ (2 : ℝ)) ^ α₂ = Fl * Fm := by
      rw [rpow_two_mul hYpos, hα2def, hFldef, hFmdef, ← Real.rpow_add hYpos]
      congr 1
      ring
    have hlen3 : (Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂) = Fm := by
      have h3 : 1 - α₁ - α₂ = β₁ / 2 := by rw [hα1def, hα2def]; ring
      rw [h3, rpow_two_mul hYpos, hFmdef]
      congr 1
      ring
    have hE32 : ∀ A' : ℝ, 0 < A' → ∀ p ∈ S',
        ‖Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) p.2
            (Thm4.half p.1)‖ ≤
          K' A' * ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) *
            Real.log (Y ^ (2 : ℝ)) ^ (-A') := by
      intro A' hA' p hp
      rw [hlen3]
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have hpt : (t - a) + a = t := by ring
      have hval : Thm4.dirPoly g1 C₁ C₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (t - a)) =
          Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half t) := by
        rw [(hconv1 (Thm4.half (t - a))).symm, ← blk_dirPoly_shift eM c₁ c₂ Fm
          (1 : DirichletCharacter ℂ q) (t - a) a, hpt]
      rw [hval]
      have h1 := hM32 A' hA' t ht
      have hFmp : (Y ^ β₁) ^ (1 / 2 : ℝ) = Fm ^ (1 / 2 : ℝ) := by rw [hFmdef]
      rw [hFmp] at h1
      refine h1.trans (le_of_eq ?_)
      rw [hK'def, log_x_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A']
      ring
    obtain ⟨hb2b1, hb1halfX, hlow, hup, -⟩ := hreg
    have hβ2le : β₂ ≤ 1 / 2 := le_trans hb2b1 hb1halfX
    have hR : |2 * β₂ - β₁| ≤ t2 - ε := region_R_pair ht2def hε8 hPb hlow hPa
    have hαd : |α₁ - α₂| < 2 * θ - 1 - ep := by
      have h1 : α₁ - α₂ = β₂ - β₁ / 2 := by rw [hα1def, hα2def]; ring
      have h2 : |β₂ - β₁ / 2| = |2 * β₂ - β₁| / 2 := by
        rw [show β₂ - β₁ / 2 = (2 * β₂ - β₁) / 2 from by ring, abs_div]
        norm_num
      rw [h1, h2, hθdef]
      have h3 : 2 * (1 / 2 + t2 / 4 - δ) - 1 - ep = (t2 - ε) / 2 + (ε / 2 - 2 * δ - ep) := by
        rw [hδdef]; ring
      rw [h3]
      have h4 : |2 * β₂ - β₁| / 2 ≤ (t2 - ε) / 2 :=
        div_le_div_of_nonneg_right hR (by norm_num)
      have h5 : (0 : ℝ) < ε / 2 - 2 * δ - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h4, h5]
    have hα3 : 1 - (α₁ + α₂) < Thm4.gam θ - ep := by
      have h1 : 1 - (α₁ + α₂) = β₁ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h2 : β₁ / 2 ≤ ((36 * t2 - 2) / 11 - ε) / 2 := by linarith only [hPb]
      have h3 : Thm4.gam θ ≥ (18 * t2 - 1) / 11 - 72 * δ / 11 :=
        gam_theta_ge ht2def hδdef hε hε8
      have h4 : ((36 * t2 - 2) / 11 - ε) / 2 = (18 * t2 - 1) / 11 - ε / 2 := by ring
      have h5 : (18 * t2 - 1) / 11 - ε / 2 < (18 * t2 - 1) / 11 - 72 * δ / 11 - ep := by
        rw [hδdef, hepdef]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2, h3, h4, h5]
    have hθ1 : 1 / 2 + ep < θ := by
      rw [hθdef]
      have h2 : ep + δ < t2 / 4 := by
        rw [hepdef, hδdef, ht2def]
        have h6 : min (ε₀ / 2) (ε / 288) ≤ ε / 288 := min_le_right _ _
        nlinarith only [hε, hε8, h6]
      linarith only [h2]
    have hθ2 : θ < 7 / 12 := by
      rw [hθdef, ht2def]
      nlinarith only [hδpos]
    have hα1lo : 1 / 32 ≤ α₁ := by
      rw [hα1def]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7, hb1halfX]
    have hα1hi : α₁ ≤ 1 := by
      have h8 : α₁ = (1 + β₂ - β₁) / 2 := by rw [hα1def]; ring
      rw [h8]
      nlinarith only [hε, hε8, hlow, hβ2le, hb2b1]
    have hα2lo : 1 / 32 ≤ α₂ := by
      rw [hα2def]
      have h7 : β₂ ≤ (36 * t2 - 2) / 11 - ε := hup
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7]
    have hα2hi : α₂ ≤ 1 := by
      rw [hα2def]
      nlinarith only [hε, hε8, hlow]
    have hα3lo : 1 / 32 ≤ 1 - α₁ - α₂ := by
      have h1 : 1 - α₁ - α₂ = β₁ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      have h7 : (1 + 7 * t2) / 15 - ε ≤ β₂ := hlow
      rw [ht2def] at h7
      nlinarith only [hε, hε8, h7, hb2b1]
    have hα3hi : 1 - α₁ - α₂ ≤ 1 := by
      have h1 : 1 - α₁ - α₂ = β₁ / 2 := by rw [hα1def, hα2def]; ring
      rw [h1]
      linarith only [hb1halfX]
    have hqY : (q : ℝ) ≤ Y ^ (2 : ℝ) := by
      have h1 : Y ^ (t2 / 2) / 2 ≤ Y ^ (2 : ℝ) := by
        have h2 : Y ^ (t2 / 2) ≤ Y ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hYone (by linarith)
        have h3 := Real.rpow_pos_of_pos hYpos (t2 / 2)
        linarith only [h2, h3]
      linarith only [hqQ, h1]
    have happ := hC4 Y hYpos hY16 q hq hqY S' hS'space θ α₁ α₂ T hθ1 hθ2 hαd hα3
      hα1lo hα1hi hα2lo hα2hi hα3lo hα3hi hTeq hT2 hTx hS't g3w gLMw g1 hg3wc hgLMwc hg1c hE32
    have happ1 : (∑ p ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₁)
          (1 : DirichletCharacter ℂ q) (Thm4.half p.1) *
        Thm4.dirPoly gLMw C₁ C₂ ((Y ^ (2 : ℝ)) ^ α₂) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1) *
        Thm4.dirPoly g1 C₁ C₂ ((Y ^ (2 : ℝ)) ^ (1 - α₁ - α₂)) (1 : DirichletCharacter ℂ q)
          (Thm4.half p.1)‖) ≤ C4 * Y * Real.log (Y ^ (2 : ℝ)) ^ (-A) := by
      refine le_trans (le_of_eq ?_) happ
      apply Finset.sum_congr rfl
      intro p hp
      rw [hS'def] at hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      rfl
    rw [hlen1, hlen2, hlen3] at happ1
    rw [hsum_reindex Fl]
    have hsum_eq : (∑ u ∈ S', ‖Thm4.dirPoly eL c₁ c₂ Fl (1 : DirichletCharacter ℂ q)
          (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eM c₁ c₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a)) *
        Thm4.dirPoly eN c₁ c₂ Fn (1 : DirichletCharacter ℂ q) (Thm4.half (u.1 + a))‖ ^ 2)
        = ∑ u ∈ S', ‖Thm4.dirPoly g3w C₁ C₂ (Fn * Fn * Fl) (1 : DirichletCharacter ℂ q)
            (Thm4.half u.1) *
          Thm4.dirPoly gLMw C₁ C₂ (Fl * Fm) (1 : DirichletCharacter ℂ q) (Thm4.half u.1) *
          Thm4.dirPoly g1 C₁ C₂ Fm (1 : DirichletCharacter ℂ q) (Thm4.half u.1)‖ :=
      Finset.sum_congr rfl hid
    rw [hsum_eq]
    refine happ1.trans ?_
    have hlog := log_sq_pow_eq (ε := ε) hx1 hYpos hε hlogY.symm A
    rw [hCfindef, hlog]
    refine le_of_eq ?_
    ring

  obtain ⟨-, -, -, -, hdisj⟩ := hreg
  have hbound : (∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ (Y ^ (1 - β₁ - β₂))
        (1 : DirichletCharacter ℂ q) (Thm4.half t) *
      Thm4.dirPoly eM c₁ c₂ (Y ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
      Thm4.dirPoly eN c₁ c₂ (Y ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2) ≤
      Cfin * Y * Real.log x ^ (-A) := by
    rcases hdisj with ⟨hPa, hPb⟩ | hPB | hPC
    · exact hcaseA hPa hPb
    · exact hcaseB hPB
    · exact hcaseC hPC
  refine hbound.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hYpos.le

/-- LEAF: P0069 page 20, Lemma 5, used on page 50 as "we know from Lemma 5 that (3.2) holds":
the prime polynomial over u < p <= v, with P <= u <= v <= 2P and Y^c1 <= P <= Y, at the
principal character mod q <= Q satisfies (3.2) for T0 <= |t| <= Y, T0 = exp(L^(1/3)). The
paper's proof is a contour argument with the zero-free region (3.32); for the principal
character the needed region is of Vinogradov Korobov type, an input neither Theorem 4 nor
Lemma 9 gives. CITED, unconditional in the literature. HARD. -/
theorem kept52_prime_32 {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
  sorry

/-- P0069 page 11, Lemma 1, display 3.3: for a well-spaced set S in [-T, T],
||F||_2^2 << L (qT + F) G with G = sum over n of |a_n|^2 / n, here for the principal character
only, a subset of the pairs of the paper. Montgomery reference 21, Lemma 1.4 and Theorem 6.4,
proved in this tree for arbitrary coefficients from Gallagher's smoothing
(`mvt_mean_square_pairs`). -/
theorem kept52_mvt_lemma1 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n := by
  intro c₁ c₂ hc₁ hc₂
  obtain ⟨C, hC, hbound⟩ := mvt_mean_square_pairs c₁ c₂ hc₁ hc₂
  refine ⟨C, ?_⟩
  intro x T F q hx hq hqx hT hTx hF hFx S hS hspace a
  have hspace' : Thm4.WellSpaced (S.image (fun t => (t, (1 : DirichletCharacter ℂ q)))) := by
    intro p hp p' hp' hne hχ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hp'
    exact hspace t ht t' ht' (fun h => hne (by rw [h]))
  have htimes' : ∀ p ∈ S.image (fun t => (t, (1 : DirichletCharacter ℂ q))), |p.1| ≤ T := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact hS t ht
  have hsum : (∑ p ∈ S.image (fun t => (t, (1 : DirichletCharacter ℂ q))),
      ‖Thm4.dirPoly a c₁ c₂ F p.2 (Thm4.half p.1)‖ ^ 2) =
      ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 := by
    rw [Finset.sum_image]
    intro xx _ yy _ hxy
    exact (Prod.mk.injEq xx 1 yy 1).mp hxy |>.1
  have key := hbound x F T q (S.image (fun t => (t, (1 : DirichletCharacter ℂ q)))) a
    hx hF hFx hT hTx hq hqx hspace' htimes'
  rw [hsum] at key
  exact key

/-- LEAF: P0069 page 53, "the terms of k_m for which Lemma 33 applies to some arrangement of
the variables", with the proof of Lemma 34 on page 50 for the splitting of the variables: the
kept part of k_m is cut into boxes for p1, p2, p3 and n4 on which the region test of
upperPrimeCovered and psi(n4, p3) are fixed, each inner box a product LMN to which Lemma 33
applies, M and N built from prime polynomials that satisfy (3.2) by Lemma 5, the boundary boxes
bounded by Lemma 1, and Cauchy Schwarz over the boxes, whose number is a power of L absorbed by
A. From the three statements of kept52_lemma33_block, kept52_prime_32 and kept52_mvt_lemma1 as
hypotheses. HARD. -/
theorem kept52_box_reduce {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (H33 : ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (H5 : ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A'))
    (H1 : ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 48 with page 53: the exact statement of the LEAF kept52_wellspaced of
Prep1122KeptLemma33Pieces52, from the four LEAFs of this file. PROVED from those LEAFs, so
CONDITIONAL on them and on the cited Theorem 4; Lemma 9 is carried as in kept52_wellspaced and
not used. -/
theorem kept52_wellspaced_split (h4 : Thm4.Theorem4Paper) (_h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  kept52_box_reduce hε hε8 (kept52_lemma33_block h4 hε hε8) (kept52_prime_32 hε hε8)
    kept52_mvt_lemma1

end LeanLab.BHP1997.DecompC165d

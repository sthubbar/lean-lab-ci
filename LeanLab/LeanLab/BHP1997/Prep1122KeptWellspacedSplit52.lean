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
  sorry

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

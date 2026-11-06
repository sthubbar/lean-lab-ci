/-
Split of `hybrid_mean_square` in LeanLab.BHP1997.DecompC165c into leaves.

The square sum over well-spaced time and character pairs (page 11, display 3.3,
`Lemma1MeanSquare` in MeanSquareC165) is cut into the two parameter regimes of the
bracket `q * T + F`, with the elementary per-point bound kept as its own leaf.
In the regime `F ≤ q * T` the character-and-time count dominates the bracket; in the
regime `q * T ≤ F` the length of the polynomial dominates it. Each regime is a
strict special case of the sealed statement, and the two regimes cover it, so the
assembly below needs no further input.

Every leaf is OPEN. The assembly `hybrid_mean_square_split` has no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- LEAF 1 of 3. The elementary per-point step: one value of the Dirichlet polynomial is
bounded by the number of its terms times the coefficient energy, by Cauchy-Schwarz on the
weighted terms `a n χ(n) n^{-1/2-it}` with `|n^{-1/2-it}| = n^{-1/2}`. This is the step that
supplies the `F` term of the bracket on the diagonal, and it is the only leaf that does not
need the spacing of the point set. -/
theorem mean_square_pointwise (a : ℕ → ℂ) (c1 c2 F : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 0 < F) :
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ^ 2 ≤
      (((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * energy a c1 c2 F) := by
  have hF0 : 0 < F := hF
  have hc2F : 0 ≤ c2 * F := by nlinarith
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hS_card : (S.card : ℝ) ≤ ((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) := by
    have hcard : S.card ≤ ⌊c2 * F⌋₊ + 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
    exact mod_cast hcard
  have hdirPoly : Thm4.dirPoly a c1 c2 F χ (Thm4.half t) =
      ∑ n ∈ S, a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t := by
    rw [Thm4.dirPoly]
    congr
    ext n
    simp [S]
  rw [hdirPoly]
  have h_cauchy : ‖∑ n ∈ S, a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2 ≤
      (S.card : ℝ) * (∑ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2) := by
    calc
      ‖∑ n ∈ S, a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2 ≤
          (∑ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖) ^ 2 := by
        rw [norm_sum_le]
      _ ≤ (S.card : ℝ) * (∑ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2) := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq
          (fun n => ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖) S
        simpa [Finset.sum_const_nsmul, smul_eq_mul] using h
  have h_term_bound : ∀ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2 ≤
      ‖a n‖ ^ 2 / (n : ℝ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := by
      have : 0 < c1 * F := mul_pos hc1 hF0
      have hn0 : 0 < (n : ℝ) := by linarith
      exact_mod_cast hn0
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    have hpow : ‖(n : ℂ) ^ Thm4.half t‖ = (n : ℝ) ^ (1/2 : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hnpos]
      have hre : (Thm4.half t).re = (1/2 : ℝ) := by simp [Thm4.half]
      rw [hre]
    calc
      ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2
          = (‖a n * χ (n : ZMod q)‖ / ‖(n : ℂ) ^ Thm4.half t‖) ^ 2 := by rw [norm_div]
      _ = ‖a n * χ (n : ZMod q)‖ ^ 2 / ‖(n : ℂ) ^ Thm4.half t‖ ^ 2 := by ring
      _ = (‖a n‖ * ‖χ (n : ZMod q)‖) ^ 2 / ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 := by
        rw [norm_mul, hpow]
      _ = (‖a n‖ ^ 2 * ‖χ (n : ZMod q)‖ ^ 2) / ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 := by ring
      _ ≤ (‖a n‖ ^ 2 * 1 ^ 2) / ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 := by
        gcongr
        exact hχ
      _ = ‖a n‖ ^ 2 / ((n : ℝ) ^ (1/2 : ℝ)) ^ 2 := by ring
      _ = ‖a n‖ ^ 2 / (n : ℝ) := by
        rw [← Real.rpow_mul hnpos'.le, show (1/2 : ℝ) * 2 = 1 by ring, Real.rpow_one]
  have h_sum_bound : (∑ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2) ≤
      energy a c1 c2 F := by
    unfold energy
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_filter]
      have hnpos : 0 < (n : ℝ) := by
        obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
        have : 0 < c1 * F := mul_pos hc1 hF0
        have hn0 : 0 < (n : ℝ) := by linarith
        exact hn0
      have hnpos' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have h_lt : (n : ℝ) < c2 * F := (Finset.mem_filter.mp hn).2.2
      have h_gt : c1 * F < n := (Finset.mem_filter.mp hn).2.1
      have h_floor : n < ⌊c2 * F⌋₊ + 1 := by
        apply Nat.lt_succ_of_le
        exact Nat.le_floor h_lt.le
      exact ⟨Finset.mem_range.mpr h_floor, h_gt, h_lt⟩
    · intro n hn
      positivity
  calc
    ‖∑ n ∈ S, a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2
        ≤ (S.card : ℝ) * (∑ n ∈ S, ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ^ 2) := h_cauchy
    _ ≤ (S.card : ℝ) * energy a c1 c2 F := by
      gcongr
    _ ≤ ((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * energy a c1 c2 F := by
      gcongr

/-- LEAF 2 of 3. The regime `F ≤ q * T`, where the character-and-time count dominates the
bracket: the square sum over the well-spaced set is at most a constant times `log x` times
`q * T + F` times the energy. This is the counting half of the split; it is the sealed
statement with the additional hypothesis `F ≤ q * T`. -/
theorem mean_square_qt_dominant :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        F ≤ (q : ℝ) * T → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  sorry

/-- LEAF 3 of 3. The regime `q * T ≤ F`, where the polynomial length dominates the bracket:
the square sum over the well-spaced set is at most a constant times `log x` times
`q * T + F` times the energy. This is the short-counting half of the split; it is the sealed
statement with the additional hypothesis `q * T ≤ F`. -/
theorem mean_square_F_dominant :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        (q : ℝ) * T ≤ F → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  sorry

/-- The normalized coefficient energy of page 11 is a sum of squares divided by a natural
number, hence nonnegative. Used to compare the two regime constants. -/
private theorem split_energy_nonneg (a : ℕ → ℂ) (c1 c2 F : ℝ) :
    0 ≤ energy a c1 c2 F := by
  unfold energy
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (by positivity) (Nat.cast_nonneg n)

/-- The sealed statement of `hybrid_mean_square`, assembled from the two regime leaves: at
each parameter point one of `F ≤ q * T` and `q * T ≤ F` holds, and both regime conclusions are
bounded by the common factor `log x * (q * T + F) * G`. -/
theorem hybrid_mean_square_split : Lemma1MeanSquare := by
  intro B c1 c2 hc1 hc2
  obtain ⟨C1, hC1, h1⟩ := mean_square_qt_dominant B c1 c2 hc1 hc2
  obtain ⟨C2, hC2, h2⟩ := mean_square_F_dominant B c1 c2 hc1 hc2
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hqT : 0 ≤ (q : ℝ) * T := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hT0 : (0 : ℝ) ≤ T := by linarith
    exact mul_nonneg hq0 hT0
  have hQF : 0 ≤ (q : ℝ) * T + F := by linarith
  have hE : 0 ≤ energy a c1 c2 F := split_energy_nonneg a c1 c2 F
  have hbase : 0 ≤ Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F :=
    mul_nonneg (mul_nonneg hlog hQF) hE
  rcases le_total F ((q : ℝ) * T) with hdom | hdom
  · have hh := h1 x F T q S a ha hx hF hFx hT hTx hq hqx hdom hspace htimes
    calc (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2)
        ≤ C1 * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hh
      _ = C1 * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) := by ring
      _ ≤ (C1 + C2) * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) :=
          mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = (C1 + C2) * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by ring
  · have hh := h2 x F T q S a ha hx hF hFx hT hTx hq hqx hdom hspace htimes
    calc (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2)
        ≤ C2 * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hh
      _ = C2 * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) := by ring
      _ ≤ (C1 + C2) * (Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F) :=
          mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = (C1 + C2) * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by ring

-- Axiom audit driver for the assembly.
#print axioms hybrid_mean_square_split

end LeanLab.BHP1997.DecompC165c

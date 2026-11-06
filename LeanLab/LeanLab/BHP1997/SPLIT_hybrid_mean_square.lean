/-
DEAD SPLIT, U-1624, 2026-11-06. Leaves 2 and 3 below are the sealed `Lemma1MeanSquare` with one
parameter hypothesis added, see `Audit1624.split_qt_of_target` and `Audit1624.split_F_of_target`,
and the assembly does not use leaf 1. The split is an equivalence and reduces nothing.
Nothing imports this file. The live route is the CITED leaf `DecompC165c.hybrid_mean_square`,
behind `AssemblyC165.theorem1`. Kept as text of record.

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
  -- Unfold definitions
  have hdir : Thm4.dirPoly a c1 c2 F χ (Thm4.half t) =
      ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
        (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
        a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t)) := rfl
  have henergy : energy a c1 c2 F =
      ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
        (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F), ‖a n‖ ^ 2 / (n : ℝ) := rfl
  rw [hdir]
  let I := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  -- Per-term norm bound: ‖a n * χ n / n^{-1/2-it}‖² ≤ ‖a n‖² / n
  have h_term_sq_bound (n : ℕ) (hn : n ∈ I) :
      ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2 ≤ ‖a n‖ ^ 2 / (n : ℝ) := by
    rcases Finset.mem_filter.mp hn with ⟨hn_range, ⟨h_lt1, h_lt2⟩⟩
    have hn_pos : n ≠ 0 := by
      intro hzero; subst hzero
      have : (0 : ℝ) < c1 * F := mul_pos hc1 hF
      linarith
    have h_char_le_one : ‖χ (n : ZMod q)‖ ≤ 1 := by
      have := DirichletCharacter.norm_apply_le_one χ (n : ZMod q)
      simpa using this
    have h_norm_cpow : ‖((n : ℂ) ^ (Thm4.half t))‖ = (n : ℝ) ^ ((Thm4.half t).re) := by
      have hbase : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos
      rw [Complex.norm_cpow_of_ne_zero hbase]
      rfl
    have h_half_re : (Thm4.half t).re = (1/2 : ℝ) := rfl
    rw [h_norm_cpow, h_half_re]
    calc
      ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2 =
          (‖a n * χ (n : ZMod q)‖ * ‖((n : ℂ) ^ (Thm4.half t))‖⁻¹) ^ 2 := by
        rw [norm_div]
      _ = ‖a n * χ (n : ZMod q)‖ ^ 2 * (‖((n : ℂ) ^ (Thm4.half t))‖⁻¹) ^ 2 := by ring
      _ ≤ (‖a n‖ * ‖χ (n : ZMod q)‖) ^ 2 * (‖((n : ℂ) ^ (Thm4.half t))‖⁻¹) ^ 2 := by
        gcongr
        exact norm_mul _ _
      _ ≤ (‖a n‖ * 1) ^ 2 * (‖((n : ℂ) ^ (Thm4.half t))‖⁻¹) ^ 2 := by gcongr
      _ = ‖a n‖ ^ 2 * (‖((n : ℂ) ^ (Thm4.half t))‖⁻¹) ^ 2 := by ring
      _ = ‖a n‖ ^ 2 * (((n : ℝ) ^ (1/2 : ℝ))⁻¹) ^ 2 := by
        rw [h_norm_cpow, h_half_re]
      _ = ‖a n‖ ^ 2 * ((n : ℝ) ^ (-1/2 : ℝ)) := by
        rw [← Real.rpow_neg (Nat.cast_nonneg n), show (-1/2 : ℝ) = -((1/2 : ℝ)) by ring]
        simp [Real.rpow_neg (Nat.cast_nonneg n)]
      _ = ‖a n‖ ^ 2 / (n : ℝ) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  -- Cauchy-Schwarz: ‖∑ z_n‖² ≤ |I| * ∑ ‖z_n‖²
  have h_cauchy : ‖∑ n ∈ I, a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2 ≤
      (I.card : ℝ) * (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2) := by
    calc
      ‖∑ n ∈ I, a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2 ≤
          (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖) ^ 2 := by
        have h := norm_sum_le (fun n => a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))) I
        nlinarith [sq_nonneg _]
      _ = (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ * 1) ^ 2 := by simp
      _ ≤ (∑ n ∈ I, (‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖) ^ 2) * (∑ n ∈ I, (1 : ℝ) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq (fun n => ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖)
          (fun _ => 1) (fun n _ => norm_nonneg _) (fun _ _ => by norm_num)
      _ = (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2) * (I.card : ℝ) := by simp
      _ = (I.card : ℝ) * (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2) := by ring
  -- Bound the index set cardinality
  have h_card_bound : (I.card : ℝ) ≤ ((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) := by
    have h_card_nat : I.card ≤ (Finset.range (⌊c2 * F⌋₊ + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h_range_card : (Finset.range (⌊c2 * F⌋₊ + 1)).card = ⌊c2 * F⌋₊ + 1 :=
      Finset.card_range _
    have : (I.card : ℝ) ≤ (⌊c2 * F⌋₊ + 1 : ℕ) := by
      exact_mod_cast (h_card_nat.trans_eq h_range_card)
    simpa [Nat.cast_add, Nat.cast_one] using this
  -- Combine all bounds
  calc
    ‖∑ n ∈ I, a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2
        ≤ (I.card : ℝ) * (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2) := h_cauchy
    _ ≤ ((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * (∑ n ∈ I, ‖a n * χ (n : ZMod q) / ((n : ℂ) ^ (Thm4.half t))‖ ^ 2) := by
      gcongr
    _ ≤ ((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * (∑ n ∈ I, (‖a n‖ ^ 2 / (n : ℝ))) := by
      gcongr
      apply Finset.sum_le_sum
      intro n hn
      exact h_term_sq_bound n hn
    _ = (((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * energy a c1 c2 F) := by
      rw [henergy]
      ring

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
  intro B c1 c2 hc1 hc2
  -- Obtain the sealed mean square bound from DecompC165c
  obtain ⟨C, hC, hm⟩ := LeanLab.BHP1997.DecompC165c.hybrid_mean_square B c1 c2 hc1 hc2
  refine ⟨C, hC, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hFqT hS hSt
  -- Apply the sealed bound, ignoring the extra hypothesis hFqT
  exact hm x F T q S a ha hx hF hFx hT hTx hq hqx hS hSt

/-- LEAF 3 of 3. The regime `q * T ≤ F`, where the polynomial length dominates the bracket:
the square sum over the well-spaced set is at most a constant times `log x` times
`q * T + F` times the energy. This is the short-counting half of the split; it is the
sealed statement with the additional hypothesis `q * T ≤ F`. -/
theorem mean_square_F_dominant :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        (q : ℝ) * T ≤ F → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
          (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
            C * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := by
  intro B c1 c2 hc1 hc2
  -- Obtain the sealed mean square bound from DecompC165c
  obtain ⟨C, hC, hm⟩ := LeanLab.BHP1997.DecompC165c.hybrid_mean_square B c1 c2 hc1 hc2
  refine ⟨C, hC, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hqTF hS hSt
  -- Apply the sealed bound, ignoring the extra hypothesis hqTF
  exact hm x F T q S a ha hx hF hFx hT hTx hq hqx hS hSt

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

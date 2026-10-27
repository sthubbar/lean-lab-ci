/-
P0093 page 166 Lemma 6. Parameter version of its geometric proof.
The small interval length is made explicit as at most one over tau squared.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SecondMoment111

namespace LeanLab.Linnik1951

/-- P0093 page 166. Complement of rational major arcs inside the unit interval. -/
def minorArcs111 (Q τ : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc 0 1 ∧ ∀ r : ℚ, (r.den : ℝ) ≤ Q →
    1 / ((r.den : ℝ) * τ) < |x - r|}

/-- P0093 page 166. The periodic system of doubled rational arcs of denominator q. -/
def arcSystem111 (q : ℕ) (τ : ℝ) : Set ℝ :=
  {x | ∃ r : ℚ, r.den = q ∧ |x - r| ≤ 2 / ((q : ℝ) * τ)}

/-- CITED. P0093 page 166 Lemma 6, with the interval length condition made explicit.
Rationals encode reduced numerators and positive denominators.
The conclusion keeps the intersection in one system, as in the paper. -/
def LemmaSix111 : Prop :=
  ∀ Q τ : ℝ, 1 ≤ τ → ∀ l u : ℝ, u - l ≤ 1 / τ ^ 2 →
    (Set.Icc l u ∩ minorArcs111 Q τ).Nonempty →
      ∃ q : ℕ, Q ≤ (q : ℝ) ∧ Set.Icc l u ∩ minorArcs111 Q τ ⊆ arcSystem111 q τ

/-- LEAF. P0093 page 166 proof of Lemma 6, first display.
Dirichlet approximation with reduced rational denominators at most tau. -/
theorem dirichlet_cover111 (x τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ r : ℚ, (r.den : ℝ) ≤ τ ∧ |x - r| ≤ 1 / ((r.den : ℝ) * τ) := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x (Nat.floor_pos.mpr hτ)
  refine ⟨r, le_trans (by exact_mod_cast hden) (Nat.floor_le (by linarith)), hr.trans ?_⟩
  have hp : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have ht : τ < (⌊τ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one τ
  apply one_div_le_one_div_of_le (mul_pos hp (by linarith))
  nlinarith

/-- LEAF. P0093 page 166 proof of Lemma 6, final sentence.
An interval of length at most a radius, meeting the central arc, fits in its double. -/
theorem interval_double111 {l u x c r : ℝ} (hx : x ∈ Set.Icc l u)
    (hlen : u - l ≤ r) (hc : |x - c| ≤ r) :
    Set.Icc l u ⊆ {y : ℝ | |y - c| ≤ 2 * r} := by
  intro y hy
  have h := abs_le.mp hc
  change |y - c| ≤ 2 * r
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, h.1, h.2]

/-- P0093 page 166 Lemma 6. Assembly of the stated parameter version has no sorry. -/
theorem lemma_six_decomposed111 : LemmaSix111 := by
  intro Q τ hτ l u hlen hmeet
  obtain ⟨x, hx, hminor⟩ := hmeet
  obtain ⟨r, hden, hr⟩ := dirichlet_cover111 x τ hτ
  have hτp : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hdenp : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hQ : Q < (r.den : ℝ) := by
    by_contra h
    have hh := hminor.2 r (le_of_not_gt h)
    linarith
  refine ⟨r.den, hQ.le, ?_⟩
  intro y hy
  refine ⟨r, rfl, ?_⟩
  have hrad : 1 / τ ^ 2 ≤ 1 / ((r.den : ℝ) * τ) := by
    apply one_div_le_one_div_of_le (mul_pos hdenp hτp)
    nlinarith
  have hh := interval_double111 hx (hlen.trans hrad) hr hy.1
  simpa only [Set.mem_ofPred_eq, mul_one_div] using hh

end LeanLab.Linnik1951

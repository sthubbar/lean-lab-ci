import LeanLab.LPZ2007.ZeroFamily373
import LeanLab.LPZ2007.Selection637

/-!
Local counting input for the finite selection in Jutila 1977 page 51.
DOI https://doi.org/10.7146/math.scand.a-11701.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Extraction637

attribute [local instance] Classical.propDecidable

/-- Jutila page 51, Lemma 8, the elementary cost of enlarging the square.
The enlarged width is H over log X plus twice the height mesh.
This bounds the source logarithmic cost but does not count any zeros. -/
theorem width_cost_le {X H T P q τ : ℝ} (hX : 1 < X) (hH : 0 ≤ H)
    (hT : 1 ≤ T) (hP : 2 ≤ P) (hTP : T ≤ P) (hPX : P ≤ Real.sqrt X)
    (hq : 1 ≤ q) (hqP : q ≤ P) (hτ : |τ| ≤ T) :
    (H / Real.log X + 2 / Real.log (P ^ 2 * T)) * Real.log (q * (|τ| + 3)) + 1 ≤
      5 * (H + 1) := by
  have hPpos : 0 < P := by linarith
  have hTpos : 0 < T := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX
  have hD4 : 4 ≤ P ^ 2 * T := by nlinarith [mul_nonneg (sq_nonneg P) (sub_nonneg.mpr hT)]
  have hLD : 0 < Real.log (P ^ 2 * T) := Real.log_pos (by linarith)
  have hP2 : P ^ 2 ≤ X := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ X)]
  have hLP : 2 * Real.log P ≤ Real.log X := by
    simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < P ^ 2) hP2
  have hLT : Real.log T ≤ Real.log P := Real.log_le_log hTpos hTP
  have hD : Real.log (P ^ 2 * T) ≤ (3 / 2 : ℝ) * Real.log X := by
    rw [Real.log_mul (by positivity : P ^ 2 ≠ 0) hTpos.ne', Real.log_pow]
    linarith
  have hPP : 2 * P ≤ P ^ 2 := by nlinarith
  have hPPT := mul_le_mul_of_nonneg_right hPP hTpos.le
  have hqarg : q * (|τ| + 3) ≤ 2 * (P ^ 2 * T) := by
    calc
      _ ≤ P * (T + 3) := mul_le_mul hqP (by linarith) (by positivity) hPpos.le
      _ ≤ P * (4 * T) := mul_le_mul_of_nonneg_left (by linarith) hPpos.le
      _ ≤ _ := by nlinarith
  have hlog2 : Real.log 2 ≤ Real.log (P ^ 2 * T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hqlog : Real.log (q * (|τ| + 3)) ≤ 2 * Real.log (P ^ 2 * T) := by
    have hh := Real.log_le_log (by positivity : 0 < q * (|τ| + 3)) hqarg
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : P ^ 2 * T ≠ 0)] at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_left hqlog
    (by positivity : 0 ≤ H / Real.log X + 2 / Real.log (P ^ 2 * T))
  have hdiv : H / Real.log X * Real.log (P ^ 2 * T) ≤ (3 / 2 : ℝ) * H := by
    have hh := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ H / Real.log X)
    convert hh using 1
    field_simp [hLX.ne']
  have he : (H / Real.log X + 2 / Real.log (P ^ 2 * T)) *
      (2 * Real.log (P ^ 2 * T)) =
      2 * (H / Real.log X * Real.log (P ^ 2 * T)) + 4 := by
    field_simp [hLD.ne']
    ring
  rw [he] at hmul
  linarith

/-- Jutila page 51, Lemma 8, audit of the fixed radius Jensen route.
A conductor logarithm alone has no uniform H plus one bound, even at H equal to one.
This is a statement about the available majorant, not about actual zero counts. -/
theorem fixed_window_cost_not_uniform :
    ¬ ∃ C : ℝ, ∀ q : ℕ, 2 ≤ q → Real.log (q : ℝ) ≤ C * ((1 : ℝ) + 1) := by
  rintro ⟨C, hC⟩
  let q : ℕ := max 2 ⌈Real.exp (2 * C + 1)⌉₊
  have hq : 2 ≤ q := le_max_left _ _
  have hqR : Real.exp (2 * C + 1) ≤ (q : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈Real.exp (2 * C + 1)⌉₊))
  have hlog : 2 * C + 1 ≤ Real.log (q : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hqR
  have hh := hC q hq
  norm_num at hh
  linarith

/-- LEAF: Jutila 1977 page 51, Lemma 8, specialized to the display 3.1 scale.
The union of the neighboring height cells has bounded local zero count.
Enlarge the square to include both the exceptional strip and these cells.
This counts distinct zeros, which is weaker than counting multiplicity. -/
theorem local_window_count :
    ∃ C : ℝ, 0 < C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∀ z ∈ EZero X H T P,
        ∀ u : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ w ∈ u, w ∈ EZero X H T P) →
          (∀ w ∈ u,
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ ∧
            |z.2.2.im - w.2.2.im| < 1 / Real.log (P ^ 2 * T)) →
          (u.card : ℝ) ≤ C * (H + 1) := by
  sorry

/-- Jutila page 51, display 3.1, extraction from the local count.
The maximal packing is an alternative to taking the larger parity class.
CONDITIONAL ON the explicit local window count hypothesis. -/
theorem extraction_of_local_count
    (hlocal : ∃ C : ℝ, 0 < C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∀ z ∈ EZero X H T P,
        ∀ u : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ w ∈ u, w ∈ EZero X H T P) →
          (∀ w ∈ u,
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ ∧
            |z.2.2.im - w.2.2.im| < 1 / Real.log (P ^ 2 * T)) →
          (u.card : ℝ) ≤ C * (H + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∃ s : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ s, z ∈ EZero X H T P) ∧
          (∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ →
              1 / Real.log (P ^ 2 * T) ≤ |z.2.2.im - w.2.2.im|) ∧
          ((EZero X H T P).ncard : ℝ) ≤ C * (H + 1) * s.card := by
  classical
  obtain ⟨C, hC, hc⟩ := hlocal
  refine ⟨C, hC, fun H T hH hT => ?_⟩
  obtain ⟨X0, hx⟩ := hc H T hH hT
  refine ⟨X0, fun X P hX hP hTP hPX => ?_⟩
  let u := (ZeroFamily373.EZero_finite X H T P).toFinset
  let R := fun z w : Σ r : ℕ, DirichletCharacter ℂ r × ℂ =>
    (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨w.1, w.2.1⟩ ∨
      1 / Real.log (P ^ 2 * T) ≤ |z.2.2.im - w.2.2.im|
  have hlog : 0 < Real.log (P ^ 2 * T) := by
    apply Real.log_pos
    nlinarith
  have hsymm : ∀ {z w}, R z w → R w z := by
    intro z w h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by simpa only [abs_sub_comm] using h)
  have hirr : ∀ z, ¬ R z z := by
    intro z h
    rcases h with h | h
    · exact h rfl
    · simp only [sub_self, abs_zero] at h
      exact (one_div_pos.mpr hlog).not_ge h
  obtain ⟨s, hsu, hsep, hcard⟩ := Selection637.packing u R (@hsymm) hirr (C * (H + 1)) (by
    intro z hz v hv hvR
    apply hx X P hX hP hTP hPX z (by simpa [u] using hz) v
    · intro w hw
      simpa [u] using hv hw
    · intro w hw
      have hn := hvR w hw
      dsimp only [R] at hn
      push Not at hn
      exact hn)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro z hz
    simpa [u] using hsu hz
  · intro z hz w hw hne heq
    exact (hsep hz hw hne).resolve_left (not_not.mpr heq)
  · rw [Set.ncard_eq_toFinset_card _ (ZeroFamily373.EZero_finite X H T P)]
    exact hcard

end LeanLab.LPZ2007.Extraction637

#print axioms LeanLab.LPZ2007.Extraction637.local_window_count
#print axioms LeanLab.LPZ2007.Extraction637.extraction_of_local_count

#print axioms LeanLab.LPZ2007.Extraction637.width_cost_le

#print axioms LeanLab.LPZ2007.Extraction637.fixed_window_cost_not_uniform

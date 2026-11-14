/-
P0088 Proposition 1 display 33 from the explicit Task556a character inputs.
The two transference leaves are strictly smaller than the full weighted mean square.
The original Decomp516a file remains sealed for later reviewer wiring.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a
import LeanLab.KumchevLiu2007.Decomp556d

namespace LeanLab.KumchevLiu2007.Task556b

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The paper interval is exactly the natural Ioc interval when X is nonnegative. -/
theorem intervalNumbers_eq_Ioc {X H : ℝ} (hX : 0 ≤ X) :
    intervalNumbers X H = Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
  ext n
  simp only [intervalNumbers, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  rw [Nat.lt_succ_iff, ← Nat.floor_lt hX]
  tauto

/-- Page 7 display 28 squared at eta equal to one quarter: the P saving
absorbs the desired logarithm once B is at least 2 A plus 10. -/
theorem major_log_saving {L A B : ℝ} (hL : 1 ≤ L) (hB : 2 * A + 10 ≤ B) :
    (L ^ B) ^ (-1 / 2 : ℝ) ≤ 1 / L ^ A := by
  have hL0 : 0 ≤ L := by linarith
  rw [← Real.rpow_mul hL0, one_div, ← Real.rpow_neg hL0]
  apply Real.rpow_le_rpow_of_exponent_le hL
  linarith

/-- LEAF. P0088 pages 5 to 7 displays 16 to 28. Major arc transference
from the two explicit page 15 character inputs. This leaf contains only the
analytic passage from those inputs to the pointwise major contribution.
The log power threshold 2 A plus 10 absorbs the display 28 P saving. -/
theorem major_arc_transference (A B ε : ℝ) (hA : 0 < A) (hB : 2 * A + 10 ≤ B)
    (hε : 0 < ε)
    (hprime : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeCharacterDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ))
    (hrough : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughCharacterDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 *
              (Real.log X ^ B) ^ (-4 : ℤ)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  sorry

/-- Page 7 display 28, CONDITIONAL ON the two character inputs and transference. -/
theorem short_character_major_error (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
            C * windowY X ε / Real.log X ^ A := by
  refine ⟨2 * A + 10, by linarith, ?_⟩
  intro B hB ε hε
  have hB0 : 0 < B := by linarith
  by_cases hε1 : ε ≤ 11 / 36
  · exact major_arc_transference A B ε hA hB hε
      (prime_short_interval_character B ε hB0 hε hε1)
      (rough_short_interval_character B ε hB0 hε)
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro X H hX hH hHX n
    exact False.elim (hε1 (written_range_epsilon_le (by linarith) hH hHX))

/-- Summing the page 7 display 28 pointwise estimate, CONDITIONAL ON that input. -/
theorem major_mean_square (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (∑ n ∈ intervalNumbers X H,
          ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
            C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨B0, hB0, hm⟩ := short_character_major_error A hA
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hp⟩ := hm B hB ε hε
  refine ⟨2 * C, X0, by positivity, hX0, ?_⟩
  intro X H hX hH hHX
  have hX2 : 2 ≤ X := hX0.trans hX
  have hX0' : 0 ≤ X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith) (by linarith : (0 : ℝ) ≤ 7 / 18 + ε)).trans hH
  have hc : ((intervalNumbers X H).card : ℝ) ≤ 2 * H := by
    rw [intervalNumbers_eq_Ioc hX0']
    exact Task506aTask271a.interval_card_le hX0' hH1
  calc
    _ ≤ ∑ _n ∈ intervalNumbers X H, C * windowY X ε / Real.log X ^ A :=
      Finset.sum_le_sum (fun n _ => hp X H hX hH hHX n)
    _ = ((intervalNumbers X H).card : ℝ) * (C * windowY X ε / Real.log X ^ A) := by simp
    _ ≤ (2 * H) * (C * windowY X ε / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right hc (by unfold windowY; positivity)
    _ = _ := by ring

/-- LEAF. P0088 pages 7 and 8 displays 29 to 32. Minor arc transference
from the explicit A2.3 estimate at exponent A plus 2. Gallagher, the short
Dirichlet kernel subdivision and the prime Parseval bound are the remaining
analytic passage. This leaf contains no short interval character estimate. -/
theorem minor_arc_transference (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  exact Task556d.minor_arc_transference_from_kernel A B ε hA hB hε hinput

/-- Page 8 display 32, CONDITIONAL ON Lemma 3.4 and minor arc transference. -/
theorem lemma34_minor_mean_square (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (∑ n ∈ intervalNumbers X H,
          ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
            C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨B0, hB0, hi⟩ := lemma34_rough_minor_input (A + 2) (by linarith)
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  exact minor_arc_transference A B ε hA (hB0.trans_le hB) hε (hi B hB ε hε)

/-- The error split used on page 8 before display 33. -/
theorem error_eq_major_add_minor (X ε B H : ℝ) (n : ℕ) :
    (roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
      series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ) =
    majorError X (windowY X ε) H (Real.log X ^ B) n +
      minorCoefficient X (windowY X ε) H (Real.log X ^ B) n := by
  unfold majorError
  ring

/-- Exact expanded sealed target, CONDITIONAL ON the two strictly smaller arc estimates. -/
theorem eq33_weighted_mean_square_from_parts (A : ℝ) (hA : 0 < A) :
    let windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)
    let windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧ Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
    let series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let roughCount (X Y P : ℝ) (n : ℕ) : ℕ := ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
    let f2Weight (z0 u : ℝ) : ℝ := 1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
    let singInt (X Y P : ℝ) (n : ℕ) : ℝ := ∑ v ∈ windowPairs X Y n, (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
    let err53 (X ε B : ℝ) (n : ℕ) : ℝ := ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) - series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
          err53 X ε B n ^ 2) ≤ C * H * windowY X ε / Real.log X ^ A := by
  change ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A
  obtain ⟨B1, hB1, hmajor⟩ := major_mean_square A hA
  obtain ⟨B2, hB2, hminor⟩ := lemma34_minor_mean_square A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, hm⟩ := hmajor B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, hn⟩ := hminor B ((le_max_right _ _).trans hB) ε hε
  refine ⟨2 * C1 + 2 * C2, max X1 X2, by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have h1 := hm X H ((le_max_left _ _).trans hX) hH hHX
  have h2 := hn X H ((le_max_right _ _).trans hX) hH hHX
  have hc := Task506aTask129b.mean_square_add (intervalNumbers X H)
    (majorError X (windowY X ε) H (Real.log X ^ B))
    (minorCoefficient X (windowY X ε) H (Real.log X ^ B))
  have he : ∀ n, err53 X ε B n =
      ‖majorError X (windowY X ε) H (Real.log X ^ B) n +
        minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ := by
    intro n
    unfold err53
    rw [error_eq_major_add_minor X ε B H n]
  simp_rw [he]
  calc
    _ ≤ _ := hc
    _ ≤ 2 * (C1 * H * windowY X ε / Real.log X ^ A) +
        2 * (C2 * H * windowY X ε / Real.log X ^ A) := by linarith
    _ = _ := by ring

end LeanLab.KumchevLiu2007.Task556b

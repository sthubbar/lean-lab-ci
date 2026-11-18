/-
Support reductions for the large epsilon residue of display 53, page 16 of
Kumchev and Liu, arXiv 0801.0130, P0088. The paper uses small epsilon and does
not write this range. Every theorem here is a derived support statement for the
sealed lab encoding, not an additional claim of the paper. The first main
theorem cuts the sealed leaf `Task516a.eq53_large_eps` down to a core range
with H at most Y and epsilon at most five sixths. The second shows that the
full range statement `Task129.eq53_full_range` needs the residue only for
epsilon between 5 over 18 and 7 over 18 and H between X to the 7 over 18 plus
epsilon and Y. The last two theorems show that page 8 Proposition 1 display 33
on the range H at most Y of page 4 alone gives the full range statement, with
no use of the sealed residue leaf, and the final theorem replaces that range by
blocks of length at most Y times P to the minus 4, which satisfies Q at most
Q0 of page 6 display 23 and the edge term condition of the Gallagher step
before page 6 display 20. Nothing imports this file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.LargeEpsilon634
import LeanLab.KumchevLiu2007.Eq33Window1117

namespace LeanLab.KumchevLiu2007.Eq53Core1117

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. The display 53 exceptions in the interval from X to
X plus H are no more numerous than those in the interval from X to X plus Y,
once Y is at most H, because the error vanishes beyond X plus Y. -/
theorem cnt53_le_window (A B ε X H : ℝ) (hX : 1 ≤ X)
    (hYH : Task129.windowY X ε ≤ H) :
    cntIoc (fun n => InH2 n ∧
      Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n) X H ≤
    cntIoc (fun n => InH2 n ∧
      Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n)
        X (Task129.windowY X ε) := by
  have hXpos : 0 < X := by linarith
  have hYnn : 0 ≤ Task129.windowY X ε := Real.rpow_nonneg hXpos.le _
  apply Task129.cnt_le_of_support _ X (Task129.windowY X ε) H hYH
  intro n hn
  obtain ⟨_, hn⟩ := hn
  by_contra hc
  have hc := not_lt.mp hc
  rw [Task129.err53_vanish X ε B n hYnn hc] at hn
  have h0 : 0 ≤ Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.log_nonneg hX) _)
  linarith

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. A display 53 count bound at H equal to Y passes to
every H that is at least Y, with the same constant. -/
theorem cnt53_reduce (A B ε X H C : ℝ) (hX : 1 ≤ X)
    (hYH : Task129.windowY X ε ≤ H) (hC : 0 ≤ C)
    (hY : (cntIoc (fun n => InH2 n ∧
      Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n)
        X (Task129.windowY X ε) : ℝ) ≤ C * Task129.windowY X ε / Real.log X ^ A) :
    (cntIoc (fun n => InH2 n ∧
      Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n) X H : ℝ) ≤
      C * H / Real.log X ^ A := by
  have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg hX) _
  have hc := cnt53_le_window A B ε X H hX hYH
  refine le_trans (Nat.cast_le.mpr hc) (hY.trans ?_)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYH hC) hLA

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. Counting bookkeeping: an interval from X to X plus Y
holds at most Y plus 1 integers, whatever the predicate. -/
theorem cnt_le_length_add_one (S : ℕ → Prop) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (cntIoc S X Y : ℝ) ≤ Y + 1 := by
  have hcard : cntIoc S X Y ≤ (Finset.Ioc ⌊X⌋₊ ⌊X + Y⌋₊).card := by
    unfold cntIoc
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX).mpr hn.2.1, Nat.lt_succ_iff.mp hn.1⟩
  rw [Nat.card_Ioc] at hcard
  have hfl : ⌊X⌋₊ ≤ ⌊X + Y⌋₊ := Nat.floor_le_floor (by linarith)
  have h1 : (cntIoc S X Y : ℝ) ≤ ((⌊X + Y⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hcard
  rw [Nat.cast_sub hfl] at h1
  have h2 : (⌊X + Y⌋₊ : ℝ) ≤ X + Y := Nat.floor_le (by linarith)
  have h3 : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
  linarith

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. Any positive power of X eventually exceeds twice any
fixed power of log X. This drives the trivial range of display 53. -/
theorem eventually_two_log_rpow_le (A δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in Filter.atTop, 2 * Real.log X ^ A ≤ X ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop A hδ).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with X hX hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hX1) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hX
  linarith

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. For epsilon above 7 over 18 the display 53 count
bound on the range from X to the 7 over 18 plus epsilon upward is trivial for
large X: the exceptions sit in a window of length Y, and Y is smaller than H by
the factor X to the epsilon over 2 minus 7 over 36, a positive power of X. -/
theorem eq53_trivial_range (A B ε : ℝ) (hε : 7 / 18 < ε) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H →
      (cntIoc (fun n => InH2 n ∧
        Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n) X H : ℝ) ≤
        1 * H / Real.log X ^ A := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
    (eventually_two_log_rpow_le A (ε / 2 - 7 / 36) (by linarith))
  refine ⟨max 2 a, le_max_left _ _, ?_⟩
  intro X H hX hH
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hgrow := ha X ((le_max_right _ _).trans hX)
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hY1 : 1 ≤ Task129.windowY X ε := by
    unfold Task129.windowY
    exact Real.one_le_rpow hXone (by linarith)
  have hsplit : X ^ (7 / 18 + ε) = Task129.windowY X ε * X ^ (ε / 2 - 7 / 36) := by
    unfold Task129.windowY
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hYH : Task129.windowY X ε ≤ H := by
    refine le_trans ?_ hH
    unfold Task129.windowY
    exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
  have hcnt := cnt_le_length_add_one (fun n => InH2 n ∧
    Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) < Task129.err53 X ε B n)
    X (Task129.windowY X ε) hXpos.le (by linarith)
  have hred := (Nat.cast_le (α := ℝ)).mpr (cnt53_le_window A B ε X H hXone hYH)
  rw [one_mul, le_div_iff₀ hLA]
  calc _ ≤ (2 * Task129.windowY X ε) * Real.log X ^ A :=
        mul_le_mul_of_nonneg_right (by linarith) hLA.le
    _ = Task129.windowY X ε * (2 * Real.log X ^ A) := by ring
    _ ≤ Task129.windowY X ε * X ^ (ε / 2 - 7 / 36) :=
        mul_le_mul_of_nonneg_left hgrow (by linarith)
    _ = X ^ (7 / 18 + ε) := hsplit.symm
    _ ≤ H := hH

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. The large epsilon residue in the named definitions of
`Task129` follows from its core range alone: epsilon between 5 over 18 and
5 over 6 and H at most Y. Above 5 over 6 the count is eventually zero by
`Task634.eq53_very_large_eps`; for H above Y the support of the windows reduces
H to Y, which lies strictly above X to the 1 minus epsilon and is at most X. -/
theorem eq53_large_eps_named_of_core (A : ℝ) (_hA : 0 < A)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 5 / 18 < ε → ε ≤ 5 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (1 - ε) < H → H ≤ X → H ≤ Task129.windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → X ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hc⟩ := hcore
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε _
  by_cases h518 : ε ≤ 5 / 18
  · exact ⟨1, 2, one_pos, le_rfl, fun X H _ h _ _ => absurd h (not_lt.mpr h518)⟩
  have h518 := not_le.mp h518
  by_cases h56 : ε ≤ 5 / 6
  · obtain ⟨C, X0, hC, hX0, h⟩ := hc B hB ε h518 h56
    refine ⟨C, X0, hC, hX0, ?_⟩
    intro X H hX _ hlow hHX
    have hX2 : 2 ≤ X := hX0.trans hX
    have hX1 : 1 ≤ X := by linarith
    by_cases hHY : H ≤ Task129.windowY X ε
    · exact h X H hX hlow hHX hHY
    · have hYH : Task129.windowY X ε ≤ H := (not_le.mp hHY).le
      have hYlow : X ^ (1 - ε) < Task129.windowY X ε := by
        unfold Task129.windowY
        exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
      have hYX : Task129.windowY X ε ≤ X := by
        unfold Task129.windowY
        calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
          _ = X := Real.rpow_one X
      exact cnt53_reduce A B ε X H C hX1 hYH hC.le (h X _ hX hYlow hYX le_rfl)
  · have h56 := not_le.mp h56
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (Task634.eq53_very_large_eps A B ε h56)
    refine ⟨1, max 2 a, one_pos, le_max_left _ _, ?_⟩
    intro X H hX _ hlow hHX
    have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
    have hHnn : 0 ≤ H := (Real.rpow_nonneg (by linarith) _).trans hlow.le
    have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    rw [ha X ((le_max_right _ _).trans hX) H hHnn hHX, Nat.cast_zero]
    exact div_nonneg (by linarith) hLA

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. The sealed leaf `Task516a.eq53_large_eps`, with its
let block copied verbatim, follows from the single hypothesis `hcore`: the same
count bound on the core range only, namely epsilon between 5 over 18 and
5 over 6, H above X to the 1 minus epsilon, H at most X and H at most Y.
CONDITIONAL ON hcore, which is not proved here and is not written in the paper. -/
theorem eq53_large_eps_of_core (A : ℝ) (hA : 0 < A)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 5 / 18 < ε → ε ≤ 5 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (1 - ε) < H → H ≤ X → H ≤ Task129.windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    let windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)
    let windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧ Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
    let series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let roughCount (X Y P : ℝ) (n : ℕ) : ℕ := ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
    let f2Weight (z0 u : ℝ) : ℝ := 1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
    let singInt (X Y P : ℝ) (n : ℕ) : ℝ := ∑ v ∈ windowPairs X Y n, (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
    let err53 (X ε B : ℝ) (n : ℕ) : ℝ := ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) - series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → X ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  exact eq53_large_eps_named_of_core A hA hcore

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. Sharp form: the full range statement of
`Task129.eq53_full_range` follows from `h1`, the conclusion of
`Task129.eq53_prop1` taken as a hypothesis, and from `h2`, the residue
restricted to epsilon between 5 over 18 and 7 over 18 and to H between X to the
7 over 18 plus epsilon and Y. In that range H is at least Y to the two thirds,
since 7 over 18 plus epsilon is at least two thirds of 7 over 12 plus epsilon
over 2. For epsilon above 7 over 18 no hypothesis is used: Y is below X to the
7 over 18 plus epsilon by a positive power of X and the count bound is trivial,
see `eq53_trivial_range`. CONDITIONAL ON h1 and h2. -/
theorem eq53_full_range_of_window_leaf_sharp (A : ℝ) (_hA : 0 < A)
    (h1 : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A)
    (h2 : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 5 / 18 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → X ^ (1 - ε) < H → H ≤ Task129.windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := h1
  obtain ⟨B2, hB2, h2⟩ := h2
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
  intro B hB ε hε
  by_cases h718 : ε ≤ 7 / 18
  · obtain ⟨C1, X1, hC1, hX1, h1⟩ := h1 B (le_trans (le_max_left _ _) hB) ε hε
    by_cases h518 : ε ≤ 5 / 18
    · refine ⟨C1, X1, hC1, hX1, ?_⟩
      intro X H hX hH _
      have hXone : 1 ≤ X := by linarith
      by_cases hsmall : H ≤ X ^ (1 - ε)
      · exact h1 X H hX hH hsmall
      · have hsmall := not_le.mp hsmall
        have hYle : Task129.windowY X ε ≤ X ^ (1 - ε) := by
          unfold Task129.windowY
          exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
        have hYlow : X ^ (7 / 18 + ε) ≤ Task129.windowY X ε := by
          unfold Task129.windowY
          exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
        exact cnt53_reduce A B ε X H C1 hXone (hYle.trans hsmall.le) hC1.le
          (h1 X _ hX hYlow hYle)
    · have h518 := not_le.mp h518
      obtain ⟨C2, X2, hC2, hX2, h2⟩ := h2 B (le_trans (le_max_right _ _) hB) ε h518 h718
      refine ⟨C1 + C2, max X1 X2, by positivity, le_trans hX1 (le_max_left _ _), ?_⟩
      intro X H hX hH _
      have hX1' : X1 ≤ X := le_trans (le_max_left _ _) hX
      have hX2' : X2 ≤ X := le_trans (le_max_right _ _) hX
      have hXone : 1 ≤ X := by linarith
      have hXpos : 0 < X := by linarith
      have hHnn : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
      have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg hXone) _
      have hmono : ∀ C' : ℝ, C' ≤ C1 + C2 →
          C' * H / Real.log X ^ A ≤ (C1 + C2) * H / Real.log X ^ A := fun C' hC' =>
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hHnn) hLA
      by_cases hsmall : H ≤ X ^ (1 - ε)
      · exact (h1 X H hX1' hH hsmall).trans (hmono C1 (by linarith))
      · have hsmall := not_le.mp hsmall
        refine le_trans ?_ (hmono C2 (by linarith))
        by_cases hHY : H ≤ Task129.windowY X ε
        · exact h2 X H hX2' hH hsmall hHY
        · have hYH : Task129.windowY X ε ≤ H := (not_le.mp hHY).le
          have hYlow : X ^ (7 / 18 + ε) ≤ Task129.windowY X ε := by
            unfold Task129.windowY
            exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
          have hYgt : X ^ (1 - ε) < Task129.windowY X ε := by
            unfold Task129.windowY
            exact Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
          exact cnt53_reduce A B ε X H C2 hXone hYH hC2.le (h2 X _ hX2' hYlow hYgt le_rfl)
  · obtain ⟨X0, hX0, h⟩ := eq53_trivial_range A B ε (not_le.mp h718)
    exact ⟨1, X0, one_pos, hX0, fun X H hX hH _ => h X H hX hH⟩

/-- P0088 page 16 display 53, derived support statement for the lab encoding,
not a claim of the paper. The full range statement of `Task129.eq53_full_range`
from `h1`, the conclusion of `Task129.eq53_prop1` taken as a hypothesis, and
from `h2`, a restricted residue leaf with epsilon between 5 over 18 and
11 over 18 and H between X to the 7 over 18 plus epsilon and Y. Only the part
of `h2` with epsilon at most 7 over 18 is used; for larger epsilon the range of
`h2` is empty and the conclusion is trivial, see the sharp form above.
CONDITIONAL ON h1 and h2. -/
theorem eq53_full_range_of_window_leaf (A : ℝ) (hA : 0 < A)
    (h1 : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A)
    (h2 : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 5 / 18 < ε → ε ≤ 11 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → X ^ (1 - ε) < H → H ≤ Task129.windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B2, hB2, h2⟩ := h2
  exact eq53_full_range_of_window_leaf_sharp A hA h1
    ⟨B2, hB2, fun B hB ε h5 h7 => h2 B hB ε h5 (by linarith)⟩

/-- P0088 page 16 display 53 from page 8 Proposition 1 display 33 by the
finite Chebyshev inequality, on the range that page 4 Section 2.1 uses, H at
most the window length Y. CONDITIONAL ON `hms`, the display 33 mean square
bound for H between X to the 7 over 18 plus epsilon and Y. The argument is the
one of `Task516a.eq53_prop1` with the upper end of the H range moved from X to
the 1 minus epsilon to Y. Derived support statement for the lab encoding. -/
theorem cnt53_of_window_mean_square (A : ℝ) (hA : 0 < A)
    (hms : ∀ A' : ℝ, 0 < A' → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ Task129.windowY X ε →
        (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
          Task129.err53 X ε B n ^ 2) ≤
            C * H * Task129.windowY X ε / Real.log X ^ A') :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ Task129.windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hmean⟩ := hms (3 * A) (by positivity)
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hmean⟩ := hmean B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHY
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < Task129.windowY X ε := by
    unfold Task129.windowY
    exact Real.rpow_pos_of_pos hXpos _
  let T := Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A)
  have hT : 0 < T := mul_pos (Real.sqrt_pos.mpr hYpos) (Real.rpow_pos_of_pos hLpos _)
  let s := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
  have hsub : ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ =>
      X < (n : ℝ) ∧ InH2 n ∧ T < Task129.err53 X ε B n)) ⊆
      s.filter (fun n => T ≤ |Task129.err53 X ε B n|) := by
    intro n hn
    obtain ⟨hr, hXn, _, he⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, hXn⟩,
      he.le.trans (le_abs_self _)⟩
  have hcard : (cntIoc (fun n => InH2 n ∧ T < Task129.err53 X ε B n) X H : ℝ) ≤
      ((s.filter (fun n => T ≤ |Task129.err53 X ε B n|)).card : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    simpa only [cntIoc, Finset.filter_congr_decidable] using hcast
  have hcheb := U1534.chebyshev_count s (Task129.err53 X ε B) hT
  have hcnt := (mul_le_mul_of_nonneg_right hcard (sq_nonneg T)).trans hcheb
  have hsum := hmean X H hX hH hHY
  have hTsq : T ^ 2 = Task129.windowY X ε * Real.log X ^ (-2 * A) := by
    dsimp [T]
    rw [mul_pow, Real.sq_sqrt hYpos.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have heq : C * H / Real.log X ^ A * T ^ 2 =
      C * H * Task129.windowY X ε / Real.log X ^ (3 * A) := by
    rw [hTsq, div_eq_mul_inv, div_eq_mul_inv,
      ← Real.rpow_neg hLpos.le, ← Real.rpow_neg hLpos.le]
    calc C * H * Real.log X ^ (-A) * (Task129.windowY X ε * Real.log X ^ (-2 * A)) =
        C * H * Task129.windowY X ε * (Real.log X ^ (-A) * Real.log X ^ (-2 * A)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hLpos]
        congr 1
        congr 1
        ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hT)).mp
    (by simpa only [mul_comm (T ^ 2)] using (hcnt.trans hsum).trans_eq heq.symm)

/-- P0088 page 16 display 53 on the full range of `Task129.eq53_full_range`,
CONDITIONAL ON the single hypothesis `hms`: page 8 Proposition 1 display 33
with the page 15 weights for H between X to the 7 over 18 plus epsilon and the
window length Y, the range of page 4 Section 2.1 where H is Y to the theta2.
In that range H is at least Y to the two thirds times a positive power of X.
Neither the sealed leaf `Task516a.eq53_large_eps` nor the upper end X to the
1 minus epsilon is used: for epsilon at most 7 over 18 an H above Y reduces to
H equal to Y by the support of the windows, and for epsilon above 7 over 18
the bound is trivial by `eq53_trivial_range`. Derived support statement for
the lab encoding, not a claim of the paper. -/
theorem eq53_full_range_of_window_mean_square (A : ℝ) (hA : 0 < A)
    (hms : ∀ A' : ℝ, 0 < A' → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ Task129.windowY X ε →
        (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
          Task129.err53 X ε B n ^ 2) ≤
            C * H * Task129.windowY X ε / Real.log X ^ A') :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hc⟩ := cnt53_of_window_mean_square A hA hms
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  by_cases h718 : ε ≤ 7 / 18
  · obtain ⟨C, X0, hC, hX0, hc⟩ := hc B hB ε hε
    refine ⟨C, X0, hC, hX0, ?_⟩
    intro X H hX hH _
    have hXone : 1 ≤ X := by linarith
    by_cases hHY : H ≤ Task129.windowY X ε
    · exact hc X H hX hH hHY
    · have hYH : Task129.windowY X ε ≤ H := (not_le.mp hHY).le
      have hYlow : X ^ (7 / 18 + ε) ≤ Task129.windowY X ε := by
        unfold Task129.windowY
        exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      exact cnt53_reduce A B ε X H C hXone hYH hC.le (hc X _ hX hYlow le_rfl)
  · obtain ⟨X0, hX0, h⟩ := eq53_trivial_range A B ε (not_le.mp h718)
    exact ⟨1, X0, one_pos, hX0, fun X H hX hH _ => h X H hX hH⟩

/-- P0088 page 16 display 53 on the full range of `Task129.eq53_full_range`,
CONDITIONAL ON the single hypothesis `hblock`: page 8 Proposition 1 display 33
with the page 15 weights over every block of n that starts between X and X
plus Y and has length between X to the 7 over 18 plus epsilon times P to the
minus 4 and Y times P to the minus 4, where P is the power of log X of page 4
display 14. Such a block satisfies Q at most Q0 of page 6 display 23 and the
edge term condition of the Gallagher step before page 6 display 20, so the
written proof of displays 16 to 32 applies to it. The covering step is
`Eq33Window1117.eq33_window_range_of_blocks`, used through the equality by
unfolding of the two copies of the display 53 definitions. Derived support
statement for the lab encoding. The block form is not written in the paper. -/
theorem eq53_full_range_of_block_mean_square (A : ℝ) (hA : 0 < A)
    (hblock : ∀ A' : ℝ, 0 < A' → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X X' H' : ℝ,
        X0 ≤ X → X ≤ X' → X' ≤ X + Task129.windowY X ε →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H' →
        H' ≤ Task129.windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∑ n ∈ (Finset.range (⌊X' + H'⌋₊ + 1)).filter (fun n : ℕ => X' < (n : ℝ)),
          Task129.err53 X ε B n ^ 2) ≤
            C * H' * Task129.windowY X ε / Real.log X ^ A') :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (Task129.windowY X ε) * Real.log X ^ (-A) <
            Task129.err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  apply eq53_full_range_of_window_mean_square A hA
  intro A' hA'
  exact Eq33Window1117.eq33_window_range_of_blocks A' hA' (hblock A' hA')

end LeanLab.KumchevLiu2007.Eq53Core1117

#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.cnt53_le_window
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.cnt53_reduce
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.cnt_le_length_add_one
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eventually_two_log_rpow_le
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_trivial_range
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_large_eps_named_of_core
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_large_eps_of_core
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_full_range_of_window_leaf_sharp
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_full_range_of_window_leaf
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.cnt53_of_window_mean_square
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_full_range_of_window_mean_square
#print axioms LeanLab.KumchevLiu2007.Eq53Core1117.eq53_full_range_of_block_mean_square

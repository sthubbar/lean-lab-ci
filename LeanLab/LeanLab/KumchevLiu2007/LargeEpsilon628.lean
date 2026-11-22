/-
P0088 page 16 display 53 and its unwritten large epsilon residue.
The corrected block mean square handles every H at least X to the
seven eighteenths plus epsilon. Only a smaller H residue remains a leaf.
The paper does not assert that residue. No paper error is claimed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Block628

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex Filter LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 2 display 5: the square window forces every represented
integer to be at least Y over four. -/
theorem block_windowPairs_empty_below (X Y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : (n : ℝ) < Y / 4) : windowPairs X Y n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨_, _, _, hl, _, he⟩ := Finset.mem_filter.mp hv
  have hs := Real.sq_sqrt hY
  have hr := Real.sqrt_nonneg Y
  have hm := Nat.cast_nonneg (α := ℝ) v.2
  have hv1 := Nat.cast_nonneg (α := ℝ) v.1
  have he' : (v.1 : ℝ) + (v.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast he
  have hsq : (Real.sqrt Y / 2) ^ 2 ≤ (v.2 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hm).mpr hl
  nlinarith

/-- P0088 page 16 display 53: below the support both the rough count and
the singular integral vanish, so the display 53 error is zero. -/
theorem block_err53_vanish_below (X ε B : ℝ) (n : ℕ) (hY : 0 ≤ windowY X ε)
    (hn : (n : ℝ) < windowY X ε / 4) : err53 X ε B n = 0 := by
  simp [err53, roughCount, singInt,
    block_windowPairs_empty_below X _ hY n hn]

/-- The page 16 choice of Y eventually exceeds eight times X when epsilon
exceeds five sixths. This is a support consequence for the lab's large range. -/
theorem block_eventually_large_window (ε : ℝ) (hε : 5 / 6 < ε) :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧ 2 * X < windowY X ε / 4 := by
  have hd : 0 < ε / 2 - 5 / 12 := by linarith
  have hp : ∀ᶠ X : ℝ in atTop, 12 ≤ X ^ (ε / 2 - 5 / 12) :=
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop 12)
  filter_upwards [hp, eventually_ge_atTop (2 : ℝ)] with X hp hX
  refine ⟨hX, ?_⟩
  have hX0 : 0 < X := by linarith
  have he : windowY X ε = X * X ^ (ε / 2 - 5 / 12) := by
    unfold windowY
    rw [show (7 / 12 + ε / 2 : ℝ) = 1 + (ε / 2 - 5 / 12) by ring,
      Real.rpow_add hX0, Real.rpow_one]
  rw [he]
  nlinarith

/-- P0088 page 16 display 53, derived support reduction: for epsilon above
five sixths there are eventually no error exceptions anywhere with H at most X. -/
theorem block_eq53_very_large_eps (A B ε : ℝ) (hε : 5 / 6 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ X →
      cntIoc (fun n => InH2 n ∧
        Real.sqrt (windowY X ε) * Real.log X ^ (-A) <
          err53 X ε B n) X H = 0 := by
  filter_upwards [block_eventually_large_window ε hε] with X hX
  intro H hH hHX
  unfold cntIoc
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hr, _, _, herr⟩ := hn
  have hnf : n ≤ ⌊X + H⌋₊ := Nat.lt_succ_iff.mp hr
  have hnr : (n : ℝ) ≤ X + H :=
    (Nat.cast_le.mpr hnf).trans (Nat.floor_le (by linarith [hX.1]))
  have hY : 0 ≤ windowY X ε := Real.rpow_nonneg (by linarith [hX.1]) _
  rw [block_err53_vanish_below X ε B n hY (by linarith [hX.2])] at herr
  exact (not_lt_of_ge (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (Real.log_nonneg (by linarith [hX.1])) _))) herr

/-- Page 16 display 53 by finite Chebyshev on the window range.
CONDITIONAL ON the two corrected block inputs through the mean square. -/
theorem count_of_window_mean_square (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) <
            err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hmean⟩ := weighted_window_mean_square (3 * A) (by positivity)
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hmean⟩ := hmean B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHY
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos hXpos _
  let T := Real.sqrt (windowY X ε) * Real.log X ^ (-A)
  have hT : 0 < T := mul_pos (Real.sqrt_pos.mpr hYpos) (Real.rpow_pos_of_pos hLpos _)
  let s := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
  have hsub : ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ =>
      X < (n : ℝ) ∧ InH2 n ∧ T < err53 X ε B n)) ⊆
      s.filter (fun n => T ≤ |err53 X ε B n|) := by
    intro n hn
    obtain ⟨hr, hXn, _, he⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, hXn⟩,
      he.le.trans (le_abs_self _)⟩
  have hcard : (cntIoc (fun n => InH2 n ∧ T < err53 X ε B n) X H : ℝ) ≤
      ((s.filter (fun n => T ≤ |err53 X ε B n|)).card : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    simpa only [cntIoc, Finset.filter_congr_decidable] using hcast
  have hcheb := U1534.chebyshev_count s (err53 X ε B) hT
  have hcnt := (mul_le_mul_of_nonneg_right hcard (sq_nonneg T)).trans hcheb
  have hsum := hmean X H hX hH hHY
  have hTsq : T ^ 2 = windowY X ε * Real.log X ^ (-2 * A) := by
    dsimp [T]
    rw [mul_pow, Real.sq_sqrt hYpos.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have heq : C * H / Real.log X ^ A * T ^ 2 =
      C * H * windowY X ε / Real.log X ^ (3 * A) := by
    rw [hTsq, div_eq_mul_inv, div_eq_mul_inv,
      ← Real.rpow_neg hLpos.le, ← Real.rpow_neg hLpos.le]
    calc C * H * Real.log X ^ (-A) * (windowY X ε * Real.log X ^ (-2 * A)) =
        C * H * windowY X ε * (Real.log X ^ (-A) * Real.log X ^ (-2 * A)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hLpos]
        congr 1
        congr 1
        ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hT)).mp
    (by simpa only [mul_comm (T ^ 2)] using (hcnt.trans hsum).trans_eq heq.symm)

/-- P0088 page 16, parameter separation for the unwritten residue. If H is
above X to one minus epsilon and below X to seven eighteenths plus epsilon,
then epsilon is above eleven thirty sixths. -/
theorem low_H_epsilon {X H ε : ℝ} (hX : 1 < X)
    (hlo : X ^ (1 - ε) < H) (hhi : H < X ^ (7 / 18 + ε)) :
    11 / 36 < ε := by
  have h := (Real.rpow_lt_rpow_left_iff hX).mp (hlo.trans hhi)
  linarith

/-- LEAF, UNWRITTEN RESIDUE. This is only the part of the sealed
Task516a.eq53_large_eps not supplied by the corrected block mean square or
by empty support. P0088 page 16 display 53 is the reference for the error
and threshold. The paper does not state this H range. It is not cited as
a proved paper result. The upper bounds H below X to seven eighteenths
plus epsilon and H at most Y remove the parts already handled separately.
No small parameter test certified a counterexample. -/
theorem low_H_large_eps (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ,
      11 / 36 < ε → ε ≤ 5 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (1 - ε) < H → H ≤ X → H ≤ windowY X ε →
        H < X ^ (7 / 18 + ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

/-- Page 2 display 5, support bookkeeping for page 16 display 53.
Every exception lies below X plus Y. This supplies an upstream support
comparison without importing Decomp129 or the sealed target. -/
theorem exception_count_le_window (A B ε X H : ℝ) (hX : 1 ≤ X) :
    cntIoc (fun n => InH2 n ∧
      Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H ≤
    cntIoc (fun n => InH2 n ∧
      Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n)
        X (windowY X ε) := by
  unfold cntIoc
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  obtain ⟨_, hXn, hnH2, herr⟩ := hn
  have hYnn : 0 ≤ windowY X ε := Real.rpow_nonneg (by linarith) _
  have hnY : (n : ℝ) < X + windowY X ε := by
    by_contra h
    have hge := not_lt.mp h
    rw [Eq33Window1117.err53_vanish_above X ε B n hYnn hge] at herr
    exact (not_lt_of_ge (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (Real.log_nonneg hX) _))) herr
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hnY.le), hXn, hnH2, herr⟩

/-- P0088 page 16 display 53, repaired assembly for the exact named large
epsilon target. CONDITIONAL ON major_arc_block, rough_block_energy and
low_H_large_eps. Above the block mean square lower bound use Chebyshev.
Below it only the strictly smaller unwritten leaf is used. Above epsilon
five sixths use empty support. No refuted Task556 leaf is used. -/
theorem large_eps_from_repaired_blocks (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → 5 / 18 < ε → X ^ (1 - ε) < H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B1, hB1, hw⟩ := count_of_window_mean_square A hA
  obtain ⟨B2, hB2, hl⟩ := low_H_large_eps A hA
  refine ⟨max B1 B2, hB1.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  by_cases hepshi : ε ≤ 5 / 6
  · obtain ⟨C1, X1, hC1, hX1, hw⟩ := hw B ((le_max_left _ _).trans hB) ε hε
    by_cases hepslo : 11 / 36 < ε
    · obtain ⟨C2, X2, hC2, hX2, hl⟩ := hl B ((le_max_right _ _).trans hB) ε hepslo hepshi
      refine ⟨max C1 C2, max X1 X2, hC1.trans_le (le_max_left _ _),
        hX1.trans (le_max_left _ _), ?_⟩
      intro X H hX h518 hlow hHX
      have hx1 : X1 ≤ X := (le_max_left _ _).trans hX
      have hx2 : X2 ≤ X := (le_max_right _ _).trans hX
      have hX1' : 1 < X := by linarith [hX1.trans hx1]
      have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hX1') _
      have hYpos : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
      have hYX : windowY X ε ≤ X := by
        unfold windowY
        calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
          _ = X := Real.rpow_one X
      have hlocal : ∀ J : ℝ, X ^ (1 - ε) < J → J ≤ X → J ≤ windowY X ε →
          (cntIoc (fun n => InH2 n ∧
            Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X J : ℝ) ≤
            max C1 C2 * J / Real.log X ^ A := by
        intro J hjlow hjX hjY
        have hJ : 0 ≤ J := (Real.rpow_nonneg (by linarith) _).trans hjlow.le
        by_cases hj : X ^ (7 / 18 + ε) ≤ J
        · exact (hw X J hx1 hj hjY).trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hJ) hLA.le)
        · exact (hl X J hx2 hjlow hjX hjY (not_le.mp hj)).trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hJ) hLA.le)
      by_cases hHY : H ≤ windowY X ε
      · exact hlocal H hlow hHX hHY
      · have hYH : windowY X ε ≤ H := (not_le.mp hHY).le
        have hYlow : X ^ (1 - ε) < windowY X ε := by
          unfold windowY
          exact Real.rpow_lt_rpow_of_exponent_lt hX1' (by linarith)
        have hcnt := hlocal (windowY X ε) hYlow hYX le_rfl
        exact (Nat.cast_le.mpr (exception_count_le_window A B ε X H hX1'.le)).trans
          (hcnt.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYH (hC1.trans_le (le_max_left _ _)).le) hLA.le))
    · refine ⟨C1, X1, hC1, hX1, ?_⟩
      intro X H hX h518 hlow hHX
      have hX1' : 1 < X := by linarith [hX1.trans hX]
      have hYpos : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
      have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hX1') _
      have hYlo : X ^ (7 / 18 + ε) ≤ windowY X ε := by
        unfold windowY
        exact Real.rpow_le_rpow_of_exponent_le hX1'.le (by linarith)
      have hHlo : X ^ (7 / 18 + ε) ≤ H := by
        by_contra h
        exact hepslo (low_H_epsilon hX1' hlow (not_le.mp h))
      by_cases hHY : H ≤ windowY X ε
      · exact hw X H hX hHlo hHY
      · have hYH : windowY X ε ≤ H := (not_le.mp hHY).le
        have hcnt := hw X (windowY X ε) hX hYlo le_rfl
        exact (Nat.cast_le.mpr (exception_count_le_window A B ε X H hX1'.le)).trans
          (hcnt.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYH hC1.le) hLA.le))
  · have heps := not_le.mp hepshi
    obtain ⟨X0, hz⟩ := Filter.eventually_atTop.mp (block_eq53_very_large_eps A B ε heps)
    refine ⟨1, max 2 X0, one_pos, le_max_left _ _, ?_⟩
    intro X H hX _ hlow hHX
    have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
    have hH : 0 ≤ H := (Real.rpow_nonneg (by linarith) _).trans hlow.le
    rw [hz X ((le_max_right _ _).trans hX) H hH hHX, Nat.cast_zero]
    exact div_nonneg (by linarith) (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)

end LeanLab.KumchevLiu2007.Task628

#print axioms LeanLab.KumchevLiu2007.Task628.block_windowPairs_empty_below
#print axioms LeanLab.KumchevLiu2007.Task628.block_err53_vanish_below
#print axioms LeanLab.KumchevLiu2007.Task628.block_eventually_large_window
#print axioms LeanLab.KumchevLiu2007.Task628.block_eq53_very_large_eps
#print axioms LeanLab.KumchevLiu2007.Task628.count_of_window_mean_square
#print axioms LeanLab.KumchevLiu2007.Task628.low_H_epsilon
#print axioms LeanLab.KumchevLiu2007.Task628.low_H_large_eps
#print axioms LeanLab.KumchevLiu2007.Task628.exception_count_le_window
#print axioms LeanLab.KumchevLiu2007.Task628.large_eps_from_repaired_blocks

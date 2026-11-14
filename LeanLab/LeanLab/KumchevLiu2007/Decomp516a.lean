/-
Repair leaves for Kumchev and Liu, arXiv 0801.0130, P0088 pages 13 to 16.
Definitions are written as let expressions inside each leaf statement.
This file imports neither Decomp129 nor a module that imports it.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c

namespace LeanLab.KumchevLiu2007.Task516a

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 8 Proposition 1 display 33 with the page 15 weights and
hypotheses, in the written range on page 16 after display 55. The short
interval character estimates and Lemma 3.4 remain analytic inputs.
This is the weighted mean square estimate before Chebyshev counting. -/
theorem eq33_weighted_mean_square (A : ℝ) (hA : 0 < A) :
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
  sorry

/-- Page 16 display 53 follows from Proposition 1 display 33 by the
finite Chebyshev inequality. CONDITIONAL on eq33_weighted_mean_square. -/
theorem eq53_prop1 (A : ℝ) (hA : 0 < A) :
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
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  let windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)
  let windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧ Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
  let series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
  let roughCount (X Y P : ℝ) (n : ℕ) : ℕ := ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
  let f2Weight (z0 u : ℝ) : ℝ := 1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
  let singInt (X Y P : ℝ) (n : ℕ) : ℝ := ∑ v ∈ windowPairs X Y n, (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
  let err53 (X ε B : ℝ) (n : ℕ) : ℝ := ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) - series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
  change ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A 
  obtain ⟨B0, hB0, hmean⟩ := eq33_weighted_mean_square (3 * A) (by positivity)
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hmean⟩ := hmean B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < windowY X ε := Real.rpow_pos_of_pos hXpos _
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
  have hsum := hmean X H hX hH hHX
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


/-- LEAF, UNWRITTEN RESIDUE. Display 53 of page 16 when epsilon exceeds
5 over 18 and H exceeds X to the 1 minus epsilon. For epsilon at most 5 over 18
this range reduces to the written one by the support of the windows, proved
in `Decomp129.eq53_full_range`. The paper treats epsilon as a small fixed number and
does not write this case; it is recorded as BLOCKED NO WRITTEN PROOF in PROGRESS.md. -/
theorem eq53_large_eps (A : ℝ) (hA : 0 < A) :
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
  sorry

/-- LEAF. Page 14 display 48, the lower bound of P2 of n, P by
log P to the minus 1 on H2, together with Lemma 3.8 display 49 with y equal to H
and Chebyshev's inequality: S2 of n, P is at least c over log P for all but
O of H L to the minus A integers n in H2 in the interval X, X plus H.
CITED: Lemma 3.8 and display 48 are proved on pages 14 and 15. -/
theorem eq48_49_series_lower (A : ℝ) (hA : 0 < A) :
    let series2 (n : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          ‖series2 n (Real.log X ^ B)‖ < c / Real.log (Real.log X ^ B)) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

end LeanLab.KumchevLiu2007.Task516a

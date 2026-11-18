/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130.
Support reduction for Proposition 1 display 33 of page 8 in the lab encoding.
The sealed leaf Task516a.eq33_weighted_mean_square lets H run up to X to the 1 minus epsilon,
while the windows of page 2 display 5 have length Y. Page 4 Section 2.1 sets H equal to Y
to the theta2. Every n at least X plus Y has an empty window set, so its error term vanishes.
Hence mean square leaves that carry the extra premise H at most Y are enough for the sealed text.
Everything here is a derived support statement. No analytic input of the paper is proved here.
This file adds no definition and is imported by nothing.
Block step: the written proof of pages 5 to 8 needs Q = H/P at most Q0 = Y/P^3, page 4
display 14 and page 6 display 23, and the edge term of the Gallagher step before page 6
display 20 needs H at most about Y times P to the minus 4. Cutting the n interval into
blocks of length at most Y times P to the minus 4 shows a block form of display 33 implies
the sealed text.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556b

namespace LeanLab.KumchevLiu2007.Eq33Window1117

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 2 display 5 and page 4 display 12. No pair in the two windows
represents an n at least X plus Y, since the first entry is below X and the
square of the second entry is at most Y. Derived support statement for the lab
encoding, stated for the Task556a copy of the window set. -/
theorem windowPairs_empty_above (X Y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : X + Y ≤ (n : ℝ)) : windowPairs X Y n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  unfold windowPairs at hv
  obtain ⟨_, _, hhi, _, hqhi, heq⟩ := Finset.mem_filter.mp hv
  have hq2 : (v.2 : ℝ) ^ 2 ≤ Y := by
    have hsq := (sq_le_sq₀ (Nat.cast_nonneg v.2) (Real.sqrt_nonneg Y)).mpr hqhi.le
    nlinarith only [hsq, Real.sq_sqrt hY]
  have hcast : (v.1 : ℝ) + (v.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast heq
  linarith

/-- P0088 page 8 display 33 with the page 2 display 5 windows. The error term
of display 33 vanishes at every n at least X plus Y, because both the rough
count and the singular integral sum run over the empty window set. Derived
support statement for the lab encoding, stated for the Task556a copy. -/
theorem err53_vanish_above (X ε B : ℝ) (n : ℕ) (hY : 0 ≤ windowY X ε)
    (hn : X + windowY X ε ≤ (n : ℝ)) : err53 X ε B n = 0 := by
  simp [err53, roughCount, singInt, windowPairs_empty_above X _ hY n hn]

/-- P0088 page 8 display 33. When H is at least the window length Y, the mean
square over the integers of the interval from X to X plus H equals the mean
square over the interval from X to X plus Y, since the error term vanishes
beyond X plus Y. Derived support statement for the lab encoding. -/
theorem sum_err53_sq_eq_window (X ε B H : ℝ) (hY : 0 ≤ windowY X ε)
    (hYH : windowY X ε ≤ H) :
    (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) =
      ∑ n ∈ intervalNumbers X (windowY X ε), err53 X ε B n ^ 2 := by
  symm
  apply Finset.sum_subset
  · intro n hn
    unfold intervalNumbers at hn ⊢
    obtain ⟨hr, hXn⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hXn⟩
    have hr' := Finset.mem_range.mp hr
    have hmono : ⌊X + windowY X ε⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_le_floor (by linarith)
    omega
  · intro n hn hnot
    have hge : X + windowY X ε ≤ (n : ℝ) := by
      by_contra hlt
      rw [not_le] at hlt
      apply hnot
      unfold intervalNumbers at hn ⊢
      obtain ⟨_, hXn⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hXn⟩
      exact Nat.lt_succ_of_le (Nat.le_floor hlt.le)
    rw [err53_vanish_above X ε B n hY hge]
    norm_num

/-- P0088 page 8 Proposition 1 display 33 with the page 15 weights, in the
written range of page 16 after display 55. The exact sealed statement text of
`Task516a.eq33_weighted_mean_square`, CONDITIONAL ON the same mean square
bound restricted to H at most the window length Y of page 2 display 5. If H
exceeds Y then epsilon is below 5/18, Y lies in the written range, and the sum
over the longer interval equals the sum over the interval of length Y.
Derived support statement for the lab encoding. -/
theorem eq33_weighted_mean_square_of_window_range (A : ℝ) (_hA : 0 < A)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A) :
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
  obtain ⟨B0, hB0, hc⟩ := hcore
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hc⟩ := hc B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX
  have hX1 : 1 < X := by linarith
  have hXpos : 0 < X := by linarith
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hX1) A
  have hYpos : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos hXpos _
  by_cases hHY : H ≤ windowY X ε
  · exact hc X H hX hH hHX hHY
  · rw [not_le] at hHY
    have hlt : X ^ (7 / 12 + ε / 2) < X ^ (1 - ε) := by
      have h := hHY.trans_le hHX
      unfold windowY at h
      exact h
    have hexp : 7 / 12 + ε / 2 < 1 - ε := (Real.rpow_lt_rpow_left_iff hX1).mp hlt
    have hYlo : X ^ (7 / 18 + ε) ≤ windowY X ε := by
      unfold windowY
      exact Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
    have hYhi : windowY X ε ≤ X ^ (1 - ε) := hHY.le.trans hHX
    have h1 := hc X (windowY X ε) hX hYlo hYhi le_rfl
    rw [sum_err53_sq_eq_window X ε B H hYpos.le hHY.le]
    refine h1.trans ?_
    have hstep : C * windowY X ε * windowY X ε ≤ C * H * windowY X ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHY.le hC.le) hYpos.le
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr hLA.le)

/-- P0088 page 8 Proposition 1 display 33 with the page 15 weights, in the
written range of page 16 after display 55. The exact sealed statement text of
`Task516a.eq33_weighted_mean_square`, CONDITIONAL ON the major arc mean square
of page 7 display 28 and the minor arc mean square of page 8 display 32, each
restricted to H at most the window length Y of page 2 display 5. The split is
the one used on page 8 before display 33. Derived support statement for the
lab encoding. -/
theorem eq33_weighted_mean_square_of_window_arcs (A : ℝ) (hA : 0 < A)
    (hmajor : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H,
          ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
            C * H * windowY X ε / Real.log X ^ A)
    (hminor : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H,
          ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
            C * H * windowY X ε / Real.log X ^ A) :
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
  have hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
    obtain ⟨B1, hB1, hmajor⟩ := hmajor
    obtain ⟨B2, hB2, hminor⟩ := hminor
    refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), ?_⟩
    intro B hB ε hε
    obtain ⟨C1, X1, hC1, hX1, hm⟩ := hmajor B ((le_max_left _ _).trans hB) ε hε
    obtain ⟨C2, X2, hC2, hX2, hn⟩ := hminor B ((le_max_right _ _).trans hB) ε hε
    refine ⟨2 * C1 + 2 * C2, max X1 X2, by positivity,
      hX1.trans (le_max_left _ _), ?_⟩
    intro X H hX hH hHX hHY
    have h1 := hm X H ((le_max_left _ _).trans hX) hH hHX hHY
    have h2 := hn X H ((le_max_right _ _).trans hX) hH hHX hHY
    have hc := Task506aTask129b.mean_square_add (intervalNumbers X H)
      (majorError X (windowY X ε) H (Real.log X ^ B))
      (minorCoefficient X (windowY X ε) H (Real.log X ^ B))
    have he : ∀ n, err53 X ε B n =
        ‖majorError X (windowY X ε) H (Real.log X ^ B) n +
          minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ := by
      intro n
      unfold err53
      rw [Task556b.error_eq_major_add_minor X ε B H n]
    simp_rw [he]
    calc
      _ ≤ _ := hc
      _ ≤ 2 * (C1 * H * windowY X ε / Real.log X ^ A) +
          2 * (C2 * H * windowY X ε / Real.log X ^ A) := by linarith
      _ = _ := by ring
  exact eq33_weighted_mean_square_of_window_range A hA hcore

/-- P0088 page 8 display 33, generic covering step with no paper definition.
For a nonnegative function f, if the sum of f over the integers of every block
from X' to X' plus H0, with X' between X and X plus H, is at most K times H0,
then the sum over the integers from X to X plus H is at most 2 K H whenever
H0 is at most H. The interval is cut into at most H over H0 plus one half open
blocks of length H0 starting at X plus j H0. Derived support statement for the
lab encoding. The block form is not written in the paper. -/
theorem sum_interval_le_of_blocks (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (X H H0 K : ℝ)
    (hX : 0 ≤ X) (hH0 : 0 < H0) (hH0H : H0 ≤ H) (hK : 0 ≤ K)
    (hblock : ∀ X' : ℝ, X ≤ X' → X' ≤ X + H →
      (∑ n ∈ (Finset.range (⌊X' + H0⌋₊ + 1)).filter (fun n : ℕ => X' < (n : ℝ)), f n) ≤ K * H0) :
    (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)), f n) ≤ 2 * K * H := by
  have hH : 0 < H := lt_of_lt_of_le hH0 hH0H
  have hN : ((⌈H / H0⌉₊ : ℕ) : ℝ) < H / H0 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hH.le hH0.le)
  have hmaps : ∀ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
      ⌈((n : ℝ) - X) / H0⌉₊ - 1 ∈ Finset.range ⌈H / H0⌉₊ := by
    intro n hn
    obtain ⟨hr, hXn⟩ := Finset.mem_filter.mp hn
    have hnle : (n : ℝ) ≤ X + H := by
      have h1 : n ≤ ⌊X + H⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      exact (Nat.le_floor_iff (by linarith)).mp h1
    have hpos : 0 < ((n : ℝ) - X) / H0 := div_pos (by linarith) hH0
    have h1 : 0 < ⌈((n : ℝ) - X) / H0⌉₊ := Nat.ceil_pos.mpr hpos
    have h2 : ⌈((n : ℝ) - X) / H0⌉₊ ≤ ⌈H / H0⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith) hH0.le)
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine (Finset.sum_le_sum (g := fun _ => K * H0) ?_).trans ?_
  · intro j hj
    have hjN : j + 1 ≤ ⌈H / H0⌉₊ := Finset.mem_range.mp hj
    have hjlt : (j : ℝ) < H / H0 := by
      have h1 : ((j + 1 : ℕ) : ℝ) ≤ ((⌈H / H0⌉₊ : ℕ) : ℝ) := by exact_mod_cast hjN
      push_cast at h1
      linarith
    have hjH : (j : ℝ) * H0 < H := (lt_div_iff₀ hH0).mp hjlt
    have hj0 : 0 ≤ (j : ℝ) * H0 := mul_nonneg (Nat.cast_nonneg j) hH0.le
    refine le_trans ?_ (hblock (X + (j : ℝ) * H0) (by linarith) (by linarith))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn1, hg⟩ := Finset.mem_filter.mp hn
      obtain ⟨hr, hXn⟩ := Finset.mem_filter.mp hn1
      have hpos : 0 < ((n : ℝ) - X) / H0 := div_pos (by linarith) hH0
      have hc1 : 0 < ⌈((n : ℝ) - X) / H0⌉₊ := Nat.ceil_pos.mpr hpos
      have hceq : ⌈((n : ℝ) - X) / H0⌉₊ = j + 1 := by omega
      have hup : ((n : ℝ) - X) / H0 ≤ (j : ℝ) + 1 := by
        have h1 := Nat.le_ceil (((n : ℝ) - X) / H0)
        rw [hceq] at h1
        push_cast at h1
        exact h1
      have hlo : (j : ℝ) < ((n : ℝ) - X) / H0 := by
        have h1 := Nat.ceil_lt_add_one hpos.le
        rw [hceq] at h1
        push_cast at h1
        linarith
      have hup' : (n : ℝ) - X ≤ ((j : ℝ) + 1) * H0 := (div_le_iff₀ hH0).mp hup
      have hlo' : (j : ℝ) * H0 < (n : ℝ) - X := (lt_div_iff₀ hH0).mp hlo
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, by linarith⟩
      exact Nat.lt_succ_of_le (Nat.le_floor (by linarith))
    · intro n _ _
      exact hf n
  · have hKH0 : 0 ≤ K * H0 := mul_nonneg hK hH0.le
    calc (∑ _j ∈ Finset.range ⌈H / H0⌉₊, K * H0)
        = ((⌈H / H0⌉₊ : ℕ) : ℝ) * (K * H0) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (H / H0 + 1) * (K * H0) := mul_le_mul_of_nonneg_right hN.le hKH0
      _ = K * (H + H0) := by field_simp
      _ ≤ 2 * K * H := by nlinarith [mul_le_mul_of_nonneg_left hH0H hK]

/-- P0088 page 8 Proposition 1 display 33 in the range H at most the window
length Y of page 2 display 5, CONDITIONAL ON hblock, the same mean square bound
over every block of n that starts between X and X plus Y and has length at most
Y times P to the minus 4, where P is the power of log X of page 4 display 14.
That length satisfies Q at most Q0 of page 6 display 23 and keeps the edge term
of the Gallagher step before page 6 display 20 below P to the minus 3, so the
written proof of displays 16 to 32 applies to such a block. An interval longer
than one block is cut into blocks by
`sum_interval_le_of_blocks`, at the cost of the factor 2 in the constant, and
X0 is raised to at least 3 so that log X is at least 1. Derived support
statement for the lab encoding. The block form is not written in the paper. -/
theorem eq33_window_range_of_blocks (A : ℝ) (_hA : 0 < A)
    (hblock : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X X' H' : ℝ,
        X0 ≤ X → X ≤ X' → X' ≤ X + windowY X ε →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H' →
        H' ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∑ n ∈ (Finset.range (⌊X' + H'⌋₊ + 1)).filter (fun n : ℕ => X' < (n : ℝ)),
          err53 X ε B n ^ 2) ≤ C * H' * windowY X ε / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨B0, hB0, hb⟩ := hblock
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := hb B hB ε hε
  refine ⟨2 * C, max X0 3, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hHlo hHY
  have hX0X : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX3
  have hLB : 1 ≤ Real.log X ^ B := Real.one_le_rpow hlog1 (hB0.le.trans hB)
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (by linarith) A
  have hp2pos : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (by linarith) _
  have hp2le : (Real.log X ^ B) ^ (-4 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hLB (by norm_num))
  have hYpos : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos hXpos _
  have hlopos : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos hXpos _
  have hHpos : 0 < H := lt_of_lt_of_le hlopos hHlo
  have hKnn : 0 ≤ C * windowY X ε / Real.log X ^ A :=
    div_nonneg (mul_nonneg hC.le hYpos.le) hLA.le
  unfold intervalNumbers
  by_cases hcase : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)
  · have hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H := by
      have h1 : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ X ^ (7 / 18 + ε) * 1 :=
        mul_le_mul_of_nonneg_left hp2le hlopos.le
      linarith
    have h1 := hb X X H hX0X le_rfl (by linarith) hlo hcase
    refine h1.trans ?_
    have e1 : C * H * windowY X ε / Real.log X ^ A =
        (C * windowY X ε / Real.log X ^ A) * H := by ring
    have e2 : 2 * C * H * windowY X ε / Real.log X ^ A =
        2 * ((C * windowY X ε / Real.log X ^ A) * H) := by ring
    rw [e1, e2]
    linarith [mul_nonneg hKnn hHpos.le]
  · rw [not_le] at hcase
    have h5 := sum_interval_le_of_blocks (fun n => err53 X ε B n ^ 2)
      (fun n => sq_nonneg _) X H (windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ))
      (C * windowY X ε / Real.log X ^ A) hXpos.le (mul_pos hYpos hp2pos) hcase.le hKnn
      (by
        intro X' hXX' hX'H
        have h1 := hb X X' (windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) hX0X hXX'
          (by linarith) (mul_le_mul_of_nonneg_right (hHlo.trans hHY) hp2pos.le) le_rfl
        refine h1.trans (le_of_eq ?_)
        ring)
    refine h5.trans (le_of_eq ?_)
    ring

/-- P0088 page 8 Proposition 1 display 33 with the page 15 weights, in the
written range of page 16 after display 55. The exact sealed statement text of
`Task516a.eq33_weighted_mean_square`, CONDITIONAL ON hblock, the mean square
bound over every block of n that starts between X and X plus Y and has length
at most Y times P to the minus 4, which satisfies Q at most Q0 of page 4
display 14 and page 6 display 23 and the edge term condition of the Gallagher
step before page 6 display 20. Combines
`eq33_window_range_of_blocks` with `eq33_weighted_mean_square_of_window_range`.
Derived support statement for the lab encoding. The block form is not written
in the paper. -/
theorem eq33_weighted_mean_square_of_blocks (A : ℝ) (hA : 0 < A)
    (hblock : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X X' H' : ℝ,
        X0 ≤ X → X ≤ X' → X' ≤ X + windowY X ε →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H' →
        H' ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∑ n ∈ (Finset.range (⌊X' + H'⌋₊ + 1)).filter (fun n : ℕ => X' < (n : ℝ)),
          err53 X ε B n ^ 2) ≤ C * H' * windowY X ε / Real.log X ^ A) :
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
  have hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → H ≤ windowY X ε →
        (∑ n ∈ intervalNumbers X H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
    obtain ⟨B0, hB0, hw⟩ := eq33_window_range_of_blocks A hA hblock
    refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
    obtain ⟨C, X0, hC, hX0, hw⟩ := hw B hB ε hε
    exact ⟨C, X0, hC, hX0, fun X H hX hH _ hHY => hw X H hX hH hHY⟩
  exact eq33_weighted_mean_square_of_window_range A hA hcore

end LeanLab.KumchevLiu2007.Eq33Window1117

#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.windowPairs_empty_above
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.err53_vanish_above
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.sum_err53_sq_eq_window
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.eq33_weighted_mean_square_of_window_range
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.eq33_weighted_mean_square_of_window_arcs
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.sum_interval_le_of_blocks
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.eq33_window_range_of_blocks
#print axioms LeanLab.KumchevLiu2007.Eq33Window1117.eq33_weighted_mean_square_of_blocks

/-
Repair inputs for P0088 displays 28 and 32 on short blocks.
These inputs replace the refuted Task556 character route.
They do not assert the character normalization refuted by Eq33RouteE and Eq33RouteF.
The major arc range keeps the Gallagher edge condition from pages 5 and 6.
The complete energy assembly includes the initial interval required on page 8.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33Window1117
import LeanLab.KumchevLiu2007.BlockKernel628
import LeanLab.KumchevLiu2007.InitialRange634

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. P0088 page 7 display 28 with the page 15 weights.
Use blocks with H at most Y P to the minus four, as required by the edge
term before page 6 display 20. The lower bound loses four logarithmic powers
relative to the final H range. A positive epsilon margin absorbs that loss.
This is a corrected analytic input for every A, not the false unrestricted
pointwise conclusion of Task556b.major_arc_transference.
The Huxley methods invoked on page 15 remain cited. -/
theorem major_arc_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  sorry

/-- LEAF. P0088 page 7 hypothesis A2.3 and page 15 display 52 on short
blocks. This is the bulk Lemma 3.4 input isolated by Eq33RouteD, with the
lower block length reduced by four logarithmic powers. A positive epsilon
margin absorbs that loss. The initial interval is proved separately from
Task634.initial_energy_small. This leaf has no prime sum, representation
count or Fourier coefficient mean square. -/
theorem rough_block_bulk (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  sorry

/-- P0088 pages 7 and 8 displays 30 and 31. The proved Gallagher and
subdivision steps turn a bound on the complete short sum energy, including
the initial interval, into a uniform kernel mass bound. CONDITIONAL ON henergy. -/
theorem kernel_mass_of_complete_energy {X Y H P A C : ℝ}
    (hX : 3 ≤ X) (hH : 2 ≤ H) (hHX : H ≤ X) (hC : 0 ≤ C)
    (henergy : ∀ α : ℝ, α ∉ majorArcs H P →
      ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
        ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∀ β ∈ Set.Icc (0 : ℝ) 1,
      kernelMass Y H P β ≤ 16 * π ^ 2 * C * H / Real.log X ^ A := by
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX
  have hLpos : 0 < Real.log X := by linarith
  have hHpos : 0 < H := by linarith
  have hlogH : Real.log H ≤ Real.log X := Real.log_le_log hHpos hHX
  have hLp : 0 < Real.log X ^ (A + 2) := Real.rpow_pos_of_pos hLpos _
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hLpos _
  have hG : ∀ α : ℝ, α ∉ majorArcs H P →
      (∫ β in (-(1 / (2 * H)))..(1 / (2 * H)),
        ‖roughSum Y P (α + β)‖ ^ 2) ≤
        π ^ 2 / 4 * C / Real.log X ^ (A + 2) := by
    intro α hα
    have g := Eq33RouteB.gallagher_roughSum Y P H α hHpos
    calc _ ≤ _ := g
      _ ≤ (π / (2 * H)) ^ 2 * (C * H ^ 2 / Real.log X ^ (A + 2)) := by
        exact mul_le_mul_of_nonneg_left (henergy α hα) (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hM0 : 0 ≤ π ^ 2 / 4 * C / Real.log X ^ (A + 2) := by positivity
  have hloc : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc (γ - 1 / H) (γ + 1 / H),
        ‖roughSum Y P α‖ ^ 2) ≤
        4 * (π ^ 2 / 4 * C / Real.log X ^ (A + 2)) :=
    fun γ _ => Eq33RouteB.display31_shift Y P H γ _ hHpos hM0 hG
  intro β hβ
  have hk := Eq33RouteB.display30_subdivision Y P H β _ hH hβ hloc
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hLpos, Real.rpow_two]
  have hstep : 8 * H * (1 + Real.log H) *
      (4 * (π ^ 2 / 4 * C / Real.log X ^ (A + 2))) ≤
      8 * H * (2 * Real.log X) *
      (4 * (π ^ 2 / 4 * C / Real.log X ^ (A + 2))) := by
    gcongr
    linarith
  have heq : 8 * H * (2 * Real.log X) *
      (4 * (π ^ 2 / 4 * C / Real.log X ^ (A + 2))) =
      16 * π ^ 2 * C * H / Real.log X ^ A * (1 / Real.log X) := by
    rw [hpow]
    field_simp
    ring
  have hfin : 16 * π ^ 2 * C * H / Real.log X ^ A * (1 / Real.log X) ≤
      16 * π ^ 2 * C * H / Real.log X ^ A :=
    mul_le_of_le_one_right (by positivity) (by rw [div_le_one hLpos]; exact hL1)
  linarith

/-- P0088 page 7 display 29 on translated n blocks, followed by page 8
Gallagher. CONDITIONAL ON henergy. The shifted block start does not change
the fixed prime and square windows or the minor arcs. -/
theorem minor_block_of_complete_energy {X X' Y H P A C : ℝ}
    (hX : 3 ≤ X) (hX' : 0 ≤ X') (hXY : 0 ≤ X - Y) (hY : 1 ≤ Y)
    (hH : 2 ≤ H) (hHX : H ≤ X) (hC : 0 ≤ C)
    (henergy : ∀ α : ℝ, α ∉ majorArcs H P →
      ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
        ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    (∑ n ∈ intervalNumbers X' H, ‖minorCoefficient X Y H P n‖ ^ 2) ≤
      64 * π ^ 2 * C * H * Y / Real.log X ^ A := by
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hM : 0 ≤ 16 * π ^ 2 * C * H / Real.log X ^ A := by positivity
  have hm := kernel_mass_of_complete_energy hX hH hHX hC henergy
  have ht := minor_mean_square_shifted hX' hXY hY (by linarith) hM hm
  calc _ ≤ _ := ht
    _ = _ := by ring

/-- Pages 4 and 6, the short block range is nonempty only when epsilon is
at most seven eighteenths. In that case the fixed windows lie below X and
the block length is at most X. This is a parameter consequence, not an
analytic input. -/
theorem block_window_parameters {X H B ε : ℝ} (hX : 3 ≤ X) (hB : 0 ≤ B)
    (hε : 0 < ε)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) :
    ε ≤ 7 / 18 ∧ 1 ≤ windowY X ε ∧ windowY X ε ≤ X ∧ H ≤ X := by
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB
  have hp : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (by linarith) _
  have he : X ^ (7 / 18 + ε) ≤ X ^ (7 / 12 + ε / 2) := by
    have := hlo.trans hhi
    unfold windowY at this
    nlinarith
  have he' : 7 / 18 + ε ≤ 7 / 12 + ε / 2 :=
    (Real.rpow_le_rpow_left_iff hX1).mp he
  have heps : ε ≤ 7 / 18 := by linarith
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1.le (by positivity)
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
      _ = X := Real.rpow_one X
  have hp1 : (Real.log X ^ B) ^ (-4 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hP1 (by norm_num))
  refine ⟨heps, hY1, hYX, hhi.trans ?_⟩
  exact (mul_le_of_le_one_right (by linarith) hp1).trans hYX

/-- Page 6 short block convention, derived parameter step. Every admissible
block eventually has length at least two, since a fixed logarithmic loss is
smaller than a positive power of X. -/
theorem block_length_eventually (B ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H → 2 ≤ H := by
  have hd : 0 < 7 / 18 + ε := by linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (4 * B) hd).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨X0, ht⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 3 X0, le_max_left _ _, ?_⟩
  intro X H hX hH
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have h := ht X ((le_max_right _ _).trans hX)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at h
  have he : (Real.log X ^ B) ^ (4 : ℕ) = Real.log X ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    norm_num
    ring
  have h2 : 2 ≤ X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hP 4), he]
    linarith
  exact h2.trans hH

/-- Page 8 after display 31. The repaired upper block range supplies the
smallness premise of the proved elementary initial energy bound. No minor
arc hypothesis is needed. -/
theorem block_initial_energy {X Y H B A α : ℝ}
    (hX : 3 ≤ X) (hY : 0 < Y) (hroot : Real.sqrt Y ≤ H)
    (hB : A + 2 ≤ 4 * B)
    (hhi : H ≤ Y * (Real.log X ^ B) ^ (-4 : ℤ)) :
    (∫ t in (Y / 4 - H)..(Y / 4),
      ‖roughShortSum Y (Real.log X ^ B) H α t‖ ^ 2) ≤
        4 * H ^ 2 / Real.log X ^ (A + 2) := by
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX
  have hL : 0 < Real.log X := by linarith
  have hpow : (Real.log X ^ B) ^ (-4 : ℤ) = Real.log X ^ (-4 * B) := by
    rw [zpow_neg, zpow_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
      ← Real.rpow_neg hL.le]
    congr 1
    norm_num
    ring
  have hsmall : H * Real.log X ^ (A + 2) ≤ Y := by
    calc
      _ ≤ (Y * (Real.log X ^ B) ^ (-4 : ℤ)) * Real.log X ^ (A + 2) := by
        exact mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg hL.le _)
      _ = Y * Real.log X ^ (-4 * B + (A + 2)) := by
        rw [hpow, mul_assoc, ← Real.rpow_add hL]
      _ ≤ Y * Real.log X ^ (0 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hY.le
      _ = Y := by simp
  exact Task634.initial_energy_small Y _ H α _ _ hY hL hroot hsmall

/-- Page 15 Lemma 3.4 parameter margin, derived block step. The lower
block length eventually exceeds square root Y. Its power gap is seven
seventy seconds plus three quarters of epsilon. -/
theorem block_root_eventually (B ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        Real.sqrt (windowY X ε) ≤ H := by
  have hd : 0 < 7 / 72 + 3 * ε / 4 := by linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (4 * B) hd).bound one_pos
  obtain ⟨X0, ht⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 3 X0, le_max_left _ _, ?_⟩
  intro X H hX hH
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have h := ht X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at h
  have he : (Real.log X ^ B) ^ (4 : ℕ) = Real.log X ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    norm_num
    ring
  have hroot : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  refine le_trans ?_ hH
  rw [hroot, zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hP 4), he]
  calc X ^ (7 / 24 + ε / 4) * Real.log X ^ (4 * B) ≤
      X ^ (7 / 24 + ε / 4) * X ^ (7 / 72 + 3 * ε / 4) := by gcongr
    _ = X ^ (7 / 18 + ε) := by
      rw [← Real.rpow_add hX0]
      congr 1
      ring

/-- Pages 7 and 8. The only analytic short energy input on repaired blocks
is the bulk estimate. The omitted initial interval is supplied by the
proved prefix bound. CONDITIONAL ON rough_block_bulk. -/
theorem rough_block_energy (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        ((∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) +
          ∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  obtain ⟨B0, hB0, hb⟩ := rough_block_bulk A hA
  refine ⟨max B0 (A + 2), hB0.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := hb B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨X1, hX1, hr⟩ := block_root_eventually B ε hε
  refine ⟨4 + C, max X0 X1, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α hα
  have hx0 : X0 ≤ X := (le_max_left _ _).trans hX
  have hx1 : X1 ≤ X := (le_max_right _ _).trans hX
  have hX3 : 3 ≤ X := hX1.trans hx1
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hB' : A + 2 ≤ 4 * B := by linarith [le_trans (le_max_right B0 (A + 2)) hB]
  have hi := block_initial_energy (α := α) hX3 hY (hr X H hx1 hlo) hB' hhi
  have hm := hb X H hx0 hlo hhi α hα
  calc _ ≤ 4 * H ^ 2 / Real.log X ^ (A + 2) + C * H ^ 2 / Real.log X ^ (A + 2) :=
        add_le_add hi hm
    _ = _ := by ring

end LeanLab.KumchevLiu2007.Task628

#print axioms LeanLab.KumchevLiu2007.Task628.kernel_mass_of_complete_energy
#print axioms LeanLab.KumchevLiu2007.Task628.minor_block_of_complete_energy

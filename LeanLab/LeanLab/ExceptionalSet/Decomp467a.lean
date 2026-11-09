import LeanLab.ExceptionalSet.Decomp450e
import LeanLab.ExceptionalSet.MomentSupply446
import LeanLab.ExceptionalSet.TailSupply385

/-!
P0082 pages 365 and 366, displays 24 to 27.
This companion exposes the sole cited input to the minor arc argument.
Five results are CONDITIONAL ON the explicit Karacuba Lemma10 input.
The logarithm absorption result has no cited premise.
No original analytic admission is used as a theorem.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp467a

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE expSumF Lemma10)
open LeanLab.ExceptionalSet.Decomp404e
open LeanLab.ExceptionalSet.DecompJ200
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor count_of_tail_and_moment)

/-- P0082 page366 before display27. Theorem2 from the explicit Karacuba input
controls only the distant phase sum. CONDITIONAL ON h10. -/
theorem far_phase_of_karacuba (h10 : Lemma10) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ t : ℝ, F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
            ‖phaseSum γ N t‖ ≤ C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  refine ⟨min ((γ - 1) / 24) (1 / 12), lt_min (by linarith) (by norm_num), fun δ hδ hδsmall => ?_⟩
  have hδγ : δ < (γ - 1) / 24 := hδsmall.trans_le (min_le_left _ _)
  have hδ12 : δ < 1 / 12 := hδsmall.trans_le (min_le_right _ _)
  obtain ⟨η, B, hη, hs⟩ := (LeanLab.ExceptionalSet.U1539.theorem2_of_all_leaves h10)
    γ h1 h2 (1 - 2 * δ) (12 * δ) (by linarith) (by linarith) (by positivity) (by linarith)
  obtain ⟨Nr, hr⟩ := Decomp450e.frequency_range_supplied γ δ h1 h2 hδ hδsmall
  obtain ⟨C, hC, Nd, hd⟩ := Decomp450c.decay_rescale_supplied γ η (|B| + 1) h1 h2 hη (by positivity)
  refine ⟨η / 6, by positivity, fun κ hκ hκsmall =>
    ⟨C, hC, max 2 (max Nr Nd), fun N hN t htlow hthigh => ?_⟩⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNd : Nd ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hm : 1 ≤ N / 2 := by omega
  obtain ⟨hl, hu⟩ := hr N hNr t htlow hthigh
  have hsum := hs (N / 2) hm t hl hu
  have hsum' : ‖expSumF γ t (N / 2)‖ ≤
      (|B| + 1) * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) := by
    refine hsum.trans ?_
    gcongr
    exact (le_abs_self B).trans (by linarith)
  calc
    _ ≤ ‖expSumF γ t (N / 2)‖ + 2 := PhaseInterval446.phase_interval_norm_le γ t N
    _ ≤ (|B| + 1) * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) + 2 :=
      by linarith [hsum']
    _ ≤ _ := hd κ hκ hκsmall N hNd

/-- P0082 page366 before display27. The distant contribution follows from
the phase estimate and the proved weighted energy. CONDITIONAL ON h10. -/
theorem far_moment_of_karacuba (h10 : Lemma10) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          farMoment γ δ κ N ≤
            B * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
  obtain ⟨δ₀, hδ₀, hphase⟩ := far_phase_of_karacuba h10 γ h1 h2
  obtain ⟨Ce, hCe, he⟩ := Energy446.leaf_weighted_energy_supplied
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hphase⟩ := hphase δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Cs, hCs, Ns, hs⟩ := hphase κ hκ hκsmall
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨Cs * Ce ^ 2, by positivity, max 2 (max Ns Np), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsN := hs N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hX2, _, hΔ, hΔ1, _⟩ := hp N
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  have henergy := he (F γ N ^ (6 * δ)) (F γ N)
    (calE γ κ N ^ (-(1 / 8 : ℝ))) (by positivity) hX2 hΔ hΔ1
  have hlocal := Localization446.leaf_far_localization_supplied γ δ κ N
    (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) (by positivity) hΔ1
    (fun α hα β hβ hdist => by
      apply hsN (β - α)
      · simpa only [abs_sub_comm] using hdist
      · have ha := hα.2
        have hb := hβ.2
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
  have hI : 0 ≤ ∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
        (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hratio : calE γ κ N ^ (-(3 / 2 : ℝ)) /
      (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 = calE γ κ N ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_sub hE]
    norm_num
  calc
    _ ≤ (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) *
        (Ce * F γ N * Real.log (F γ N) / calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 :=
      hlocal.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI henergy 2) (by positivity))
    _ = (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 *
        (calE γ κ N ^ (-(3 / 2 : ℝ)) / (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2) := by ring
    _ ≤ (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
      rw [hratio]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)) (by positivity)

/-- P0082 page366 after display27. One twelfth of the common scale absorbs
the two logarithms. This is a scalar consequence of the existing quarter estimate. -/
theorem log_F_sq_le_calE_twelfth (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 2 ≤ calE γ κ N ^ (1 / 12 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := log_F_sq_le_calE_quarter γ (κ / 3) h1 h2 (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  convert hN₀ N hN using 1
  simp only [calE, ← Real.exp_mul]
  congr 1
  ring

/-- P0082 pages365 and366 displays25 to27. The full truncated second moment
uses the proved nearby moment and expansion. CONDITIONAL ON h10. -/
theorem truncated_moment_of_karacuba (h10 : Lemma10) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) := by
  obtain ⟨δf, hδf, hf⟩ := far_moment_of_karacuba h10 γ h1 h2
  obtain ⟨δn, hδn, hn⟩ := MomentSupply446.near_moment_supplied γ h1 h2
  refine ⟨min δf δn, lt_min hδf hδn, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hf⟩ := hf δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bf, hBf, Nf, hf⟩ := hf κ hκ hκsmall
  obtain ⟨Bn, hBn, Nn, hn⟩ := hn δ hδ (hδsmall.trans_le (min_le_right _ _)) κ hκ
  obtain ⟨Nl, hl⟩ := log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  obtain ⟨Np, hp⟩ := calE_power_le_F_power γ κ (11 / 12) (2 * δ) h1 (by positivity)
  refine ⟨Bf + Bn, add_pos hBf hBn, max 16 (max (max Nf Nn) (max Nl Np)), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNN := (le_max_right _ _).trans hN
  have hNf : Nf ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNN)
  have hNn : Nn ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNN)
  have hNl : Nl ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNN)
  have hNp : Np ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNN)
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hfar : farMoment γ δ κ N ≤
      Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) := by
    calc
      _ ≤ Bf * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := hf N hNf
      _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (1 / 12 : ℝ) * calE γ κ N ^ (-1 : ℝ) := by
        gcongr
        exact hl N hNl
      _ = _ := by
        rw [mul_assoc (Bf * N * F γ N ^ 2), ← Real.rpow_add hE]
        norm_num
  have hbase : F γ N ^ (2 - 2 * δ) ≤ F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) := by
    rw [Real.rpow_sub hX, Real.rpow_two, Real.rpow_neg hE.le]
    change F γ N ^ 2 / F γ N ^ (2 * δ) ≤ F γ N ^ 2 / calE γ κ N ^ (11 / 12 : ℝ)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hE _) (hp N hNp)
  have hnear : nearMoment γ δ κ N ≤
      Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) := by
    calc
      _ ≤ Bn * N * F γ N ^ (2 - 2 * δ) := hn N hNn
      _ ≤ Bn * N * (F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖truncatedMinor γ δ κ N n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Decomp371a.window_subset_Ioc γ h1 N hN16)
        (fun n _ _ => sq_nonneg _)
    _ ≤ farMoment γ δ κ N + nearMoment γ δ κ N := MomentSplit428.leaf_moment_split_supplied γ δ κ N
    _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) +
        Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) := add_le_add hfar hnear
    _ = _ := by ring

/-- P0082 page366 after display27. The printed minus one quarter exceptional bound follows from the explicit Karacuba input. CONDITIONAL ON h10. -/
theorem minor_quarter_of_karacuba (h10 : Lemma10) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hm⟩ := truncated_moment_of_karacuba h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, Nm, hm⟩ := hm κ hκ hκsmall
  obtain ⟨Nt, ht⟩ := TailSupply385.leaf_tail_supplied γ h1 h2 δ κ hδ hκ
  refine ⟨4 * B, by positivity, max Nm Nt, fun N hN => ?_⟩
  have hNm : Nm ≤ N := (le_max_left _ _).trans hN
  have hNt : Nt ≤ N := (le_max_right _ _).trans hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hT : 0 < F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_pos hX (Real.rpow_pos_of_pos hE _)
  have hc := count_of_tail_and_moment (window γ N)
    (minorInt γ δ κ N) (truncatedMinor γ δ κ N)
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)))
    (B * N * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)))
    hT (fun n _ => ht N hNt n) (hm N hNm)
  change (Eγ_minor_block γ δ κ N : ℝ) *
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 ≤ _ at hc
  have hp : calE γ κ N ^ (-(11 / 12 : ℝ)) =
      calE γ κ N ^ (-(1 / 4 : ℝ)) * (calE γ κ N ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hfactor : B * (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(11 / 12 : ℝ)) =
      (4 * B * N * calE γ κ N ^ (-(1 / 4 : ℝ))) *
        (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 := by
    rw [hp]
    ring
  rw [hfactor] at hc
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp hc

/-- P0082 page366 after display27. The printed minus one quarter saving
implies the exact sealed leaf_minor_bound conclusion. CONDITIONAL ON h10. -/
theorem minor_bound_of_karacuba (h10 : Lemma10) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hb⟩ := minor_quarter_of_karacuba h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hb⟩ := hb δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, N₀, hb⟩ := hb κ hκ hκsmall
  refine ⟨B, hB, max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  exact (hb N ((le_max_right _ _).trans hN)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE (by norm_num)) (by positivity))

end LeanLab.ExceptionalSet.Decomp467a

/-
An unconditional bridge for the trivial-arc input in P0079 page 10, Section 5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.PrimeTail418
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5, the final X divided by log X estimate.
The exact statement of trivial_moment353 follows from the proved periodic tail. -/
theorem trivial_moment418 (s : ℕ) (l : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (hl : l ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l η ε X α) ≤
        C * X / log X := by
  let a : ℝ := 1 / (2 * log 2)
  let K : ℝ := (4 / Real.pi ^ 2) * log 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  refine ⟨K / a ^ 2, by positivity, ?_⟩
  filter_upwards [trivial_eventually_tail353 s μ ε hmass hε,
    (cutoff_tendsto353 s μ ε hmass hε).eventually
      (eventually_ge_atTop (max 1 (1 / |l|))),
    cutoff_log_lower293 s μ ε hmass hε,
    eventually_ge_atTop (2 : ℝ)] with X ht hL hlogL hX
  have hL1 : 1 ≤ cutoff293 s μ ε X := (le_max_left _ _).trans hL
  have hLl : 1 / |l| ≤ cutoff293 s μ ε X := (le_max_right _ _).trans hL
  have hL0 : 0 < cutoff293 s μ ε X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have hR : 1 / |l| ≤ (cutoff293 s μ ε X) ^ 2 := by nlinarith
  rw [ht]
  calc
    _ ≤ (4 / Real.pi ^ 2) * (log 4 * X * log X) / (cutoff293 s μ ε X) ^ 2 :=
      primeMoment_tail418 l ε X η _ hl hX hR
    _ = K * X * log X / (cutoff293 s μ ε X) ^ 2 := by dsimp [K]; ring
    _ ≤ (K / a ^ 2) * X / log X := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hlog).mpr
      have hpow : (a * log X) ^ 2 ≤ (cutoff293 s μ ε X) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlogL 2
      calc
        K * X * log X * log X = (K / a ^ 2 * X) * (a * log X) ^ 2 := by
          field_simp
        _ ≤ (K / a ^ 2 * X) * (cutoff293 s μ ε X) ^ 2 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)

/-- P0079 page 10, Section 5 and display 17. The periodic moment input is proved in trivial_moment418.
The exact trivial target follows from the second moments and logarithmic growth. -/
theorem trivial_small418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * X * (cutoff293 s μ ε X) ^ s := by
  obtain ⟨C1, hC1, H1⟩ := trivial_moment418 s l1 μ η ε hs h1 hμ hη hε hε'
  obtain ⟨C2, hC2, H2⟩ := trivial_moment418 s l2 μ η ε hs h2 hμ hη hε hε'
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  intro δ hδ
  have Hlog := tendsto_log_atTop.eventually
    (eventually_ge_atTop ((C1 + C2) / (2 * δ)))
  filter_upwards [H1, H2, Hlog, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hm1 hm2 hlogbound hX hmassX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hmass
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hmassX)
  have hlog : 0 < log X := log_pos (by linarith)
  have hmean : (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l1 η ε X α) +
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l2 η ε X α) ≤ 2 * δ * X := by
    calc
      _ ≤ C1 * X / log X + C2 * X / log X := add_le_add hm1 hm2
      _ = ((C1 + C2) / log X) * X := by ring
      _ ≤ (2 * δ) * X := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply (div_le_iff₀ hlog).mpr
        have H := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp hlogbound
        nlinarith only [H]
  calc
    _ ≤ (cutoff293 s μ ε X) ^ s / 2 *
        ((∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l1 η ε X α) +
          (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l2 η ε X α)) :=
      trivial_reduction353 s l1 l2 μ γ η ε X hL
    _ ≤ (cutoff293 s μ ε X) ^ s / 2 * (2 * δ * X) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

end LeanLab.LZPowersOfTwo

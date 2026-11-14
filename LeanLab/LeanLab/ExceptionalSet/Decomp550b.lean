import LeanLab.ExceptionalSet.Decomp550a
import LeanLab.ExceptionalSet.Decomp523a
import LeanLab.ExceptionalSet.Decomp524a

/-!
P0082 pages 359 and 364 to 365. Boundary supplies using the explicit grid majorant.
Source: https://doi.org/10.5802/aif.1621
The majorant is proved in Decomp550a. Cancellation remains a separate existing input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp550b
open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Decomp523a

/-- P0082 page 359 Lemma 4, derived finite upper count.
The finite grid construction supplies the majorant with clean axioms. -/
theorem erdos_turan_supplied :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (f : ℕ → ℝ) (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      (((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)) ≤
        C * ((b - a) * s.card + (s.card : ℝ) / (H + 1) +
          ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖) := by
  obtain ⟨C, hC, hm⟩ := Decomp550a.one_sided_majorant_supplied
  refine ⟨C, hC, fun s f a b H ha hab hb hH => ?_⟩
  obtain ⟨c₀, c, hc₀, hc, hmajor⟩ := hm a b H ha hab hb hH
  exact finite_count_of_majorant s f a b C c₀ H c hc₀ hc hmajor

/-- P0082 page 359 Lemma 4 and page 365 boundary width.
The finite upper count is clean. This assembly is CONDITIONAL ON
the explicit Theorem2 hypothesis. No admitted discrepancy estimate is used. -/
theorem dyadic_band_bound_supplied (hT : U1539.Theorem2) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
          b - a ≤ calE γ κ N ^ (-(1 / 8 : ℝ)) →
          (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b)).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨C, hC, hET⟩ := erdos_turan_supplied
  let δ : ℝ := min ((γ - 1) / 48) (1 / 24)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ < min ((γ - 1) / 24) (1 / 12) := by
    have hleft : δ ≤ (γ - 1) / 48 := min_le_left _ _
    have hright : δ ≤ 1 / 24 := min_le_right _ _
    exact lt_min (by linarith) (by linarith)
  obtain ⟨η, A, hη, hA, Nη, hNη⟩ :=
    Decomp524a.integer_frequency_decay524 hT γ δ h1 h2 hδ hδsmall
  refine ⟨min 1 (4 * η), lt_min (by norm_num) (by positivity),
    fun κ hκ hκcap => ?_⟩
  have hκC : κ ≤ 1 := hκcap.trans (min_le_left _ _)
  have hκη : κ ≤ 4 * η := hκcap.trans (min_le_right _ _)
  obtain ⟨NF, hNF⟩ := Decomp524a.cutoff_frequency_range524 γ (6 * δ) h1 (by positivity)
  refine ⟨C * (2 + 2 * A), by positivity, max 16 (max Nη NF), le_max_left _ _,
    fun N hN a b ha hab hb hlen => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNη' : Nη ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNF' : NF ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let w : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let H : ℕ := ⌈w⁻¹⌉₊
  obtain ⟨hδw, hδ1⟩ := delta_bounds γ κ N hκ hlog
  obtain ⟨hH1, _, hH, hinv⟩ := cutoff_bounds w hδw hδ1
  have hfreq (h : ℕ) (hh : h ∈ Finset.range H) :
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (((h : ℝ) + 1) * F γ n)‖ ≤ A * N * w ^ 2 := by
    have hhH : h + 1 ≤ H := by have := Finset.mem_range.mp hh; omega
    have hcut : (H : ℝ) ≤ F γ N ^ (6 * δ) := by
      have hid : (calE γ κ N ^ (-(1 / 8 : ℝ)))⁻¹ =
          Real.exp (κ / 8 * Real.log N ^ (3 - 2 * γ)) := by
        rw [delta_exp, ← Real.exp_neg]
        congr 1
        ring
      dsimp [H, w]
      rw [hid]
      exact hNF N hNF' κ hκ.le hκC
    have hhF : ((h + 1 : ℕ) : ℝ) ≤ F γ N ^ (6 * δ) :=
      (by exact_mod_cast hhH : ((h + 1 : ℕ) : ℝ) ≤ (H : ℝ)).trans hcut
    have he := hNη N hNη' (h + 1) (by omega) hhF
    simp only [Nat.cast_add, Nat.cast_one] at he
    exact he.trans (decay_to_delta_sq γ κ η A N hκη hA.le hlog)
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ N := by
    rw [Nat.card_Ioc]
    exact_mod_cast (Nat.sub_le N (N / 2))
  exact count_of_fourier_bound (Finset.Ioc (N / 2) N) (fun n => F γ n)
    a b w A C N H hδw hA.le hC.le hcard hlen (sub_nonneg.mpr hab) hH hinv hfreq
    (hET _ _ a b H ha hab hb hH1)


/-- P0082 page 364 display 23 and page 365 boundary width.
Exact supply for leaf_boundary_outer_low.
CONDITIONAL ON U1539.lemma10 through theorem2_via_karacuba. The majorant is clean. -/
theorem leaf_boundary_outer_low_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ₀, hκ₀, hs⟩ := dyadic_band_bound_supplied U1539.theorem2_via_karacuba γ h1 h2
  refine ⟨κ₀, hκ₀, fun κ hκ hκcap => ?_⟩
  obtain ⟨B, hB, N₀, hN₀, hb⟩ := hs κ hκ hκcap
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := hN₀.trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  obtain ⟨hΔ, hΔ1⟩ := delta_bounds γ κ N hκ hlog
  have hc := hb N hN 0 (Δ / 2) (by norm_num) (by positivity) (by linarith) (by dsimp [Δ] at *; linarith)
  have hsub : (window γ N).filter (fun n : ℕ => Int.fract (F γ n) < Δ / 2) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < (Δ / 2)) := by
    intro n hn
    obtain ⟨hnW, hband⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ h1 N hN16 hnW, ⟨Int.fract_nonneg _, hband⟩⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hc

/-- P0082 page 364 display 23 and page 365 boundary width.
Exact supply for leaf_boundary_inner_low.
CONDITIONAL ON U1539.lemma10 through theorem2_via_karacuba. The majorant is clean. -/
theorem leaf_boundary_inner_low_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ₀, hκ₀, hs⟩ := dyadic_band_bound_supplied U1539.theorem2_via_karacuba γ h1 h2
  refine ⟨κ₀, hκ₀, fun κ hκ hκcap => ?_⟩
  obtain ⟨B, hB, N₀, hN₀, hb⟩ := hs κ hκ hκcap
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := hN₀.trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  obtain ⟨hΔ, hΔ1⟩ := delta_bounds γ κ N hκ hlog
  have hc := hb N hN (Δ / 2) Δ (by positivity) (by linarith) hΔ1 (by dsimp [Δ] at *; linarith)
  have hsub : (window γ N).filter (fun n : ℕ => Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        (Δ / 2) ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ) := by
    intro n hn
    obtain ⟨hnW, hband⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ h1 N hN16 hnW, hband⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hc

/-- P0082 page 364 display 23 and page 365 boundary width.
Exact supply for leaf_boundary_inner_high.
CONDITIONAL ON U1539.lemma10 through theorem2_via_karacuba. The majorant is clean. -/
theorem leaf_boundary_inner_high_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ₀, hκ₀, hs⟩ := dyadic_band_bound_supplied U1539.theorem2_via_karacuba γ h1 h2
  refine ⟨κ₀, hκ₀, fun κ hκ hκcap => ?_⟩
  obtain ⟨B, hB, N₀, hN₀, hb⟩ := hs κ hκ hκcap
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := hN₀.trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  obtain ⟨hΔ, hΔ1⟩ := delta_bounds γ κ N hκ hlog
  have hc := hb N hN (1 - Δ) 1 (by linarith) (by linarith) le_rfl (by dsimp [Δ]; ring_nf; exact le_rfl)
  have hsub : (window γ N).filter (fun n : ℕ => 1 - Δ < Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ / 2) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        (1 - Δ) ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) := by
    intro n hn
    obtain ⟨hnW, hband⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ h1 N hN16 hnW, ⟨hband.1.le, Int.fract_lt_one _⟩⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hc

/-- P0082 page 364 display 23 and page 365 boundary width.
Exact supply for leaf_boundary_outer_high.
CONDITIONAL ON U1539.lemma10 through theorem2_via_karacuba. The majorant is clean. -/
theorem leaf_boundary_outer_high_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κ₀, hκ₀, hs⟩ := dyadic_band_bound_supplied U1539.theorem2_via_karacuba γ h1 h2
  refine ⟨κ₀, hκ₀, fun κ hκ hκcap => ?_⟩
  obtain ⟨B, hB, N₀, hN₀, hb⟩ := hs κ hκ hκcap
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := hN₀.trans hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let Δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  obtain ⟨hΔ, hΔ1⟩ := delta_bounds γ κ N hκ hlog
  have hc := hb N hN (1 - Δ / 2) 1 (by linarith) (by linarith) le_rfl (by dsimp [Δ] at *; linarith)
  have hsub : (window γ N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n)) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        (1 - Δ / 2) ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) := by
    intro n hn
    obtain ⟨hnW, hband⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ h1 N hN16 hnW, ⟨hband.le, Int.fract_lt_one _⟩⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hc

end LeanLab.ExceptionalSet.Decomp550b

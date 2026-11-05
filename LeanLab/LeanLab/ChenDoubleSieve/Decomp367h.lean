import LeanLab.ChenDoubleSieve.Decomp367b

/-!
Moving upper endpoints for the one dimensional prime reciprocal mass.
Source: https://arxiv.org/pdf/0705.1652, page 39 prime sum replacement.
This is a derived preparation lemma, not the two dimensional F5 limit.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task348

/-- Enlarging an exponent interval increases its prime reciprocal mass. -/
theorem powerPrimeMass_mono {N : ℕ} (hN : 1 ≤ N) {a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    powerPrimeMass a₂ b₁ N ≤ powerPrimeMass a₁ b₂ N := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    obtain ⟨hlo, hup⟩ := Finset.mem_Ioc.mp hpI
    have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨lt_of_le_of_lt (Nat.floor_mono (rpow_le_rpow_of_exponent_le hbase ha)) hlo,
        hup.trans (Nat.floor_mono (rpow_le_rpow_of_exponent_le hbase hb))⟩, hprime⟩
  · intros
    positivity

/-- A convergent moving upper exponent has the same one dimensional mass limit.
The index can follow any filter tending to infinity. -/
theorem powerPrimeMass_moving_upper {ι : Type*} {l : Filter ι}
    {n : ι → ℕ} (hn : Tendsto n l atTop) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {v : ι → ℝ} (hv : Tendsto v l (𝓝 b)) :
    Tendsto (fun i => powerPrimeMass a (v i) (n i)) l (𝓝 (log (b / a))) := by
  have hb : 0 < b := ha.trans hab
  apply tendsto_order.2
  constructor
  · intro c hc
    have hexp : a * exp c < b := by
      have he := (lt_log_iff_exp_lt (div_pos hb ha)).1 hc
      have he' := (lt_div_iff₀ ha).1 he
      nlinarith
    let t : ℝ := (max a (a * exp c) + b) / 2
    have hmax : max a (a * exp c) < b := max_lt hab hexp
    have hat : a ≤ t := by dsimp [t]; linarith [le_max_left a (a * exp c)]
    have htb : t < b := by dsimp [t]; linarith
    have hct : c < log (t / a) := by
      apply (lt_log_iff_exp_lt (div_pos (ha.trans_le hat) ha)).2
      apply (lt_div_iff₀ ha).2
      dsimp [t]
      nlinarith [le_max_right a (a * exp c)]
    have hm := ((powerPrimeMass_tendsto ha hat).comp hn).eventually (eventually_gt_nhds hct)
    filter_upwards [hn.eventually_ge_atTop 1, hv.eventually (eventually_gt_nhds htb), hm]
      with i hi hv' hm'
    exact hm'.trans_le (powerPrimeMass_mono hi (le_refl a) hv'.le)
  · intro c hc
    have hexp : b < a * exp c := by
      have he := (log_lt_iff_lt_exp (div_pos hb ha)).1 hc
      have he' := (div_lt_iff₀ ha).1 he
      nlinarith
    let t : ℝ := (b + a * exp c) / 2
    have hbt : b < t := by dsimp [t]; linarith
    have hat : a ≤ t := hab.le.trans hbt.le
    have htc : log (t / a) < c := by
      apply (log_lt_iff_lt_exp (div_pos (ha.trans_le hat) ha)).2
      apply (div_lt_iff₀ ha).2
      dsimp [t]
      nlinarith
    have hm := ((powerPrimeMass_tendsto ha hat).comp hn).eventually (eventually_lt_nhds htc)
    filter_upwards [hn.eventually_ge_atTop 1, hv.eventually (eventually_lt_nhds hbt), hm]
      with i hi hv' hm'
    exact (powerPrimeMass_mono hi (le_refl a) hv'.le).trans_lt hm'

end LeanLab.ChenDoubleSieve.Task367

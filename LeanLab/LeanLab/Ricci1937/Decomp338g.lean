import LeanLab.Ricci1937.Decomp338f

/-!
Ricci 1937, uniform greedy finite main sum.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary uniform greedy head comparison for second memoir page 111 formula 28.11.
The varying gap sequence limit supplies one top threshold for all even gaps. -/
lemma decomp338_greedy_head_uniform (Y : ℕ) :
    ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t → (0.04 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily t (decomp338GreedyCutoff h Y t) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (decomp338GreedyCutoff h Y t 19) t).filter Nat.Prime, (1 - nuN h p)) := by
  by_contra hbad
  push_neg at hbad
  choose h t heven hge hfail using hbad
  have ht : Tendsto t atTop atTop := tendsto_atTop_mono hge tendsto_id
  have hh := decomp338_greedy_normalized_head h t heven ht Y
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  have hhN := hN N le_rfl
  have hfN := hfail N
  linarith

/-- Auxiliary canonical cumulative mass budget for second memoir pages 99 and 109.
The printed greedy block upper masses imply the exact cumulative printed budget. -/
lemma decomp338_greedy_cumulative_budget (h Y t : ℕ) (hYt : Y ≤ t) (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ (Ioc (decomp338GreedyCutoff h Y t n) t).filter Nat.Prime, nuN h p) ≤
      ((n + 1 : ℕ) : ℝ) / 2 + 0.48 := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  let e : ℕ → ℕ := fun i => match i with
    | 0 => t
    | j + 1 => c j
  have he : Antitone e := by
    apply antitone_nat_of_succ_le
    intro i
    cases i with
    | zero => exact hw
    | succ i => exact hc (by omega : i ≤ i + 1)
  apply decomp338_cumulative_mass_budget h e he (n + 1) (by omega)
  intro i hi
  cases i with
  | zero => exact (decomp338_greedy_step_bounds h Y t 0 hYt).2.2
  | succ i => exact (decomp338_greedy_step_bounds h Y (c i) (i + 1) (hlo i)).2.2

/-- Supply proof of the finite positive main sum piece.
Second memoir page 99 formula 18.3, page 111 formula 28.11 and page 112 formula 30.2.
This is a density statement and contains no integer count. -/
theorem decomp338_greedy_main_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ a : ℝ, 0 < a ∧ ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t →
        a * (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) ≤
          ∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
            ∀ j ∈ range (t + 1),
              (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1),
            (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  refine ⟨100, by norm_num, ?_⟩
  intro Y hY
  obtain ⟨T, hT⟩ := decomp338_greedy_head_uniform Y
  refine ⟨0.02, by norm_num, max T (max Y 19), ?_⟩
  intro h t heven ht
  have hYt : Y ≤ t := by omega
  have ht19 : 19 ≤ t := by omega
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  have hmass : ∀ i < t - 19,
      (∑ p ∈ (Ioc (c (19 + i + 1)) t).filter Nat.Prime, nuN h p) ≤
        (((19 + i + 2 : ℕ) : ℝ) + 1) / 2 := by
    intro i hi
    have hh := decomp338_greedy_cumulative_budget h Y t hYt (19 + i + 1) (by omega)
    have heq : (19 + i + 1 + 1 : ℕ) = 19 + i + 2 := by omega
    rw [heq] at hh
    change (∑ p ∈ (Ioc (c (19 + i + 1)) t).filter Nat.Prime, nuN h p) ≤ _ at hh
    linarith
  have hhead := hT h t heven (by omega)
  have hpos := decomp338_pair_normalized_positive h t heven c hc hw (t - 19) Y hY
    (hlo (19 + (t - 19))) hmass hhead
  rw [show 19 + (t - 19) = t by omega] at hpos
  let E := ∑ S ∈ decomp305PrimeFamily t c t, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
  let D := ∏ p ∈ (Ioc (c t) t).filter Nat.Prime, (1 - nuN h p)
  let z := ∏ p ∈ Nat.primesLE (c t), (1 - nuN h p)
  have hD : 0 < D := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  change (0.02 : ℝ) ≤ E / D at hpos
  have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hD).mp hpos)
    (show 0 ≤ z from prod_nonneg (fun p hp =>
      (sub_pos.mpr (nuN_lt_one heven (Nat.mem_primesLE.mp hp).2)).le))
  have hct : c t ≤ t := (hc (Nat.zero_le t)).trans hw
  have hcomplete := decomp305_prime_family_complete (nuN h) t c hc t hct
  change (∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) = E * z at hcomplete
  have hsets : Nat.primesLE t = (Ioc (c t) t).filter Nat.Prime ∪ Nat.primesLE (c t) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpt, hprime⟩ := Nat.mem_primesLE.mp hp
      by_cases hpc : p ≤ c t
      · exact mem_union.mpr (Or.inr (Nat.mem_primesLE.mpr ⟨hpc, hprime⟩))
      · exact mem_union.mpr (Or.inl (mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨by omega, hpt⟩, hprime⟩))
    · intro hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hpI).2, hprime⟩
      · obtain ⟨hpc, hprime⟩ := Nat.mem_primesLE.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpc.trans hct, hprime⟩
  have hdisj : Disjoint ((Ioc (c t) t).filter Nat.Prime) (Nat.primesLE (c t)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hq' := (Nat.mem_primesLE.mp hq).1
    omega
  have hprod : (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) = D * z := by
    rw [hsets, prod_union hdisj]
  rw [hcomplete, hprod]
  nlinarith

end
end LeanLab.Ricci1937

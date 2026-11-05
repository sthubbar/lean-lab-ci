import LeanLab.ChenDoubleSieve.Decomp348j
import LeanLab.ChenDoubleSieve.Decomp348l

/-!
Bounded reciprocal pair mass for Wu 2004 page 39 equation 10.5.
The one dimensional prime mass limit is already proved in Decomp348j.
These helpers do not assume the OPEN two dimensional integral limit.
Source: https://arxiv.org/pdf/0705.1652, page 39.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348

/-- A rectangle of reciprocal prime masses has the product limit.
This is an elementary precursor to the moving triangular domain. -/
theorem prime_rectangle_mass_tendsto {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun N : ℕ => pairMass
      (((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime) ×ˢ
       ((Finset.Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ d⌋₊).filter Nat.Prime)))
      atTop (𝓝 (log (b / a) * log (d / c))) := by
  simpa only [pairMass_product, powerPrimeMass] using
    (powerPrimeMass_tendsto ha hab).mul (powerPrimeMass_tendsto hc hcd)

/-- Every prime in the actual lower band lies in a wider power interval.
The strict lower endpoint avoids a floor equality exception. -/
theorem lowerPrimeBand_subset_power {N : ℕ} (hN : 2 ≤ N) :
    lowerPrimeBand N ⊆
      (Finset.Ioc ⌊(N : ℝ) ^ (kappa1 / 2)⌋₊ ⌊(N : ℝ) ^ (1 : ℝ)⌋₊).filter Nat.Prime := by
  intro p hp
  obtain ⟨hprime, hlow, hup⟩ := lowerPrimeBand_range N p hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ) ^ (kappa1 / 2) < (N : ℝ) ^ kappa1 :=
    rpow_lt_rpow_of_exponent_lt hNgt (by norm_num [kappa1])
  apply mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime⟩
  · exact (Nat.floor_lt (rpow_nonneg hNpos.le _)).2 (hpow.trans_le hlow)
  · simpa only [rpow_one, Nat.floor_natCast] using hup

/-- The single prime band has uniformly bounded reciprocal mass. -/
theorem lowerPrimeBand_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → (∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ)) ≤ K := by
  have ht := powerPrimeMass_tendsto (a := kappa1 / 2) (b := 1)
    (by norm_num [kappa1]) (by norm_num [kappa1])
  have hc : 0 ≤ log (1 / (kappa1 / 2)) :=
    log_nonneg (by norm_num [kappa1])
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (ht.eventually (eventually_lt_nhds (show log (1 / (kappa1 / 2)) <
      log (1 / (kappa1 / 2)) + 1 by linarith)))
  refine ⟨log (1 / (kappa1 / 2)) + 1, by linarith, max 2 M, ?_⟩
  intro N hN
  calc
    _ ≤ powerPrimeMass (kappa1 / 2) 1 N :=
      sum_le_sum_of_subset_of_nonneg (lowerPrimeBand_subset_power (by omega))
        (by intros; positivity)
    _ ≤ _ := (hM N (by omega)).le

/-- The full F5 reciprocal pair mass is bounded independently of N. -/
theorem fullPairs5_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → pairMass (fullPairs5 N) ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := lowerPrimeBand_mass_bounded
  refine ⟨K ^ 2, sq_pos_of_pos hK, max 1 M, ?_⟩
  intro N hN
  calc
    _ ≤ pairMass (lowerPrimeBand N ×ˢ lowerPrimeBand N) :=
      pairMass_mono (fullPairs5_subset (by omega))
    _ = (∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ)) *
        (∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ)) := pairMass_product _ _
    _ ≤ K * K := mul_le_mul (hM N (by omega)) (hM N (by omega))
      (sum_nonneg (by intros; positivity)) hK.le
    _ = K ^ 2 := by ring

end LeanLab.ChenDoubleSieve.Task367

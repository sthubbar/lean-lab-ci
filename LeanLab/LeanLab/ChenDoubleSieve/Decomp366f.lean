import LeanLab.ChenDoubleSieve.Decomp366d

/-!
Exact endpoint control for the one dimensional F4 band mass.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The existing power interval Mertens limit supplies the interior mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- Changing each end of a finite reciprocal interval by at most one endpoint
costs at most the reciprocal lower cutoff. -/
theorem reciprocal_endpoint_difference (S T : Finset ℕ) {z : ℝ} (hz : 0 < z) (a b : ℕ)
    (hST : S \ T ⊆ {a}) (hTS : T \ S ⊆ {b})
    (hS : ∀ p ∈ S, z ≤ (p : ℝ)) (hT : ∀ p ∈ T, z ≤ (p : ℝ)) :
    |(∑ p ∈ S, 1 / (p : ℝ)) - ∑ p ∈ T, 1 / (p : ℝ)| ≤ 1 / z := by
  have hcardS : (S \ T).card ≤ 1 := by
    simpa using Finset.card_le_card hST
  have hcardT : (T \ S).card ≤ 1 := by
    simpa using Finset.card_le_card hTS
  have hsumS : (∑ p ∈ S \ T, 1 / (p : ℝ)) ≤ 1 / z := by
    calc
      _ ≤ (S \ T).card • (1 / z) := sum_le_card_nsmul _ _ _ (by
        intro p hp
        exact one_div_le_one_div_of_le hz (hS p (mem_sdiff.mp hp).1))
      _ ≤ 1 • (1 / z) := nsmul_le_nsmul_left (by positivity) hcardS
      _ = _ := one_nsmul _
  have hsumT : (∑ p ∈ T \ S, 1 / (p : ℝ)) ≤ 1 / z := by
    calc
      _ ≤ (T \ S).card • (1 / z) := sum_le_card_nsmul _ _ _ (by
        intro p hp
        exact one_div_le_one_div_of_le hz (hT p (mem_sdiff.mp hp).1))
      _ ≤ 1 • (1 / z) := nsmul_le_nsmul_left (by positivity) hcardT
      _ = _ := one_nsmul _
  have hs := sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) (inter_subset_left (s₁ := S) (s₂ := T))
  have ht := sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) (inter_subset_left (s₁ := T) (s₂ := S))
  have hi : T ∩ S = S ∩ T := inter_comm _ _
  have heS : S \ (S ∩ T) = S \ T := by ext p; simp
  have heT : T \ (T ∩ S) = T \ S := by ext p; simp
  rw [heS] at hs
  rw [heT] at ht
  rw [hi] at ht
  have hnS : 0 ≤ ∑ p ∈ S \ T, 1 / (p : ℝ) := sum_nonneg (by intros; positivity)
  have hnT : 0 ≤ ∑ p ∈ T \ S, 1 / (p : ℝ) := sum_nonneg (by intros; positivity)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The closed open real prime interval and the floored open closed interval
differ by at most the reciprocal positive lower endpoint. -/
theorem prime_interval_endpoint_difference {N : ℕ} {x y : ℝ} (hx : 0 < x) (hy : y ≤ N) :
    |(∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ x ≤ (p : ℝ) ∧ (p : ℝ) < y),
      1 / (p : ℝ)) -
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1 / (p : ℝ)| ≤ 1 / x := by
  let S := (Finset.range N).filter (fun p : ℕ => p.Prime ∧ x ≤ (p : ℝ) ∧ (p : ℝ) < y)
  let T := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime
  have hST : S \ T ⊆ {⌊x⌋₊} := by
    intro p hp
    obtain ⟨hpS, hpT⟩ := mem_sdiff.mp hp
    obtain ⟨hpN, hprime, hpx, hpy⟩ := mem_filter.mp hpS
    have hpyle : p ≤ ⌊y⌋₊ := Nat.le_floor hpy.le
    have hpxle : p ≤ ⌊x⌋₊ := by
      by_contra hh
      apply hpT
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpyle⟩, hprime⟩
    have hxle : ⌊x⌋₊ ≤ p := by
      exact_mod_cast (Nat.floor_le hx.le).trans hpx
    simpa only [Finset.mem_singleton] using le_antisymm hpxle hxle
  have hTS : T \ S ⊆ {⌊y⌋₊} := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := mem_sdiff.mp hp
    obtain ⟨hI, hprime⟩ := mem_filter.mp hpT
    obtain ⟨hpx, hpy⟩ := mem_Ioc.mp hI
    have hxlt : x < (p : ℝ) := by
      have hh := Nat.lt_floor_add_one x
      have hpcast : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast (show ⌊x⌋₊ + 1 ≤ p by omega)
      linarith
    have hpeq : p = ⌊y⌋₊ := by
      by_contra hh
      have hpylt : p < ⌊y⌋₊ := by omega
      have hpyR : (p : ℝ) < y := Nat.lt_of_lt_floor hpylt
      apply hpS
      apply mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, hprime, hxlt.le, hpyR⟩
      exact_mod_cast hpyR.trans_le hy
    simpa only [Finset.mem_singleton] using hpeq
  have hS : ∀ p ∈ S, x ≤ (p : ℝ) := by
    intro p hp
    exact (mem_filter.mp hp).2.2.1
  have hT : ∀ p ∈ T, x ≤ (p : ℝ) := by
    intro p hp
    have hl := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hh := Nat.lt_floor_add_one x
    have hc : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast (show ⌊x⌋₊ + 1 ≤ p by omega)
    linarith
  exact reciprocal_endpoint_difference S T hx ⌊x⌋₊ ⌊y⌋₊ hST hTS hS hT

/-- The exact F4 band differs negligibly from the existing floored power band. -/
theorem primeBand4_mass_error {N : ℕ} (hN : 2 ≤ N) :
    |(∑ p ∈ primeBand4 N, 1 / (p : ℝ)) - powerPrimeMass kappa1 kappa2 N| ≤
      1 / (N : ℝ) ^ kappa1 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hup : (N : ℝ) ^ kappa2 ≤ N := by
    have hh := rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
      (by norm_num [kappa2] : kappa2 ≤ 1)
    simpa only [rpow_one] using hh
  have he : primeBand4 N = (Finset.range N).filter
      (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ kappa2) := by
    ext p
    simp only [primeBand4, lowerPrimeBand, mem_filter]
    tauto
  rw [he]
  exact prime_interval_endpoint_difference (rpow_pos_of_pos hpos _) hup

/-- The exact one dimensional F4 prime band has the logarithmic mass limit. -/
theorem primeBand4_mass_tendsto :
    Tendsto (fun N : ℕ => ∑ p ∈ primeBand4 N, 1 / (p : ℝ)) atTop
      (𝓝 (log (kappa2 / kappa1))) := by
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => (∑ p ∈ primeBand4 N, 1 / (p : ℝ)) -
      powerPrimeMass kappa1 kappa2 N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ (hz.const_div_atTop 1)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact primeBand4_mass_error hN
  have ht := he.add (powerPrimeMass_tendsto
    (by norm_num [kappa1] : 0 < kappa1) (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2))
  simpa only [zero_add, sub_add_cancel] using ht

/-- The unweighted ordered F4 prime triangle has half the squared logarithmic mass. -/
theorem fullPairs4_mass_tendsto :
    Tendsto (fun N : ℕ => pairMass (fullPairs4 N)) atTop
      (𝓝 (log (kappa2 / kappa1) ^ 2 / 2)) :=
  fullPairs4_mass_of_band primeBand4_mass_tendsto

end LeanLab.ChenDoubleSieve.Task366

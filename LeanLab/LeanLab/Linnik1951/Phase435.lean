/-
P0093 page 163 equations 7.10 and 7.11. Remove the common rotation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Repair493EntropyData

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 163 after equation 7.10. More than half of a finite
interval, with its endpoint allowance, contains an adjacent pair. -/
theorem adjacent_pair435 (M : ℕ) (S : Finset ℕ) (hS : S ⊆ range M)
    (hcard : M + 1 < 2 * S.card) : ∃ n : ℕ, n ∈ S ∧ n + 1 ∈ S := by
  classical
  by_contra h
  push_neg at h
  have hd : Disjoint S (S.image (fun n => n + 1)) := by
    apply Finset.disjoint_left.mpr
    intro m hm him
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp him
    exact h n hn hm
  have hsub : S ∪ S.image (fun n => n + 1) ⊆ range (M + 1) := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have := Finset.mem_range.mp (hS hm)
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have := Finset.mem_range.mp (hS hn)
      exact Finset.mem_range.mpr (by omega)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (add_left_injective 1), Finset.card_range] at hc
  omega

/-- P0093 page 163 the two displays after equation 7.10 and equation
7.11. If a set of dyadic phases clusters within rho of a common
rotation and contains an adjacent pair, all its phases lie within
four rho of integers. This uses no Fourier or measure estimate. -/
theorem rotation_removal435 (α φ ρ : ℝ) (S : Finset ℕ)
    (hcluster : ∀ m ∈ S, ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - φ - z| ≤ ρ)
    (n : ℕ) (hn : n ∈ S) (hn1 : n + 1 ∈ S) :
    ∀ m ∈ S, ∃ z : ℤ, |α * (2 : ℝ) ^ (m + 1) - z| ≤ 4 * ρ := by
  obtain ⟨a, ha⟩ := hcluster n hn
  obtain ⟨b, hb⟩ := hcluster (n + 1) hn1
  have hpow : α * (2 : ℝ) ^ (n + 1 + 1) = 2 * (α * (2 : ℝ) ^ (n + 1)) := by
    rw [pow_succ]
    ring
  rw [hpow] at hb
  have hφ : |φ - ((b - 2 * a : ℤ) : ℝ)| ≤ 3 * ρ := by
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    apply abs_le.mpr
    push_cast
    constructor <;> linarith
  intro m hm
  obtain ⟨c, hc⟩ := hcluster m hm
  refine ⟨c + (b - 2 * a), ?_⟩
  have hc' := abs_le.mp hc
  have hφ' := abs_le.mp hφ
  apply abs_le.mpr
  push_cast at *
  constructor <;> linarith

/-- P0093 page 163 equation 7.11. A common rotation cluster of
fraction at least one minus epsilon over two gives the required
near integer index count, once epsilon is below one half and M is
at least four. The radius is one quarter of the desired radius. -/
theorem cluster_to_near_indices435 (M r : ℕ) (hM : 4 ≤ M) (α φ ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (S : Finset ℕ)
    (hS : S ⊆ range M) (hc : (1 - ε / 2) * (M : ℝ) ≤ S.card)
    (hp : ∀ m ∈ S, ∃ z : ℤ,
      |α * (2 : ℝ) ^ (m + 1) - φ - z| ≤ (1 / 2 : ℝ) ^ r / 4) :
    (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card := by
  classical
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hcardR : (M : ℝ) + 1 < 2 * S.card := by nlinarith
  have hcard : M + 1 < 2 * S.card := by exact_mod_cast hcardR
  obtain ⟨n, hn, hn1⟩ := adjacent_pair435 M S hS hcard
  have hrot := rotation_removal435 α φ ((1 / 2 : ℝ) ^ r / 4) S hp n hn hn1
  have hsub : S ⊆ nearIntegerIndices412 M r α := by
    intro m hm
    obtain ⟨z, hz⟩ := hrot m hm
    apply Finset.mem_filter.mpr
    refine ⟨hS hm, z, ?_⟩
    linarith
  have hle : (S.card : ℝ) ≤ (nearIntegerIndices412 M r α).card := by
    exact_mod_cast Finset.card_le_card hsub
  nlinarith

end LeanLab.Linnik1951

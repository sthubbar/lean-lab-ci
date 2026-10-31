/-
P0095 Lu 2010, page 2379 equation 63 and page 2392 equation 86.
CODEX task47, unit U-8095. AI wrote this Lean code. Binary Goldbach is open.

Finite coefficient packets with genuine Dirichlet characters at each modulus.
The norm bound on the induced Gauss factors and the zero-integral weight bound remain
explicit hypotheses. This file does not assert those hypotheses for Lu's zero sums.
-/
import LeanLab.ExceptionalSet.Lu2010Coefficient

namespace LeanLab.ExceptionalSet.Lu2010Expansion63
open Finset Real
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Packets
open LeanLab.ExceptionalSet.Lu2010Coefficient
open LeanLab.ExceptionalSet.Lu2010Eq86
open LeanLab.ExceptionalSet.Lu2010Assembly

/-- The rational coefficient of one conductor pair in equation 63. -/
noncomputable def packetCoeff (r : ℕ) (z : ℕ → ℂ)
    (χ : (q : ℕ) → DirichletCharacter ℂ q) (p : ℕ × ℕ) : ℂ :=
  if r ∣ p.1 then z p.1 * χ p.1 p.2 / (p.1.totient : ℂ) ^ 2 else 0

/-- The character values cost no extra factor in the coefficient estimate. -/
theorem packetCoeff_bound (r Q : ℕ) (z : ℕ → ℂ)
    (χ : (q : ℕ) → DirichletCharacter ℂ q)
    (hz : ∀ q ∈ Icc 1 Q, ‖z q‖ ≤ r) (p : ℕ × ℕ) (hp : p ∈ farey Q) :
    ‖packetCoeff r z χ p‖ ^ 2 ≤
      if r ∣ p.1 then (r : ℝ) ^ 2 / (p.1.totient : ℝ) ^ 4 else 0 := by
  have hpI : p.1 ∈ Icc 1 Q := mem_Icc.mpr ⟨(mem_farey.mp hp).1, (mem_farey.mp hp).2.1⟩
  have hχ : ‖χ p.1 p.2‖ ≤ 1 := (χ p.1).norm_le_one _
  have hχ2 : ‖χ p.1 p.2‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (χ p.1 p.2)]
  unfold packetCoeff
  split_ifs with hd
  · simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow]
    have hsq := pow_le_pow_left₀ (norm_nonneg (z p.1)) (hz p.1 hpI) 2
    calc (‖z p.1‖ ^ 2 * ‖χ p.1 p.2‖ ^ 2) / ((p.1.totient : ℝ) ^ 2) ^ 2
        ≤ ((r : ℝ) ^ 2 * 1) / ((p.1.totient : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (r : ℝ) ^ 2 / (p.1.totient : ℝ) ^ 4 := by ring
  · simp

/-- A packet of conductor pair modulus r has energy at most 2 K cubed over r. -/
theorem packetCoeff_energy {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (z : ℕ → ℂ)
    (χ : (q : ℕ) → DirichletCharacter ℂ q)
    {K : ℝ} (hK : 0 ≤ K) (hphi : ∀ q ∈ Icc 1 Q, (q : ℝ) ≤ K * q.totient)
    (hz : ∀ q ∈ Icc 1 Q, ‖z q‖ ≤ r) :
    ∑ p ∈ farey Q, ‖packetCoeff r z χ p‖ ^ 2 ≤ 2 * K ^ 3 / (r : ℝ) :=
  coefficient_energy_pair hr Q _ hK hphi (packetCoeff_bound r Q z χ hz)

/-- Coefficients of the finite sum over conductor pairs. -/
noncomputable def coefficients {ι : Type*} (s : Finset ι) (w : ι → ℝ) (r : ι → ℕ)
    (z : ι → ℕ → ℂ) (χ : ι → (q : ℕ) → DirichletCharacter ℂ q) (p : ℕ × ℕ) : ℂ :=
  ∑ i ∈ s, (w i : ℂ) * packetCoeff (r i) (z i) (χ i) p

/-- A common lower cutoff R gives the inverse R saving after summing all packets. -/
theorem coefficients_energy {ι : Type*} (s : Finset ι) (w : ι → ℝ) (r : ι → ℕ)
    (z : ι → ℕ → ℂ) (χ : ι → (q : ℕ) → DirichletCharacter ℂ q) (Q : ℕ)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, R ≤ r i)
    (hphi : ∀ q ∈ Icc 1 Q, (q : ℝ) ≤ K * q.totient)
    (hz : ∀ i ∈ s, ∀ q ∈ Icc 1 Q, ‖z i q‖ ≤ r i) :
    ∑ p ∈ farey Q, ‖coefficients s w r z χ p‖ ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 * (2 * K ^ 3 / R) := by
  apply weighted_packet_energy s (farey Q) w (fun i => packetCoeff (r i) (z i) (χ i)) hw
  intro i hi
  have hr0 : 0 < r i := by have := hr i hi; exact_mod_cast (lt_of_lt_of_le hR this)
  exact (packetCoeff_energy (by omega) Q (z i) (χ i) hK hphi (hz i hi)).trans
    (div_le_div_of_nonneg_left (by positivity) hR (hr i hi))

/-- The elementary mean-square estimate before absorbing the logarithmic totient factor. -/
theorem window_energy {ι : Type*} (s : Finset ι) (w : ι → ℝ) (r : ι → ℕ)
    (z : ι → ℕ → ℂ) (χ : ι → (q : ℕ) → DirichletCharacter ℂ q)
    {N : ℕ} (hN : 1 ≤ N) {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, R ≤ r i)
    (hphi : ∀ q ∈ Icc 1 ⌊PP N⌋₊, (q : ℝ) ≤ K * q.totient)
    (hz : ∀ i ∈ s, ∀ q ∈ Icc 1 ⌊PP N⌋₊, ‖z i q‖ ≤ r i) :
    ∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ (coefficients s w r z χ) (k : ℤ)‖ ^ 2 ≤
      10 * dd N * (∑ i ∈ s, w i) ^ 2 * K ^ 3 / R := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ : 1 ≤ ⌊PP N⌋₊ := Nat.one_le_floor_iff _ |>.2
    (Real.one_le_rpow hN1 (by unfold c; norm_num))
  have hE := coefficients_energy s w r z χ ⌊PP N⌋₊ hR hK hw hr hphi hz
  calc (∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ (coefficients s w r z χ) (k : ℤ)‖ ^ 2)
      ≤ (((2 * rad N + 1 : ℕ) : ℝ) + 2 * (⌊PP N⌋₊ : ℝ) ^ 2) *
          ∑ p ∈ farey ⌊PP N⌋₊, ‖coefficients s w r z χ p‖ ^ 2 := rationalSum_window hQ N _
    _ ≤ (5 * dd N) * ∑ p ∈ farey ⌊PP N⌋₊, ‖coefficients s w r z χ p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (spacing_cost hN) (sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (5 * dd N) * ((∑ i ∈ s, w i) ^ 2 * (2 * K ^ 3 / R)) :=
      mul_le_mul_of_nonneg_left hE (by unfold dd; positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Lu2010Expansion63

#print axioms LeanLab.ExceptionalSet.Lu2010Expansion63.packetCoeff_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Expansion63.packetCoeff_energy
#print axioms LeanLab.ExceptionalSet.Lu2010Expansion63.coefficients_energy
#print axioms LeanLab.ExceptionalSet.Lu2010Expansion63.window_energy

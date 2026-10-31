/-
P0095 Lu 2010, page 2379 equation 63 and page 2392 equation 86.
CODEX task47, unit U-8097. AI wrote this Lean code. Binary Goldbach is open.
The totient factor and the printed exponent for the finite packet model.
The actual induced Gauss factors and the zero integral weights remain to be identified.
-/
import LeanLab.ExceptionalSet.Lu2010Expansion63
import LeanLab.ExceptionalSet.Lu2010Bound12
import LeanLab.HeathBrown1985.Elementary

namespace LeanLab.ExceptionalSet.Lu2010Eq86Scale
open Finset Real
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Expansion63
open LeanLab.ExceptionalSet.Lu2010Eq86

/-- An explicit uniform upper bound for q over phi q in the denominator range. -/
noncomputable def K (N : ℕ) : ℝ := Real.exp 1 * (1 + Real.log N / Real.log 2)

theorem K_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ K N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold K
  positivity [Real.log_nonneg hN1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The existing elementary totient estimate supplies the uniform packet hypothesis. -/
theorem totient_cost {N : ℕ} (hN : 1 ≤ N) (q : ℕ) (hq : q ∈ Icc 1 ⌊PP N⌋₊) :
    (q : ℝ) ≤ K N * q.totient := by
  obtain ⟨hq1, hqP⟩ := mem_Icc.mp hq
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hqN : (q : ℝ) ≤ N := by
    calc (q : ℝ) ≤ (⌊PP N⌋₊ : ℝ) := by exact_mod_cast hqP
      _ ≤ PP N := Nat.floor_le (by unfold PP; positivity)
      _ ≤ N := by
        unfold PP
        exact (Real.rpow_le_rpow_of_exponent_le hN1 (by unfold c; norm_num)).trans_eq (Real.rpow_one _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have homega : (q.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    exact (LeanLab.HeathBrown1985.card_primeFactors_mul_log_two_le q hq1).trans
      (Real.log_le_log hq0 hqN)
  have hdiv : (q : ℝ) / q.totient ≤ K N := by
    refine (LeanLab.HeathBrown1985.div_totient_le q hq1).trans ?_
    unfold K
    gcongr
  exact (div_le_iff₀ hphi).mp hdiv

/-- The cubed totient factor is a fixed constant times N to the power 0.0002. -/
theorem K_cube_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    K N ^ 3 ≤ C * (N : ℝ) ^ (0.0002 : ℝ) := by
  let A : ℝ := Real.exp 1 * (1 + (Real.log 2)⁻¹)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A ^ 3 * (1 + 4 / (0.0002 : ℝ)) ^ 4, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hK : K N ≤ A * (1 + Real.log N) := by
    unfold K
    dsimp [A]
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (Real.exp_pos 1).le hL,
      mul_nonneg (Real.exp_pos 1).le (inv_nonneg.mpr hlog2.le)]
  have hLpow : (1 + Real.log N) ^ 3 ≤ (1 + Real.log N) ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (1 + Real.log N)) hL]
  calc K N ^ 3 ≤ (A * (1 + Real.log N)) ^ 3 := pow_le_pow_left₀ (K_nonneg hN) hK 3
    _ = A ^ 3 * (1 + Real.log N) ^ 3 := mul_pow _ _ _
    _ ≤ A ^ 3 * (1 + Real.log N) ^ 4 := mul_le_mul_of_nonneg_left hLpow (by positivity)
    _ ≤ A ^ 3 * ((1 + 4 / (0.0002 : ℝ)) ^ 4 * (N : ℝ) ^ (0.0002 : ℝ)) :=
      mul_le_mul_of_nonneg_left (LeanLab.ExceptionalSet.Lu2010Bound12.log_four_bound (by norm_num) hN1)
        (by positivity)
    _ = _ := by ring

/-- The scalar exponent in equation 86, with P zero equal to P times N to minus 0.0001. -/
theorem exponent86 {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ 2 * (N : ℝ) ^ (0.0002 : ℝ) / (N : ℝ) ^ (-0.0001 : ℝ) =
      (N : ℝ) ^ (2.0003 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
  norm_num

/-- The printed equation 86 bound for finite packets with the stated factor and weight bounds. -/
theorem equation86_packets {ι : Type*} {Cw : ℝ} (_hCw : 0 ≤ Cw) :
    ∃ C86 : ℝ, 0 ≤ C86 ∧ ∀ N : ℕ, 1 ≤ N → ∀ (s : Finset ι) (w : ι → ℝ) (r : ι → ℕ)
      (z : ι → ℕ → ℂ) (χ : ι → (q : ℕ) → DirichletCharacter ℂ q),
      (∀ i ∈ s, 0 ≤ w i) →
      (∀ i ∈ s, PP N * (N : ℝ) ^ (-0.0001 : ℝ) ≤ r i) →
      (∀ i ∈ s, ∀ q ∈ Icc 1 ⌊PP N⌋₊, ‖z i q‖ ≤ r i) →
      (∑ i ∈ s, w i) ≤ Cw * N →
      ∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ (coefficients s w r z χ) (k : ℤ)‖ ^ 2 ≤
        C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) := by
  obtain ⟨Ck, hCk, hK⟩ := K_cube_bound
  refine ⟨10 * Cw ^ 2 * Ck, by positivity, ?_⟩
  intro N hN s w r z χ hw hr hz hW
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hP0 : 0 < PP N * (N : ℝ) ^ (-0.0001 : ℝ) := by unfold PP; positivity
  have hd0 : 0 ≤ dd N := by unfold dd; positivity
  have hW0 : 0 ≤ ∑ i ∈ s, w i := sum_nonneg hw
  have hW2 := pow_le_pow_left₀ hW0 hW 2
  have hK0 := K_nonneg hN
  have hbase := window_energy s w r z χ hN hP0 hK0 hw hr (totient_cost hN) hz
  calc (∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ (coefficients s w r z χ) (k : ℤ)‖ ^ 2)
      ≤ 10 * dd N * (∑ i ∈ s, w i) ^ 2 * K N ^ 3 /
          (PP N * (N : ℝ) ^ (-0.0001 : ℝ)) := hbase
    _ ≤ 10 * dd N * (Cw * N) ^ 2 * (Ck * (N : ℝ) ^ (0.0002 : ℝ)) /
          (PP N * (N : ℝ) ^ (-0.0001 : ℝ)) := by
      gcongr
      exact hK N hN
    _ = (10 * Cw ^ 2 * Ck) * PP N ^ (-1 : ℝ) * dd N *
          ((N : ℝ) ^ 2 * (N : ℝ) ^ (0.0002 : ℝ) / (N : ℝ) ^ (-0.0001 : ℝ)) := by
      rw [Real.rpow_neg_one]
      ring
    _ = _ := by rw [exponent86 hN]

end LeanLab.ExceptionalSet.Lu2010Eq86Scale

#print axioms LeanLab.ExceptionalSet.Lu2010Eq86Scale.K_nonneg
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86Scale.totient_cost
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86Scale.K_cube_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86Scale.exponent86
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86Scale.equation86_packets

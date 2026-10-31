import LeanLab.Romanov.TotientWeights134
import LeanLab.Romanov.Residues134

/-!
# The reciprocal totient bound for SigmaOne

Gallagher pages 134 to 136 supply the finite divisor and residue estimates.
The target HBPSigmaOneBound was stated in SigmaOne.lean in task65.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.Romanov.SigmaBridge134

open Finset Real
open LeanLab.Romanov.Decomp134b
open LeanLab.Romanov.TotientWeights134
open LeanLab.LPZ2007
open LeanLab.LPZ2007.Lemma61Port
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- The odd squarefree moduli below the logarithmic cutoff of Gallagher Lemma 7. -/
def cutoff (N d : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 ⌊log (N : ℝ) ^ d⌋₊).filter OddSqf

/-- Every member of the common cutoff is an odd squarefree modulus below the real cutoff. -/
theorem cutoff_spec (N d : ℕ) (hN : 3 ≤ N) {q : ℕ} (hq : q ∈ cutoff N d) :
    1 ≤ q ∧ OddSqf q ∧ (q : ℝ) ≤ log N ^ d := by
  classical
  obtain ⟨hqI, hqs⟩ := mem_filter.mp hq
  obtain ⟨hq1, hqle⟩ := mem_Icc.mp hqI
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact ⟨hq1, hqs, (Nat.le_floor_iff (pow_nonneg (log_nonneg hN1) d)).mp hqle⟩

/-- Monotonicity embeds every guarded divisor expansion into one common squarefree cutoff. -/
theorem truncated_divisor_sum_le (m N d : ℕ) (hm : 3 ≤ m) (hmN : m ≤ N) :
    ∑ q ∈ m.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ log m ^ d), totientWeight q ≤
      ∑ q ∈ cutoff N d with q ∣ m, totientWeight q := by
  classical
  let U := m.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ log m ^ d)
  have hsf : ∑ q ∈ U, totientWeight q = ∑ q ∈ U with Squarefree q, totientWeight q := by
    conv_rhs => rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hq : Squarefree q
    · simp only [hq, ite_true]
    · simp only [hq, ite_false, totientWeight_zero_of_not_squarefree hq]
  change (∑ q ∈ U, totientWeight q) ≤ _
  rw [hsf]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hqU, hqs⟩ := mem_filter.mp hq
    obtain ⟨hqd, hqo, hqcut⟩ := mem_filter.mp hqU
    have hq1 : 1 ≤ q := Nat.pos_of_mem_divisors hqd
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hpow : log (m : ℝ) ^ d ≤ log (N : ℝ) ^ d :=
      pow_le_pow_left₀ (log_nonneg (by linarith)) (log_le_log (by linarith) hmNR) d
    apply mem_filter.mpr
    refine ⟨?_, (Nat.mem_divisors.mp hqd).1⟩
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨hq1, Nat.le_floor (hqcut.trans hpow)⟩, hqo, hqs⟩
  · intro q _ _
    exact totientWeight_nonneg q

/-- The finite SigmaOne estimate from Gallagher Lemma 7 and the exponent residue count. -/
theorem sigmaOne_finite_bound : ∃ d : ℕ, ∃ A : ℝ, 0 < A ∧
    ∀ K L N : ℕ, 3 ≤ N →
      (∀ ν : Fin (K + 1) → Fin L, 3 ≤ N - sv ν) →
      (∀ ν : Fin (K + 1) → Fin L, sv ν ≤ N) →
      sigmaOne (K + 1) N L ≤ A *
        ((L : ℝ) ^ (K + 1) * (16 * log 2 * exp 27) +
          (L : ℝ) ^ K * (2 * exp 27 * ((d : ℝ) + 1) * log N)) := by
  classical
  obtain ⟨d, C, hC⟩ := LeanLab.Romanov.Decomp134b.lemma7
  let A : ℝ := |C| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨d, A, hA, fun K L N hN hrem hsum => ?_⟩
  let T := cutoff N d
  have hT (q : ℕ) (hq : q ∈ T) : OddSqf q := (cutoff_spec N d hN hq).2.1
  have hTcut (q : ℕ) (hq : q ∈ T) : OddSqf q ∧ (q : ℝ) ≤ log N ^ d :=
    ⟨hT q hq, (cutoff_spec N d hN hq).2.2⟩
  have hpoint (ν : Fin (K + 1) → Fin L) :
      ((N - sv ν : ℕ) : ℝ) / (N - sv ν).totient ≤
        A * (∑ q ∈ T with q ∣ N - sv ν, totientWeight q) := by
    let m := N - sv ν
    have hm : 3 ≤ m := hrem ν
    let U := m.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ log m ^ d)
    have hu0 : 0 ≤ ∑ q ∈ U, totientWeight q := sum_nonneg (fun q _ => totientWeight_nonneg q)
    have hCA : C ≤ A := by dsimp [A]; linarith [le_abs_self C]
    calc (m : ℝ) / m.totient ≤ C * (∑ q ∈ U, totientWeight q) := hC m hm
      _ ≤ A * (∑ q ∈ U, totientWeight q) := mul_le_mul_of_nonneg_right hCA hu0
      _ ≤ A * (∑ q ∈ T with q ∣ m, totientWeight q) :=
        mul_le_mul_of_nonneg_left (truncated_divisor_sum_le m N d hm (Nat.sub_le _ _)) hA.le
  have hswap : (∑ ν : Fin (K + 1) → Fin L,
      ∑ q ∈ T with q ∣ N - sv ν, totientWeight q) =
      ∑ q ∈ T, totientWeight q * (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ) := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    ring
  have hcard (q : ℕ) (hq : q ∈ T) :
      (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ) ≤
        (L : ℝ) ^ (K + 1) / xi q + (L : ℝ) ^ K :=
    LeanLab.Romanov.Residues134.remainder_count_le (hT q hq).1 K L N hsum
  have hfinite : (∑ q ∈ T,
      totientWeight q * (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ)) ≤
      (L : ℝ) ^ (K + 1) * (16 * log 2 * exp 27) +
        (L : ℝ) ^ K * (2 * exp 27 * ((d : ℝ) + 1) * log N) := by
    calc (∑ q ∈ T, totientWeight q * (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ))
        ≤ ∑ q ∈ T, totientWeight q * ((L : ℝ) ^ (K + 1) / xi q + (L : ℝ) ^ K) :=
          sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hcard q hq) (totientWeight_nonneg q))
      _ = ∑ q ∈ T, ((L : ℝ) ^ (K + 1) * (totientWeight q / xi q) +
          (L : ℝ) ^ K * totientWeight q) := by
            apply sum_congr rfl
            intro q _
            ring
      _ = (L : ℝ) ^ (K + 1) * (∑ q ∈ T, totientWeight q / xi q) +
          (L : ℝ) ^ K * (∑ q ∈ T, totientWeight q) := by
            rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (weight_order_sum_le T hT) (by positivity))
        (mul_le_mul_of_nonneg_left (weight_cutoff_sum_le T N d hN hTcut) (by positivity))
  unfold sigmaOne
  calc (∑ ν : Fin (K + 1) → Fin L, ((N - sv ν : ℕ) : ℝ) / (N - sv ν).totient)
      ≤ ∑ ν : Fin (K + 1) → Fin L, A * (∑ q ∈ T with q ∣ N - sv ν, totientWeight q) :=
        sum_le_sum (fun ν _ => hpoint ν)
    _ = A * (∑ q ∈ T,
        totientWeight q * (#{ν : Fin (K + 1) → Fin L | q ∣ N - sv ν} : ℝ)) := by
          rw [← mul_sum, hswap]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinite hA.le

/-- The existing HBP display 27 target is discharged without any cited input. -/
theorem hbp_sigmaOne_bound : HBPSigmaOneBound := by
  classical
  obtain ⟨d, A, hA, hfinite⟩ := sigmaOne_finite_bound
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let B : ℝ := 1 / log 2
  have hB : 0 < B := by dsimp [B]; positivity
  let M : ℝ := 16 * log 2 * exp 27
  have hM : 0 < M := by dsimp [M]; positivity
  let D : ℝ := 2 * exp 27 * ((d : ℝ) + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  intro K hK
  rcases K with _ | J
  · omega
  let C : ℝ := A * (M * B ^ (J + 1) + D * B ^ J)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, 2 * (J + 1), le_rfl, fun N hN _hEven => ?_⟩
  have hN3 : 3 ≤ N := by omega
  have hN0 : 0 < N := by omega
  let L : ℕ := Nat.log 2 (N / (2 * (J + 1)))
  have hcut : 2 * ((J + 1) * 2 ^ L) ≤ N := sigmaOne_paper_cutoff (J + 1) N (by omega) hN
  have hrem (ν : Fin (J + 1) → Fin L) : 3 ≤ N - sv ν := by
    have h := sigmaOne_remainder_bounds (J + 1) N L hN0 hcut ν
    omega
  have hsum (ν : Fin (J + 1) → Fin L) : sv ν ≤ N := by
    have h := LeanLab.Linnik.U1434Lemma21.sv_le ν
    omega
  have hsigma := hfinite J L N hN3 hrem hsum
  have hpowNat : 2 ^ L ≤ N := by
    have hmul : 2 ^ L ≤ (J + 1) * 2 ^ L := by
      calc 2 ^ L ≤ J * 2 ^ L + 2 ^ L := Nat.le_add_left _ _
        _ = (J + 1) * 2 ^ L := by ring
    omega
  have hpowR : (2 : ℝ) ^ L ≤ N := by exact_mod_cast hpowNat
  have hlog := log_le_log (by positivity : (0 : ℝ) < 2 ^ L) hpowR
  rw [log_pow] at hlog
  have hL : (L : ℝ) ≤ B * log N := by
    calc (L : ℝ) ≤ log N / log 2 := (le_div_iff₀ hlog2).mpr hlog
      _ = B * log N := by dsimp [B]; ring
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpower1 : (L : ℝ) ^ (J + 1) ≤ B ^ (J + 1) * log N ^ (J + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg L) hL (J + 1)
  have hpower0 : (L : ℝ) ^ J ≤ B ^ J * log N ^ J := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg L) hL J
  change sigmaOne (J + 1) N L ≤ C * log N ^ (J + 1)
  calc sigmaOne (J + 1) N L ≤ A * ((L : ℝ) ^ (J + 1) * M + (L : ℝ) ^ J * (D * log N)) := hsigma
    _ ≤ A * ((B ^ (J + 1) * log N ^ (J + 1)) * M + (B ^ J * log N ^ J) * (D * log N)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hpower1 hM.le)
        (mul_le_mul_of_nonneg_right hpower0 (mul_nonneg hD.le hlogN.le))) hA.le
    _ = C * log N ^ (J + 1) := by
      dsimp [C]
      rw [pow_succ]
      ring

end LeanLab.Romanov.SigmaBridge134

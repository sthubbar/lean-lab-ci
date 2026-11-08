import LeanLab.PNTPort.BV.Helpers
import LeanLab.ExceptionalSet.Arithmetic465

/-!
Elementary totient envelopes for P0082 page360, the proof of Lemma5.
A logarithm replaces the sharper log log factor printed in the paper.
The weaker logarithmic envelope suffices for the exponential E savings.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Finset Real

/-- P0082 page360, the totient estimate used in Lemma5. A weaker logarithmic
factor follows from the existing reciprocal totient sum, with no prime distribution input. -/
theorem totient_ratio_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) / n.totient ≤ C * (1 + Real.log n) := by
  obtain ⟨C, hC, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he := LeanLab.PNTPort.BV.inv_totient_eq (m := n) (by omega)
  calc
    _ = ∑ d ∈ n.divisors, LeanLab.PNTPort.BV.sqfTot d := by
      calc
        _ = (n : ℝ) * (1 / (n.totient : ℝ)) := by ring
        _ = (n : ℝ) * ((1 / (n : ℝ)) * ∑ d ∈ n.divisors, LeanLab.PNTPort.BV.sqfTot d) := by rw [he]
        _ = _ := by field_simp
    _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) / d.totient :=
      sum_le_sum (fun d _ => LeanLab.PNTPort.BV.sqfTot_le d)
    _ ≤ ∑ d ∈ Icc 1 n, (1 : ℝ) / d.totient := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hd).1⟩
      · intro d _ _
        positivity
    _ ≤ _ := hsum n

/-- P0082 page360 first display in the proof of Lemma5. Bounding both
totient ratios by L bounds its summand by L squared times gcd m q over q. -/
theorem totient_kernel_le (Q q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ Q) (m : ℤ)
    (L : ℝ) (hL : 0 ≤ L)
    (hφ : ∀ n : ℕ, 1 ≤ n → n ≤ Q → (n : ℝ) / n.totient ≤ L) :
    (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) ≤
      L ^ 2 * (Int.gcd m q : ℝ) / q := by
  let g := Int.gcd m q
  have hq0 : 0 < q := by omega
  have hg : 0 < g := by
    simpa only [g, Int.gcd_def, Int.natAbs_natCast] using Nat.gcd_pos_of_pos_right m.natAbs hq0
  have hgd : g ∣ q := by
    have h := Int.gcd_dvd_right m (q : ℤ)
    exact_mod_cast h
  have hgq : g ≤ q := Nat.le_of_dvd hq0 hgd
  have ht : 1 ≤ q / g := Nat.div_pos hgq hg
  have htQ : q / g ≤ Q := (Nat.div_le_self q g).trans hqQ
  have hprod := mul_le_mul (hφ q hq hqQ) (hφ (q / g) ht htQ) (by positivity) hL
  have hmul := mul_le_mul_of_nonneg_right hprod (show 0 ≤ (g : ℝ) / q by positivity)
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hφq : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  have hφt : ((q / g).totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q / g)).ne'
  have hid : ((q : ℝ) / q.totient * ((q / g : ℕ) : ℝ) / (q / g).totient) * ((g : ℝ) / q) =
      (q : ℝ) / ((q.totient : ℝ) * ((q / g).totient : ℝ)) := by
    rw [Nat.cast_div_charZero hgd]
    field_simp
    <;> ring
  change _ ≤ L ^ 2 * (g : ℝ) / q
  convert hmul using 1
  · convert hid.symm using 1 <;> ring
  · ring

/-- P0082 page360, multiples reindexing in the proof of Lemma5.
The reciprocal sum over positive multiples of r through Q is at most
one plus log Q divided by r. -/
theorem sum_inverse_multiples (Q r : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), (q : ℝ)⁻¹ ≤ (1 + Real.log Q) / r := by
  classical
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have himage : (Icc 1 Q).filter (fun q => r ∣ q) = (Icc 1 (Q / r)).image (fun k => r * k) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqI, hd⟩ := mem_filter.mp hq
      obtain ⟨k, rfl⟩ := hd
      apply mem_image.mpr
      refine ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · have := (mem_Icc.mp hqI).1
        by_contra hk
        have : k = 0 := by omega
        simp [this] at *
      · exact (Nat.le_div_iff_mul_le hr0).mpr (by simpa [mul_comm] using (mem_Icc.mp hqI).2)
    · intro hq
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right r k⟩
      · exact Nat.mul_pos hr0 (mem_Icc.mp hk).1
      · have h := (Nat.le_div_iff_mul_le hr0).mp (mem_Icc.mp hk).2
        simpa [mul_comm] using h
  rw [himage, sum_image]
  · simp_rw [Nat.cast_mul, mul_inv]
    rw [← mul_sum]
    have hb := LeanLab.HeathBrown1985.sum_inv_Icc_le_log Q
    have hsub : Icc 1 (Q / r) ⊆ Icc 1 Q := Icc_subset_Icc_right (Nat.div_le_self Q r)
    have hs : ∑ k ∈ Icc 1 (Q / r), (k : ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 Q, (k : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    calc
      _ ≤ (r : ℝ)⁻¹ * (1 + Real.log Q) := mul_le_mul_of_nonneg_left (hs.trans hb) (by positivity)
      _ = _ := by ring
  · intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hr0 h

end LeanLab.ExceptionalSet.Supply465

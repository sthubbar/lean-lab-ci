/-
P0066, page 104, the arithmetic progression count leading to equation 5.7.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Eq56Link
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma3Reduction

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Eq57

open Vaughan1977Eq55 Vaughan1977Eq56 Vaughan1977Lemma3

/-- Candidate even sums for a fixed first prime and divisor. -/
def T (x : ℝ) (d p : ℕ) : Finset ℕ :=
  (Nset x).filter (fun n => d ∣ n ∧ p < n ∧ (n - p).Prime)

theorem residue_complement (p : ℕ) {d : ℕ} (hd : 0 < d) :
    p + (d - p % d) ≡ 0 [MOD d] := by
  calc
    p + (d - p % d) ≡ p % d + (d - p % d) [MOD d] :=
      (Nat.mod_modEq p d).symm.add_right _
    _ = d := Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt p hd))
    _ ≡ 0 [MOD d] := Nat.modulus_modEq_zero

/-- Subtracting the first prime injects T into the appropriate prime interval. -/
theorem card_T_le_interval {x : ℝ} (hx : 6 ≤ x) {d p : ℕ} (hd : 0 < d)
    (hp : p ∈ P1 x) : (T x d p).card ≤ pi_interval x (x - p) d (d - p % d) := by
  apply Finset.card_le_card_of_injOn (fun n => n - p)
  · intro n hn
    change n ∈ T x d p at hn
    simp only [T, Finset.mem_filter, Nset, Finset.mem_Ioc] at hn
    obtain ⟨⟨hnlo, hnhi⟩, hdn, hpn, hpr⟩ := hn
    have hpI := (Finset.mem_filter.mp hp).1
    have hpx : (p : ℝ) ≤ x - 3 := by
      have hpxn := (Finset.mem_Icc.mp hpI).2
      have hfl := Nat.floor_le (by linarith : 0 ≤ x - 3)
      have hc : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpxn
      linarith
    have hnx : x < n := (Nat.floor_lt (by linarith : 0 ≤ x)).mp hnlo
    have hnx2 : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mp hnhi
    have hcast : ((n - p : ℕ) : ℝ) = (n : ℝ) - p := Nat.cast_sub hpn.le
    change n - p ∈ (Ioc ⌊x - p⌋₊ ⌊x + (x - p)⌋₊).filter
      (fun q => q.Prime ∧ q ≡ d - p % d [MOD d])
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hpr, ?_⟩
    · rw [Nat.floor_lt (by linarith : 0 ≤ x - p), hcast]
      linarith
    · rw [Nat.le_floor_iff (by linarith : 0 ≤ x + (x - p)), hcast]
      linarith
    · apply Nat.ModEq.add_left_cancel' p
      have hs : p + (n - p) = n := Nat.add_sub_cancel' hpn.le
      rw [hs]
      exact (Nat.modEq_zero_iff_dvd.mpr hdn).trans (residue_complement p hd).symm
  · intro n hn m hm he
    change n ∈ T x d p at hn
    change m ∈ T x d p at hm
    change n - p = m - p at he
    have hpn := (Finset.mem_filter.mp hn).2.2.1
    have hpm := (Finset.mem_filter.mp hm).2.2.1
    omega

/-- Regroup the finite divisor sum by its first prime. -/
theorem D_eq (x : ℝ) (d : ℕ) :
    D x d = ∑ p ∈ P1 x, Real.log p * (T x d p).card := by
  calc
    D x d = ∑ n ∈ (Nset x).filter (d ∣ ·),
        ∑ p ∈ P1 x, if p < n ∧ (n - p).Prime then Real.log p else 0 := by
      simp only [D, F, Finset.sum_filter]
    _ = ∑ p ∈ P1 x, ∑ n ∈ (Nset x).filter (d ∣ ·),
        if p < n ∧ (n - p).Prime then Real.log p else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp [T, Finset.filter_filter, mul_comm]

theorem sum_logs_le_theta (x : ℝ) : ∑ p ∈ P1 x, Real.log p ≤ Chebyshev.theta x := by
  unfold P1 Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.filter_subset_filter
    intro p hp
    have hpI := Finset.mem_Icc.mp hp
    exact Finset.mem_Ioc.mpr ⟨by omega,
      hpI.2.trans (Nat.floor_le_floor (by linarith : x - 3 ≤ x))⟩
  · intro p hp hnp
    exact Real.log_natCast_nonneg p

/-- The inner sum bound used in 5.7, CONDITIONAL ON the coprime Brun Titchmarsh input. -/
theorem D_le_of_BT (hBT : Lemma3Coprime) {x : ℝ} (hx : 6 ≤ x) {d : ℕ}
    (hd : 0 < d) (hdx : (d : ℝ) < x) :
    D x d ≤ 2 * x * Chebyshev.theta x / ((d.totient : ℝ) * Real.log (x / d)) := by
  have hlog : 0 < Real.log (x / d) := Real.log_pos ((one_lt_div (by exact_mod_cast hd)).mpr hdx)
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcoef : 0 ≤ 2 * x / ((d.totient : ℝ) * Real.log (x / d)) := by positivity
  rw [D_eq]
  calc
    ∑ p ∈ P1 x, Real.log p * (T x d p).card
        ≤ ∑ p ∈ P1 x, Real.log p * (2 * x / ((d.totient : ℝ) * Real.log (x / d))) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
      have hc : ((T x d p).card : ℝ) ≤ pi_interval x (x - p) d (d - p % d) := by
        exact_mod_cast card_T_le_interval hx hd hp
      exact hc.trans (lemma3_of_coprime hBT x (x - p) d (d - p % d) hd hdx)
    _ = (∑ p ∈ P1 x, Real.log p) * (2 * x / ((d.totient : ℝ) * Real.log (x / d))) := by
      rw [Finset.sum_mul]
    _ ≤ Chebyshev.theta x * (2 * x / ((d.totient : ℝ) * Real.log (x / d))) :=
      mul_le_mul_of_nonneg_right (sum_logs_le_theta x) hcoef
    _ = _ := by ring

/-- Equation 5.7 on any finite set of positive moduli below x, in the weak form. -/
theorem eq57 (hBT : Lemma3Coprime) {x : ℝ} (hx : 6 ≤ x) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) < x) :
    ∑ d ∈ s, f d * D x d ≤ ∑ d ∈ s,
      2 * x * Chebyshev.theta x * f d / ((d.totient : ℝ) * Real.log (x / d)) := by
  apply Finset.sum_le_sum
  intro d hd
  have h := mul_le_mul_of_nonneg_left (D_le_of_BT hBT hx (hs d hd).1 (hs d hd).2) (f_nonneg d)
  convert h using 1 <;> ring

example : 3 + (2 - 3 % 2) ≡ 0 [MOD 2] := residue_complement 3 (by decide)

example : ∑ p ∈ P1 (6 : ℝ), Real.log p ≤ Chebyshev.theta 6 := sum_logs_le_theta 6

end LeanLab.SchnirelmannBounds.Vaughan1977Eq57

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.residue_complement
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.card_T_le_interval
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.D_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.sum_logs_le_theta
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.D_le_of_BT
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq57.eq57

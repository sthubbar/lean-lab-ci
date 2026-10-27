/-
P0066, page 104, equation 5.6 for the concrete weights of Vaughan1977Eq55.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Eq56
import LeanLab.SchnirelmannBounds.Vaughan1977Eq55

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Eq56

open Vaughan1977Eq55 Vaughan1977Lemma10 Vaughan1977Lemma12

theorem oddPF_eq {n : ℕ} (hn : n ≠ 0) : oddPF n = n.primeFactors.filter (2 < ·) := by
  ext p
  simp only [oddPF, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨_, hp, hp2, hpn⟩
    exact ⟨⟨hp, hpn, hn⟩, hp2⟩
  · rintro ⟨⟨hp, hpn, _⟩, hp2⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn), hp, hp2, hpn⟩

/-- The divisor expansion equals the exact power of Pn used in G. -/
theorem sum_divisors_eq_Pn {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, f d = Pn n ^ (11 / 4 : ℝ) := by
  have hP : Pn n = ∏ p ∈ oddPF n, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    simp [Pn, prodQ]
  rw [sum_divisors_f hn, hP, ← Real.finsetProd_rpow]
  · rw [oddPF_eq hn, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases ht : 2 < p
    · have hne : p ≠ 2 := by omega
      simp [primeWeight, hne, ht]
    · have he : p = 2 := by omega
      simp [he, primeWeight]
  · intro p hp
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.2.1
    apply div_nonneg <;> linarith

/-- A finite common range for the divisor sums. -/
theorem sum_divisors_eq_Icc {n M : ℕ} (hn : n ≠ 0) (hnM : n ≤ M) :
    ∑ d ∈ n.divisors, f d = ∑ d ∈ Icc 1 M with d ∣ n, f d := by
  congr 1
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans hnM⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, hn⟩

/-- Equation 5.6 with the common divisor range extended to 2x. -/
theorem eq56_extended (x : ℝ) (hx : 1 ≤ x) :
    G x = ∑ d ∈ Icc 1 ⌊2 * x⌋₊, f d * ∑ n ∈ (Nset x).filter (d ∣ ·), F x n := by
  have hx0 : 0 ≤ x := by linarith
  have hn0 : ∀ n ∈ Nset x, n ≠ 0 := by
    intro n hn
    have h := (Finset.mem_Ioc.mp hn).1
    omega
  calc
    G x = ∑ n ∈ Nset x, ∑ d ∈ Icc 1 ⌊2 * x⌋₊, if d ∣ n then F x n * f d else 0 := by
      unfold G
      apply Finset.sum_congr rfl
      intro n hn
      have hnM := (Finset.mem_Ioc.mp hn).2
      rw [← sum_divisors_eq_Pn (hn0 n hn), sum_divisors_eq_Icc (hn0 n hn) hnM,
        Finset.mul_sum, Finset.sum_filter]
    _ = ∑ d ∈ Icc 1 ⌊2 * x⌋₊, ∑ n ∈ Nset x, if d ∣ n then F x n * f d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hdn : d ∣ n <;> simp [hdn, mul_comm]

/-- A nonzero F in the interval is supported on even integers. -/
theorem even_of_F_ne_zero {x : ℝ} (hx : 6 ≤ x) {n : ℕ} (hn : n ∈ Nset x)
    (hF : F x n ≠ 0) : Even n := by
  obtain ⟨p, hp, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨hp3, hpx⟩, hpp⟩, hpn, hq⟩ := hp
  have hnx : x < n := (Nat.floor_lt (by linarith : 0 ≤ x)).mp (Finset.mem_Ioc.mp hn).1
  have hpxr : (p : ℝ) ≤ x - 3 := by
    have h1 := Nat.floor_le (by linarith : 0 ≤ x - 3)
    have h2 : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpx
    linarith
  have hq3 : 3 ≤ n - p := by
    have hlt : (p : ℝ) + 3 < n := by linarith
    have hlt' : p + 3 < n := by exact_mod_cast hlt
    omega
  have h1 : Odd p := hpp.odd_of_ne_two (by omega)
  have h2 : Odd (n - p) := hq.odd_of_ne_two (by omega)
  have h := h1.add_odd h2
  rwa [Nat.add_sub_cancel' hpn.le] at h

/-- An odd divisor of a positive even integer is at most half that integer. -/
theorem odd_divisor_le_half {n d : ℕ} (hn0 : n ≠ 0) (hn : Even n) (hdn : d ∣ n)
    (hd : ¬ 2 ∣ d) : 2 * d ≤ n := by
  obtain ⟨k, rfl⟩ := hdn
  have hk0 : k ≠ 0 := by intro h; simp [h] at hn0
  have hdiv : 2 ∣ d * k := even_iff_two_dvd.mp hn
  have hkdiv : 2 ∣ k := (Nat.prime_two.dvd_mul.mp hdiv).resolve_left hd
  have hk2 : 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hkdiv
  nlinarith

/-- The inner divisor sum in 5.6, with F restricted to the interval of 5.3. -/
def D (x : ℝ) (d : ℕ) : ℝ := ∑ n ∈ (Nset x).filter (d ∣ ·), F x n

/-- Equation 5.6 with exactly the printed divisor range d at most x. -/
theorem eq56 (x : ℝ) (hx : 6 ≤ x) :
    G x = ∑ d ∈ Icc 1 ⌊x⌋₊, f d * D x d := by
  rw [eq56_extended x (by linarith)]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_le_floor (by linarith)))
  intro d hd hdx
  by_cases hfd : f d = 0
  · simp [hfd]
  have hdodd : ¬ 2 ∣ d := fun h => hfd (f_even h)
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdx' : ⌊x⌋₊ < d := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hdx
    omega
  have hdxr : x < d := (Nat.floor_lt (by linarith : 0 ≤ x)).mp hdx'
  unfold D
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hF : F x n = 0
  · simp [hF]
  have hnset := (Finset.mem_filter.mp hn).1
  have hdn := (Finset.mem_filter.mp hn).2
  have hnI := Finset.mem_Ioc.mp hnset
  have hn0 : n ≠ 0 := by omega
  have hhalf := odd_divisor_le_half hn0 (even_of_F_ne_zero hx hnset hF) hdn hdodd
  have hhalfr : (2 : ℝ) * d ≤ n := by exact_mod_cast hhalf
  have hnM : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mp hnI.2
  exfalso
  linarith

/-- The d equal to 1 term is precisely Psi. -/
theorem tail_identity (x : ℝ) (hx : 6 ≤ x) :
    G x - Psi x = ∑ d ∈ Icc 2 ⌊x⌋₊, f d * D x d := by
  have hM : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    norm_num
    linarith
  have hI : Icc 1 ⌊x⌋₊ = insert 1 (Icc 2 ⌊x⌋₊) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [eq56 x hx, hI, Finset.sum_insert (by simp), f_one, one_mul]
  have hD : D x 1 = Psi x := by
    simp only [D, one_dvd, Finset.filter_true]
    exact (psi_eq x hx).symm
  rw [hD]
  ring

example : ∑ d ∈ (6 : ℕ).divisors, f d = Pn 6 ^ (11 / 4 : ℝ) :=
  sum_divisors_eq_Pn (by decide)

example : 2 * 3 ≤ (6 : ℕ) := odd_divisor_le_half (by decide) (by decide) (by decide) (by decide)

end LeanLab.SchnirelmannBounds.Vaughan1977Eq56

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.oddPF_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.sum_divisors_eq_Pn
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.sum_divisors_eq_Icc
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.eq56_extended
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.even_of_F_ne_zero
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.odd_divisor_le_half
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.eq56
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.tail_identity

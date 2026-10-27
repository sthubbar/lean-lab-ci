/-
P0066, page 105, the elementary inner sum bound for the large divisor range.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Eq57

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail

open Vaughan1977Eq55 Vaughan1977Eq56 Vaughan1977Eq57

/-- Even multiples in the interval supporting F. -/
def E (x : ℝ) (d : ℕ) : Finset ℕ := (Nset x).filter (fun n => d ∣ n ∧ Even n)

theorem F_le_theta (x : ℝ) (n : ℕ) : F x n ≤ Chebyshev.theta x := by
  refine le_trans ?_ (sum_logs_le_theta x)
  unfold F
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp hnp
  exact Real.log_natCast_nonneg p

theorem D_eq_even {x : ℝ} (hx : 6 ≤ x) (d : ℕ) : D x d = ∑ n ∈ E x d, F x n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [E, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  · intro n hn hne
    have hnset := (Finset.mem_filter.mp hn).1
    have hdn := (Finset.mem_filter.mp hn).2
    by_contra hF
    exact hne (Finset.mem_filter.mpr ⟨hnset, hdn, even_of_F_ne_zero hx hnset hF⟩)

theorem two_mul_dvd {n d : ℕ} (hn : Even n) (hdn : d ∣ n) (hd : ¬ 2 ∣ d) : 2 * d ∣ n :=
  (Nat.prime_two.coprime_iff_not_dvd.mpr hd).mul_dvd_of_dvd_of_dvd
    (even_iff_two_dvd.mp hn) hdn

/-- Even multiples of an odd divisor are sparse, including when d is near x. -/
theorem card_E_le {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d) (hodd : ¬ 2 ∣ d) :
    (E x d).card ≤ ⌊x / d⌋₊ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcard : (E x d).card ≤ (Icc 1 ⌊x / d⌋₊).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / (2 * d))
    · intro n hn
      change n ∈ E x d at hn
      obtain ⟨hnset, hdn, hnev⟩ := Finset.mem_filter.mp hn
      have hnI := Finset.mem_Ioc.mp hnset
      have hn0 : 0 < n := by omega
      have hdiv := two_mul_dvd hnev hdn hodd
      have he : n / (2 * d) * (2 * d) = n := Nat.div_mul_cancel hdiv
      have hq0 : 0 < n / (2 * d) := by
        by_contra h
        have hq : n / (2 * d) = 0 := Nat.eq_zero_of_not_pos h
        rw [hq] at he
        simp at he
        omega
      have her : ((n / (2 * d) : ℕ) : ℝ) * (2 * d) = n := by exact_mod_cast he
      have hnx : (n : ℝ) ≤ 2 * x := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mp hnI.2
      change n / (2 * d) ∈ Icc 1 ⌊x / d⌋₊
      refine Finset.mem_Icc.mpr ⟨hq0, ?_⟩
      apply Nat.le_floor
      rw [le_div_iff₀ hd0]
      nlinarith
    · intro n hn m hm heq
      change n ∈ E x d at hn
      change m ∈ E x d at hm
      change n / (2 * d) = m / (2 * d) at heq
      have hn' := (Finset.mem_filter.mp hn).2
      have hm' := (Finset.mem_filter.mp hm).2
      have hnrec := Nat.div_mul_cancel (two_mul_dvd hn'.2 hn'.1 hodd)
      have hmrec := Nat.div_mul_cancel (two_mul_dvd hm'.2 hm'.1 hodd)
      rw [← hnrec, ← hmrec, heq]
  simpa using hcard

/-- The elementary large divisor estimate on page 105, with a weak inequality. -/
theorem D_le_trivial {x : ℝ} (hx : 6 ≤ x) {d : ℕ} (hd : 0 < d) (hodd : ¬ 2 ∣ d) :
    D x d ≤ x / d * Chebyshev.theta x := by
  rw [D_eq_even hx]
  calc
    ∑ n ∈ E x d, F x n ≤ ∑ _n ∈ E x d, Chebyshev.theta x := by
      apply Finset.sum_le_sum
      intro n hn
      exact F_le_theta x n
    _ = ((E x d).card : ℝ) * Chebyshev.theta x := by simp
    _ ≤ (⌊x / d⌋₊ : ℝ) * Chebyshev.theta x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_E_le (by linarith) hd hodd)
        (Chebyshev.theta_nonneg x)
    _ ≤ x / d * Chebyshev.theta x :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (Chebyshev.theta_nonneg x)

theorem f_mul_D_le {x : ℝ} (hx : 6 ≤ x) {d : ℕ} (hd : 0 < d) :
    f d * D x d ≤ x * Chebyshev.theta x * (f d / d) := by
  by_cases heven : 2 ∣ d
  · simp [f_even heven]
  · have h := mul_le_mul_of_nonneg_left (D_le_trivial hx hd heven) (f_nonneg d)
    convert h using 1; ring

example : 2 * 3 ∣ (12 : ℕ) := two_mul_dvd (by decide) (by decide) (by decide)

end LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.F_le_theta
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.D_eq_even
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.two_mul_dvd
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.card_E_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.D_le_trivial
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail.f_mul_D_le

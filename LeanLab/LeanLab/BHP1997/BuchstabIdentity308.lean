/-
BHP1997, page 53. Three exact applications of the finite Buchstab identity.
The retained and deleted fourth terms stay separate in the analytic proof.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Rough308

namespace LeanLab.BHP1997.Task308
open Classical

/-- Page 53. The first prime sum with a common lower roughness cutoff. -/
noncomputable def buchstabFirstTerm (n w z : ℕ) : ℝ :=
  ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n), roughIndicator (n / p) w

/-- Page 53. The second ordered prime sum with the common lower cutoff. -/
noncomputable def buchstabSecondTerm (n w z : ℕ) : ℝ :=
  ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n),
    ∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
      roughIndicator (n / p / q) w

/-- Page 53. The negative third prime sum with roughness cutoff at the last prime. -/
noncomputable def buchstabThirdTerm (n w z : ℕ) : ℝ :=
  ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n),
    ∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
      ∑ r ∈ q.primesBelow.filter (fun r => w ≤ r ∧ r ∣ n / p / q),
        roughIndicator (n / p / q / r) r

/-- Page 53. The exact four-term identity at natural cutoffs.
This reuses the already proved finite Buchstab identity three times. -/
theorem buchstab_four_term (n w z : ℕ) (hwz : w ≤ z) :
    roughIndicator n z = roughIndicator n w - buchstabFirstTerm n w z +
      buchstabSecondTerm n w z - buchstabThirdTerm n w z := by
  have hsum :
      (∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n), roughIndicator (n / p) p) =
      ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n),
        (roughIndicator (n / p) w -
          (∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
            roughIndicator (n / p / q) w) +
          ∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
            ∑ r ∈ q.primesBelow.filter (fun r => w ≤ r ∧ r ∣ n / p / q),
              roughIndicator (n / p / q / r) r) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [rough_buchstab_finite (n / p) w p (Finset.mem_filter.mp hp).2.1]
    have hinner :
        (∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
          roughIndicator (n / p / q) q) =
        ∑ q ∈ p.primesBelow.filter (fun q => w ≤ q ∧ q ∣ n / p),
          (roughIndicator (n / p / q) w -
            ∑ r ∈ q.primesBelow.filter (fun r => w ≤ r ∧ r ∣ n / p / q),
              roughIndicator (n / p / q / r) r) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact rough_buchstab_finite (n / p / q) w q (Finset.mem_filter.mp hq).2.1
    rw [hinner, Finset.sum_sub_distrib]
    ring
  rw [rough_buchstab_finite n w z hwz, hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold buchstabFirstTerm buchstabSecondTerm buchstabThirdTerm
  ring

/-- Page 53. A nonempty prime-factor instance of all four exact terms.
At n equal to thirty, w two and z five, the signed terms are one, two, one and zero. -/
theorem buchstab_four_term_instance :
    roughIndicator 30 5 = 0 ∧ roughIndicator 30 2 = 1 ∧
      buchstabFirstTerm 30 2 5 = 2 ∧ buchstabSecondTerm 30 2 5 = 1 ∧
      buchstabThirdTerm 30 2 5 = 0 := by
  have h5 : (5 : ℕ).primesBelow = {2, 3} := by decide
  have h3 : (3 : ℕ).primesBelow = {2} := by decide
  have h2 : (2 : ℕ).primesBelow = ∅ := by decide
  norm_num [buchstabFirstTerm, buchstabSecondTerm, buchstabThirdTerm,
    h5, h3, h2, Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton]
  norm_num [roughIndicator, Nat.minFac_eq, Nat.minFacAux]


end LeanLab.BHP1997.Task308

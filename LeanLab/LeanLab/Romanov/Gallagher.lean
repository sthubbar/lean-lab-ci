import LeanLab.LanguascoPintzZaccagnini2007.Lemma61
import LeanLab.DensityGoldbach.AlsetriShaoLocal

/-!
# A Gallagher-type lemma: `Σ_{ξ(q) ≤ x} f(q) ≤ 2 e^27 log(2x)`

Lab proof, unit U-5609, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics,
Gallagher 1975, Lemma 4 as Heath-Brown and Puchta 2002 use it in Section 4 for Σ₁, in the form with
the weight `f(q) = ∏_{p ∣ q} 1/(p - 2)`, which dominates `1/q`, `1/φ(q)` and `q/φ(q)²` on odd
squarefree `q`. Binary Goldbach is OPEN; this is the Linnik-Goldbach line.

Every odd squarefree `q` with `ξ(q) ≤ x` divides `M_j = ∏_{e ≤ 2^(j+1)} (2^e - 1)`, `j = ⌊log₂ x⌋`,
so the sum is at most `∏_{p ∣ M_j} (1 + 1/(p - 2)) ≤ e^27 · 2(j + 1) log 2 ≤ 2 e^27 log(2x)`.

* `gallagher_f`: for every `x ≥ 1` and every finite set `T` of odd squarefree `q` with
  `ξ(q) ≤ x`, `Σ_{q ∈ T} f(q) ≤ 2 e^27 log(2x)`, PROVED.
* `gallagher_inv`: the same bound for `Σ 1/q`, PROVED.
* `hbp_lemma6`: Heath-Brown and Puchta's Lemma 6, Gallagher's Lemma 4, read on arXiv
  math/0201299 page 15: `Σ_{ε(q) ≤ x} μ²(q) q/φ(q)² ≪ log x` over odd `q`, with the explicit
  `2 e^27 log(2x)`, PROVED.
* `hbp_27_summable`: the series `Σ_{q odd} μ²(q)/(q ε(q))` of their (27) converges, PROVED.
-/

namespace LeanLab.LPZ2007

open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

theorem gallagher_f (x : ℕ) (hx : 1 ≤ x) (T : Finset ℕ) (hT : ∀ q ∈ T, OddSqf q ∧ xi q ≤ x) :
    ∑ q ∈ T, fd q ≤ 2 * exp 27 * log (2 * x) := by
  set j := Nat.log 2 x with hj
  have hlt : x < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hle : 2 ^ j ≤ x := Nat.pow_log_le_self 2 (by omega)
  calc ∑ q ∈ T, fd q = ∑ q ∈ T, ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 2) :=
        sum_congr rfl fun q hq => fd_eq (hT q hq).1
    _ = ∑ s ∈ T.image Nat.primeFactors, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
        rw [sum_image]
        intro a ha b hb hab
        rw [← Nat.prod_primeFactors_of_squarefree (hT a ha).1.2.2,
          ← Nat.prod_primeFactors_of_squarefree (hT b hb).1.2.2, hab]
    _ ≤ ∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
        refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
        · rw [mem_image] at hs
          obtain ⟨q, hq, rfl⟩ := hs
          have hsp := xi_spec_sqf (hT q hq).1
          rw [mem_powerset]
          exact Nat.primeFactors_mono (hsp.2.2.trans (Romanov.dvd_M hsp.1 (by
            have := (hT q hq).2; omega))) (Romanov.M_ne_zero j)
        · refine prod_nonneg fun p hp => ?_
          have := pf_M_ge_three j p (mem_powerset.1 hs hp)
          have : (3 : ℝ) ≤ p := by exact_mod_cast this
          have : 0 < (p : ℝ) - 2 := by linarith
          positivity
    _ ≤ exp 27 * (2 * (j + 1) * log 2) := sumH_M_le j
    _ ≤ 2 * exp 27 * log (2 * x) := by
        have h1 : ((j : ℝ) + 1) * log 2 ≤ log (2 * x) := by
          rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
          apply Real.log_le_log (by positivity)
          have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
          push_cast
          rw [this]
          have : ((2 ^ j : ℕ) : ℝ) ≤ x := by exact_mod_cast hle
          push_cast at this
          linarith
        have := exp_pos 27
        nlinarith

lemma inv_le_fd {q : ℕ} (hos : OddSqf q) : (1 : ℝ) / q ≤ fd q := by
  rw [fd_eq hos]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hos.2.2]
  push_cast
  rw [one_div, ← prod_inv_distrib]
  refine prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hos.2.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  have : (3 : ℝ) ≤ p := by exact_mod_cast (by have := hpr.two_le; omega : 3 ≤ p)
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem gallagher_inv (x : ℕ) (hx : 1 ≤ x) (T : Finset ℕ) (hT : ∀ q ∈ T, OddSqf q ∧ xi q ≤ x) :
    ∑ q ∈ T, (1 : ℝ) / q ≤ 2 * exp 27 * log (2 * x) :=
  le_trans (sum_le_sum fun q hq => inv_le_fd (hT q hq).1) (gallagher_f x hx T hT)

lemma q_div_phi_sq_le {q : ℕ} (hos : OddSqf q) :
    (q : ℝ) / (Nat.totient q : ℝ) ^ 2 ≤ fd q := by
  rw [fd_eq hos]
  have hpf3 : ∀ p ∈ q.primeFactors, 3 ≤ p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hos.2.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
    have := hpr.two_le; omega
  have hq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hos.2.2]
    push_cast; rfl
  have hφ : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [LeanLab.DensityGoldbach.AlsetriShaoLocal.totient_squarefree hos.1 hos.2.2]
    push_cast
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (by have := hpf3 p hp; omega)]; simp
  rw [hq, hφ, ← prod_pow, ← prod_div_distrib]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have : (3 : ℝ) ≤ p := by exact_mod_cast hpf3 p hp
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hpf3 p hp
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith

/-- **Heath-Brown and Puchta Lemma 6**, Gallagher's Lemma 4, over odd squarefree `q`. -/
theorem hbp_lemma6 (x : ℕ) (hx : 1 ≤ x) (T : Finset ℕ) (hT : ∀ q ∈ T, OddSqf q ∧ xi q ≤ x) :
    ∑ q ∈ T, (q : ℝ) / (Nat.totient q : ℝ) ^ 2 ≤ 2 * exp 27 * log (2 * x) :=
  le_trans (sum_le_sum fun q hq => q_div_phi_sq_le (hT q hq).1) (gallagher_f x hx T hT)

/-- The series `Σ_{q odd} μ²(q)/(q ε(q))` of Heath-Brown and Puchta's (27) converges. -/
theorem hbp_27_summable :
    Summable (fun q : ℕ => if OddSqf q then (1 : ℝ) / (q * xi q) else 0) := by
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) lemma61_proved
  · split_ifs <;> positivity
  · unfold seriesTerm
    split_ifs with h
    · have hx : (0 : ℝ) < xi q := by exact_mod_cast (xi_spec_sqf h).1
      rw [show (1 : ℝ) / (q * xi q) = (1 / q) / xi q by rw [div_div]]
      exact div_le_div_of_nonneg_right (inv_le_fd h) hx.le
    · exact le_rfl

end

end LeanLab.LPZ2007

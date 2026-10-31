import LeanLab.Xi2012.NatSiegelWalfisz

/-!
Xi 2012, arXiv 1206.2148v1, page 2 remark after equation 3.
The general implication is CONDITIONAL ON the family's Siegel-Walfisz condition.
The all-primes specialization will use the proved natural Siegel-Walfisz theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

/-- Page 2 remark, CONDITIONAL ON SiegelWalfiszNat A delta. -/
theorem thetaNat_total_of_condition (A : ℕ → Finset ℕ) (δ : ℕ → ℝ)
    (hSW : SiegelWalfiszNat A δ) :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ x : ℕ, 3 ≤ x →
      |thetaNat (A x) x 1 1 - δ x * x| ≤ C * x / Real.log x ^ c := by
  intro c hc
  obtain ⟨C, hC⟩ := hSW (c / 2) (by positivity)
  refine ⟨C, fun x hx => ?_⟩
  have hq : (1 : ℝ) ≤ Real.log x ^ (c / 2) :=
    Real.one_le_rpow (LeanLab.Xi2012.one_lt_log hx).le (by positivity)
  have h := hC x (by omega) 1 le_rfl (by simpa using hq) 1
    (by norm_num) x (by positivity) le_rfl
  simpa only [Nat.totient_one, Nat.cast_one, div_one,
    show (2 : ℝ) * (c / 2) = c by ring] using h

/-- The all-primes case of the page 2 remark has no cited input. -/
theorem thetaNat_primes_total :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ x : ℕ, 3 ≤ x →
      |thetaNat (primesUpTo x) x 1 1 - x| ≤ C * x / Real.log x ^ c := by
  simpa only [one_mul] using
    (thetaNat_total_of_condition primesUpTo (fun _ => 1) siegelWalfiszNat_primes)

end LeanLab.Xi2012.NatEncoding

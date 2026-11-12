import LeanLab.ExceptionalSet.UpJ200.TailPartition385
import LeanLab.ExceptionalSet.PrimeKernel264

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.PrimeTail385`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Application of the unit block summation to the prime kernel tail.
Source: P0082 page 365, the derivation of display 24.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.PrimeTail385

open Real MeasureTheory Set ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC)

noncomputable section

/-- The prime kernel integrand in P0082 page 357 display 6. -/
def integrand (P X Δ v α : ℝ) : ℂ :=
  Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))

/-- Reflection preserves the absolute integrand, independently of the phase frequency.
Source: P0082 page 356 display 3 and page 365, the two tails. -/
theorem norm_integrand_neg (P X Δ v x : ℝ) :
    ‖integrand P X Δ v (-x)‖ = ‖integrand P X Δ v x‖ := by
  have he (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hs : Sp P X (-x) = conj (Sp P X x) := by
    simp only [Sp, map_sum, map_mul, Complex.conj_ofReal, he, neg_mul]
  have hk : Kfun Δ (-x) = Kfun Δ x := by
    simp only [Kfun, mul_neg, Real.sinc_neg]
  simp only [integrand, norm_mul, norm_pow, U1539.norm_eC, mul_one]
  rw [hs, Complex.norm_conj, hk]

/-- The positive prime kernel tail at an integer cutoff, P0082 page 365 before display 24. -/
theorem positive_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in Ioi (K : ℝ), ‖integrand P X Δ v α‖) ≤
      (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  let A := (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2)
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
  have hb (k : ℕ) (hk : K ≤ k) :
      (∫ α in (k : ℝ)..(k : ℝ) + 1, ‖integrand P X Δ v α‖) ≤ A / (k : ℝ) ^ 2 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    simpa only [integrand, A, div_div, mul_pow, mul_assoc] using
      PrimeEnergy385.prime_kernel_block_le P X Δ k v hX hΔ hΔ1 hk0
  simpa only [A, div_div] using
    TailPartition385.integral_Ioi_le_of_blocks _ hf K hK A hA hb

/-- Both prime kernel tails at an integer cutoff, P0082 page 365 before display 24. -/
theorem outside_nat_tail_le (P X Δ v : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, ‖integrand P X Δ v α‖) ≤
      2 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := by
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
  have hn : (∫ α in Iio (-(K : ℝ)), ‖integrand P X Δ v α‖) =
      (∫ α in Ioi (K : ℝ), ‖integrand P X Δ v α‖) := by
    rw [← integral_Iic_eq_integral_Iio,
      ← integral_comp_neg_Ioi (K : ℝ) (fun α => ‖integrand P X Δ v α‖)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun α _ => norm_integrand_neg P X Δ v α)
  have hd : Disjoint (Iio (-(K : ℝ))) (Ioi (K : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h1 : x < -(K : ℝ) := hx
    have h2 : (K : ℝ) < x := hy
    have h0 := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hset : (Icc (-(K : ℝ)) (K : ℝ))ᶜ = Iio (-(K : ℝ)) ∪ Ioi (K : ℝ) := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  rw [hset, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn, hn]
  have h := positive_tail_le P X Δ v hX hΔ hΔ1 K hK
  calc _ ≤ (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) +
      (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * ((K : ℝ) - 1)) := add_le_add h h
    _ = _ := by ring

end

end LeanLab.ExceptionalSet.UpJ200.PrimeTail385

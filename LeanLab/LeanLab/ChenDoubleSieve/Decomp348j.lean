import LeanLab.ChenPrimeExceptional.Task101PowerCutoffs
import LeanLab.ChenDoubleSieve.Decomp348i

/-!
Prime reciprocal power intervals for the partial summation in equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The existing task101 Mertens block estimate is reused unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open LeanLab.PNTSieve.Mertens (E)

/-- The reciprocal prime mass on a fixed interval of positive exponents. -/
def powerPrimeMass (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
    1 / (p : ℝ)

/-- Prime reciprocal mass on power intervals tends to the logarithmic ratio. -/
theorem powerPrimeMass_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (powerPrimeMass a b) atTop (𝓝 (log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hy : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ a⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have hlogy : Tendsto (fun N : ℕ => log (⌊(N : ℝ) ^ a⌋₊ : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hy)
  have herrbound : Tendsto (fun N : ℕ => 22 / log (⌊(N : ℝ) ^ a⌋₊ : ℝ))
      atTop (𝓝 0) := hlogy.const_div_atTop 22
  have hlogratio : Tendsto (fun N : ℕ =>
      log (log (⌊(N : ℝ) ^ b⌋₊ : ℝ) / log (⌊(N : ℝ) ^ a⌋₊ : ℝ)))
      atTop (𝓝 (log (b / a))) :=
    (LeanLab.ChenPrimeExceptional.Task101.log_floor_rpow_ratio hb ha).log (div_pos hb ha).ne'
  have herr : Tendsto (fun N : ℕ => powerPrimeMass a b N -
      log (log (⌊(N : ℝ) ^ b⌋₊ : ℝ) / log (⌊(N : ℝ) ^ a⌋₊ : ℝ)))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ herrbound
    filter_upwards [hy.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)] with N hyN hN
    have horder : ⌊(N : ℝ) ^ a⌋₊ ≤ ⌊(N : ℝ) ^ b⌋₊ :=
      Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
    have he := LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_error hyN horder
    have hya : 0 < log (⌊(N : ℝ) ^ a⌋₊ : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < ⌊(N : ℝ) ^ a⌋₊ by omega))
    have hwb : 0 < log (⌊(N : ℝ) ^ b⌋₊ : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < ⌊(N : ℝ) ^ b⌋₊ by omega))
    rw [log_div hwb.ne' hya.ne']
    unfold powerPrimeMass
    rw [LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_eq horder]
    exact he
  have ht := herr.add hlogratio
  simpa using ht

end LeanLab.ChenDoubleSieve.Task348

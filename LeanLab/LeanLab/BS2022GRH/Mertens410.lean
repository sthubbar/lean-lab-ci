/- AI wrote this Lean code for CODEX task410.
The lower half of Schoenfeld Corollary 3 from the sharp reciprocal estimate.
Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169c

namespace LeanLab.BS2022GRH.Mertens410
open Real Finset
noncomputable section

/-- The finite logarithmic correction dominates its convergent full sum.
Schoenfeld p. 341 displays 6.25 and 6.27. The common constant is already identified. -/
theorem log_product_correction_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    DecompC169c.mertensConstant - eulerMascheroniConstant ≤
      log (∏ p ∈ S, (1 - 1 / (p : ℝ))) + ∑ p ∈ S, (1 : ℝ) / p := by
  have hpPos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hd : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hnonpos (p : {p : ℕ // p.Prime}) :
      log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ) ≤ 0 := by
    have h := log_le_sub_one_of_pos (hpPos p.1 p.2)
    linarith
  have h := DecompC169c.mertens_correction_summable.neg.sum_le_tsum (S.subtype Nat.Prime)
    (fun p _ => neg_nonneg.mpr (hnonpos p))
  rw [sum_neg_distrib, tsum_neg] at h
  have hc : (∑' p : {p : ℕ // p.Prime},
      (log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))) ≤
      ∑ p ∈ S.subtype Nat.Prime, (log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)) := by
    linarith
  rw [sum_subtype_of_mem (fun p : ℕ => log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) hS] at hc
  rw [DecompC169c.mertensConstant, log_prod (fun p hp => (hpPos p (hS p hp)).ne'),
    ← sum_add_distrib]
  linarith

/-- A sharp reciprocal upper bound supplies the ordinary product lower bound.
This proves the lower calculation in Schoenfeld p. 341 display 6.27 and p. 342.
CONDITIONAL ON the displayed reciprocal estimate. -/
theorem ordinary_product_lower_of_reciprocal (x E : ℝ) (hx : 1 < x)
    (hrec : (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤
      log (log x) + DecompC169c.mertensConstant + E) :
    exp (-eulerMascheroniConstant) / log x * (1 - E) ≤
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ)) := by
  have hpPos (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) : 0 < 1 - 1 / (p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hd : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hc := log_product_correction_lower (Nat.primesLE ⌊x⌋₊)
    (fun p hp => Nat.prime_of_mem_primesLE hp)
  have hlog : -eulerMascheroniConstant - log (log x) - E ≤
      log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ))) := by linarith
  have he := exp_le_exp.mpr hlog
  rw [exp_log (prod_pos hpPos)] at he
  have hid : exp (-eulerMascheroniConstant - log (log x) - E) =
      exp (-eulerMascheroniConstant) / log x * exp (-E) := by
    rw [show -eulerMascheroniConstant - log (log x) - E =
      -eulerMascheroniConstant + -log (log x) + -E by ring,
      exp_add, exp_add, exp_neg (log (log x)), exp_log (log_pos hx)]
    ring
  rw [hid] at he
  have hE : 1 - E ≤ exp (-E) := by linarith [add_one_le_exp (-E)]
  exact (mul_le_mul_of_nonneg_left hE (div_nonneg (exp_pos _).le (log_pos hx).le)).trans he

end
end LeanLab.BS2022GRH.Mertens410
#print axioms LeanLab.BS2022GRH.Mertens410.log_product_correction_lower
#print axioms LeanLab.BS2022GRH.Mertens410.ordinary_product_lower_of_reciprocal

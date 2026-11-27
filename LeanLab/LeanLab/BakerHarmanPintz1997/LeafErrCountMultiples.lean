import Mathlib.Data.Nat.Factorization.Basic

namespace LeanLab.BakerHarmanPintz1997.Decomp409b

open Finset

/-- The multiples in a natural interval correspond to their quotients. -/
theorem leaf_err_count_multiples_card (A B q : ℕ) (hq : 0 < q) :
    ((Ioc A B).filter (fun k => q ∣ k)).card = B / q - A / q := by
  classical
  calc
    _ = (Ioc (A / q) (B / q)).card := by
      apply Finset.card_bij (fun k _ => k / q)
      · intro k hk
        obtain ⟨hk, hd⟩ := mem_filter.mp hk
        obtain ⟨hAk, hkB⟩ := mem_Ioc.mp hk
        apply mem_Ioc.mpr
        constructor
        · apply (Nat.div_lt_iff_lt_mul hq).mpr
          simpa [Nat.div_mul_cancel hd] using hAk
        · exact Nat.div_le_div_right hkB
      · intro k hk l hl hkl
        have hkq := Nat.div_mul_cancel (mem_filter.mp hk).2
        have hlq := Nat.div_mul_cancel (mem_filter.mp hl).2
        exact hkq.symm.trans ((congrArg (fun t => t * q) hkl).trans hlq)
      · intro j hj
        obtain ⟨hAj, hjB⟩ := mem_Ioc.mp hj
        refine ⟨j * q, mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, dvd_mul_left q j⟩, ?_⟩
        · exact (Nat.div_lt_iff_lt_mul hq).mp hAj
        · exact (Nat.le_div_iff_mul_le hq).mp hjB
        · exact Nat.mul_div_cancel j hq
    _ = _ := Nat.card_Ioc _ _

#print axioms leaf_err_count_multiples_card

end LeanLab.BakerHarmanPintz1997.Decomp409b

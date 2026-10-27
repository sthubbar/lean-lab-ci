/-
Saouter 1998, P0018, unit U-0361, run 20261018T0103Z-27139. The generic block step of
Saouter1998/Ladder.lean, restated here so the B = 10^9 ladder does not import the 402 modules of
the B = 10^8 ladder. Same proofs. AI-written Lean code, Claude, 2026-10-18.
-/
import LeanLab.Saouter1998.Lucas
import LeanLab.Saouter1998.ChainDef

namespace LeanLab.Saouter1998.B9

open LeanLab.HelfgottPlatt LeanLab.Saouter1998

theorem chainC_sound (B : ℕ) : ∀ (l : List ℕ) (a : ℕ), Core.chainC B a l = true →
    (a :: l).IsChain (LadderStep B)
  | [], a, _ => List.IsChain.singleton a
  | b :: t, a, h => by
    simp only [Core.chainC, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons ⟨h.1.1, h.1.2⟩ (chainC_sound B t b h.2)

/-- One block of Saouter's ladder extends the ternary range from `a + B` to `last + B`. -/
theorem step {B a last : ℕ} {C : List Core.Cert} (hB : EvenGoldbachUpTo B) (h4 : 4 ≤ B)
    (hT : TernaryGoldbachUpTo (a + B)) (ha : a.Prime) (ha3 : 3 ≤ a)
    (hc : C.all Core.certB = true) (hk : Core.chk B a last C = true) :
    TernaryGoldbachUpTo (last + B) ∧ last.Prime ∧ 3 ≤ last := by
  simp only [Core.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  obtain ⟨⟨hch, hlast⟩, hal⟩ := hk
  have hpr := all_prime_of_certs hc
  have hmem : last ∈ C.map Prod.fst := List.mem_of_getLast? hlast
  have hD : (C.map Prod.fst).getLastD a = last := by
    rw [List.getLastD_eq_getLast?, hlast]; rfl
  refine ⟨?_, hpr last hmem, by omega⟩
  intro n hn h7 hnX
  by_cases hs : n ≤ a + B
  · exact hT n hn h7 hs
  · exact ternary_of_ladder_aux hB (C.map Prod.fst) a ha ha3 hpr (chainC_sound B _ a hch) n hn
      (by omega) (by rw [hD]; exact hnX)

/-- The bottom rung: the prime 3 alone covers odd n up to 3 + B. -/
theorem base {B : ℕ} (hB : EvenGoldbachUpTo B) : TernaryGoldbachUpTo (3 + B) :=
  ternary_of_ladder hB [] (by simp) (List.IsChain.singleton 3) le_rfl

end LeanLab.Saouter1998.B9

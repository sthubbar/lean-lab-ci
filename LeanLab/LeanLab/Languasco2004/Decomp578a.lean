/-
Jia 1996 pages 252, 253 and 278 to 284.
Source https://doi.org/10.4064/aa-77-3-207-287.
Separate source estimates for the region one transfers.
All source estimates remain OPEN. Assemblies are CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565c
import LeanLab.Languasco2004.Numeric565
import LeanLab.Languasco2004.Feed578aPair

namespace LeanLab.Languasco2004.Decomp578a
open Finset Real Decomp279a Decomp316a Source565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 283 and 284 support: enlarge an exceptional predicate by pointwise inclusion.
The eventual threshold is kept separate from the epsilon cutoff. -/
theorem exceptional_mono (P Q : ℝ → ℝ → ℕ → Prop)
    (hQ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (Q ε N)).card : ℝ) ≤ C * windowLength N ε / log N ^ B)
    (hPQ : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ N : ℝ, T ≤ N →
      ∀ n ∈ window N ε, P ε N n → Q ε N n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (P ε N)).card : ℝ) ≤ C * windowLength N ε / log N ^ B := by
  obtain ⟨e, he, hQ⟩ := hQ
  refine ⟨e, he, ?_⟩
  intro ε B hε hεe hB
  obtain ⟨C, N₀, hC⟩ := hQ ε B hε hεe hB
  obtain ⟨T, hT⟩ := hPQ ε hε
  refine ⟨C, max N₀ T, ?_⟩
  intro N hN
  have hsub : (window N ε).filter (P ε N) ⊆ (window N ε).filter (Q ε N) := by
    intro n hn
    obtain ⟨hn, hP⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn, hT N ((le_max_right _ _).trans hN) n hn hP⟩
  have hc : (((window N ε).filter (P ε N)).card : ℝ) ≤
      (((window N ε).filter (Q ε N)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (hC N ((le_max_left _ _).trans hN))

/-- Displays 58 and 62 support: two half budgets control the sum of two errors.
This is finite exceptional set bookkeeping with no distribution premise. -/
theorem exceptional_add (f g S : ℝ → ℝ → ℕ → ℝ) (c : ℝ)
    (hf : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n => (c / 2) * S ε N n < f ε N n)).card : ℝ) ≤
          C * windowLength N ε / log N ^ B)
    (hg : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n => (c / 2) * S ε N n < g ε N n)).card : ℝ) ≤
          C * windowLength N ε / log N ^ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (fun n => c * S ε N n < f ε N n + g ε N n)).card : ℝ) ≤
          C * windowLength N ε / log N ^ B := by
  apply exceptional_mono _ _ (exceptional_union _ _ hf hg)
  intro ε hε
  refine ⟨0, ?_⟩
  intro N hN n hn hbad
  by_contra h
  obtain ⟨hf, hg⟩ := not_or.mp h
  have hf' := le_of_not_gt hf
  have hg' := le_of_not_gt hg
  linarith

/-- Page 252 Lemma 16: the trilinear progression remainder on dyadic prime blocks.
Finite caps agree with the source in the eventual localization range. -/
def trilinearRemainder (N Y P Q R : ℝ) (n : ℕ) (a b c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P ∧ Nat.Coprime p n),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧ Q < q ∧ (q : ℝ) ≤ 2 * Q ∧ Nat.Coprime q n),
      ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ R < r ∧ (r : ℝ) ≤ 2 * R ∧ Nat.Coprime r n),
        a p * b q * c r *
          ((Decomp565c.progressionCount N Y n (p * q * r) : ℝ) -
            Y / ((Nat.totient (p * q * r) : ℝ) * log N))

/-- LEAF. Jia page 252 Lemma 16 and its page 253 proof from Lemmas 14 and 15.
The displayed trilinear remainder is distinct from the sieve transfer in display 62.
Both constants in the exceptional estimate are explicit. Bounded weights are normalized to one.
Only region i is needed for region one of Lemma 28. -/
theorem lemma16_progression_input :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ P Q R : ℝ → ℝ, ∀ a b c : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (16 / 135 : ℝ) ≤ R N ∧ R N ≤ Q N ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ P N ∧
        P N ≤ (localization N ε) ^ (89 / 462 : ℝ) ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ Q N ∧ Q N ≤ P N) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1 ∧ |b N m| ≤ 1 ∧ |c N m| ≤ 1) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * localization N ε / log N ^ B <
          |trilinearRemainder N (localization N ε) (P N) (Q N) (R N) n (a N) (b N) (c N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by sorry

/-- LEAF. Jia page 283 display 58, using page 278 upper and lower linear sieve comparison.
CONDITIONAL ON the unchanged page 253 Lemma 17 input.
This estimates only the pair low cutoff count, not the combined Iwaniec error. -/
theorem pair_sieve_transfer (h17 : type_of% Decomp565c.lemma17_progression_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |pairMass false true N (localization N ε) n ((localization N ε) ^ delta ε) -
            singular n / log N * pairMass true true N (localization N ε) n ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := Feed578aPair.pair_sieve_transfer_from_leaves h17

/-- LEAF. Jia page 284 display 62, with the page 278 linear sieve comparison.
CONDITIONAL ON the page 252 trilinear progression remainder of Lemma 16.
This estimates only the triple low cutoff count. -/
theorem triple_sieve_transfer (h16 : type_of% lemma16_progression_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |tripleMass false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleMass true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia displays 58 and 62: exact supplied type of the sealed iwaniec_transfer.
CONDITIONAL ON the two single transfer leaves, Lemma 16 and the unchanged Lemma 17. -/
theorem iwaniec_transfer_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < iwaniecError true N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  have h := exceptional_add
    (fun ε N n => |pairMass false true N (localization N ε) n ((localization N ε) ^ delta ε) -
      singular n / log N * pairMass true true N (localization N ε) n ((localization N ε) ^ delta ε)|)
    (fun ε N n => |tripleMass false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
      singular n / log N * tripleMass true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)
    (fun ε N n => scale N (localization N ε) n) 0.0000001
    (by convert pair_sieve_transfer Decomp565c.lemma17_progression_input using 1 <;> congr! <;> norm_num)
    (by convert triple_sieve_transfer lemma16_progression_input using 1 <;> congr! <;> norm_num)
  convert h using 1 <;> simp only [iwaniecError] <;> congr!

#print axioms exceptional_mono
#print axioms exceptional_add
#print axioms trilinearRemainder
#print axioms lemma16_progression_input
#print axioms pair_sieve_transfer
#print axioms triple_sieve_transfer
#print axioms iwaniec_transfer_from_parts
end
end LeanLab.Languasco2004.Decomp578a

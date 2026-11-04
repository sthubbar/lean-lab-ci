/-
AI wrote this Lean code for CODEX task295.
P0037 Section 2 page 207 and Section 5.2 page 212.
This connects the existing bitmap checker to the sealed Boolean leaf format.
It is CONDITIONAL ON the supplied prime certificates and bitmap equality.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Shift

namespace LeanLab.DtRS1998.Task295.Coverage

open LeanLab.Verifications.Top50.Bits

/-- A local obstruction for the smooth-factor endpoint search.
Supporting experiment for P0037 Section 5.2 page 212. -/
theorem complement_residue_obstruction (N p q : ℕ) (hN : N % 3 = 1)
    (hs : p + q = N) (hq : 3 < q) (hprime : q.Prime) : p % 3 ≠ 1 := by
  intro hp
  have hq0 : q % 3 = 0 := by omega
  have hdiv : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq0
  have h := hprime.eq_one_or_self_of_dvd 3 hdiv
  omega

/-- The existing shifted bitmap supplies the exact finite Boolean certificate.
P0037 page 207, the recurrence for F, used on page 212.
CONDITIONAL ON the supplied prime certificates and accepted bitmap. -/
theorem certificate_of_bitmap {B L lo W : ℕ} (Ds : List ℕ)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (hlo : ∀ d ∈ Ds, lo ≤ d)
    (hQ : ∀ d ∈ Ds, d ≤ B ∧ (B - d).Prime)
    (hcover : wem 0 0 L &&& gmR (wpm2 lo W) (Ds.map (fun d => d - lo)) = wem 0 0 L) :
    ∃ qs : List ℕ, qs.length = Ds.length ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (L / 2 + 1)).all (fun j =>
        qs.any (fun q => decide (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  refine ⟨Ds.map (fun d => B - d), by simp, ?_, ?_⟩
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact (hQ d hd).2
  · apply List.all_eq_true.mpr
    intro j hj
    have hjL := List.mem_range.mp hj
    have hj2 : 2 * j ≤ L := by omega
    have hbit : (wem 0 0 L).testBit (2 * j) = true :=
      testBit_wem (lo := 0) (A := 0) (B := L) (n := 2 * j)
        le_rfl (Nat.zero_le _) hj2 (by simp)
    rw [← hcover, Nat.testBit_and, Bool.and_eq_true] at hbit
    obtain ⟨s, hs, hp⟩ := of_gmR _ _ (2 * j) hbit.2
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
    have hprime := prime_of_wpm2 h2 hW hp
    obtain ⟨hdB, _⟩ := hQ d hd
    have hld := hlo d hd
    apply List.any_eq_true.mpr
    refine ⟨B - d, List.mem_map.mpr ⟨d, hd, rfl⟩, decide_eq_true ?_⟩
    refine ⟨by omega, ?_⟩
    rw [show B + 2 * j - (B - d) = lo + (2 * j + (d - lo)) by omega]
    exact hprime

/-- The nonempty interval from 6 through 10 satisfies every checker hypothesis.
P0037 page 207, a concrete instance of the recurrence. -/
theorem bitmap_instance :
    ∃ qs : List ℕ, qs.length = 1 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (4 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide (q ≤ 6 + 2 * j ∧ (6 + 2 * j - q).Prime))) = true := by
  apply certificate_of_bitmap (B := 6) (L := 4) (lo := 2) (W := 6) [3]
    (by decide) (by decide)
  · intro d hd
    rcases List.mem_singleton.mp hd with rfl
    decide
  · intro d hd
    rcases List.mem_singleton.mp hd with rfl
    decide
  · decide +kernel

#print axioms certificate_of_bitmap
#print axioms bitmap_instance
#print axioms complement_residue_obstruction

end LeanLab.DtRS1998.Task295.Coverage

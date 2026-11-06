import LeanLab.Ricci1937.Decomp338s

/-!
Ricci 1937, finite mixed W count supplier.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Clean supply of the finite mixed Z leaf for both shift signs.
First memoir pages 75, 88 and 89 and second memoir pages 106, 107 and 115.
The actual additive residue conditions supply the encoded density main term. -/
theorem decomp338_mixed_z_finite_proved (a b ξ N t v : ℕ) (m : ℤ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1)) (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap (2 * m.natAbs) v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by

  let P := Nat.primesLE t
  let h := 2 * m.natAbs
  let k := if 0 ≤ m then 0 else h
  let F := decomp338MixedZProduct h k v t
  let H := decomp338EncodedGap h v t
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ P) :
      |(#{x ∈ range N | (∏ p ∈ S, p) ∣ F x} : ℝ) - (N : ℝ) * ∏ p ∈ S, nuN H p| ≤
        cnt H (∏ p ∈ S, p) := decomp338_mixed_Z_remainder h k N v t S hS
  have hraw := decompJ365_decreasing_lower_explicit (range N) P J F hP cutoff level H N
    (nuN H) herror L hL hlevel
  apply hraw.trans
  have hincl : #{x ∈ range N | ∀ p ∈ P, ¬p ∣ F x} ≤
      #{x ∈ range N | (∀ p ∈ Nat.primesLE v, ¬p ∣ x * (x + h)) ∧
        ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ x + k} := by
    apply card_le_card
    intro x hx
    obtain ⟨hxN, hsurv⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hxN, ?_, ?_⟩
    · intro p hp hd
      obtain ⟨hpv, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpP : p ∈ P := Nat.mem_primesLE.mpr ⟨hpv.trans hvt, hpprime⟩
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_pos hpv] using hd
    · intro p hp hd
      obtain ⟨hpP, hpv⟩ := mem_sdiff.mp hp
      have hpv' : ¬p ≤ v := fun h => hpv (Nat.mem_primesLE.mpr ⟨h, hP p hpP⟩)
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_neg hpv'] using hd
  exact_mod_cast hincl.trans (decomp338_mixed_survivors_le_zCount a b ξ N t v m hv hvt hN hsizeA hsizeB hthA hthB)

end
end LeanLab.Ricci1937

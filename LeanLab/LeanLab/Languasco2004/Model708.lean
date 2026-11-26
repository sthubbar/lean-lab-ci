/-
Jia 1996 pages 262, 263 and 279, Lemma 21 and display 48.
Source https://doi.org/10.4064/aa-77-3-207-287.
Exact cofactor form of the sealed Omega4 integer count.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Cofactor708
import LeanLab.Languasco2004.Decomp568a
namespace LeanLab.Languasco2004.Model708
open Finset Real Decomp568a Cofactor708
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 263 and 279 support: the selected prime factors are not removed
by the strict cutoff q. The model is exactly the ordinary rough cofactor count. -/
theorem modelSifted_eq_cofactor (Y : ℝ) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≤ p) :
    modelSifted Y (p * q) q =
      ((Ioc ⌊Y / ((p * q : ℕ) : ℝ)⌋₊ ⌊2 * (Y / ((p * q : ℕ) : ℝ))⌋₊).filter
        (fun m => ∀ r : ℕ, r.Prime → (r : ℝ) < q → ¬ r ∣ m)).card := by
  have hrough : ∀ r : ℕ, r.Prime → (r : ℝ) < q → ¬ r ∣ p * q := by
    intro r hr hrq hrd
    have hrq' : r < q := by exact_mod_cast hrq
    rcases hr.dvd_mul.mp hrd with hrp | hrq
    · have he : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
      omega
    · have he : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
      omega
  have hc := sifted_multiples_card ⌊Y⌋₊ ⌊2 * Y⌋₊ (p * q) q
    (Nat.mul_pos hp.pos hq.pos) hrough
  change modelSifted Y (p * q) q = _ at hc
  simpa only [← mul_div_assoc, Nat.floor_div_natCast] using hc

#print axioms modelSifted_eq_cofactor
end
end LeanLab.Languasco2004.Model708

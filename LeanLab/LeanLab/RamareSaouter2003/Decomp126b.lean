import Mathlib

/-!
P0099, Lemma 8 and its written proof on p. 27.
The factorization parameters are positive natural numbers.
The congruence base is an integer, as in the paper.
AI wrote this Lean code. Binary Goldbach is OPEN.
The assembly remains CONDITIONAL ON the external Pocklington leaf.
-/

namespace LeanLab.RamareSaouter2003.Decomp126b

/-- CITED. Lemma 8, p. 27. The complete known factorization of the positive
even F is represented by the condition for every prime divisor of F. -/
def lemma8_stmt : Prop := ∀ N R F s r : ℕ,
    2 ≤ N → 2 ≤ F → Even F → Nat.Coprime R F → Odd N →
    N = R * F + 1 → R = 2 * F * s + r → r < 2 * F → N < 2 * F ^ 3 →
    (∃ a : ℤ, Int.ModEq (N : ℤ) (a ^ (N - 1)) 1 ∧
      ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) →
    (N.Prime ↔ s = 0 ∨ ¬ IsSquare ((r : ℤ) ^ 2 - 8 * s))

/-- LEAF. The coprimality and evenness assumptions make R odd.
Lemma 8, p. 27, the parity needed in identifying the two factors. -/
theorem odd_R {R F : ℕ} (hcop : Nat.Coprime R F) (hF : Even F) : Odd R := by
  have h2 : 2 ∣ F := even_iff_two_dvd.mp hF
  have hc : Nat.Coprime R 2 := hcop.of_dvd_right h2
  exact Nat.Coprime.odd_of_right hc

/-- LEAF. The Pocklington divisor property used in the first sentence of the
proof of Lemma 8 on p. 27. External source: Brillhart, Lehmer and Selfridge,
New primality criteria and factorizations of 2^m plus or minus 1, reference 6.
Every divisor greater than one is one modulo F. -/
theorem pocklington_divisors {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hN : N = R * F + 1) {a : ℤ} (ha : Int.ModEq (N : ℤ) (a ^ (N - 1)) 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1 := by
  sorry

/-- LEAF. A composite N with the Pocklington divisor property has a grouping
into two factors giving r = u + v and 2s = uv. The size and parity argument
is the middle of the written proof of Lemma 8, p. 27. -/
theorem composite_roots {N R F s r : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hF : Even F) (hRodd : Odd R) (hN : N = R * F + 1)
    (hR : R = 2 * F * s + r) (hr : r < 2 * F) (hbound : N < 2 * F ^ 3)
    (hdiv : ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1)
    (hcomp : ¬ N.Prime) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u + v ∧ 2 * s = u * v := by
  obtain ⟨d, e, hdN, heN, hde⟩ := (Nat.not_prime_iff_exists_mul_eq hN2).mp hcomp
  have hd2 : 1 < d := by
    by_contra h
    have hh : d = 0 ∨ d = 1 := by omega
    rcases hh with rfl | rfl <;> simp_all
  have he2 : 1 < e := by
    by_contra h
    have hh : e = 0 ∨ e = 1 := by omega
    rcases hh with rfl | rfl <;> simp_all
  obtain ⟨u, hu, hdu⟩ := hdiv d ⟨e, hde.symm⟩ hd2
  obtain ⟨v, hv, hev⟩ := hdiv e ⟨d, by nlinarith [hde]⟩ he2
  have hfactors : N = (u * F + 1) * (v * F + 1) := by rw [← hde, hdu, hev]
  have hprod : u + v ≤ u * v + 1 := by
    have hz : (u : ℤ) + v ≤ u * v + 1 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ (u : ℤ) - 1 by omega)
        (show (0 : ℤ) ≤ (v : ℤ) - 1 by omega)]
    exact_mod_cast hz
  have hsum : u + v < 2 * F := by
    by_contra h
    have hh : 2 * F ≤ u + v := by omega
    have h1 := mul_le_mul_of_nonneg_right (show 2 * F ≤ u * v + 1 by omega) (Nat.zero_le (F ^ 2))
    have h2 := mul_le_mul_of_nonneg_right hh (Nat.zero_le F)
    nlinarith [hfactors]
  have hReq : R = F * (u * v) + u + v := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < F by omega)
    nlinarith [hN, hfactors]
  have hFmod : F % 2 = 0 := Nat.even_iff.mp hF
  have hRmod : R % 2 = 1 := Nat.odd_iff.mp hRodd
  have hsumodd : (u + v) % 2 = 1 := by
    rw [hReq] at hRmod
    simpa [Nat.add_mod, Nat.mul_mod, hFmod] using hRmod
  have huvmod : (u * v) % 2 = 0 := by
    have hupar : u % 2 = 0 ∨ u % 2 = 1 := by omega
    have hvpar : v % 2 = 0 ∨ v % 2 = 1 := by omega
    rcases hupar with hupar | hupar <;> rcases hvpar with hvpar | hvpar <;>
      simp_all [Nat.add_mod, Nat.mul_mod]
  obtain ⟨w, hw⟩ := Nat.dvd_of_mod_eq_zero huvmod
  have hrem : R % (2 * F) = r := by
    rw [hR]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  have hrem' : R % (2 * F) = u + v := by
    rw [hReq, hw]
    rw [show F * (2 * w) + u + v = (2 * F) * w + (u + v) by ring]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hsum]
  have hroot : r = u + v := hrem.symm.trans hrem'
  refine ⟨u, v, hu, hv, hroot, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < F by omega)
  nlinarith [hR, hReq, hroot]

/-- LEAF. The discriminant identity at the end of the proof of Lemma 8,
p. 27. A factor pair gives the square of u minus v. -/
theorem discriminant_of_roots {r s u v : ℕ} (hr : r = u + v) (hs : 2 * s = u * v) :
    IsSquare ((r : ℤ) ^ 2 - 8 * s) := by
  have hrZ : (r : ℤ) = (u : ℤ) + v := by exact_mod_cast hr
  have hsZ : (2 : ℤ) * s = (u : ℤ) * v := by exact_mod_cast hs
  have hquad : (1 : ℤ) * ((u : ℤ) * u) + (-(r : ℤ)) * u + 2 * s = 0 := by
    nlinarith
  have hd := discrim_eq_sq_of_quadratic_eq_zero hquad
  have he : (r : ℤ) ^ 2 - 8 * s = (2 * (u : ℤ) - r) ^ 2 := by
    dsimp [discrim] at hd
    nlinarith [hd]
  rw [he]
  exact IsSquare.sq _

/-- LEAF. The converse quadratic step implicit in the iff of Lemma 8,
p. 27. A square discriminant and positive s give positive natural roots. -/
theorem roots_of_square {r s : ℕ} (hs : 0 < s) (hdisc : IsSquare ((r : ℤ) ^ 2 - 8 * s)) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ r = u + v ∧ 2 * s = u * v := by
  obtain ⟨z, hz⟩ := hdisc
  let d : ℕ := z.natAbs
  have habs : ((d : ℕ) : ℤ) ^ 2 = z ^ 2 := Int.natAbs_sq z
  have hsq : (r : ℤ) ^ 2 = 8 * s + (d : ℤ) ^ 2 := by nlinarith [hz, habs]
  have hnat : r ^ 2 = 8 * s + d ^ 2 := by exact_mod_cast hsq
  have hlt : d < r := by nlinarith
  have hmod := congrArg (fun x : ℕ => x % 2) hnat
  have hpar : (r + d) % 2 = 0 := by
    have hrpar : r % 2 = 0 ∨ r % 2 = 1 := by omega
    have hdpar : d % 2 = 0 ∨ d % 2 = 1 := by omega
    rcases hrpar with hrpar | hrpar <;> rcases hdpar with hdpar | hdpar <;>
      (norm_num [Nat.add_mod, Nat.mul_mod, pow_two, hrpar, hdpar] at hmod <;>
        norm_num [Nat.add_mod, Nat.mul_mod, pow_two, hrpar, hdpar])
  have hdiffpar : (r - d) % 2 = 0 := by omega
  let u := (r - d) / 2
  let v := (r + d) / 2
  have hu2 : 2 * u = r - d := by dsimp [u]; omega
  have hv2 : 2 * v = r + d := by dsimp [v]; omega
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hsum : r = u + v := by omega
  refine ⟨u, v, hu, hv, hsum, ?_⟩
  have huZ : (2 : ℤ) * u = (r : ℤ) - d := by
    rw [← Nat.cast_sub hlt.le]
    exact_mod_cast hu2
  have hvZ : (2 : ℤ) * v = (r : ℤ) + d := by exact_mod_cast hv2
  have hprodZ : (4 : ℤ) * u * v = 8 * s := by
    calc
      (4 : ℤ) * u * v = (2 * (u : ℤ)) * (2 * (v : ℤ)) := by ring
      _ = ((r : ℤ) - d) * ((r : ℤ) + d) := by rw [huZ, hvZ]
      _ = 8 * s := by nlinarith [hsq]
  have hp : (2 : ℤ) * s = (u : ℤ) * v := by nlinarith [hprodZ]
  exact_mod_cast hp

/-- LEAF. Expanding the two factors from the quadratic roots recovers N.
The displayed product in the proof of Lemma 8, p. 27. -/
theorem factorization_of_roots {N R F s r u v : ℕ} (hN : N = R * F + 1)
    (hR : R = 2 * F * s + r) (hr : r = u + v) (hs : 2 * s = u * v) :
    N = (u * F + 1) * (v * F + 1) := by
  rw [hN, hR, hr]
  calc
    (2 * F * s + (u + v)) * F + 1 = (2 * s) * F ^ 2 + (u + v) * F + 1 := by ring
    _ = (u * F + 1) * (v * F + 1) := by rw [hs]; ring

/-- LEAF. Both reconstructed factors are proper when F is at least two
and the roots are positive. Lemma 8, p. 27, converse implication. -/
theorem not_prime_of_factorization {N F u v : ℕ} (hF : 2 ≤ F) (hu : 0 < u) (hv : 0 < v)
    (hN : N = (u * F + 1) * (v * F + 1)) : ¬ N.Prime := by
  have huF : 0 < u * F := mul_pos hu (by omega)
  have hvF : 0 < v * F := mul_pos hv (by omega)
  rw [hN]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- Lemma 8 assembled from the divisor property and arithmetic leaves.
No sorry occurs in the assembly. It is CONDITIONAL ON all remaining leaves. -/
theorem lemma8 : lemma8_stmt := by
  intro N R F s r hN2 hF2 hF hcop _hOdd hN hR hr hbound hcert
  obtain ⟨a, ha, hgcd⟩ := hcert
  have hdiv := pocklington_divisors hN2 hF2 hN ha hgcd
  have hRodd := odd_R hcop hF
  constructor
  · intro hp
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      intro hdisc
      obtain ⟨u, v, hu, hv, hsum, hprod⟩ := roots_of_square (Nat.pos_of_ne_zero hs) hdisc
      exact not_prime_of_factorization hF2 hu hv (factorization_of_roots hN hR hsum hprod) hp
  · intro hc
    by_contra hn
    obtain ⟨u, v, hu, hv, hsum, hprod⟩ :=
      composite_roots hN2 hF2 hF hRodd hN hR hr hbound hdiv hn
    have hspos : 0 < s := by nlinarith [mul_pos hu hv]
    rcases hc with hs | hnot
    · omega
    · exact hnot (discriminant_of_roots hsum hprod)

end LeanLab.RamareSaouter2003.Decomp126b

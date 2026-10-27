import Mathlib

/-!
# R-0057, T3 MOONSHOT: Walsh-Fourier analysis on binary digits and Goldbach at N = 2^k

Unit U-1569, PC run 20261027T0004Z-17012. AI wrote this Lean code.

For `N = 2^k` write an odd `n < N` as `n = 2u + 1` with `u < 2^m`, `m = k - 1`. Then
`N - n = 2 (2^m - 1 - u) + 1`, and `2^m - 1 - u` is the bitwise complement of `u` on `m` bits.
So at powers of two the Goldbach reflection is a translation, XOR with all ones, in the group
`(Z/2)^m`, and the Goldbach count is a Boolean autocorrelation. The Walsh-Plancherel identity
then gives `2^m r(2^k) = Σ_S (-1)^|S| H(S)^2`, with `H` the Walsh transform of the odd prime
indicator in digit coordinates.

PROVED here, unconditional:
* `walsh_mul`: `χ_S(x ⊕ y) = χ_S(x) χ_S(y)`.
* `walsh_orth`: `Σ_S χ_S(x) = 2^m` if `x = 0`, else `0`.
* `walsh_autocorr`: `Σ_S H(S)^2 χ_S(c) = 2^m Σ_u f(u) f(u ⊕ c)`, any `f` into a commutative ring.
* `walsh_parseval`: the case `c = 0`; the energy over all `S` does not depend on the signs.
* `walsh_allones`: `χ_S(1,...,1) = (-1)^|S|`.
* `goldbach_pow_two_walsh`: the specialization at `c` all ones, the identity of the route.
* `reflect_pow_two`: `2^(m+1) - (2u+1) = 2 (2^m - 1 - u) + 1` for `u < 2^m`.
* `odd_energy_floor`: the exact split of the signed sum into even level energy minus odd level
  energy. With `walsh_parseval` this says `r(2^k) > 0` iff the odd level share of the Walsh
  energy is below one half; a sup bound `H(S)^2 ≤ σ` alone leaves the odd share up to
  `2^(m-1) σ`, the L2 wall. The last sentence is the plain-math reading, not a Lean statement.
* NOT formalized: that `bxor u (all ones)` read as a number is `2^m - 1 - u`; the route uses it
  through `reflect_pow_two` and the Python check `r_direct = r_walsh` for every m from 8 to 24.
KNOWN mathematics, folklore Walsh analysis. Binary Goldbach is OPEN; this is not progress on it.
-/

namespace LeanLab.Routes.U1569

open Finset BigOperators

variable {m : ℕ}

/-- The Walsh character `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}` on `Fin m → Bool`. -/
def chi (S : Finset (Fin m)) (x : Fin m → Bool) : ℤ :=
  ∏ i ∈ S, (if x i then -1 else 1)

/-- Pointwise XOR of bit vectors. -/
def bxor (x y : Fin m → Bool) : Fin m → Bool := fun i => xor (x i) (y i)

lemma sgn_xor (a b : Bool) :
    (if xor a b then (-1 : ℤ) else 1) = (if a then -1 else 1) * (if b then -1 else 1) := by
  cases a <;> cases b <;> simp

theorem walsh_mul (S : Finset (Fin m)) (x y : Fin m → Bool) :
    chi S (bxor x y) = chi S x * chi S y := by
  unfold chi bxor
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => sgn_xor _ _)

theorem walsh_orth (x : Fin m → Bool) :
    ∑ S : Finset (Fin m), chi S x = if x = fun _ => false then (2 : ℤ) ^ m else 0 := by
  have h : ∑ S : Finset (Fin m), chi S x =
      ∏ i : Fin m, ((if x i then (-1 : ℤ) else 1) + 1) := by
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one, chi]
    rw [Finset.powerset_univ]
  rw [h]
  split_ifs with hx
  · subst hx; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ false := by
      by_contra hc; push_neg at hc; exact hx (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp at hi; simp [hi]

/-- Walsh transform, unnormalized. -/
def H {R : Type*} [CommRing R] (f : (Fin m → Bool) → R) (S : Finset (Fin m)) : R :=
  ∑ u, f u * (chi S u : R)

lemma bxor_eq_zero_iff (u v c : Fin m → Bool) :
    bxor (bxor u v) c = (fun _ => false) ↔ v = bxor u c := by
  constructor
  · intro h; funext i; have := congrFun h i; simp [bxor] at this ⊢
    cases hu : u i <;> cases hv : v i <;> cases hc : c i <;> simp_all
  · intro h; subst h; funext i; simp [bxor]

theorem walsh_autocorr {R : Type*} [CommRing R] (f : (Fin m → Bool) → R) (c : Fin m → Bool) :
    ∑ S : Finset (Fin m), H f S * H f S * (chi S c : R) =
      (2 : R) ^ m * ∑ u, f u * f (bxor u c) := by
  have key : ∀ S : Finset (Fin m), H f S * H f S * (chi S c : R) =
      ∑ u, ∑ v, f u * f v * (chi S (bxor (bxor u v) c) : R) := by
    intro S
    simp only [H, Finset.sum_mul, Finset.mul_sum, walsh_mul]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    push_cast; ring
  simp only [key]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl (fun u _ => ?_)).trans (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ v, (∑ S : Finset (Fin m), (chi S (bxor (bxor u v) c) : R)) =
      if v = bxor u c then (2 : R) ^ m else 0 := by
    intro v
    have := congrArg (fun z : ℤ => (z : R)) (walsh_orth (bxor (bxor u v) c))
    simp only [Int.cast_sum] at this
    rw [this]
    simp only [bxor_eq_zero_iff]
    split_ifs <;> simp
  simp only [h2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem walsh_parseval {R : Type*} [CommRing R] (f : (Fin m → Bool) → R) :
    ∑ S : Finset (Fin m), H f S * H f S = (2 : R) ^ m * ∑ u, f u * f u := by
  have := walsh_autocorr f (fun _ => false)
  have hc : ∀ S : Finset (Fin m), chi S (fun _ => false) = 1 := by
    intro S; simp [chi]
  have hb : ∀ u : Fin m → Bool, bxor u (fun _ => false) = u := by
    intro u; funext i; simp [bxor]
  simpa [hc, hb] using this

theorem walsh_allones (S : Finset (Fin m)) : chi S (fun _ => true) = (-1) ^ S.card := by
  simp [chi]

/-- The route identity: with `f u = 1_P(2u+1)` this is `2^m r(2^(m+1)) = Σ_S (-1)^|S| H(S)^2`,
once `bxor u 1` is identified with the complement `2^m - 1 - u`, see `reflect_pow_two`. -/
theorem goldbach_pow_two_walsh {R : Type*} [CommRing R] (f : (Fin m → Bool) → R) :
    ∑ S : Finset (Fin m), ((-1 : R) ^ S.card) * (H f S * H f S) =
      (2 : R) ^ m * ∑ u, f u * f (bxor u (fun _ => true)) := by
  rw [← walsh_autocorr f (fun _ => true)]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [walsh_allones]; push_cast; ring

theorem reflect_pow_two (m u : ℕ) (hu : u < 2 ^ m) :
    2 ^ (m + 1) - (2 * u + 1) = 2 * (2 ^ m - 1 - u) + 1 := by
  rw [pow_succ]; omega

/-- The L2 wall in Walsh form: the signed sum is the main term plus even levels minus odd
levels; a nonnegativity statement for it is a statement about the odd level energy, and the
odd level energy is not bounded by any sup bound below `#odd sets · σ`. Here: the exact split. -/
theorem odd_energy_floor (h : Finset (Fin m) → ℤ) :
    ∑ S : Finset (Fin m), (-1) ^ S.card * h S =
      ∑ S ∈ univ.filter (fun S : Finset (Fin m) => Even S.card), h S -
      ∑ S ∈ univ.filter (fun S : Finset (Fin m) => ¬ Even S.card), h S := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun S : Finset (Fin m) => Even S.card)]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_filter.1 hS).2.neg_one_pow, one_mul])
  · exact Finset.sum_congr rfl (fun S hS => by
      rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hS).2).neg_one_pow]; ring)

/-- Vacuity and sanity: at `m = 2`, i.e. `N = 8`, with `f u = 1_P(2u+1)` on `u = 0,1,2,3`,
odd numbers `1,3,5,7`, the signed Walsh energy equals `4 · #{u : 2u+1, 7-2u both prime} = 4·2`. -/
def fEx : (Fin 2 → Bool) → ℤ := fun x =>
  let u := (if x 0 then 1 else 0) + 2 * (if x 1 then 1 else 0)
  if u = 0 then 0 else 1

example : ∑ S : Finset (Fin 2), ((-1 : ℤ) ^ S.card) * (H fEx S * H fEx S) = 4 * 2 := by
  rw [goldbach_pow_two_walsh]; decide

end LeanLab.Routes.U1569

#print axioms LeanLab.Routes.U1569.walsh_mul
#print axioms LeanLab.Routes.U1569.walsh_orth
#print axioms LeanLab.Routes.U1569.walsh_autocorr
#print axioms LeanLab.Routes.U1569.walsh_parseval
#print axioms LeanLab.Routes.U1569.walsh_allones
#print axioms LeanLab.Routes.U1569.goldbach_pow_two_walsh
#print axioms LeanLab.Routes.U1569.reflect_pow_two
#print axioms LeanLab.Routes.U1569.odd_energy_floor

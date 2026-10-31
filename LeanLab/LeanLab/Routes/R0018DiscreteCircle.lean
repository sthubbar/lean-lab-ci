/-
Route R-0018, T3 MOONSHOT: the discrete circle method at denominator N.

For a finite set `A` of integers in `(0, N)`, put `S a = ∑_{x ∈ A} ζ^{a x}` with `ζ = e(1/N)`.
Then `N · #{(x, y) ∈ A × A : x + y = N} = ∑_{a < N} S a ^ 2` EXACTLY, since `0 < x + y < 2N`
and `N ∣ x + y` forces `x + y = N`. With `A` the primes below `N` this is the binary Goldbach
count `r(N)` as a finite Fourier sum, a circle method that samples only the `N`-th roots of unity.

Lean content: `pair_count_identity` (the bilinear form), `goldbach_identity` (the exact
identity), `parseval_count` (Parseval), `l2_barrier` (|N r - |A|²| ≤ N |A| - |A|², the log
loss), and vacuity checks. The route's finding, numerical only, is in ROUTES.md R-0018:
the arcs with denominator q ∣ N and q small sum to about (N/φ(N)) π(N)²/N, not the
singular series 𝔖(N) π(N)²/N, so the arcs with q > √N carry a NEGATIVE term of main size,
about -(N/φ(N) - 𝔖(N)) π(N)²/N; for N = 2^20 that is about half of r(N).

AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

open Finset Complex

namespace LeanLab.Routes.R0018

/-- The root of unity `e(1/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The exponential sum `S(a/N) = ∑_{x ∈ A} e(a x / N)`. -/
noncomputable def S (N : ℕ) (A : Finset ℕ) (a : ℕ) : ℂ := ∑ x ∈ A, zeta N ^ (a * x)

/-- The ordered pair count `#{(x, y) ∈ A × B : x + y = N}`. -/
def pairCount (N : ℕ) (A B : Finset ℕ) : ℕ := ((A ×ˢ B).filter (fun p => p.1 + p.2 = N)).card

lemma zeta_prim {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N := by
  unfold zeta
  have := Complex.isPrimitiveRoot_exp N hN
  simpa [mul_div_assoc] using this

/-- Orthogonality: `∑_{a < N} ζ^{a m}` is `N` if `N ∣ m` and `0` otherwise. -/
lemma sum_zeta_pow {N : ℕ} (hN : N ≠ 0) (m : ℕ) :
    ∑ a ∈ range N, zeta N ^ (a * m) = if N ∣ m then (N : ℂ) else 0 := by
  have hp := zeta_prim hN
  have hrw : ∀ a, zeta N ^ (a * m) = (zeta N ^ m) ^ a := fun a => by
    rw [← pow_mul, mul_comm]
  simp_rw [hrw]
  split_ifs with hd
  · have h1 : zeta N ^ m = 1 := (hp.pow_eq_one_iff_dvd m).2 hd
    simp [h1]
  · have h1 : zeta N ^ m ≠ 1 := fun h => hd ((hp.pow_eq_one_iff_dvd m).1 h)
    rw [geom_sum_eq h1]
    have h2 : (zeta N ^ m) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]
    simp [h2]

/-- Bilinear form: `∑_{a < N} S_A(a) S_B(a) = N · #{(x, y) ∈ A × B : N ∣ x + y}`. -/
theorem pair_count_identity {N : ℕ} (hN : N ≠ 0) (A B : Finset ℕ) :
    ∑ a ∈ range N, S N A a * S N B a =
      (N : ℂ) * (((A ×ˢ B).filter (fun p => N ∣ p.1 + p.2)).card : ℂ) := by
  classical
  have h1 : ∀ a, S N A a * S N B a = ∑ p ∈ A ×ˢ B, zeta N ^ (a * (p.1 + p.2)) := by
    intro a
    unfold S
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← pow_add, mul_add]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [sum_zeta_pow hN]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

/-- For `0 < x, y < N`, `N ∣ x + y` exactly when `x + y = N`. -/
lemma dvd_iff_eq {N x y : ℕ} (hx : 0 < x) (hx' : x < N) (hy : 0 < y) (hy' : y < N) :
    N ∣ x + y ↔ x + y = N := by
  constructor
  · rintro ⟨k, hk⟩
    have hk1 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      have : N * 2 ≤ N * k := Nat.mul_le_mul_left N h
      omega
    have : k = 1 := by omega
    subst this; omega
  · intro h; exact ⟨1, by omega⟩

/-- **The discrete circle method at denominator `N`, exact.** For `A ⊆ (0, N)`,
`∑_{a < N} S(a/N)² = N · #{(x, y) ∈ A × A : x + y = N}`. With `A` the primes below `N`
the right side is `N r(N)`, the ordered binary Goldbach count. -/
theorem goldbach_identity {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) :
    ∑ a ∈ range N, S N A a ^ 2 = (N : ℂ) * (pairCount N A A : ℂ) := by
  classical
  simp_rw [sq]
  rw [pair_count_identity hN A A]
  congr 3
  refine Finset.filter_congr fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact dvd_iff_eq (hA _ hp.1).1 (hA _ hp.1).2 (hA _ hp.2).1 (hA _ hp.2).2

/-- The zero frequency is the trivial main term `|A|`. -/
lemma S_zero (N : ℕ) (A : Finset ℕ) : S N A 0 = (A.card : ℂ) := by
  simp [S]

lemma norm_zeta_pow {N : ℕ} (hN : N ≠ 0) (k : ℕ) : ‖zeta N ^ k‖ = 1 := by
  have hp := zeta_prim hN
  rw [norm_pow]
  have : ‖zeta N‖ = 1 := hp.norm'_eq_one hN
  rw [this, one_pow]

/-- `conj (S_A a) = S_B a` for `B = {N - y : y ∈ A}` when `A ⊆ [0, N]`. -/
lemma conj_S {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, x ≤ N) (a : ℕ) :
    (starRingEnd ℂ) (S N A a) = S N (A.image (fun y => N - y)) a := by
  classical
  have hp := zeta_prim hN
  have hinj : Set.InjOn (fun y => N - y) (A : Set ℕ) := by
    intro x hx y hy hxy
    have := hA x hx; have := hA y hy
    simp only at hxy; omega
  unfold S
  rw [map_sum, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyN := hA y hy
  have hn : ‖zeta N ^ (a * y)‖ = 1 := norm_zeta_pow hN _
  have hprod : zeta N ^ (a * y) * zeta N ^ (a * (N - y)) = 1 := by
    rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hyN, mul_comm, pow_mul, hp.pow_eq_one,
      one_pow]
  have hne : zeta N ^ (a * y) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hconj : (starRingEnd ℂ) (zeta N ^ (a * y)) = (zeta N ^ (a * y))⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
  rw [hconj]
  exact (eq_inv_of_mul_eq_one_right hprod).symm

/-- **Parseval at denominator `N`.** For `A ⊆ [0, N)`, `∑_{a < N} |S(a/N)|² = N |A|`. -/
theorem parseval_count {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, x < N) :
    ∑ a ∈ range N, ‖S N A a‖ ^ 2 = (N : ℝ) * A.card := by
  classical
  have hA' : ∀ x ∈ A, x ≤ N := fun x hx => (hA x hx).le
  have key : ∑ a ∈ range N, S N A a * S N (A.image (fun y => N - y)) a =
      (N : ℂ) * (A.card : ℂ) := by
    rw [pair_count_identity hN]
    congr 2
    -- the pairs (x, N - y) with N ∣ x + N - y are exactly the diagonal x = y
    have : ((A ×ˢ A.image (fun y => N - y)).filter (fun p => N ∣ p.1 + p.2)) =
        A.image (fun x => (x, N - x)) := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hu, y, hy, rfl⟩, hd⟩
        refine ⟨u, hu, rfl, ?_⟩
        have hu' := hA u hu; have hy' := hA y hy
        -- N ∣ u + (N - y) with u, y < N forces u = y
        rcases hd with ⟨k, hk⟩
        have hk1 : k = 1 := by
          rcases Nat.lt_or_ge k 1 with h | h
          · interval_cases k; omega
          · rcases Nat.lt_or_ge k 2 with h2 | h2
            · omega
            · have : N * 2 ≤ N * k := Nat.mul_le_mul_left N h2
              omega
        subst hk1; omega
      · rintro ⟨x, hx, rfl, rfl⟩
        exact ⟨⟨hx, x, hx, rfl⟩, ⟨1, by have := hA x hx; omega⟩⟩
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
  have hsum : ∑ a ∈ range N, (‖S N A a‖ ^ 2 : ℂ) = (N : ℂ) * (A.card : ℂ) := by
    rw [← key]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← conj_S hN A hA' a, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  exact_mod_cast hsum

/-- **The L² barrier at denominator `N`.** For `A ⊆ (0, N)`,
`|N · #{x + y = N} - |A|²| ≤ N |A| - |A|²`. With `A` the primes below `N` the main term
`|A|²/N` is about `N / log² N` and the bound on the rest is about `N / log N`: absolute
values lose one log, so cancellation among the signs of `S(a/N)²` is necessary. -/
theorem l2_barrier {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, 0 < x ∧ x < N) :
    |(N : ℝ) * pairCount N A A - (A.card : ℝ) ^ 2| ≤ (N : ℝ) * A.card - (A.card : ℝ) ^ 2 := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hid := goldbach_identity hN A hA
  have hpar := parseval_count hN A (fun x hx => (hA x hx).2)
  have hsplit := Finset.sum_range_succ' (fun a => S N A a ^ 2) (N - 1)
  have hsplit2 := Finset.sum_range_succ' (fun a => ‖S N A a‖ ^ 2) (N - 1)
  rw [Nat.sub_add_cancel hNpos] at hsplit hsplit2
  rw [hsplit, S_zero] at hid
  rw [hsplit2, S_zero] at hpar
  simp only [Complex.norm_natCast] at hpar
  have hrest : (N : ℂ) * (pairCount N A A : ℂ) - (A.card : ℂ) ^ 2 =
      ∑ a ∈ range (N - 1), S N A (a + 1) ^ 2 := by
    rw [← hid]; ring
  have hnorm : ‖(N : ℂ) * (pairCount N A A : ℂ) - (A.card : ℂ) ^ 2‖ ≤
      ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ ^ 2 := by
    rw [hrest]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_pow]
  have hcast : ‖(N : ℂ) * (pairCount N A A : ℂ) - (A.card : ℂ) ^ 2‖ =
      |(N : ℝ) * pairCount N A A - (A.card : ℝ) ^ 2| := by
    have e : ((N : ℂ) * (pairCount N A A : ℂ) - (A.card : ℂ) ^ 2) =
        (((N : ℝ) * pairCount N A A - (A.card : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast] at hnorm
  linarith

/-- Vacuity: `N = 10`, `A` the primes below 10; the ordered pairs are (3,7), (5,5), (7,3). -/
example : pairCount 10 {2, 3, 5, 7} {2, 3, 5, 7} = 3 := by decide

example : ∑ a ∈ range 10, S 10 {2, 3, 5, 7} a ^ 2 = 30 := by
  rw [goldbach_identity (by norm_num)]
  · rw [show pairCount 10 {2, 3, 5, 7} {2, 3, 5, 7} = 3 by decide]; norm_num
  · intro x hx; simp at hx; omega

/-- For `N = 2^k` the `q ∣ N` major arc constant is `N/φ(N) = 2`, while the Hardy-Littlewood
constant is `2 C₂ ≈ 1.3203`. Here only the elementary half: `φ(2^(k+1)) * 2 = 2^(k+1)`. -/
theorem totient_two_pow (k : ℕ) : Nat.totient (2 ^ (k + 1)) * 2 = 2 ^ (k + 1) := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  simp [pow_succ]

end LeanLab.Routes.R0018

#print axioms LeanLab.Routes.R0018.goldbach_identity
#print axioms LeanLab.Routes.R0018.parseval_count
#print axioms LeanLab.Routes.R0018.l2_barrier
#print axioms LeanLab.Routes.R0018.totient_two_pow

import LeanLab.AlmostPrimeSums.Decomp243a

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Finite modulus bookkeeping for BJS p. 53 equations 165 to 166.
A prime above the sifted cutoff has a unique cofactor with prime factors below it.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Remainder243

open Finset Real

/-- The large prime and small prime cofactor are uniquely determined by their product.
This is the no multiplicity loss step in BJS p. 53 equation 166. -/
theorem large_prime_product_injective (Q D : Finset ℕ) (z : ℝ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ (q : ℝ))
    (hD : ∀ d ∈ D, 0 < d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z) :
    Set.InjOn (fun qd : ℕ × ℕ => qd.1 * qd.2) (Q.product D) := by
  intro x hx y hy hxy
  change x.1 * x.2 = y.1 * y.2 at hxy
  obtain ⟨hxQ, hxD⟩ := mem_product.mp hx
  obtain ⟨hyQ, hyD⟩ := mem_product.mp hy
  have hxprime := (hQ x.1 hxQ).1
  have hyprime := (hQ y.1 hyQ).1
  have hdiv : x.1 ∣ y.1 * y.2 := by
    rw [← hxy]
    exact dvd_mul_right _ _
  have hq : x.1 = y.1 := by
    rcases hxprime.dvd_mul.mp hdiv with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hxprime hyprime).mp h
    · have hp := hxprime.mem_primeFactors h (hD y.2 hyD).1.ne'
      exact False.elim ((not_lt_of_ge (hQ x.1 hxQ).2) ((hD y.2 hyD).2 x.1 hp))
  apply Prod.ext hq
  apply Nat.eq_of_mul_eq_mul_left hxprime.pos
  simpa only [hq] using hxy

/-- Summing errors at products of a large prime and a small prime cofactor
costs no multiplicity factor. Derived finite form of BJS p. 53 equation 166. -/
theorem double_remainder_le (Q D : Finset ℕ) (z : ℝ) (H : ℕ) (R : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ (q : ℝ))
    (hD : ∀ d ∈ D, 0 < d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hR : ∀ d ∈ Icc 1 H, 0 ≤ R d) :
    (∑ qd ∈ (Q.product D).filter (fun qd => qd.1 * qd.2 ≤ H), R (qd.1 * qd.2)) ≤
      ∑ d ∈ Icc 1 H, R d := by
  classical
  let S := (Q.product D).filter (fun qd => qd.1 * qd.2 ≤ H)
  have hinj : Set.InjOn (fun qd : ℕ × ℕ => qd.1 * qd.2) S :=
    (large_prime_product_injective Q D z hQ hD).mono (filter_subset _ _)
  apply sum_le_sum_of_injOn (fun qd : ℕ × ℕ => qd.1 * qd.2) hinj
  · intro n hn
    obtain ⟨qd, hqd, rfl⟩ := mem_image.mp hn
    obtain ⟨hm, hH⟩ := mem_filter.mp hqd
    obtain ⟨hq, hd⟩ := mem_product.mp hm
    exact mem_Icc.mpr ⟨Nat.mul_pos (hQ _ hq).1.pos (hD _ hd).1, hH⟩
  · intro qd _
    exact le_rfl
  · intro d hd _
    exact hR d hd

/-- Absolute progression errors satisfy the nonnegative version of the finite
modulus bound. BJS p. 53 equations 165 to 166. -/
theorem double_absolute_remainder_le (Q D : Finset ℕ) (z : ℝ) (H : ℕ) (R : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ z ≤ (q : ℝ))
    (hD : ∀ d ∈ D, 0 < d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < z) :
    (∑ qd ∈ (Q.product D).filter (fun qd => qd.1 * qd.2 ≤ H), |R (qd.1 * qd.2)|) ≤
      ∑ d ∈ Icc 1 H, |R d| :=
  double_remainder_le Q D z H (fun d => |R d|) hQ hD (fun _ _ => abs_nonneg _)

end LeanLab.AlmostPrimeSums.Remainder243

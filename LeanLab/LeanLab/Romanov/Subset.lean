import LeanLab.Romanov.Final

/-!
# Romanov's theorem for a set of primes of positive relative density

Lab proof, unit U-5617, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known in method,
Romanov 1934; the collision bound of `coll_le` holds for any subset of the primes, so only the
diagonal count changes. Binary Goldbach is OPEN; T2, restricted primes on the Linnik-Goldbach line.

* `romanov_subset`: if `A ⊆ P` has `#(A ∩ [0, 2^(L+1)]) · L ≥ c₀ 2^(L+1)` for `L ≥ L₀`, which
  is relative lower density `c₀ log 2` in the primes, then for an absolute `c > 0` and every
  `L ≥ max L₀ 2` at least `c · 2^(L+2)` numbers below `2^(L+2)` are `p + 2^k` with `p ∈ A`.
-/

namespace LeanLab.Romanov

open Finset Real

attribute [local instance] Classical.propDecidable

theorem romanov_subset (A : Set ℕ) (hAP : ∀ p ∈ A, p.Prime) (c₀ : ℝ) (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hdens : ∀ L : ℕ, L₀ ≤ L →
      c₀ * 2 ^ (L + 1) ≤ (#((Nat.primesBelow (2 ^ (L + 1) + 1)).filter (· ∈ A)) : ℝ) * L) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, max L₀ 2 ≤ L → ∃ I : Finset ℕ,
      (∀ n ∈ I, n < 2 ^ (L + 2) ∧ ∃ p ∈ A, ∃ k : ℕ, n = p + 2 ^ k) ∧ c * 2 ^ (L + 2) ≤ #I := by
  classical
  have hR := R₁_pos
  set κ : ℝ := 1 + 2 * R₁ / c₀ with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨c₀ / (2 * κ), by positivity, fun L hL => ?_⟩
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  set N := 2 ^ (L + 1) with hNdef
  set A' := (Nat.primesBelow (N + 1)).filter (· ∈ A) with hA'def
  set P := Nat.primesBelow (2 ^ (L + 2)) with hPdef
  set T := A' ×ˢ range L with hTdef
  refine ⟨T.image f, fun n hn => ?_, ?_⟩
  · rw [mem_image] at hn
    obtain ⟨⟨p, k⟩, hpk, rfl⟩ := hn
    rw [hTdef, mem_product, hA'def, mem_filter, Nat.mem_primesBelow, mem_range] at hpk
    obtain ⟨⟨⟨hp, _⟩, hpA⟩, hk⟩ := hpk
    refine ⟨?_, p, hpA, k, rfl⟩
    have h1 : 2 ^ k < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) hk
    have h2 : 2 ^ (L + 2) = 4 * 2 ^ L := by ring
    have h3 : N = 2 * 2 ^ L := by rw [hNdef]; ring
    simp only [f]
    omega
  · have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
    have hA : ∀ p ∈ A', p < N + 1 ∧ p ∈ P := by
      intro p hp
      rw [hA'def, mem_filter, Nat.mem_primesBelow] at hp
      refine ⟨hp.1.1, ?_⟩
      rw [hPdef, Nat.mem_primesBelow]
      refine ⟨?_, hp.1.2⟩
      have h2 : 2 ^ (L + 2) = 4 * 2 ^ L := by ring
      have h3 : N = 2 * 2 ^ L := by rw [hNdef]; ring
      have h4 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      omega
    have hcs := card_sq_le T
    have hcoll := coll_le A' P (N + 1) L hA
    have hQ := Q_le P hP L (by omega)
    have hT : #T = #A' * L := by rw [hTdef, card_product, card_range]
    set S : ℝ := (#T : ℝ) with hSdef
    set X : ℝ := (#(T.image f) : ℝ) with hXdef
    have hNr : ((N : ℕ) : ℝ) = (2 : ℝ) ^ (L + 1) := by rw [hNdef]; push_cast; ring
    have hS4 : c₀ * N ≤ S := by
      rw [hSdef, hT, hNr]; push_cast; exact hdens L hL0
    have hN0 : (0 : ℝ) < N := by rw [hNdef]; positivity
    have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS4
    have hE : (coll T : ℝ) ≤ S + 2 * (R₁ * N) := by
      have h1 : (coll T : ℝ) ≤ ((L * #A' + 2 * ∑ k ∈ range L, ∑ k' ∈ range L,
          if k < k' then gap P (2 ^ k' - 2 ^ k) (N + 1) else 0 : ℕ) : ℝ) := by
        exact_mod_cast hcoll
      push_cast at h1
      have hQ' : ((∑ k ∈ range L, ∑ k' ∈ range L,
          if k < k' then gap P (2 ^ k' - 2 ^ k) (N + 1) else 0 : ℕ) : ℝ) ≤ R₁ * N := by
        rw [hNr]; exact hQ
      push_cast at hQ'
      have : (L : ℝ) * #A' = S := by rw [hSdef, hT]; push_cast; ring
      linarith
    have hcsr : S ^ 2 ≤ X * coll T := by
      rw [hSdef, hXdef]; exact_mod_cast hcs
    have hX0 : 0 ≤ X := Nat.cast_nonneg _
    have hmain : S ≤ X * κ := by
      have h1 : S ^ 2 ≤ X * (S + 2 * (R₁ * N)) :=
        le_trans hcsr (mul_le_mul_of_nonneg_left hE hX0)
      have hRN : 2 * (R₁ * N) ≤ 2 * R₁ / c₀ * S := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
        nlinarith
      have h2 : X * (S + 2 * (R₁ * N)) ≤ X * (S * κ) := by
        apply mul_le_mul_of_nonneg_left _ hX0
        rw [hκ]; nlinarith
      have h3 : S * S ≤ S * (X * κ) := by nlinarith
      exact le_of_mul_le_mul_left h3 hS0
    have h22 : ((2 : ℝ) ^ (L + 2)) = 2 * N := by rw [hNr]; ring
    rw [h22]
    calc c₀ / (2 * κ) * (2 * (N : ℝ)) = (c₀ * N) / κ := by field_simp
      _ ≤ S / κ := div_le_div_of_nonneg_right hS4 hκ0.le
      _ ≤ X := by rw [div_le_iff₀ hκ0]; exact hmain

/-- Vacuity test: the density hypothesis holds for `A = P` with `c₀ = 1/4`, `L₀ = 2`. -/
theorem dens_primes (L : ℕ) (hL : 2 ≤ L) :
    (1 / 4 : ℝ) * 2 ^ (L + 1) ≤
      (#((Nat.primesBelow (2 ^ (L + 1) + 1)).filter (· ∈ {p : ℕ | p.Prime})) : ℝ) * L := by
  have hf : (Nat.primesBelow (2 ^ (L + 1) + 1)).filter (· ∈ {p : ℕ | p.Prime}) =
      Nat.primesBelow (2 ^ (L + 1) + 1) :=
    filter_true_of_mem fun p hp => Nat.prime_of_mem_primesBelow hp
  rw [hf, Nat.primesBelow_card_eq_primeCounting']
  have hNr : (((2 ^ (L + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ ((L : ℝ) + 1) := by
    push_cast; rw [← Real.rpow_natCast]; push_cast; ring_nf
  have hpow : (L : ℝ) + 2 ≤ (2 : ℝ) ^ (L : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast add_two_le_two_pow L hL
  have h := S_ge (L : ℝ) (2 ^ (L + 1)) (by exact_mod_cast hL) hNr hpow
  have e : Nat.primeCounting' (2 ^ (L + 1) + 1) = Nat.primeCounting (2 ^ (L + 1)) := rfl
  rw [e]
  push_cast at h ⊢
  linarith

end LeanLab.Romanov

/-
R-0013, T3 MOONSHOT: the pigeonhole route. The primes below N that do not divide N lie in the
reduced residues mod N, a set of size φ(N) that is symmetric under n ↦ N - n. If they fill more
than half of it, a prime and its reflection collide and N is a sum of two primes, with no sieve,
no circle method and no parity problem. The route dies on size: φ(N) ≫ N / log log N while
π(N) ~ N / log N, so the criterion can hold only for N of bounded size.
Run 20261019T1902Z-2936, unit U-1101. AI-written Lean code, Claude. Checked only by the Lean
kernel. Elementary, almost surely folklore; not claimed new. Nothing here is progress on
Goldbach; Goldbach is open.
-/
import Mathlib

namespace LeanLab.Routes.R0013

/-- The primes below `N` that do not divide `N`. -/
def primesCoprime (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- **Pigeonhole in a symmetric set.** If `A ⊆ S ⊆ [0, N]`, `S` is closed under `n ↦ N - n`
and `2 |A| > |S|`, then two elements of `A` sum to `N`. -/
theorem pigeonhole_reflect (N : ℕ) (S A : Finset ℕ) (hAS : A ⊆ S)
    (hle : ∀ a ∈ S, a ≤ N) (hsym : ∀ a ∈ S, N - a ∈ S) (hcard : S.card < 2 * A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = N := by
  set B := A.image (fun a => N - a) with hB
  have hBcard : B.card = A.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := hle x (hAS hx); have hy' := hle y (hAS hy)
    simp only at hxy; omega
  have hBS : B ⊆ S := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact hsym a (hAS ha)
  have hne : (A ∩ B).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card hAS hBS
    omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter] at hx
  obtain ⟨hxA, hxB⟩ := hx
  rw [hB, Finset.mem_image] at hxB
  obtain ⟨a, haA, hax⟩ := hxB
  refine ⟨a, haA, x, hxA, ?_⟩
  have := hle a (hAS haA)
  omega

/-- **The totient criterion.** If more than half of the reduced residues mod `N` are primes,
precisely if `φ(N) < 2 · #{p < N prime, p ∤ N}`, then `N` is a sum of two primes, both prime to
`N`. -/
theorem goldbach_of_totient (N : ℕ) (h : N.totient < 2 * (primesCoprime N).card) :
    ∃ p q, p.Prime ∧ q.Prime ∧ ¬ p ∣ N ∧ ¬ q ∣ N ∧ p + q = N := by
  set S := (Finset.range N).filter (fun n => N.Coprime n) with hS
  have hSc : S.card = N.totient := by rw [hS, Nat.totient]
  have hAS : primesCoprime N ⊆ S := by
    intro p hp
    simp only [primesCoprime, Finset.mem_filter, Finset.mem_range] at hp
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨hp.1, ((Nat.Prime.coprime_iff_not_dvd hp.2.1).mpr hp.2.2).symm⟩
  have hle : ∀ a ∈ S, a ≤ N := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_range] at ha; omega
  have hsym : ∀ a ∈ S, N - a ∈ S := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨haN, hc⟩ := ha
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        have h1 : N = 1 := by simpa using hc
        rw [h1] at h
        exact absurd h (by decide)
      · exact h0
    refine ⟨by omega, ?_⟩
    have h1 : (N - a).Coprime N := (Nat.coprime_self_sub_left haN.le).mpr hc.symm
    exact h1.symm
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    pigeonhole_reflect N S (primesCoprime N) hAS hle hsym (by rw [hSc]; exact h)
  simp only [primesCoprime, Finset.mem_filter, Finset.mem_range] at hp hq
  exact ⟨p, q, hp.2.1, hq.2.1, hp.2.2, hq.2.2, hpq⟩

/-- Vacuity: the hypothesis holds at `N = 30`, where `φ(30) = 8` and the primes below 30 prime
to 30 are 7, 11, 13, 17, 19, 23, 29. -/
theorem criterion_30 : (30 : ℕ).totient < 2 * (primesCoprime 30).card := by
  decide

/-- The criterion fails at `N = 58`: `φ(58) = 28` and only 14 primes below 58 are prime to 58. -/
theorem criterion_fails_58 : ¬ (58 : ℕ).totient < 2 * (primesCoprime 58).card := by
  decide

end LeanLab.Routes.R0013

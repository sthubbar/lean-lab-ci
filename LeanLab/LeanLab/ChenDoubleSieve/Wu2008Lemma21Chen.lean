import LeanLab.ChenDoubleSieve.Wu2008Lemma21Err
import LeanLab.ChenDoubleSieve.Statements

/-!
# Wu 2008 Lemma 2.1 for Wu's own sequence `A = {N - p}`, in terms of the lab's `D12 N`

P0043, unit U-5413, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

`Achen N = {N - p : p prime, p < N, p ∤ N}`. `lemma21_chen`:
`2 S(A; P(N), K) + S₄ ≤ 2 D_{1,2}(N) + S₁ + 2S₂ + S₃ + 2 (N/(K - 1) + √N + 1)` for `1 < K ≤ Σ`,
with `D_{1,2}(N) = ChenDoubleSieve.D12 N`, the definition stated with Wu 2004 and 2008 in
`Statements.lean`. Leaving out the `p ∣ N` only shrinks the left side's `A`. Binary Goldbach is OPEN.
-/

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu08

open Wu41 (S)

/-- Wu's `A = {N - p}`, with the primes dividing `N` left out. -/
def Achen (N : ℕ) : Finset ℕ :=
  ({p ∈ range N | p.Prime ∧ ¬ p ∣ N} : Finset ℕ).image fun p => N - p

lemma Achen_spec (N : ℕ) : ∀ a ∈ Achen N, 0 < a ∧ a < N ∧ a.Coprime N := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
  obtain ⟨hpN, hpr, hpd⟩ := mem_filter.1 hp
  have hpN' := mem_range.1 hpN
  refine ⟨by omega, by have := hpr.pos; omega, ?_⟩
  exact (Nat.coprime_self_sub_left hpN'.le).2 ((Nat.Prime.coprime_iff_not_dvd hpr).2 hpd)

/-- `#{a ∈ A : Ω(a) ≤ 2} ≤ D_{1,2}(N)`. -/
lemma D12_Achen_le (N : ℕ) : D12 (Achen N) ≤ ChenDoubleSieve.D12 N := by
  unfold D12 Achen ChenDoubleSieve.D12
  set s := ({p ∈ range N | p.Prime ∧ ¬ p ∣ N} : Finset ℕ)
  have h1 : ({a ∈ s.image (fun p => N - p) | Ω a ≤ 2} : Finset ℕ) =
      ({p ∈ s | Ω (N - p) ≤ 2} : Finset ℕ).image (fun p => N - p) := by
    rw [filter_image]
  rw [h1]
  refine (card_image_le).trans (card_le_card ?_)
  intro p hp
  obtain ⟨hps, hΩ⟩ := mem_filter.1 hp
  obtain ⟨hpN, hpr, -⟩ := mem_filter.1 hps
  exact mem_filter.2 ⟨mem_range.2 (by have := mem_range.1 hpN; omega), hpr, hΩ⟩

/-- **Wu 2008 Lemma 2.1 for `A = {N - p}`, with the lab's `D_{1,2}(N)`.** -/
theorem lemma21_chen (N : ℕ) {K Sg : ℝ} (hK1 : 1 < K) (hK : K ≤ Sg) :
    (2 * S (Achen N) 1 N K + S₄ (Achen N) N K Sg : ℝ) ≤
      2 * ChenDoubleSieve.D12 N + S₁ (Achen N) N K Sg + 2 * S₂ (Achen N) N Sg
        + S₃ (Achen N) N K Sg + 2 * (N / (K - 1) + Real.sqrt N + 1) := by
  have h := lemma21_explicit (Achen N) N hK1 hK (Achen_spec N)
  have hD : (D12 (Achen N) : ℝ) ≤ ChenDoubleSieve.D12 N := by exact_mod_cast D12_Achen_le N
  linarith

end LeanLab.ChenDoubleSieve.Wu08

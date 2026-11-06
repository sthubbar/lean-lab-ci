import LeanLab.AlmostPrimeSums.Prime243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The actual unsifted Chen triple count is bounded by a double prime sum.
This is the first counting step of BJS p. 57 equation 186, before the
prime counting and two Abel estimates. No enlarged switching blocks are needed.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Triple243

open Finset Real
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Decomp1527c LeanLab.AlmostPrimeSums.Decomp243b

noncomputable section

/-- The double prime counting majorant for the actual unsifted triple set.
BJS p. 57 equation 186, before the prime counting estimate. -/
def primeTripleMajorant (N : ℕ) : ℝ :=
  ∑ p₁ ∈ middlePrimes N,
    ∑ p₂ ∈ primesIco ((N : ℝ) ^ ((1 : ℝ) / 3)) (√((N : ℝ) / p₁)),
      (Nat.primeCounting ⌊(N : ℝ) / (p₁ * p₂)⌋₊ : ℝ)

/-- The actual T cardinality is at most its double prime counting majorant.
This is the first inequality in BJS p. 57 equation 186, applied directly to T.
Selecting one representation for each product suffices for the injection. -/
theorem triple_count_le_prime_majorant (N : ℕ) :
    (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) ≤
      primeTripleMajorant N := by
  classical
  let S := TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))
  let T := (middlePrimes N).sigma fun p₁ =>
    (primesIco ((N : ℝ) ^ ((1 : ℝ) / 3)) (√((N : ℝ) / p₁))).sigma fun p₂ =>
      Nat.primesLE ⌊(N : ℝ) / (p₁ * p₂)⌋₊
  have hwit : ∀ m ∈ S, ∃ p₁ p₂ p₃ : ℕ,
      p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ p₁ ∧
      (p₁ : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧ (N : ℝ) ^ ((1 : ℝ) / 3) ≤ p₂ ∧
      p₂ ≤ p₃ ∧ m = p₁ * p₂ * p₃ := by
    intro m hm
    exact (mem_filter.mp hm).2.2
  choose p q r hp hq hr hzp hpy hyq hqr he using hwit
  let f : S → T := fun x => ⟨⟨p x.1 x.2, ⟨q x.1 x.2, r x.1 x.2⟩⟩, by
    have hpp : (0 : ℝ) < p x.1 x.2 := by exact_mod_cast (hp x.1 x.2).pos
    have hqp : (0 : ℝ) < q x.1 x.2 := by exact_mod_cast (hq x.1 x.2).pos
    have hprodNat : p x.1 x.2 * q x.1 x.2 * r x.1 x.2 < N := by
      rw [← he x.1 x.2]
      exact mem_range.mp (mem_filter.mp x.2).1
    have hprod : (p x.1 x.2 : ℝ) * q x.1 x.2 * r x.1 x.2 < N := by
      exact_mod_cast hprodNat
    have hqrR : (q x.1 x.2 : ℝ) ≤ r x.1 x.2 := by exact_mod_cast hqr x.1 x.2
    have hqb : (q x.1 x.2 : ℝ) < √((N : ℝ) / p x.1 x.2) := by
      apply (lt_sqrt (by positivity)).2
      apply (lt_div_iff₀ hpp).2
      have hh := mul_le_mul_of_nonneg_left hqrR (mul_nonneg hpp.le hqp.le)
      nlinarith
    have hrb : r x.1 x.2 ≤ ⌊(N : ℝ) / (p x.1 x.2 * q x.1 x.2)⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ (mul_pos hpp hqp)).2
      nlinarith
    exact mem_sigma.mpr ⟨mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_ceil.mpr (hpy x.1 x.2)), hp x.1 x.2, hzp x.1 x.2⟩,
      mem_sigma.mpr ⟨mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_ceil.mpr hqb), hq x.1 x.2, hyq x.1 x.2⟩,
        Nat.mem_primesLE.mpr ⟨hrb, hr x.1 x.2⟩⟩⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hpq : p x.1 x.2 = p y.1 y.2 := congrArg (fun z : T => z.1.1) hxy
    have hqq : q x.1 x.2 = q y.1 y.2 := congrArg (fun z : T => z.1.2.1) hxy
    have hrq : r x.1 x.2 = r y.1 y.2 := congrArg (fun z : T => z.1.2.2) hxy
    apply Subtype.ext
    rw [he x.1 x.2, he y.1 y.2, hpq, hqq, hrq]
  have hc := Finset.card_le_card_of_injective hinj
  have hcR : (S.card : ℝ) ≤ T.card := by exact_mod_cast hc
  simpa only [S, T, primeTripleMajorant, card_sigma,
    Nat.primesLE_card_eq_primeCounting, Nat.cast_sum] using hcR

end
end LeanLab.AlmostPrimeSums.Triple243

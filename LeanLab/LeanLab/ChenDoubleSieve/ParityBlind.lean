import LeanLab.ChenDoubleSieve.Wu2008Lemma21

/-!
# Chen's weight is parity blind: it gives a prime and a large semiprime the same credit

T3 unit U-5412, route R-5050, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

Chen's weight from Wu 2008 Lemma 2.1, for one `a`,
`w(a) = 2·[a sifted to K] − S₁(a) − 2S₂(a) − S₃(a) + S₄(a)`, takes the value `2` both on a prime
`a ≥ Σ` and on `a = q₁q₂` with `Σ ≤ q₁ < q₂`, `q₁q₂² ≥ N`: `weight_prime`, `weight_semiprime`.
So a lower bound built from this weight cannot count primes `N - p` apart from such semiprimes;
this is why Chen's theorem counts `Ω(N - p) ≤ 2`, the parity barrier seen pointwise. The route
is BLOCKED by parity; nothing here is progress on Goldbach, which is OPEN.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu08

open Wu41 (Sifted S PS mem_PS)

/-- The five counts of Chen's weight at one `a`, as in `pointwise`. -/
def cS0 (N : ℕ) (K : ℝ) (a : ℕ) : ℕ := if 1 ∣ a ∧ Sifted N K a then 1 else 0
def cS1 (N : ℕ) (K Sg : ℝ) (a : ℕ) : ℕ := #{p ∈ PS N K Sg | p ∣ a ∧ Sifted N K a}
def cS2 (N : ℕ) (Sg : ℝ) (a : ℕ) : ℕ :=
  #{q ∈ pairs N Sg (N : ℝ) Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a}
def cS3 (N : ℕ) (K Sg : ℝ) (a : ℕ) : ℕ :=
  #{q ∈ pairs N K Sg Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a}
def cS4 (N : ℕ) (K Sg : ℝ) (a : ℕ) : ℕ :=
  #{t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a}

/-- Chen's weight at `a`, an integer. -/
def weight (N : ℕ) (K Sg : ℝ) (a : ℕ) : ℤ :=
  2 * cS0 N K a - cS1 N K Sg a - 2 * cS2 N Sg a - cS3 N K Sg a + cS4 N K Sg a

/-- If every prime factor of `a` is at least `Σ`, the counts `S₁`, `S₃`, `S₄` vanish. -/
lemma counts_zero_of_large {N a : ℕ} {K Sg : ℝ} (h : ∀ q, q.Prime → q ∣ a → Sg ≤ q) :
    cS1 N K Sg a = 0 ∧ cS3 N K Sg a = 0 ∧ cS4 N K Sg a = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cS1; rw [card_eq_zero, filter_eq_empty_iff]
    rintro p hp ⟨hpa, -⟩
    obtain ⟨hpr, -, hpS, -⟩ := mem_PS.1 hp
    exact absurd (h p hpr hpa) (not_le.2 hpS)
  · unfold cS3; rw [card_eq_zero, filter_eq_empty_iff]
    rintro q hq ⟨hd, -⟩
    simp only [pairs, mem_filter] at hq
    obtain ⟨-, h1, -, -, -, -, hS, -⟩ := hq
    exact absurd (h q.1 h1 (dvd_trans (dvd_mul_right _ _) hd)) (not_le.2 hS)
  · unfold cS4; rw [card_eq_zero, filter_eq_empty_iff]
    rintro t ht ⟨hd, -⟩
    simp only [triples, mem_filter, mem_product] at ht
    obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := ht
    obtain ⟨hpr, -, hpS, -⟩ := mem_PS.1 h1
    exact absurd (h _ hpr (dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hd)))
      (not_le.2 hpS)

lemma sifted_of_large {N a : ℕ} {K Sg : ℝ} (hK : K ≤ Sg) (h : ∀ q, q.Prime → q ∣ a → Sg ≤ q) :
    Sifted N K a := fun q hq hqK _ hqa => absurd (h q hq hqa) (by
      push Not; linarith)

/-- **A prime `a ≥ Σ` gets weight `2`.** -/
theorem weight_prime {N a : ℕ} {K Sg : ℝ} (hK : K ≤ Sg) (ha : a.Prime) (haS : Sg ≤ a) :
    weight N K Sg a = 2 := by
  have hlarge : ∀ q, q.Prime → q ∣ a → Sg ≤ q := by
    intro q hq hqa
    rw [(Nat.prime_dvd_prime_iff_eq hq ha).1 hqa]; exact haS
  obtain ⟨h1, h3, h4⟩ := counts_zero_of_large (N := N) (K := K) hlarge
  have h0 : cS0 N K a = 1 := by
    unfold cS0; rw [if_pos ⟨one_dvd a, sifted_of_large hK hlarge⟩]
  have h2 : cS2 N Sg a = 0 := by
    unfold cS2; rw [card_eq_zero, filter_eq_empty_iff]
    rintro q hq ⟨hd, -⟩
    simp only [pairs, mem_filter] at hq
    obtain ⟨-, hp1, hp2, -, -, -, -, -, h12, -⟩ := hq
    have e1 := (Nat.prime_dvd_prime_iff_eq hp1 ha).1 (dvd_trans (dvd_mul_right _ _) hd)
    have e2 := (Nat.prime_dvd_prime_iff_eq hp2 ha).1 (dvd_trans (dvd_mul_left _ _) hd)
    omega
  unfold weight; rw [h0, h1, h2, h3, h4]; norm_num

/-- **A semiprime `q₁q₂` with `Σ ≤ q₁ < q₂` and `q₁q₂² ≥ N` also gets weight `2`.** -/
theorem weight_semiprime {N q₁ q₂ : ℕ} {K Sg : ℝ} (hK : K ≤ Sg) (h1 : q₁.Prime) (h2 : q₂.Prime)
    (h12 : q₁ < q₂) (hS : Sg ≤ q₁) (hN : N ≤ q₁ * q₂ ^ 2) :
    weight N K Sg (q₁ * q₂) = 2 := by
  have hdiv : ∀ q, q.Prime → q ∣ q₁ * q₂ → q = q₁ ∨ q = q₂ := by
    intro q hq hqa
    rcases (Nat.Prime.dvd_mul hq).1 hqa with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h1).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq h2).1 h)
  have hlarge : ∀ q, q.Prime → q ∣ q₁ * q₂ → Sg ≤ q := by
    intro q hq hqa
    have hq12 : (q₁ : ℝ) ≤ q₂ := by exact_mod_cast h12.le
    rcases hdiv q hq hqa with rfl | rfl
    · exact hS
    · linarith
  obtain ⟨c1, c3, c4⟩ := counts_zero_of_large (N := N) (K := K) hlarge
  have c0 : cS0 N K (q₁ * q₂) = 1 := by
    unfold cS0; rw [if_pos ⟨one_dvd _, sifted_of_large hK hlarge⟩]
  have c2 : cS2 N Sg (q₁ * q₂) = 0 := by
    unfold cS2; rw [card_eq_zero, filter_eq_empty_iff]
    rintro q hq ⟨hd, -⟩
    simp only [pairs, mem_filter] at hq
    obtain ⟨-, hp1, hp2, -, -, -, -, -, hlt, hbound⟩ := hq
    have e1 := hdiv q.1 hp1 (dvd_trans (dvd_mul_right _ _) hd)
    have e2 := hdiv q.2 hp2 (dvd_trans (dvd_mul_left _ _) hd)
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rw [e1, e2] at hlt hbound <;> omega
  unfold weight; rw [c0, c1, c2, c3, c4]; norm_num

/-- Vacuity: with `N = 100`, `Σ = 3`, both `a = 97` and `a = 3 · 7 = 21`, `3 · 7² = 147 ≥ 100`,
get weight `2`. -/
example : weight 100 2 3 97 = 2 ∧ weight 100 2 3 (3 * 7) = 2 :=
  ⟨weight_prime (by norm_num) (by norm_num) (by norm_num),
    weight_semiprime (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)⟩

end LeanLab.ChenDoubleSieve.Wu08

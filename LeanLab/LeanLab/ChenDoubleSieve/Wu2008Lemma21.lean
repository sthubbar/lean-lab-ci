import LeanLab.ChenDoubleSieve.Lemma41

/-!
# Wu 2008 Lemma 2.1, Chen's inequality for `D_{1,2}(N)`, exact pointwise form

P0043 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, 2,
Acta Arith. 131, 2008, arXiv 0709.3764, Lemma 2.1, inequality (2.1), first stated by Chen 1978
without proof. Unit U-5408, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

For a finite set `A` of integers `0 < a < N` coprime to `N`, as Wu's `A = {N - p}` is apart from
`p ∣ N`, and real `K ≤ Σ` for `N^κ ≤ N^σ`:
`2 S(A; P(N), K) + S₄ ≤ 2 #{a ∈ A : Ω(a) ≤ 2} + S₁ + 2 S₂ + S₃ + 2E`, `lemma21_nat`, where
`S₁ = Σ_{K ≤ p < Σ} S(A_p; P(N), K)`,
`S₂ = Σ_{Σ ≤ p₁ < p₂, p₁p₂² < N} S(A_{p₁p₂}; P(Np₁), p₂)`,
`S₃ = Σ_{K ≤ p₁ < Σ ≤ p₂, p₁p₂² < N} S(A_{p₁p₂}; P(Np₁), p₂)`,
`S₄ = Σ_{K ≤ p₁ < p₂ < p₃ < Σ} S(A_{p₁p₂p₃}; P(Np₁), p₂)`, all primes coprime to `N`, and
`E = #{a ∈ A : a has no prime factor below K, minFac(a)² ∣ a}`, which is Wu's `O(N^{1-κ})`.
`p₂ < (N/p₁)^{1/2}` is written `p₁p₂² < N`, the same for positive integers.
No condition `σ ≤ 1/3` or `3σ + κ > 1` is needed for the pointwise form.

READING. Wu 2008 defines `P(z) = ∏_{p ≤ z}`, with `≤`; then `S(A_{p₁p₂}; P(Np₁), p₂)` would
sift out `p₂` itself, which divides every element, and `S₂ = S₃ = S₄ = 0`. We read `p < z`,
Wu 2004's convention and the one the proof needs. Cosmetic.
Binary Goldbach is OPEN; this is the combinatorial step of Chen's lower bound sieve.
-/

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu08

open Wu41 (Sifted S PS mem_PS S_eq_sum)

/-- Pairs `p₁ < p₂` of primes coprime to `N` with `lo ≤ p₁ < hi₁`, `lo₂ ≤ p₂`, `p₁ p₂² < N`. -/
def pairs (N : ℕ) (lo hi₁ lo₂ : ℝ) : Finset (ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧
    lo ≤ q.1 ∧ (q.1 : ℝ) < hi₁ ∧ lo₂ ≤ q.2 ∧ q.1 < q.2 ∧ q.1 * q.2 ^ 2 < N}

/-- Triples `p₁ < p₂ < p₃` of primes of `[K, Σ)` coprime to `N`. -/
def triples (N : ℕ) (K Sg : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  {t ∈ (PS N K Sg ×ˢ PS N K Sg) ×ˢ PS N K Sg | t.1.1 < t.1.2 ∧ t.1.2 < t.2}

variable (A : Finset ℕ) (N : ℕ) (K Sg : ℝ)

def S₁ : ℕ := ∑ p ∈ PS N K Sg, S A p N K
def S₂ : ℕ := ∑ q ∈ pairs N Sg (N : ℝ) Sg, S A (q.1 * q.2) (N * q.1) q.2
def S₃ : ℕ := ∑ q ∈ pairs N K Sg Sg, S A (q.1 * q.2) (N * q.1) q.2
def S₄ : ℕ := ∑ t ∈ triples N K Sg, S A (t.1.1 * t.1.2 * t.2) (N * t.1.1) t.1.2
/-- `D_{1,2}` restricted to `A`. -/
def D12 : ℕ := #{a ∈ A | Ω a ≤ 2}
/-- The error: `a` sifted to `K` whose smallest prime factor is repeated. -/
def Esq : ℕ := #{a ∈ A | Sifted N K a ∧ a.minFac ^ 2 ∣ a}

/-! ## Pointwise facts -/

section pointwise
variable {N : ℕ} {K Sg : ℝ} {a : ℕ}

lemma prime_dvd_not_dvd_N (hcop : a.Coprime N) {q : ℕ} (hq : q.Prime) (hqa : q ∣ a) :
    ¬ q ∣ N := fun h => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqa h)

lemma not_dvd_mul_of {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hne : q ≠ p) (hN : ¬ q ∣ N) :
    ¬ q ∣ N * p := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact hN h
  · exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).1 h)

/-- In a counted triple, `p₁` is the least prime factor of `a`. -/
lemma triple_p1 (ha : 0 < a) (hcop : a.Coprime N) {t : (ℕ × ℕ) × ℕ}
    (ht : t ∈ triples N K Sg) (hdvd : t.1.1 * t.1.2 * t.2 ∣ a)
    (hs : Sifted (N * t.1.1) t.1.2 a) : t.1.1 = a.minFac := by
  simp only [triples, mem_filter, mem_product] at ht
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h12, -⟩ := ht
  have hp1 := (mem_PS.1 h1).1
  have hp2 := (mem_PS.1 h2).1
  have hp1a : t.1.1 ∣ a := dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hdvd)
  have ha1 : a ≠ 1 := fun h => hp1.one_lt.ne' (Nat.eq_one_of_dvd_one (h ▸ hp1a))
  have hle := Nat.minFac_le_of_dvd hp1.two_le hp1a
  by_contra hne
  have hlt : a.minFac < t.1.1 := lt_of_le_of_ne hle (Ne.symm hne)
  have hmp := Nat.minFac_prime ha1
  exact hs a.minFac hmp (by exact_mod_cast hlt.trans h12)
    (not_dvd_mul_of hmp hp1 hlt.ne (prime_dvd_not_dvd_N hcop hmp (Nat.minFac_dvd a)))
    (Nat.minFac_dvd a)

/-- Two counted triples have the same `p₂`. -/
lemma triple_p2 (ha : 0 < a) (hcop : a.Coprime N) {t t' : (ℕ × ℕ) × ℕ}
    (ht : t ∈ triples N K Sg) (hdvd : t.1.1 * t.1.2 * t.2 ∣ a) (hs : Sifted (N * t.1.1) t.1.2 a)
    (ht' : t' ∈ triples N K Sg) (hdvd' : t'.1.1 * t'.1.2 * t'.2 ∣ a)
    (hs' : Sifted (N * t'.1.1) t'.1.2 a) : t.1.2 = t'.1.2 := by
  have e1 := triple_p1 ha hcop ht hdvd hs
  have e1' := triple_p1 ha hcop ht' hdvd' hs'
  have key : ∀ {t t' : (ℕ × ℕ) × ℕ}, t ∈ triples N K Sg → t.1.1 * t.1.2 * t.2 ∣ a →
      t' ∈ triples N K Sg → Sifted (N * t'.1.1) t'.1.2 a → t.1.1 = t'.1.1 →
      ¬ t.1.2 < t'.1.2 := by
    intro t t' ht hdvd ht' hs' he hlt
    simp only [triples, mem_filter, mem_product] at ht
    obtain ⟨⟨⟨h1, h2⟩, -⟩, h12, -⟩ := ht
    have hp1 := (mem_PS.1 h1).1
    have hp2 := (mem_PS.1 h2).1
    have hp2a : t.1.2 ∣ a := dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hdvd)
    exact hs' t.1.2 hp2 (by exact_mod_cast hlt)
      (by rw [← he]; exact not_dvd_mul_of hp2 hp1 h12.ne' (prime_dvd_not_dvd_N hcop hp2 hp2a))
      hp2a
  rcases lt_trichotomy t.1.2 t'.1.2 with h | h | h
  · exact absurd h (key ht hdvd ht' hs' (e1.trans e1'.symm))
  · exact h
  · exact absurd h (key ht' hdvd' ht hs (e1'.trans e1.symm))

/-- The counted triples number at most `#{p ∈ [K, Σ) : p ∣ a} - 2`, and none exist unless
that set has three elements. -/
lemma c4_bound (ha : 0 < a) (hcop : a.Coprime N) :
    #{t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a} + 2 ≤
      #{p ∈ PS N K Sg | p ∣ a} ∨
    #{t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a} = 0 := by
  set V := {t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a}
  rcases V.eq_empty_or_nonempty with h | ⟨t₀, ht₀⟩
  · right; rw [h, card_empty]
  left
  obtain ⟨ht₀T, hd₀, hs₀⟩ := mem_filter.1 ht₀
  have hT := ht₀T
  simp only [triples, mem_filter, mem_product] at hT
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h12, -⟩ := hT
  set RS := ({p ∈ PS N K Sg | p ∣ a} : Finset ℕ)
  have hp1RS : t₀.1.1 ∈ RS := mem_filter.2 ⟨h1,
    dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hd₀)⟩
  have hp2RS : t₀.1.2 ∈ RS := mem_filter.2 ⟨h2,
    dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hd₀)⟩
  have hsub : V.image (fun t => t.2) ⊆ (RS.erase t₀.1.1).erase t₀.1.2 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
    obtain ⟨htT, hd, hs⟩ := mem_filter.1 ht
    have e1 := (triple_p1 ha hcop htT hd hs).trans (triple_p1 ha hcop ht₀T hd₀ hs₀).symm
    have e2 := triple_p2 ha hcop htT hd hs ht₀T hd₀ hs₀
    have hT' := htT
    simp only [triples, mem_filter, mem_product] at hT'
    obtain ⟨⟨-, h3⟩, h12', h23'⟩ := hT'
    refine mem_erase.2 ⟨by rw [← e2]; exact h23'.ne', mem_erase.2 ⟨by rw [← e1]; omega,
      mem_filter.2 ⟨h3, dvd_trans (dvd_mul_left _ _) hd⟩⟩⟩
  have hinj : Set.InjOn (fun t : (ℕ × ℕ) × ℕ => t.2) V := by
    intro t ht t' ht' h
    obtain ⟨htT, hd, hs⟩ := mem_filter.1 ht
    obtain ⟨htT', hd', hs'⟩ := mem_filter.1 ht'
    have e1 := (triple_p1 ha hcop htT hd hs).trans (triple_p1 ha hcop htT' hd' hs').symm
    have e2 := triple_p2 ha hcop htT hd hs htT' hd' hs'
    exact Prod.ext (Prod.ext e1 e2) h
  have := card_le_card hsub
  rw [card_image_of_injOn hinj] at this
  have hc1 := card_erase_of_mem hp1RS
  have hc2 : #((RS.erase t₀.1.1).erase t₀.1.2) = #(RS.erase t₀.1.1) - 1 :=
    card_erase_of_mem (mem_erase.2 ⟨h12.ne', hp2RS⟩)
  have : 2 ≤ #RS := by
    have := card_le_card (show ({t₀.1.1, t₀.1.2} : Finset ℕ) ⊆ RS by
      intro x hx; rcases mem_insert.1 hx with rfl | hx
      · exact hp1RS
      · rw [mem_singleton.1 hx]; exact hp2RS)
    rw [card_pair h12.ne] at this; exact this
  omega

lemma three_le_cardFactors {p₁ p₂ p₃ a : ℕ} (h1 : p₁.Prime) (h2 : p₂.Prime) (h3 : p₃.Prime)
    (ha : a ≠ 0) (hd : p₁ * p₂ * p₃ ∣ a) : 3 ≤ Ω a := by
  obtain ⟨c, rfl⟩ := hd
  have hc : c ≠ 0 := by rintro rfl; simp at ha
  rw [ArithmeticFunction.cardFactors_mul
      (Nat.mul_ne_zero (Nat.mul_ne_zero h1.ne_zero h2.ne_zero) h3.ne_zero) hc,
    ArithmeticFunction.cardFactors_mul (Nat.mul_ne_zero h1.ne_zero h2.ne_zero) h3.ne_zero,
    ArithmeticFunction.cardFactors_mul h1.ne_zero h2.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime h1, ArithmeticFunction.cardFactors_apply_prime h2,
    ArithmeticFunction.cardFactors_apply_prime h3]
  omega

/-- **Wu 2008 Lemma 2.1 for one `a`.** -/
theorem pointwise (hK : K ≤ Sg) (ha0 : 0 < a) (haN : a < N) (hcop : a.Coprime N) :
    2 * (if 1 ∣ a ∧ Sifted N K a then 1 else 0)
      + #{t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a}
    ≤ 2 * (if Ω a ≤ 2 then 1 else 0)
      + #{p ∈ PS N K Sg | p ∣ a ∧ Sifted N K a}
      + 2 * #{q ∈ pairs N Sg (N : ℝ) Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a}
      + #{q ∈ pairs N K Sg Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a}
      + 2 * (if Sifted N K a ∧ a.minFac ^ 2 ∣ a then 1 else 0) := by
  set c4 := #{t ∈ triples N K Sg | t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (N * t.1.1) t.1.2 a}
    with hc4def
  -- a counted triple forces `Ω a ≥ 3`
  have hc4Ω : 0 < c4 → 3 ≤ Ω a := by
    intro h
    obtain ⟨t, ht⟩ := card_pos.1 h
    obtain ⟨htT, hd, -⟩ := mem_filter.1 ht
    simp only [triples, mem_filter, mem_product] at htT
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -, -⟩ := htT
    exact three_le_cardFactors (mem_PS.1 h1).1 (mem_PS.1 h2).1 (mem_PS.1 h3).1 ha0.ne' hd
  by_cases hs : Sifted N K a
  swap
  · have h0 : c4 = 0 := by
      rw [hc4def, card_eq_zero, filter_eq_empty_iff]
      rintro t htT ⟨-, hs'⟩
      simp only [triples, mem_filter, mem_product] at htT
      obtain ⟨⟨⟨h1, -⟩, -⟩, h12, -⟩ := htT
      obtain ⟨hp1, hKp1, -, -⟩ := mem_PS.1 h1
      refine hs fun q hq hqK hqN hqa => hs' q hq ?_ ?_ hqa
      · have : (t.1.1 : ℝ) < t.1.2 := by exact_mod_cast h12
        linarith
      · have hne : q ≠ t.1.1 := by
          rintro rfl; linarith
        exact not_dvd_mul_of hq hp1 hne hqN
    rw [if_neg (fun h => hs h.2), h0]
    omega
  rw [if_pos ⟨one_dvd a, hs⟩]
  set RS := ({p ∈ PS N K Sg | p ∣ a} : Finset ℕ) with hRS
  have hc1 : #{p ∈ PS N K Sg | p ∣ a ∧ Sifted N K a} = #RS := by
    rw [hRS]; congr 1; apply filter_congr; intro p _; tauto
  rw [hc1]
  have hb := c4_bound (K := K) (Sg := Sg) ha0 hcop
  rw [← hc4def, ← hRS] at hb
  by_cases hΩ : Ω a ≤ 2
  · have : c4 = 0 := by by_contra h; have := hc4Ω (Nat.pos_of_ne_zero h); omega
    rw [if_pos hΩ, this]; omega
  rw [if_neg hΩ]
  by_cases hsq : a.minFac ^ 2 ∣ a
  · rw [if_pos ⟨hs, hsq⟩]; omega
  rw [if_neg (fun h => hsq h.2)]
  push Not at hΩ
  -- the two least prime factors
  have ha1 : a ≠ 1 := by rintro rfl; simp at hΩ
  set e₁ := a.minFac with he₁
  have he₁p : e₁.Prime := Nat.minFac_prime ha1
  set b := a / e₁ with hb_def
  have hab : a = e₁ * b := (Nat.mul_div_cancel' (Nat.minFac_dvd a)).symm
  have hb0 : b ≠ 0 := by rintro h; rw [h, mul_zero] at hab; omega
  have hΩb : 2 ≤ Ω b := by
    have := ArithmeticFunction.cardFactors_mul he₁p.ne_zero hb0
    rw [← hab, ArithmeticFunction.cardFactors_apply_prime he₁p] at this; omega
  have hbnp : ¬ b.Prime := fun h => by
    rw [ArithmeticFunction.cardFactors_apply_prime h] at hΩb; omega
  have hb1 : b ≠ 1 := by rintro h; rw [h] at hΩb; simp at hΩb
  set e₂ := b.minFac with he₂
  have he₂p : e₂.Prime := Nat.minFac_prime hb1
  have he₂b : e₂ ∣ b := Nat.minFac_dvd b
  have he₂a : e₂ ∣ a := by rw [hab]; exact dvd_mul_of_dvd_right he₂b _
  have he₁a : e₁ ∣ a := Nat.minFac_dvd a
  have hne : e₂ ≠ e₁ := by
    intro h
    apply hsq
    rw [hab, sq]
    exact mul_dvd_mul_left _ (h ▸ he₂b)
  have h12 : e₁ < e₂ := lt_of_le_of_ne (Nat.minFac_le_of_dvd he₂p.two_le he₂a) hne.symm
  have hsqb : e₂ ^ 2 ≤ b := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hb0) hbnp
  have hprod : e₁ * e₂ ^ 2 < N := by
    calc e₁ * e₂ ^ 2 ≤ e₁ * b := Nat.mul_le_mul_left _ hsqb
      _ = a := hab.symm
      _ < N := haN
  have hsecond : ∀ q, q.Prime → q ∣ a → q ≠ e₁ → e₂ ≤ q := by
    intro q hq hqa hqe
    have : q ∣ b := by
      rw [hab] at hqa
      rcases (Nat.Prime.dvd_mul hq).1 hqa with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq he₁p).1 h) hqe
      · exact h
    exact Nat.minFac_le_of_dvd hq.two_le this
  have hle_of : ∀ q, q.Prime → q ∣ a → e₁ ≤ q := fun q hq hqa => Nat.minFac_le_of_dvd hq.two_le hqa
  have hKq : ∀ q, q.Prime → q ∣ a → K ≤ q := by
    intro q hq hqa
    by_contra h
    exact hs q hq (lt_of_not_ge h) (prime_dvd_not_dvd_N hcop hq hqa) hqa
  have hcopq : ∀ q, q.Prime → q ∣ a → q.Coprime N := fun q hq hqa =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 (prime_dvd_not_dvd_N hcop hq hqa)
  have hdvd12 : e₁ * e₂ ∣ a :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes he₁p he₂p).2 h12.ne) he₁a he₂a
  have hsift12 : Sifted (N * e₁) e₂ a := by
    intro q hq hqe hqN hqa
    have hqne : q ≠ e₁ := by rintro rfl; exact hqN (dvd_mul_left _ _)
    have := hsecond q hq hqa hqne
    have : (e₂ : ℝ) ≤ q := by exact_mod_cast this
    linarith
  have he1N : e₁ < N := by
    have : 1 ≤ e₂ ^ 2 := Nat.one_le_pow _ _ he₂p.pos
    nlinarith
  have he2N : e₂ < N := by
    have : e₂ ≤ e₂ ^ 2 := by nlinarith [he₂p.pos]
    nlinarith [he₁p.pos]
  have he12R : (e₁ : ℝ) < e₂ := by exact_mod_cast h12
  rcases le_or_gt Sg (e₁ : ℝ) with hS1 | hS1
  · -- `Σ ≤ e₁`: the pair `(e₁, e₂)` is counted in `S₂`, and no prime of `a` lies below `Σ`
    have hpair : (e₁, e₂) ∈ {q ∈ pairs N Sg (N : ℝ) Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a} := by
      simp only [mem_filter, pairs, mem_product, mem_range]
      exact ⟨⟨⟨he1N, he2N⟩, he₁p, he₂p, hcopq _ he₁p he₁a, hcopq _ he₂p he₂a, hS1,
        by exact_mod_cast he1N, by linarith, h12, hprod⟩, hdvd12, hsift12⟩
    have h2 := card_pos.2 ⟨_, hpair⟩
    have hRS0 : #RS = 0 := by
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨hpP, hpa⟩ := mem_filter.1 hp
      obtain ⟨hpp, -, hpS, -⟩ := mem_PS.1 hpP
      have := hle_of p hpp hpa
      have : (e₁ : ℝ) ≤ p := by exact_mod_cast this
      linarith
    omega
  rcases lt_or_ge (e₂ : ℝ) Sg with hS2 | hS2
  · -- `e₂ < Σ`: `e₁, e₂` both counted in `S₁`
    have hsub : ({e₁, e₂} : Finset ℕ) ⊆ RS := by
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact mem_filter.2 ⟨mem_PS.2 ⟨he₁p, hKq _ he₁p he₁a, hS1, hcopq _ he₁p he₁a⟩, he₁a⟩
      · rw [mem_singleton.1 hx]
        exact mem_filter.2 ⟨mem_PS.2 ⟨he₂p, hKq _ he₂p he₂a, hS2, hcopq _ he₂p he₂a⟩, he₂a⟩
    have := card_le_card hsub
    rw [card_pair h12.ne] at this
    omega
  · -- `e₁ < Σ ≤ e₂`: the pair is counted in `S₃`, and only `e₁` lies in `S₁`
    have hpair : (e₁, e₂) ∈ {q ∈ pairs N K Sg Sg | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) q.2 a} := by
      simp only [mem_filter, pairs, mem_product, mem_range]
      exact ⟨⟨⟨he1N, he2N⟩, he₁p, he₂p, hcopq _ he₁p he₁a, hcopq _ he₂p he₂a,
        hKq _ he₁p he₁a, hS1, hS2, h12, hprod⟩, hdvd12, hsift12⟩
    have h3 := card_pos.2 ⟨_, hpair⟩
    have hRS1 : RS ⊆ {e₁} := by
      intro p hp
      obtain ⟨hpP, hpa⟩ := mem_filter.1 hp
      obtain ⟨hpp, -, hpS, -⟩ := mem_PS.1 hpP
      rw [mem_singleton]
      by_contra hpe
      have := hsecond p hpp hpa hpe
      have : (e₂ : ℝ) ≤ p := by exact_mod_cast this
      linarith
    have := card_le_card hRS1
    rw [card_singleton] at this
    have he1RS : e₁ ∈ RS :=
      mem_filter.2 ⟨mem_PS.2 ⟨he₁p, hKq _ he₁p he₁a, hS1, hcopq _ he₁p he₁a⟩, he₁a⟩
    have := card_pos.2 ⟨_, he1RS⟩
    omega

end pointwise

/-- **Wu 2008 Lemma 2.1, Chen's inequality, exact form in `ℕ`**:
`2 S(A; P(N), K) + S₄ ≤ 2 #{a ∈ A : Ω(a) ≤ 2} + S₁ + 2 S₂ + S₃ + 2E`. -/
theorem lemma21_nat (A : Finset ℕ) (N : ℕ) {K Sg : ℝ} (hK : K ≤ Sg)
    (hA : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    2 * S A 1 N K + S₄ A N K Sg ≤
      2 * D12 A + S₁ A N K Sg + 2 * S₂ A N Sg + S₃ A N K Sg + 2 * Esq A N K := by
  unfold S₁ S₂ S₃ S₄ D12 Esq
  simp only [S_eq_sum, card_filter]
  rw [sum_comm (s := PS N K Sg), sum_comm (s := pairs N Sg (N : ℝ) Sg),
    sum_comm (s := pairs N K Sg Sg), sum_comm (s := triples N K Sg)]
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun a ha => ?_
  obtain ⟨h0, hN, hc⟩ := hA a ha
  have := pointwise hK h0 hN hc
  simp only [card_filter, mul_sum] at this
  exact this

/-- Vacuity: the pair sets are inhabited; `(3, 5)` is an `S₂`-shaped pair for `N = 101`,
`Σ = 3`, since `3 · 5² = 75 < 101`. -/
theorem pairs_ex : (3, 5) ∈ pairs 101 3 (101 : ℝ) 3 := by
  simp only [pairs, mem_filter, mem_product, mem_range]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.ChenDoubleSieve.Wu08

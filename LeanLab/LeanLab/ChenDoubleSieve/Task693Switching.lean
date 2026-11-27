import LeanLab.ChenDoubleSieve.Lemma41
noncomputable section
open scoped Classical
open LeanLab.ChenDoubleSieve
/-!
Elementary cofactor reduction for Wu 2004 pages 39 and 40 before equation 10.6.
The same argument applies to Upsilon eight in page 41 equation 10.11.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ChenDoubleSieve.Task693
/-- A positive cofactor below q squared is prime unless it is one or repeats p.
This is the elementary switching reduction before Wu 2004 equation 10.6. -/
theorem cofactor_prime_or_exception {N p q a m : ℕ}
    (hp : p.Prime) (haN : a.Coprime N) (ha : a = p * q * m)
    (hs : Wu41.Sifted (N * p) q a) (hm : 0 < m) (hsize : m < q ^ 2) :
    m = 1 ∨ m.Prime ∨ p ∣ m := by
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m.Prime
  · exact Or.inr (Or.inl hmp)
  by_cases hpm : p ∣ m
  · exact Or.inr (Or.inr hpm)
  exfalso
  have hr := Nat.minFac_prime hm1
  have hrd : m.minFac ∣ m := Nat.minFac_dvd m
  have hra : m.minFac ∣ a := by rw [ha]; exact dvd_mul_of_dvd_right hrd _
  have hrN : ¬ m.minFac ∣ N := by
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp (haN.coprime_dvd_left hra)
  have hrp : ¬ m.minFac ∣ p := by
    intro hdiv
    have he : m.minFac = p := (Nat.dvd_prime hp).mp hdiv |>.resolve_left hr.ne_one
    exact hpm (he ▸ hrd)
  have hrNp : ¬ m.minFac ∣ N * p := by
    intro hd
    exact (hr.dvd_mul.mp hd).elim hrN hrp
  have hrq : m.minFac < q := by
    have hsq := Nat.minFac_sq_le_self hm hmp
    nlinarith
  exact hs m.minFac hr (by exact_mod_cast hrq) hrNp hra
open Finset

/-- Exact finite switching reduction before Wu 2004 equation 10.6.
The upper bound retains unit cofactors, repeated first primes and noncoprime elements. -/
theorem sieve_switching_count (A : Finset ℕ) (N p q : ℕ) (hp : p.Prime)
    (hA : ∀ a ∈ A, a ≤ N) (hcut : N < p * q ^ 3) :
    Wu41.S A (p * q) (N * p) q ≤
      #{a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} +
      #{a ∈ A | a = p * q} + #{a ∈ A | p ^ 2 * q ∣ a} +
      #{a ∈ A | ¬ a.Coprime N} := by
  have hq : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := by omega
    simp [hq0] at hcut
  have hpq : 0 < p * q := Nat.mul_pos hp.pos hq
  have hincl : {a ∈ A | p * q ∣ a ∧ Wu41.Sifted (N * p) q a} ⊆
      ({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q}) ∪
      {a ∈ A | p ^ 2 * q ∣ a} ∪ {a ∈ A | ¬ a.Coprime N} := by
    intro a ha
    obtain ⟨haA, hda, hs⟩ := mem_filter.mp ha
    by_cases hac : a.Coprime N
    swap
    · exact mem_union_right _ (mem_filter.mpr ⟨haA, hac⟩)
    apply mem_union_left
    obtain ⟨m, ham⟩ := hda
    by_cases hm0 : m = 0
    · apply mem_union_right
      refine mem_filter.mpr ⟨haA, ?_⟩
      simp [ham, hm0]
    have hm : 0 < m := by omega
    have hsize : m < q ^ 2 := by
      apply Nat.lt_of_mul_lt_mul_left (a := p * q)
      calc p * q * m = a := ham.symm
           _ ≤ N := hA a haA
           _ < p * q ^ 3 := hcut
           _ = p * q * q ^ 2 := by ring
    rcases cofactor_prime_or_exception hp hac ham hs hm hsize with h1 | hprime | hrep
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨haA, by simpa [h1] using ham⟩
    · apply mem_union_left
      apply mem_union_left
      apply mem_filter.mpr
      refine ⟨haA, ⟨m, ham⟩, ?_⟩
      rw [ham, Nat.mul_div_cancel_left m hpq]
      exact hprime
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨haA, ?_⟩
      obtain ⟨k, hk⟩ := hrep
      refine ⟨k, ?_⟩
      rw [ham, hk]
      ring
  unfold Wu41.S
  have hc := card_le_card hincl
  have h1 := card_union_le {a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} {a ∈ A | a = p * q}
  have h2 := card_union_le
    ({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q})
    {a ∈ A | p ^ 2 * q ∣ a}
  have h3 := card_union_le
    (({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q}) ∪
      {a ∈ A | p ^ 2 * q ∣ a}) {a ∈ A | ¬ a.Coprime N}
  omega

/-- Real sifting level version of the cofactor reduction.
Wu 2004 page 41 equation 10.11 uses this for Upsilon ten at level N to sigma one. -/
theorem cofactor_prime_or_exception_at_level {N p q a m : ℕ} {z : ℝ}
    (hp : p.Prime) (haN : a.Coprime N) (ha : a = p * q * m)
    (hs : LeanLab.ChenDoubleSieve.Wu41.Sifted (N * p) z a)
    (hz : 0 ≤ z) (hm : 0 < m) (hsize : (m : ℝ) < z ^ 2) :
    m = 1 ∨ m.Prime ∨ p ∣ m := by
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m.Prime
  · exact Or.inr (Or.inl hmp)
  by_cases hpm : p ∣ m
  · exact Or.inr (Or.inr hpm)
  exfalso
  have hr := Nat.minFac_prime hm1
  have hrd : m.minFac ∣ m := Nat.minFac_dvd m
  have hra : m.minFac ∣ a := by rw [ha]; exact dvd_mul_of_dvd_right hrd _
  have hrN : ¬ m.minFac ∣ N :=
    (Nat.Prime.coprime_iff_not_dvd hr).mp (haN.coprime_dvd_left hra)
  have hrp : ¬ m.minFac ∣ p := by
    intro hdiv
    have he : m.minFac = p := (Nat.dvd_prime hp).mp hdiv |>.resolve_left hr.ne_one
    exact hpm (he ▸ hrd)
  have hrNp : ¬ m.minFac ∣ N * p := by
    intro hd
    exact (hr.dvd_mul.mp hd).elim hrN hrp
  have hrz : (m.minFac : ℝ) < z := by
    have hsq : (m.minFac : ℝ) ^ 2 ≤ m := by exact_mod_cast Nat.minFac_sq_le_self hm hmp
    have hr0 : (0 : ℝ) ≤ m.minFac := Nat.cast_nonneg _
    nlinarith
  exact hs m.minFac hr hrz hrNp hra

open Real

/-- The exponent conditions in Wu 2004 equation 10.1 force a cofactor below z squared.
This product form covers the four pair terms in equations 10.10 to 10.12. -/
theorem power_cut_product {x p q z α β γ : ℝ} (hx : 1 < x)
    (hp : x ^ α ≤ p) (hq : x ^ β ≤ q) (hz : x ^ γ ≤ z)
    (he : 1 < α + β + 2 * γ) : x < p * q * z ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hp0 : 0 ≤ p := (rpow_pos_of_pos hx0 α).le.trans hp
  have hq0 : 0 ≤ q := (rpow_pos_of_pos hx0 β).le.trans hq
  have hz0 : 0 ≤ z := (rpow_pos_of_pos hx0 γ).le.trans hz
  have hpow : x < x ^ (α + β + 2 * γ) := by
    simpa using rpow_lt_rpow_of_exponent_lt hx he
  have hsq : (x ^ γ) ^ 2 ≤ z ^ 2 := by nlinarith [rpow_pos_of_pos hx0 γ]
  have hfact : x ^ (α + β + 2 * γ) = x ^ α * x ^ β * (x ^ γ) ^ 2 := by
    rw [rpow_add hx0, rpow_add hx0]
    congr 1
    rw [mul_comm (2 : ℝ) γ]
    simpa using rpow_mul_natCast hx0.le γ 2
  rw [hfact] at hpow
  exact hpow.trans_le (mul_le_mul
    (mul_le_mul hp hq (rpow_pos_of_pos hx0 β).le hp0) hsq (sq_nonneg _) (mul_nonneg hp0 hq0))


/-- Exact real-level finite switching reduction for Wu 2004 page 41 equation 10.11.
The four exceptional counts are explicit and no analytic input is used. -/
theorem sieve_switching_count_at_level (A : Finset ℕ) (N p q : ℕ) (hp : p.Prime)
    (hA : ∀ a ∈ A, a ≤ N) (z : ℝ) (hz : 0 ≤ z)
    (hcut : (N : ℝ) < (p : ℝ) * q * z ^ 2) :
    Wu41.S A (p * q) (N * p) z ≤
      #{a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} +
      #{a ∈ A | a = p * q} + #{a ∈ A | p ^ 2 * q ∣ a} +
      #{a ∈ A | ¬ a.Coprime N} := by
  have hq : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := by omega
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    simp only [hq0, Nat.cast_zero, mul_zero, zero_mul] at hcut
    linarith
  have hpq : 0 < p * q := Nat.mul_pos hp.pos hq
  have hincl : {a ∈ A | p * q ∣ a ∧ Wu41.Sifted (N * p) z a} ⊆
      ({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q}) ∪
      {a ∈ A | p ^ 2 * q ∣ a} ∪ {a ∈ A | ¬ a.Coprime N} := by
    intro a ha
    obtain ⟨haA, hda, hs⟩ := mem_filter.mp ha
    by_cases hac : a.Coprime N
    swap
    · exact mem_union_right _ (mem_filter.mpr ⟨haA, hac⟩)
    apply mem_union_left
    obtain ⟨m, ham⟩ := hda
    by_cases hm0 : m = 0
    · apply mem_union_right
      refine mem_filter.mpr ⟨haA, ?_⟩
      simp [ham, hm0]
    have hm : 0 < m := by omega
    have hsize : (m : ℝ) < z ^ 2 := by
      have hprod : (0 : ℝ) < (p : ℝ) * q := by exact_mod_cast hpq
      apply (mul_lt_mul_iff_right₀ hprod).mp
      calc (p : ℝ) * q * m = a := by exact_mod_cast ham.symm
           _ ≤ N := by exact_mod_cast hA a haA
           _ < (p : ℝ) * q * z ^ 2 := hcut
    rcases cofactor_prime_or_exception_at_level hp hac ham hs hz hm hsize with h1 | hprime | hrep
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨haA, by simpa [h1] using ham⟩
    · apply mem_union_left
      apply mem_union_left
      apply mem_filter.mpr
      refine ⟨haA, ⟨m, ham⟩, ?_⟩
      rw [ham, Nat.mul_div_cancel_left m hpq]
      exact hprime
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨haA, ?_⟩
      obtain ⟨k, hk⟩ := hrep
      refine ⟨k, ?_⟩
      rw [ham, hk]
      ring
  unfold Wu41.S
  have hc := card_le_card hincl
  have h1 := card_union_le {a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} {a ∈ A | a = p * q}
  have h2 := card_union_le
    ({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q})
    {a ∈ A | p ^ 2 * q ∣ a}
  have h3 := card_union_le
    (({a ∈ A | p * q ∣ a ∧ (a / (p * q)).Prime} ∪ {a ∈ A | a = p * q}) ∪
      {a ∈ A | p ^ 2 * q ∣ a}) {a ∈ A | ¬ a.Coprime N}
  omega


end LeanLab.ChenDoubleSieve.Task693

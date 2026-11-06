import LeanLab.ChirreHagen2025.Additional122

/-!
P0075 page 14 display A.1. Separate prime terms from proper prime powers
before reindexing the remaining finite sum. This concerns only the finite
arithmetic split and does not use the numerical estimate questioned in Audit377.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp377c
open ArithmeticFunction

/-- P0075 page 14 display A.1, exact separation of the prime contribution.
Mangoldt vanishes outside prime powers. No numerical or analytic input occurs. -/
theorem prime_separation (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ^ 2 / (n : ℝ)) =
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log (p : ℝ) ^ 2 / (p : ℝ)) +
      (∑ n ∈ Finset.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) (Finset.Icc 1 ⌊x⌋₊),
        vonMangoldt n ^ 2 / (n : ℝ)) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime n
  · simp [hp, vonMangoldt_apply_prime hp]
  · by_cases hpow : IsPrimePow n
    · simp [hp, hpow]
    · simp [hp, hpow, vonMangoldt_eq_zero_iff.mpr hpow]

/-- P0075 page 14 display A.1, the logarithmic cutoff for one prime power. -/
theorem exponent_cutoff (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (x : ℝ) (hpow : (p : ℝ) ^ k ≤ x) :
    k ≤ ⌊Real.log x / Real.log (p : ℝ)⌋₊ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  apply (Nat.le_floor_iff' (by omega : k ≠ 0)).mpr
  rw [le_div_iff₀ hl, ← Real.log_pow]
  exact Real.log_le_log (by positivity) hpow

/-- P0075 page 14 display A.1, the prime cutoff for one proper prime power. -/
theorem prime_cutoff (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k)
    (x : ℝ) (hpow : (p : ℝ) ^ k ≤ x) :
    p ≤ ⌊Real.sqrt x⌋₊ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsq : (p : ℝ) ^ 2 ≤ x := (pow_le_pow_right₀ hp1 hk).trans hpow
  have hx0 : 0 ≤ x := (sq_nonneg (p : ℝ)).trans hsq
  apply (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr
  exact (Real.le_sqrt (Nat.cast_nonneg p) hx0).mpr hsq

/-- LEAF. P0075 page 14 display A.1, reindex only the proper prime powers.
A term n = p to the k with k at least two has p at most square root x
and k at most floor of log x over log p. The prime contribution is absent. -/
theorem proper_prime_power_reindex (x : ℝ) (hx : 10 ^ 13 ≤ x) :
    (∑ n ∈ Finset.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) (Finset.Icc 1 ⌊x⌋₊),
      vonMangoldt n ^ 2 / (n : ℝ)) ≤
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
        Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) := by
  classical
  let S := Finset.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) (Finset.Icc 1 ⌊x⌋₊)
  have hex (n : ℕ) (hn : n ∈ S) :
      ∃ z : (Σ _ : ℕ, ℕ), z.1.Prime ∧ 2 ≤ z.2 ∧ z.1 ^ z.2 = n := by
    have hn' := (Finset.mem_filter.mp hn).2
    obtain ⟨p, k, hp, hk, heq⟩ := hn'.1
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      apply hn'.2
      rw [← heq, hk1, pow_one]
      exact hp.nat_prime
    exact ⟨⟨p, k⟩, hp.nat_prime, hk2, heq⟩
  choose e he using hex
  let E : ℕ → (Σ _ : ℕ, ℕ) := fun n => if hn : n ∈ S then e n hn else ⟨2, 2⟩
  have hE (n : ℕ) (hn : n ∈ S) :
      (E n).1.Prime ∧ 2 ≤ (E n).2 ∧ (E n).1 ^ (E n).2 = n := by
    simpa only [E, dite_eq_left hn] using he n hn
  rw [Finset.sum_sigma']
  apply Finset.sum_le_sum_of_injOn E
  · intro n hn m hm heq
    calc n = (E n).1 ^ (E n).2 := (hE n hn).2.2.symm
         _ = (E m).1 ^ (E m).2 := by rw [heq]
         _ = m := (hE m hm).2.2
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp, hk, heq⟩ := hE n hn
    have hnN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hpx : ((E n).1 : ℝ) ^ (E n).2 ≤ x := by
      rw [← Nat.cast_pow, heq]
      exact (Nat.cast_le.mpr hnN).trans (Nat.floor_le (by linarith))
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hp.one_le, prime_cutoff _ _ hp hk x hpx⟩, hp⟩
    · exact Finset.mem_Icc.mpr ⟨hk, exponent_cutoff _ _ hp (by omega) x hpx⟩
  · intro n hn
    obtain ⟨hp, hk, heq⟩ := hE n hn
    change vonMangoldt n ^ 2 / (n : ℝ) ≤
      Real.log ((E n).1 : ℝ) ^ 2 / ((E n).1 : ℝ) ^ (E n).2
    conv_lhs => rw [← heq, vonMangoldt_apply_pow (by omega : (E n).2 ≠ 0),
      vonMangoldt_apply_prime hp, Nat.cast_pow]
  · intro z hz hzn
    positivity

/-- P0075 page 14 display A.1, exact statement of DecompJ611.leaf_sum_split.
The proper prime power reindexing is proved by a finite sum injection. -/
theorem leaf_sum_split (x : ℝ) (hx : 10 ^ 13 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ^ 2 / (n : ℝ)) ≤
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log (p : ℝ) ^ 2 / (p : ℝ)) +
        (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
          ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
            Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) := by
  rw [prime_separation]
  exact add_le_add le_rfl (proper_prime_power_reindex x hx)

end LeanLab.ChirreHagen2025.Decomp377c

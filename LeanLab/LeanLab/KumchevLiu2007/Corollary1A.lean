/-
P0088 Kumchev-Liu, Section 6.2: the combinatorial half of the proof of Corollary 1 from Theorem 3.

If `q` is a prime with `q > 3`, `q ≡ 1 (mod 5)` and `q² ≤ X`, then every `n ∈ (X, X + H]` with
`n ≡ 4 (mod 24)`, `n ≢ 1 (mod 5)` and `n` not a sum of four prime squares gives
`m = n - q² ∈ (X - q², X - q² + H]` with `m ∈ ℋ₃` and `m` not a sum of three prime squares.
With `q ≡ 2 (mod 5)` the same holds for `n ≡ 1 (mod 5)`. So
`E₄(X + H) - E₄(X) ≤ (E₃(X₁ + H) - E₃(X₁)) + (E₃(X₂ + H) - E₃(X₂))`, `Xⱼ = X - qⱼ²`, the
paper's (83) and (84).

* `cnt_le_shift`: the shift `n ↦ n - k` injects one count into the other.
* `cnt_split`: a count splits along any predicate.
* `E4_le_two_E3`: the displayed inequality.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1165. Checked only by the
Lean kernel. Binary Goldbach is OPEN; these are Hua type problems.
-/
import LeanLab.KumchevLiu2007.Statements

namespace LeanLab.KumchevLiu2007
open Real

attribute [local instance] Classical.propDecidable

lemma mem_cnt {S : ℕ → Prop} {X H : ℝ} {n : ℕ} :
    n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n) ↔
      n ≤ ⌊X + H⌋₊ ∧ X < n ∧ S n := by
  simp [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- **The shift**: if every `n > k` with `S n` has `T (n - k)`, and `k ≤ X`, then the count of `S`
in `(X, X + H]` is at most the count of `T` in `(X - k, X - k + H]`. -/
theorem cnt_le_shift (S T : ℕ → Prop) {X H : ℝ} (k : ℕ) (hk : (k : ℝ) ≤ X) (hH : 0 ≤ H)
    (hST : ∀ n : ℕ, k < n → S n → T (n - k)) : cntIoc S X H ≤ cntIoc T (X - k) H := by
  unfold cntIoc
  apply Finset.card_le_card_of_injOn (fun n => n - k)
  · intro n hn
    rw [Finset.mem_coe, mem_cnt] at hn
    obtain ⟨hn1, hn2, hn3⟩ := hn
    have hkn : k < n := by exact_mod_cast lt_of_le_of_lt hk hn2
    rw [Finset.mem_coe, mem_cnt]
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by rw [Nat.cast_sub hkn.le]
    have hX0 : 0 ≤ X + H := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hnle : (n : ℝ) ≤ X + H := le_trans (by exact_mod_cast hn1) (Nat.floor_le hX0)
    refine ⟨?_, ?_, hST n hkn hn3⟩
    · apply Nat.le_floor
      rw [hcast]; linarith
    · rw [hcast]; linarith
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_cnt] at ha hb
    have hka : k < a := by exact_mod_cast lt_of_le_of_lt hk ha.2.1
    have hkb : k < b := by exact_mod_cast lt_of_le_of_lt hk hb.2.1
    simp only at hab
    omega

/-- A count splits along any predicate `R`. -/
theorem cnt_split (S R : ℕ → Prop) (X H : ℝ) :
    cntIoc S X H = cntIoc (fun n => S n ∧ R n) X H + cntIoc (fun n => S n ∧ ¬ R n) X H := by
  unfold cntIoc
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2.2 h1.2.2.2

lemma sq_mod5_of_mod5_one {q : ℕ} (h : q % 5 = 1) : q ^ 2 % 5 = 1 := by
  rw [Nat.pow_mod, h]

lemma sq_mod5_of_mod5_two {q : ℕ} (h : q % 5 = 2) : q ^ 2 % 5 = 4 := by
  rw [Nat.pow_mod, h]

/-- The reduction for one prime `q`: if `n ≡ 4 (mod 24)` is not a sum of four prime squares,
`n > q²`, and `n - q²` is prime to `5`, then `n - q² ∈ ℋ₃` is not a sum of three. -/
lemma shift_exceptional {q n : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) (hn : q ^ 2 < n)
    (h4 : InH4 n) (hnot : ¬ IsFourPrimeSquares n) (h5 : (n - q ^ 2) % 5 ≠ 0) :
    InH3 (n - q ^ 2) ∧ ¬ IsThreePrimeSquares (n - q ^ 2) := by
  have hq24 := sq_mod_24 hq h2 h3
  unfold InH4 at h4
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rintro ⟨a, b, c, ha, hb, hc, he⟩
  exact hnot ⟨a, b, c, q, ha, hb, hc, hq, by omega⟩

/-- **(83) and (84)**: with primes `q₁ ≡ 1`, `q₂ ≡ 2 (mod 5)`, both above `3`, and `qⱼ² ≤ X`,
`E₄(X + H) - E₄(X) ≤ (E₃(X - q₁² + H) - E₃(X - q₁²)) + (E₃(X - q₂² + H) - E₃(X - q₂²))`. -/
theorem E4_le_two_E3 {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (h₁ : q₁ % 5 = 1)
    (h₂ : q₂ % 5 = 2) (h₁3 : 3 < q₁) (h₂3 : 3 < q₂) {X H : ℝ} (hH : 0 ≤ H)
    (hX₁ : ((q₁ ^ 2 : ℕ) : ℝ) ≤ X) (hX₂ : ((q₂ ^ 2 : ℕ) : ℝ) ≤ X) :
    E4Short X H ≤ E3Short (X - (q₁ ^ 2 : ℕ)) H + E3Short (X - (q₂ ^ 2 : ℕ)) H := by
  unfold E4Short E3Short
  rw [cnt_split _ (fun n => n % 5 = 1) X H]
  have hA := cnt_le_shift (fun n => (InH4 n ∧ ¬ IsFourPrimeSquares n) ∧ ¬ n % 5 = 1)
    (fun n => InH3 n ∧ ¬ IsThreePrimeSquares n) (q₁ ^ 2) hX₁ hH (fun n hn hS => by
      refine shift_exceptional hq₁ (by omega) (by omega) hn hS.1.1 hS.1.2 ?_
      have := sq_mod5_of_mod5_one h₁
      omega)
  have hB := cnt_le_shift (fun n => (InH4 n ∧ ¬ IsFourPrimeSquares n) ∧ n % 5 = 1)
    (fun n => InH3 n ∧ ¬ IsThreePrimeSquares n) (q₂ ^ 2) hX₂ hH (fun n hn hS => by
      refine shift_exceptional hq₂ (by omega) (by omega) hn hS.1.1 hS.1.2 ?_
      have := sq_mod5_of_mod5_two h₂
      omega)
  omega

#print axioms cnt_le_shift
#print axioms cnt_split
#print axioms E4_le_two_E3

end LeanLab.KumchevLiu2007

/-
Split of roughCount_of_shortIntervalPNT, MMS arXiv 1610.02017v2 page 11 bottom
display, first Buchstab step on the rough cofactor. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp581b

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory

/-- Membership in ints by the real bounds. Derived. -/
theorem s145r_mem_ints {u v : ℝ} (hv : 0 ≤ v) (m : ℕ) :
    m ∈ ints u v ↔ u ≤ m ∧ (m : ℝ) ≤ v := by
  unfold ints
  rw [mem_Icc, Nat.ceil_le, Nat.le_floor_iff hv]

/-- Logarithmic size of the triple product. -/
theorem s145r_triple_logs {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ} (hp : p ∈ primeTriples x) :
    Real.log (tripleProduct p : ℝ) ≤ 3 / 4 * Real.log x ∧
      Real.log ((tripleProduct p : ℝ) * p.1) ≤ Real.log x := by
  classical
  have h := (mem_filter.mp hp).2
  obtain ⟨h1, h12, h23, h3⟩ := primeTriple_log_coordinates hx hp
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h₁ : (0 : ℝ) < p.1 := by exact_mod_cast h.1.pos
  have h₂ : (0 : ℝ) < p.2.1 := by exact_mod_cast h.2.1.pos
  have h₃ : (0 : ℝ) < p.2.2 := by exact_mod_cast h.2.2.1.pos
  have hpLog : Real.log (tripleProduct p : ℝ) =
      Real.log p.1 + Real.log p.2.1 + Real.log p.2.2 := by
    simp only [tripleProduct, Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero h₁.ne' h₂.ne') h₃.ne', Real.log_mul h₁.ne' h₂.ne']
  have hd : (0:ℝ) < tripleProduct p := by exact_mod_cast tripleProduct_pos hp
  rw [div_le_div_iff_of_pos_right hlx] at h12 h23
  rw [div_le_iff₀ hlx] at h3
  rw [Real.log_mul hd.ne' h₁.ne', hpLog]
  constructor <;> linarith


/-- Reindexing n equal to d m in the prime cofactor count. Derived,
MMS page 11 equation 5.1. -/
theorem s145r_prime_count_eq {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ} (hp : p ∈ primeTriples x)
    (a b : ℝ) (ha : x ≤ a) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0) else 0) =
      (((ints (x / tripleProduct p) ((x + Task379.referenceLength x) / tripleProduct p)).filter
          (fun m : ℕ => m.Prime ∧ a < (tripleProduct p : ℝ) * m ∧
            (tripleProduct p : ℝ) * m < b)).card : ℝ) := by
  classical
  set d := tripleProduct p with hd_def
  have hdpos : 0 < d := tripleProduct_pos hp
  have hd : (0:ℝ) < d := by exact_mod_cast hdpos
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Task379.referenceLength x := by
    unfold Task379.referenceLength; positivity
  have hdp : (d : ℝ) * p.1 ≤ x := by
    have := (s145r_triple_logs hx hp).2
    have hp1 : (0:ℝ) < p.1 := by exact_mod_cast ((mem_filter.mp hp).2.1.pos)
    exact (Real.log_le_log_iff (by positivity) hx0).mp this
  have hmem : ∀ m : ℕ, m ∈ ints (x / d) ((x + Task379.referenceLength x) / d) ↔
      d * m ∈ ints x (x + Task379.referenceLength x) := by
    intro m
    rw [s145r_mem_ints (by positivity), s145r_mem_ints (by positivity), div_le_iff₀ hd,
      le_div_iff₀ hd]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [Finset.card_filter, Nat.cast_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun m _ _ => d * m) ?_ ?_ ?_ ?_
  · intro m hm _
    exact (hmem m).mp hm
  · intro m₁ _ _ m₂ _ _ h
    exact Nat.eq_of_mul_eq_mul_left hdpos h
  · intro n hn hne
    have hdn : d ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b := by
      by_contra hc; exact hne (if_neg hc)
    obtain ⟨k, rfl⟩ := hdn.1
    refine ⟨k, (hmem k).mpr hn, ?_, rfl⟩
    have hk : (d * k) / d = k := Nat.mul_div_cancel_left k hdpos
    rw [hk] at hne
    have hkp : k.Prime := by
      by_contra hc; exact hne (by simp [hdn.1, hc])
    push_cast at hdn
    simp [hkp, hdn.2]
  · intro m hm _
    have hk : (d * m) / d = m := Nat.mul_div_cancel_left m hdpos
    rw [hk]
    have hxm : x ≤ (d : ℝ) * m := by
      have := (s145r_mem_ints (by positivity) _).mp ((hmem m).mp hm)
      push_cast at this; exact this.1
    by_cases hpm : m.Prime ∧ a < (d : ℝ) * m ∧ (d : ℝ) * m < b
    · have hp1m : (p.1 : ℝ) ≤ m := by
        by_contra hc
        push Not at hc
        have : (d : ℝ) * m < d * p.1 := mul_lt_mul_of_pos_left hc hd
        linarith
      rw [if_pos hpm, if_pos ⟨dvd_mul_right d m, by push_cast; exact hpm.2⟩, if_pos hpm.1,
        Task361.roughIndicator_prime hpm.1 hp1m]
      simp
    · rw [if_neg hpm]
      by_cases hq : a < (d : ℝ) * m ∧ (d : ℝ) * m < b
      · have : ¬ m.Prime := fun h => hpm ⟨h, hq⟩
        simp [this]
      · push_cast
        rw [if_neg (fun h => hq h.2)]


/-- The cited short interval prime number theorem at every rescaled scale, the
hypothesis of roughCount_of_shortIntervalPNT, as a proposition. -/
def s145r_PNTHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ x ^ (9 / 10 : ℝ) → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log (x / d) * (((ints (x / d) ((x + Task379.referenceLength x) / d)).filter
          (fun m : ℕ => m.Prime ∧ a < (d : ℝ) * m ∧ (d : ℝ) * m < b)).card : ℝ) -
          (b - a) / d| ≤ ε * Task379.referenceLength x / d

/-- MMS page 11 bottom display, first Buchstab step, the prime cofactors.
PROVED from the hypothesis: reindex n equal to d m, a prime cofactor is at
least p one, and log x over log of x over d is at most four. -/
theorem s145r_primeCofactor_count (hPNT : s145r_PNTHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            (if (n / tripleProduct p).Prime then
              Task361.roughIndicator (n / tripleProduct p) p.1 else 0) else 0) -
          (b - a) * (Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  intro ε hε
  obtain ⟨X, hX⟩ := hPNT (ε / 4) (by linarith)
  refine ⟨max X 2, fun x hx p hp a b ha hab hb => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hdpos : 0 < tripleProduct p := tripleProduct_pos hp
  have hd : (0:ℝ) < tripleProduct p := by exact_mod_cast hdpos
  have hlogd := (s145r_triple_logs hx1 hp).1
  have hd910 : (tripleProduct p : ℝ) ≤ x ^ (9 / 10 : ℝ) := by
    apply (Real.log_le_log_iff hd (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_rpow hx0]; linarith
  have h := hX x ((le_max_left _ _).trans hx) (tripleProduct p) hdpos hd910 a b ha hab hb
  rw [s145r_prime_count_eq hx1 hp a b ha]
  set N := (((ints (x / tripleProduct p) ((x + Task379.referenceLength x) / tripleProduct p)).filter
          (fun m : ℕ => m.Prime ∧ a < (tripleProduct p : ℝ) * m ∧
            (tripleProduct p : ℝ) * m < b)).card : ℝ)
  have hlxd : Real.log (x / tripleProduct p) = Real.log x - Real.log (tripleProduct p) :=
    Real.log_div hx0.ne' hd.ne'
  have hlq : Real.log x / 4 ≤ Real.log (x / tripleProduct p) := by rw [hlxd]; linarith
  have hlq0 : 0 < Real.log (x / tripleProduct p) := by linarith
  set r := Real.log x / Real.log (x / tripleProduct p) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr4 : r ≤ 4 := by rw [hr, div_le_iff₀ hlq0]; linarith
  have heq : Real.log x * N - (b - a) * (Real.log x /
      ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p))) =
      r * (Real.log (x / tripleProduct p) * N - (b - a) / tripleProduct p) := by
    rw [hr]; field_simp
  rw [heq, abs_mul, abs_of_nonneg hr0]
  have hL : 0 ≤ ε / 4 * Task379.referenceLength x / tripleProduct p := by
    unfold Task379.referenceLength; positivity
  calc r * |Real.log (x / tripleProduct p) * N - (b - a) / tripleProduct p|
      ≤ 4 * (ε / 4 * Task379.referenceLength x / tripleProduct p) :=
        mul_le_mul hr4 h (abs_nonneg _) (by norm_num)
    _ = ε * Task379.referenceLength x / tripleProduct p := by ring

/- Proof plan for the LEAF below: Remove the least prime factor q of m, at least p one, and recurse on
m over q, rough at q, at most nine levels since every factor exceeds x to the one
tenth; the last prime lies in a short interval at scale at least x to the one
tenth, where the hypothesis applies with modulus d times the removed primes, at
most x to the nine tenths; prime powers and the boundary of the ordering cost
o of the reference length over d; the prime sums over the removed primes become
the Buchstab integrals by partial summation, and the sum of the errors over the
removed primes is bounded by a power of the reciprocal prime mass. -/
/-- LEAF: MMS page 11 bottom display, Buchstab recursion for the composite
rough cofactors m equal to n over d, density buchstab of u minus one over u
divided by log p one with u frozen at log of x over d over log p one.
Class HARD. -/
theorem s145r_compositeCofactor_count (hPNT : s145r_PNTHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            (if (n / tripleProduct p).Prime then 0 else
              Task361.roughIndicator (n / tripleProduct p) p.1) else 0) -
          (b - a) * (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  sorry

/-- The rough cofactor count is the prime part plus the composite part.
Derived first Buchstab step, MMS page 11 bottom display. -/
theorem s145r_count_split (x a b : ℝ) (p : ℕ × ℕ × ℕ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          Task361.roughIndicator (n / tripleProduct p) p.1 else 0) =
      (∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0) else 0) +
      (∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then 0 else
            Task361.roughIndicator (n / tripleProduct p) p.1) else 0) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- roughCount_of_shortIntervalPNT from the two leaves above.
CONDITIONAL ON s145r_primeCofactor_count and s145r_compositeCofactor_count,
each itself conditional on the cited hypothesis. -/
theorem roughCount_of_shortIntervalPNT_of_s145_leaves
    (hPNT : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ x ^ (9 / 10 : ℝ) → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log (x / d) * (((ints (x / d) ((x + Task379.referenceLength x) / d)).filter
          (fun m : ℕ => m.Prime ∧ a < (d : ℝ) * m ∧ (d : ℝ) * m < b)).card : ℝ) -
          (b - a) / d| ≤ ε * Task379.referenceLength x / d) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0) -
          (b - a) * cofactorModel x p| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  intro ε hε
  obtain ⟨X₁, h₁⟩ := s145r_primeCofactor_count hPNT (ε / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := s145r_compositeCofactor_count hPNT (ε / 2) (by linarith)
  refine ⟨max X₁ X₂, fun x hx p hp a b ha hab hb => ?_⟩
  have e1 := h₁ x ((le_max_left _ _).trans hx) p hp a b ha hab hb
  have e2 := h₂ x ((le_max_right _ _).trans hx) p hp a b ha hab hb
  rw [s145r_count_split]
  set A := ∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0) else 0
  set B := ∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then 0 else
            Task361.roughIndicator (n / tripleProduct p) p.1) else 0
  set P := Real.log x / ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p))
  have hsplit : Real.log x * (A + B) - (b - a) * cofactorModel x p =
      (Real.log x * A - (b - a) * P) +
        (Real.log x * B - (b - a) * (cofactorModel x p - P)) := by ring
  rw [hsplit]
  have hh := abs_add_le (Real.log x * A - (b - a) * P)
    (Real.log x * B - (b - a) * (cofactorModel x p - P))
  have he : ε / 2 * Task379.referenceLength x / tripleProduct p +
      ε / 2 * Task379.referenceLength x / tripleProduct p =
      ε * Task379.referenceLength x / tripleProduct p := by ring
  linarith

end LeanLab.Ternary.MMS.Task581.Feed1122


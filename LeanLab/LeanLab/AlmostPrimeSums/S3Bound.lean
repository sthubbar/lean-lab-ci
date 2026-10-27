/-
AI-written Lean code, OpenAI Codex, task02, 2026-10-21, U-80020, T1.
P0072 Togashi and Uchiyama 1964, Section 5, pp. 67 to 68.
An elementary finite bound for S₃. The paper's analytic sieve estimates
and its asymptotic estimate for S₃ are not proved here. Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

open Finset

namespace LeanLab.AlmostPrimeSums.S3Bound

open TogashiUchiyamaSection5

/-- Multiples of d in the closed interval from zero to N, including zero. -/
lemma card_multiples_le (N d : ℕ) :
    ((range (N + 1)).filter (fun n => d ∣ n)).card ≤ N / d + 1 := by
  have h := card_le_card_of_injOn (s := (range (N + 1)).filter (fun n => d ∣ n))
    (t := range (N / d + 1)) (fun n => n / d) ?_ ?_
  · simpa using h
  · intro n hn
    have hnN : n ≤ N := by have := (mem_filter.mp hn).1; simp only [mem_range] at this; omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN))
  · intro a ha b hb hab
    have ha' := Nat.div_mul_cancel (mem_filter.mp ha).2
    have hb' := Nat.div_mul_cancel (mem_filter.mp hb).2
    change a / d = b / d at hab
    calc a = a / d * d := ha'.symm
         _ = b / d * d := congrArg (fun k => k * d) hab
         _ = b := hb'

/-- At most twice the preceding count for either n or N - n divisible by d. -/
lemma card_either_multiple_le (N d : ℕ) :
    ((range (N + 1)).filter (fun n => d ∣ n ∨ d ∣ N - n)).card ≤
      2 * (N / d + 1) := by
  have hreflect : ((range (N + 1)).filter (fun n => d ∣ N - n)).card ≤
      ((range (N + 1)).filter (fun n => d ∣ n)).card := by
    apply card_le_card_of_injOn (fun n => N - n)
    · intro n hn
      change N - n ∈ (range (N + 1)).filter (fun n => d ∣ n)
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hn).2⟩
    · intro a ha b hb hab
      have haN := (mem_filter.mp ha).1
      have hbN := (mem_filter.mp hb).1
      simp only [mem_range] at haN hbN
      change N - a = N - b at hab
      omega
  rw [filter_or]
  change (((range (N + 1)).filter (fun n => d ∣ n)) ∪
    ((range (N + 1)).filter (fun n => d ∣ N - n))).card ≤ 2 * (N / d + 1)
  have hunion := card_union_le ((range (N + 1)).filter (fun n => d ∣ n))
    ((range (N + 1)).filter (fun n => d ∣ N - n))
  have h := card_multiples_le N d
  omega

/-- Coprimality of n and N prevents a prime square from splitting between the factors. -/
theorem square_dvd_or {N n q : ℕ} (hn : n ∈ S1set N) (hq : q.Prime)
    (hd : q ^ 2 ∣ n * (N - n)) : q ^ 2 ∣ n ∨ q ^ 2 ∣ N - n := by
  have hA := mem_Aset.mp (mem_filter.mp hn).1
  have hcop : n.Coprime (N - n) := (Nat.coprime_sub_self_right hA.2.1).mpr hA.2.2
  exact (hcop.isPrimePow_dvd_mul (hq.isPrimePow.pow (by decide : 2 ≠ 0))).mp hd

/-- Section 5, p. 67: the elementary finite union bound for S₃. -/
theorem S3_card_le (N : ℕ) :
    (S3set N).card ≤ ∑ q ∈ Qset N, 2 * (N / q ^ 2 + 1) := by
  let B : ℕ → Finset ℕ := fun q =>
    (range (N + 1)).filter (fun n => q ^ 2 ∣ n ∨ q ^ 2 ∣ N - n)
  have hsub : S3set N ⊆ (Qset N).biUnion B := by
    intro n hn
    obtain ⟨hn1, q, hq, hd⟩ := mem_filter.mp hn
    have hA := mem_Aset.mp (mem_filter.mp hn1).1
    have hprime : q.Prime := (mem_filter.mp hq).2.1
    exact mem_biUnion.mpr ⟨q, hq, mem_filter.mpr
      ⟨mem_range.mpr (by omega), square_dvd_or hn1 hprime hd⟩⟩
  calc
    (S3set N).card ≤ ((Qset N).biUnion B).card := card_le_card hsub
    _ ≤ ∑ q ∈ Qset N, (B q).card := card_biUnion_le
    _ ≤ ∑ q ∈ Qset N, 2 * (N / q ^ 2 + 1) :=
      sum_le_sum (fun q _ => card_either_multiple_le N (q ^ 2))

/-- Concrete instances at N = 28, q = 3, with both residue classes present. -/
example : ((range 29).filter (fun n => 9 ∣ n)).card = 4 := by decide

example : ((range 29).filter (fun n => 9 ∣ n ∨ 9 ∣ 28 - n)).card = 8 := by decide

example : 9 ∈ S1set 28 ∧ Nat.Prime 3 ∧ 3 ^ 2 ∣ 9 * (28 - 9) := by decide

example : 3 ∈ Qset 28 ∧ (S3set 28).card = 4 ∧
    (∑ q ∈ Qset 28, 2 * (28 / q ^ 2 + 1)) = 8 := by decide

end LeanLab.AlmostPrimeSums.S3Bound

#print axioms LeanLab.AlmostPrimeSums.S3Bound.card_multiples_le
#print axioms LeanLab.AlmostPrimeSums.S3Bound.card_either_multiple_le
#print axioms LeanLab.AlmostPrimeSums.S3Bound.square_dvd_or
#print axioms LeanLab.AlmostPrimeSums.S3Bound.S3_card_le

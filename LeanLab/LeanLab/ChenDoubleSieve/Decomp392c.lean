import Mathlib

/-!
The product placement step in Iwaniec's cited sieve construction.
Source: https://doi.org/10.4064/aa-37-1-307-320, page 312 Lemma 1 proof.
This is the elementary partition step, not the full admissible weight construction.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open List
namespace LeanLab.ChenDoubleSieve.Task392

/-- At least one bin accepts the next factor under the prefix square bound. -/
theorem factor_placement {a b x M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hprod : a * b * x ^ 2 ≤ M * N) : a * x ≤ M ∨ b * x ≤ N := by
  by_contra h
  push Not at h
  have hb : 0 < b * x := hN.trans h.2
  have ht : M * N < (a * x) * (b * x) :=
    (mul_lt_mul_of_pos_left h.2 hM).trans (mul_lt_mul_of_pos_right h.1 hb)
  nlinarith only [ht, hprod]

/-- A list with the prefix square bounds can be partitioned into two bounded
products. No analytic estimate or sieve function occurs in this theorem. -/
theorem factor_partition (l : List ℝ) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hp : ∀ i : ℕ, ∀ hi : i < l.length, (l.take i).prod * l[i] ^ 2 ≤ M * N) :
    ∃ a b : List ℝ, l.Perm (a ++ b) ∧ a.prod ≤ M ∧ b.prod ≤ N := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], [], by simp, hM, hN⟩
  | @append_singleton l x ih =>
    have hpre : ∀ i : ℕ, ∀ hi : i < l.length,
        (l.take i).prod * l[i] ^ 2 ≤ M * N := by
      intro i hi
      have h := hp i (by simp; omega)
      simpa [List.take_append, List.getElem_append_left hi, Nat.sub_eq_zero_of_le hi.le] using h
    obtain ⟨a, b, hab, ha, hb⟩ := ih hpre
    have hlast := hp l.length (by simp)
    simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
      List.append_nil, List.getElem_append_right (by omega : l.length ≤ l.length),
      Nat.sub_self, List.getElem_cons_zero] at hlast
    have heq : l.prod = a.prod * b.prod := by rw [hab.prod_eq, List.prod_append]
    rw [heq] at hlast
    rcases factor_placement (by linarith : 0 < M) (by linarith : 0 < N) hlast with hx | hx
    · refine ⟨a ++ [x], b, ?_, by simpa using hx, hb⟩
      exact (hab.append_right [x]).trans (by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := b) (l₂ := [x])).append_left a)
    · refine ⟨a, b ++ [x], ?_, ha, by simpa using hx⟩
      simpa only [List.append_assoc] using hab.append_right [x]

/-- The even length support tests of the lower Rosser weights imply the
prefix square bound used in the partition argument. The first factor is
controlled by the sifting cutoff. Source: page 313 Remark 2. -/
theorem rosser_prefix_bound (l : List ℝ) (D : ℝ)
    (hone : ∀ x ∈ l, 1 ≤ x)
    (hdesc : ∀ i : ℕ, ∀ hi : i + 1 < l.length, l[i + 1] ≤ l[i])
    (hfirst : ∀ h : 0 < l.length, l[0] ^ 2 ≤ D)
    (hsupport : ∀ i : ℕ, ∀ hi : i < l.length, Odd i →
      (l.take i).prod * l[i] ^ 3 ≤ D) :
    ∀ i : ℕ, ∀ hi : i < l.length, (l.take i).prod * l[i] ^ 2 ≤ D := by
  intro i hi
  have hxi : 1 ≤ l[i] := hone _ (List.getElem_mem hi)
  have hpre : 0 ≤ (l.take i).prod := List.prod_nonneg (fun x hx =>
    (hone x (List.mem_of_mem_take hx)).trans' (by norm_num))
  by_cases hi0 : i = 0
  · subst i
    simpa using hfirst hi
  by_cases hodd : Odd i
  · apply le_trans _ (hsupport i hi hodd)
    have hp : l[i] ^ 2 ≤ l[i] ^ 3 := by nlinarith [sq_nonneg (l[i])]
    exact mul_le_mul_of_nonneg_left hp hpre
  · have hj : i - 1 < l.length := by omega
    have hjOdd : Odd (i - 1) := by
      rw [Nat.odd_iff] at hodd ⊢
      omega
    have hbound := hsupport (i - 1) hj hjOdd
    have hjpre : 0 ≤ (l.take (i - 1)).prod := List.prod_nonneg (fun x hx =>
      (hone x (List.mem_of_mem_take hx)).trans' (by norm_num))
    have hxj : 1 ≤ l[i - 1] := hone _ (List.getElem_mem hj)
    have hdec : l[i] ≤ l[i - 1] := by
      have h := hdesc (i - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
    have hp : l[i - 1] * l[i] ^ 2 ≤ l[i - 1] ^ 3 := by
      have hsq : l[i] ^ 2 ≤ l[i - 1] ^ 2 := by nlinarith
      nlinarith
    have he : (l.take i).prod = (l.take (i - 1)).prod * l[i - 1] := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        List.prod_take_succ l (i - 1) hj
    rw [he, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hp hjpre).trans hbound

/-- The lower Rosser support tests give the bounded factor partition.
This proves the elementary placement part of page 313 equation 14.
It does not assert the analytic estimate of the sieve main term. -/
theorem rosser_factor_partition (l : List ℝ) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hone : ∀ x ∈ l, 1 ≤ x)
    (hdesc : ∀ i : ℕ, ∀ hi : i + 1 < l.length, l[i + 1] ≤ l[i])
    (hfirst : ∀ h : 0 < l.length, l[0] ^ 2 ≤ M * N)
    (hsupport : ∀ i : ℕ, ∀ hi : i < l.length, Odd i →
      (l.take i).prod * l[i] ^ 3 ≤ M * N) :
    ∃ a b : List ℝ, l.Perm (a ++ b) ∧ a.prod ≤ M ∧ b.prod ≤ N := by
  exact factor_partition l M N hM hN
    (rosser_prefix_bound l (M * N) hone hdesc hfirst hsupport)

/-- Natural factors retain natural products in the same placement argument. -/
theorem nat_factor_partition (l : List ℕ) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hp : ∀ i : ℕ, ∀ hi : i < l.length,
      ((l.take i).prod : ℝ) * (l[i] : ℝ) ^ 2 ≤ M * N) :
    ∃ a b : List ℕ, l.Perm (a ++ b) ∧ (a.prod : ℝ) ≤ M ∧ (b.prod : ℝ) ≤ N := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], [], by simp, by simpa using hM, by simpa using hN⟩
  | @append_singleton l x ih =>
    have hpre : ∀ i : ℕ, ∀ hi : i < l.length,
        ((l.take i).prod : ℝ) * (l[i] : ℝ) ^ 2 ≤ M * N := by
      intro i hi
      have h := hp i (by simp; omega)
      simpa [List.take_append, List.getElem_append_left hi,
        Nat.sub_eq_zero_of_le hi.le] using h
    obtain ⟨a, b, hab, ha, hb⟩ := ih hpre
    have hlast := hp l.length (by simp)
    simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
      List.append_nil, List.getElem_append_right (by omega : l.length ≤ l.length),
      Nat.sub_self, List.getElem_cons_zero] at hlast
    have heq : (l.prod : ℝ) = a.prod * b.prod := by
      rw [hab.prod_eq, List.prod_append, Nat.cast_mul]
    rw [heq] at hlast
    rcases factor_placement (by linarith : 0 < M) (by linarith : 0 < N) hlast with hx | hx
    · refine ⟨a ++ [x], b, ?_, by simpa using hx, hb⟩
      exact (hab.append_right [x]).trans (by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := b) (l₂ := [x])).append_left a)
    · refine ⟨a, b ++ [x], ?_, ha, by simpa using hx⟩
      simpa only [List.append_assoc] using hab.append_right [x]

/-- A nonempty prime factor list satisfies every lower support hypothesis. -/
theorem rosser_partition_instance :
    ∃ a b : List ℝ, ([5, 3, 2] : List ℝ).Perm (a ++ b) ∧ a.prod ≤ 10 ∧ b.prod ≤ 15 := by
  apply rosser_factor_partition _ _ _ (by norm_num) (by norm_num)
  · norm_num
  · intro i hi
    have hi2 : i < 2 := by
      have h : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i <;> norm_num
  · norm_num
  · intro i hi hodd
    have hi3 : i < 3 := by simpa using hi
    have hi1 : i = 1 := by rw [Nat.odd_iff] at hodd; omega
    subst i
    norm_num

end LeanLab.ChenDoubleSieve.Task392

import LeanLab.OpenProblems.Erdos273

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

def divisorPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (Nat.sqrt n + 1)).filterMap fun d =>
    if n % d = 0 then some (d, n / d) else none

def divisorList (n : ℕ) : List ℕ :=
  (divisorPairs n).flatMap fun p => [p.1, p.2]

def directPool (L : ℕ) : Finset ℕ :=
  (divisorList L).toFinset.filter fun d => 4 ≤ d ∧ (d + 1).Prime

def directBudget (L : ℕ) : ℕ :=
  ∑ d ∈ directPool L, L / d

theorem divisor_mem_divisorList {n d : ℕ} (hn : 0 < n) (hdpos : 0 < d) (hd : d ∣ n) :
    d ∈ divisorList n := by
  have hmod : n % d = 0 := (Nat.dvd_iff_mod_eq_zero).mp hd
  by_cases hsmall : d ≤ Nat.sqrt n
  · have hrange : d ∈ List.range (Nat.sqrt n + 1) :=
      List.mem_range.mpr (by omega)
    have hpair : (d, n / d) ∈ divisorPairs n := by
      apply List.mem_filterMap.mpr
      refine ⟨d, hrange, ?_⟩
      simp [hmod]
    apply List.mem_flatMap_of_mem hpair
    simp
  · have hsqrt : Nat.sqrt n < d := Nat.lt_of_not_ge hsmall
    have hd2 : n < d * d := by
      have h1 := Nat.lt_succ_sqrt n
      have h2 : Nat.sqrt n + 1 ≤ d := by omega
      nlinarith
    have hdle : d ≤ n := by
      obtain ⟨c, hc⟩ := hd
      by_cases hc0 : c = 0
      · subst c
        simp at hc
        omega
      · omega
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hqle : n / d ≤ d := by
      by_contra hnot
      have hdle : d ≤ n / d := by omega
      have hsq : d * d ≤ (n / d) * d := Nat.mul_le_mul_right d hdle
      have hqprod : (n / d) * d = n := Nat.div_mul_cancel hd
      have hle : d * d ≤ n := by simpa [hqprod] using hsq
      have : d ≤ Nat.sqrt n := (Nat.le_sqrt).2 hle
      omega
    have hqsqrt : n / d ≤ Nat.sqrt n := by
      apply (Nat.le_sqrt).2
      have hsq : (n / d) * (n / d) ≤ (n / d) * d := Nat.mul_le_mul_left (n / d) hqle
      simpa [Nat.div_mul_cancel hd] using hsq
    have hqmod : n % (n / d) = 0 := by
      rw [Nat.mod_eq_zero_of_dvd]
      exact ⟨d, (Nat.div_mul_cancel hd).symm⟩
    have hdiv : n / (n / d) = d := by
      apply Nat.div_eq_of_lt_le
      · have hprod : d * (n / d) = n := Nat.mul_div_cancel' hd
        exact hprod.le
      · have hprod : d * (n / d) = n := Nat.mul_div_cancel' hd
        nlinarith [Nat.succ_mul d]
    have hrange : n / d ∈ List.range (Nat.sqrt n + 1) :=
      List.mem_range.mpr (Nat.lt_succ_of_le hqsqrt)
    have hpair : (n / d, d) ∈ divisorPairs n := by
      apply List.mem_filterMap.mpr
      refine ⟨n / d, hrange, ?_⟩
      simp [hqmod, hdiv]
    apply List.mem_flatMap_of_mem hpair
    simp

-- theorem directBudget_check : ∀ L ∈ Finset.range 55440, 0 < L → directBudget L < L := by
--   native_decide

end LeanLab.OpenProblems.Novelty1615

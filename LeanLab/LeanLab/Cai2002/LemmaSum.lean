/-
P0044, Cai 2002, Lemma 5 summed over `A = {N - p : p ≤ N^θ}`, with the non-squarefree loss
made explicit. The paper writes the loss as `O(N^{10/11})`; here it is at most `N/(m-1)` for any
integer `2 ≤ m ≤ N^{1/11}`. Only the `a` coprime to `N` with no prime factor below `N^{1/11}`
are summed, the form (4.1) uses.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Lemma5

open Finset

namespace LeanLab.Cai2002

noncomputable section

/-- `z₁ = N^{1/11}` and `z₂ = N^{1/3.29}`. -/
def z1 (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 11 : ℝ)
def z2 (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 3.29 : ℝ)

/-- The Lemma 5 weight `1 - ρ₁/2 - ρ₂/2 - ρ₃` at the paper's cutoffs. -/
def wt (N a : ℕ) : ℝ :=
  1 - (rho1 (z1 N) (z2 N) a : ℝ) / 2 - (rho2 (z1 N) (z2 N) a : ℝ) / 2 - (rho3 (z2 N) a : ℝ)

/-- The primes `p < N`, `p ≤ N^θ`, with `a = N - p` coprime to `N` and free of primes
below `N^{1/11}`. -/
def Pset (N : ℕ) (θ : ℝ) : Finset ℕ := by
  classical exact (range N).filter (fun p => Nat.Prime p ∧ ((p : ℕ) : ℝ) ≤ (N : ℝ) ^ θ ∧
    Nat.Coprime (N - p) N ∧ ∀ q ∈ (N - p).primeFactors, z1 N ≤ (q : ℝ))

/-- The non-squarefree members. -/
def Pnsq (N : ℕ) (θ : ℝ) : Finset ℕ := by
  classical exact (Pset N θ).filter (fun p => ¬ Squarefree (N - p))

lemma mem_Pset {N : ℕ} {θ : ℝ} {p : ℕ} (h : p ∈ Pset N θ) :
    p < N ∧ Nat.Prime p ∧ ((p : ℕ) : ℝ) ≤ (N : ℝ) ^ θ ∧
      Nat.Coprime (N - p) N ∧ ∀ q ∈ (N - p).primeFactors, z1 N ≤ (q : ℝ) := by
  unfold Pset at h
  simp only [mem_filter, mem_range] at h
  exact ⟨h.1, h.2⟩

lemma wt_le_one (N a : ℕ) : wt N a ≤ 1 := by
  unfold wt
  have := (Nat.cast_nonneg (rho1 (z1 N) (z2 N) a) : (0 : ℝ) ≤ _)
  have := (Nat.cast_nonneg (rho2 (z1 N) (z2 N) a) : (0 : ℝ) ≤ _)
  have := (Nat.cast_nonneg (rho3 (z2 N) a) : (0 : ℝ) ≤ _)
  linarith

/-- Lemma 5 summed: `Σ_{p ∈ Pset} w(N-p) ≤ S(N, θ) + #{non-squarefree}`. -/
theorem lemma5_sum (N : ℕ) (θ : ℝ) (hN : 1 < N) :
    ∑ p ∈ Pset N θ, wt N (N - p) ≤ (S N θ : ℝ) + ((Pnsq N θ).card : ℝ) := by
  classical
  have hpt : ∀ p ∈ Pset N θ, wt N (N - p) ≤
      (lam (N - p) : ℝ) + (if ¬ Squarefree (N - p) then (1 : ℝ) else 0) := by
    intro p hp
    obtain ⟨hpN, _, _, _, hlow⟩ := mem_Pset hp
    by_cases hsq : Squarefree (N - p)
    · rw [if_neg (not_not.mpr hsq), add_zero]
      exact lemma5_cai N (N - p) hN (by omega) (by omega) hsq hlow
    · rw [if_pos hsq]
      have := wt_le_one N (N - p)
      have : (0 : ℝ) ≤ lam (N - p) := Nat.cast_nonneg _
      linarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  apply add_le_add
  · -- Σ λ ≤ S(N, θ)
    have h1 : ∑ p ∈ Pset N θ, (lam (N - p) : ℝ) =
        (((Pset N θ).filter (fun p => Nat.IsAtMostAlmostPrime 2 (N - p))).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      apply sum_congr rfl
      intro p _
      unfold lam
      split_ifs <;> simp
    rw [h1]
    unfold S
    exact_mod_cast card_le_card (by
      intro p hp
      simp only [mem_filter] at hp
      obtain ⟨hpN, hpp, hpθ, _, _⟩ := mem_Pset hp.1
      simp only [mem_filter, mem_range]
      exact ⟨hpN, hpp, hpθ, hp.2⟩)
  · unfold Pnsq
    rw [Finset.card_filter]
    push_cast
    apply le_of_eq
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp

/-- `Σ_{k < K} 1/(m+k)² ≤ 1/(m-1) - 1/(m+K-1)` for `m ≥ 2`. -/
lemma tail_sq (m : ℕ) (hm : 2 ≤ m) (K : ℕ) :
    ∑ k ∈ range K, 1 / ((m + k : ℕ) : ℝ) ^ 2 ≤
      1 / ((m : ℝ) - 1) - 1 / ((m : ℝ) + K - 1) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have hA : (0 : ℝ) < (m : ℝ) + K - 1 := by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith
    have hB : (0 : ℝ) < (m : ℝ) + K := by linarith
    have step : 1 / (((m + K : ℕ) : ℝ)) ^ 2 ≤ 1 / ((m : ℝ) + K - 1) - 1 / ((m : ℝ) + (K + 1 : ℕ) - 1) := by
      push_cast
      rw [show (m : ℝ) + (K + 1) - 1 = m + K by ring]
      rw [div_sub_div _ _ hA.ne' hB.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- The non-squarefree loss: for any integer `2 ≤ m ≤ N^{1/11}`, `#{non-squarefree} ≤ N/(m-1)`. -/
theorem Pnsq_card_le (N : ℕ) (θ : ℝ) (m : ℕ) (hm : 2 ≤ m) (hmz : (m : ℝ) ≤ z1 N) :
    ((Pnsq N θ).card : ℝ) ≤ (N : ℝ) / ((m : ℝ) - 1) := by
  classical
  set T := (Ico m (N + 1)).biUnion (fun q => (Ioc 0 N).filter (fun a => q * q ∣ a)) with hT
  have hcard : (Pnsq N θ).card ≤ T.card := by
    apply card_le_card_of_injOn (fun p => N - p)
    · intro p hp
      have hp' : p ∈ Pnsq N θ := hp
      unfold Pnsq at hp'
      simp only [mem_filter] at hp'
      obtain ⟨hpN, _, _, _, hlow⟩ := mem_Pset hp'.1
      have hns := hp'.2
      rw [Nat.squarefree_iff_prime_squarefree] at hns
      push Not at hns
      obtain ⟨q, hq, hqq⟩ := hns
      have ha0 : N - p ≠ 0 := by omega
      have hqmem : q ∈ (N - p).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, (Dvd.intro _ rfl).trans hqq, ha0⟩
      have hzq := hlow q hqmem
      have hmq : m ≤ q := by exact_mod_cast hmz.trans hzq
      have hqle : q * q ≤ N - p := Nat.le_of_dvd (by omega) hqq
      have hq1 : 1 ≤ q := hq.one_lt.le
      have hqN : q ≤ N := (Nat.le_mul_self q).trans (hqle.trans (Nat.sub_le N p))
      simp only [hT, coe_biUnion, coe_filter, Set.mem_iUnion, Set.mem_setOf_eq, mem_coe,
        mem_Ico, mem_Ioc]
      exact ⟨q, ⟨hmq, by omega⟩, ⟨by omega, by omega⟩, hqq⟩
    · intro p hp p' hp' h
      have h1 : p ∈ Pnsq N θ := hp
      have h2 : p' ∈ Pnsq N θ := hp'
      unfold Pnsq at h1 h2
      simp only [mem_filter] at h1 h2
      have := (mem_Pset h1.1).1
      have := (mem_Pset h2.1).1
      simp only at h
      omega
  have hT : (T.card : ℝ) ≤ ∑ q ∈ Ico m (N + 1), ((N / (q * q) : ℕ) : ℝ) := by
    have := card_biUnion_le (s := Ico m (N + 1)) (t := fun q => (Ioc 0 N).filter (fun a => q * q ∣ a))
    simp only [Nat.Ioc_filter_dvd_card_eq_div] at this
    exact_mod_cast this
  have hdiv : ∀ q ∈ Ico m (N + 1), ((N / (q * q) : ℕ) : ℝ) ≤ (N : ℝ) * (1 / ((q : ℕ) : ℝ) ^ 2) := by
    intro q _
    rw [mul_one_div, sq]
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := q * q)
    push_cast at this
    exact this
  have hsum : ∑ q ∈ Ico m (N + 1), (N : ℝ) * (1 / ((q : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) / ((m : ℝ) - 1) := by
    rw [← mul_sum, sum_Ico_eq_sum_range]
    have ht := tail_sq m hm (N + 1 - m)
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hpos : 0 ≤ 1 / ((m : ℝ) + ((N + 1 - m : ℕ) : ℝ) - 1) := by
      apply div_nonneg zero_le_one
      have : (0 : ℝ) ≤ ((N + 1 - m : ℕ) : ℝ) := Nat.cast_nonneg _
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    linarith
  calc ((Pnsq N θ).card : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ ≤ _ := hT
    _ ≤ _ := sum_le_sum hdiv
    _ ≤ _ := hsum

/-- Lemma 5 of Cai 2002 with the loss explicit: for `N ≥ 2¹¹ = 2048` and `m = ⌊N^{1/11}⌋`,
`S(N, θ) ≥ Σ_{p ∈ Pset} (1 - ρ₁/2 - ρ₂/2 - ρ₃)(N - p) - N/(m - 1)`. -/
theorem lemma5_explicit (N : ℕ) (θ : ℝ) (hN : 2048 ≤ N) :
    ∑ p ∈ Pset N θ, wt N (N - p) - (N : ℝ) / ((⌊z1 N⌋₊ : ℝ) - 1) ≤ (S N θ : ℝ) := by
  have hN1 : 1 < N := by omega
  have hz : (2 : ℝ) ≤ z1 N := by
    unfold z1
    have h2 : (2 : ℝ) = ((2 : ℝ) ^ (11 : ℝ)) ^ (1 / 11 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : (2048 : ℝ) ≤ N := by exact_mod_cast hN
    have h11 : (2 : ℝ) ^ (11 : ℝ) = 2048 := by norm_num
    linarith
  have hm : 2 ≤ ⌊z1 N⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hmz : ((⌊z1 N⌋₊ : ℕ) : ℝ) ≤ z1 N := Nat.floor_le (by linarith)
  have h1 := lemma5_sum N θ hN1
  have h2 := Pnsq_card_le N θ _ hm hmz
  linarith

end

end LeanLab.Cai2002

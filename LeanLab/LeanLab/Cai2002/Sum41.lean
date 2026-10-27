/-
P0044, Cai 2002, the bookkeeping behind (4.1), page 601.
Lemma 5 gives `S(N, θ) ≥ Σ_a (1 - ρ₁/2 - ρ₂/2 - ρ₃)(a) - loss` over the sifted set
`a ∈ A, (a, N) = 1, (a, P(N^{1/11})) = 1`. The paper then writes this as
`S - S₁/2 - S₂/2 - S₃` with `S₁ = Σ_{N^{1/11} ≤ q < N^{1/3.29}, (q, N) = 1} S(A_q, P, N^{1/11})`.
VERIFY U-5174 noted that the step `Σ ρ₁ ↦ S₁` was not formalized. Here it is: the sum of `ρ₁`
over the sifted set is at most `S₁`, equality failing only because `S(A_q, P, z₁)` does not
ask `(a, N) = 1`, which only makes `S₁` larger, the safe direction for a lower bound.
AI-written Lean code, Claude, run 20261019T0605Z-16900, unit U-1037. Checked only by the Lean
kernel. Binary Goldbach is OPEN. Nothing here proves it.
-/
import Mathlib
import LeanLab.Cai2002.LemmaSum

open Finset

namespace LeanLab.Cai2002

noncomputable section

/-- The primes `q` that `S₁` sums over: `N^{1/11} ≤ q < N^{1/3.29}`, `(q, N) = 1`. Any such `q`
dividing some `a ≤ N` is at most `N`, so `range (N + 1)` loses nothing. -/
def Q1 (N : ℕ) : Finset ℕ := by
  classical exact (range (N + 1)).filter (fun q => q.Prime ∧ z1 N ≤ (q : ℝ) ∧ (q : ℝ) < z2 N ∧
    Nat.Coprime q N)

/-- `S(A_q, P, N^{1/11})`, page 601: the `a = N - p ∈ A`, `p ≤ N^θ`, with `q ∣ a` and no prime
factor `r < N^{1/11}` of `a` in `P = {r : (r, N) = 1}`. Indexed by `p`. -/
def Asift (N : ℕ) (θ : ℝ) (q : ℕ) : Finset ℕ := by
  classical exact (range N).filter (fun p => Nat.Prime p ∧ ((p : ℕ) : ℝ) ≤ (N : ℝ) ^ θ ∧
    q ∣ N - p ∧ ∀ r ∈ (N - p).primeFactors, (r : ℝ) < z1 N → ¬ Nat.Coprime r N)

/-- `S`, page 601: the size of the sifted set `a ∈ A, (a, N) = 1, (a, P(N^{1/11})) = 1`. -/
def Ssift (N : ℕ) (θ : ℝ) : ℕ := (Pset N θ).card

/-- `S₁`, page 601. -/
def S1 (N : ℕ) (θ : ℝ) : ℕ := ∑ q ∈ Q1 N, (Asift N θ q).card

/-- `S₂ = Σ ρ₂(a)` over the sifted set, page 601. -/
def S2 (N : ℕ) (θ : ℝ) : ℕ := ∑ p ∈ Pset N θ, rho2 (z1 N) (z2 N) (N - p)

/-- `S₃ = Σ ρ₃(a)` over the sifted set, page 601. -/
def S3 (N : ℕ) (θ : ℝ) : ℕ := ∑ p ∈ Pset N θ, rho3 (z2 N) (N - p)

/-- On the sifted set, `ρ₁(a)` counts the `q ∈ Q1` dividing `a`. -/
lemma rho1_eq_card {N : ℕ} {θ : ℝ} {p : ℕ} (hp : p ∈ Pset N θ) :
    rho1 (z1 N) (z2 N) (N - p) = ((Q1 N).filter (fun q => q ∣ N - p)).card := by
  classical
  obtain ⟨hpN, _, _, hcop, _⟩ := mem_Pset hp
  have ha0 : N - p ≠ 0 := by omega
  unfold rho1
  congr 1
  ext q
  simp only [Q1, mem_filter, mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hq, hqa, -⟩, h1, h2⟩
    have hqle : q ≤ N - p := Nat.le_of_dvd (by omega) hqa
    exact ⟨⟨by omega, hq, h1, h2, Nat.Coprime.coprime_dvd_left hqa hcop⟩, hqa⟩
  · rintro ⟨⟨-, hq, h1, h2, -⟩, hqa⟩
    exact ⟨⟨hq, hqa, ha0⟩, h1, h2⟩

/-- Double counting: `Σ_{a sifted} ρ₁(a) = Σ_{q ∈ Q1} #{a sifted : q ∣ a}`. -/
lemma sum_rho1_eq (N : ℕ) (θ : ℝ) :
    ∑ p ∈ Pset N θ, rho1 (z1 N) (z2 N) (N - p) =
      ∑ q ∈ Q1 N, ((Pset N θ).filter (fun p => q ∣ N - p)).card := by
  classical
  rw [sum_congr rfl (fun p hp => rho1_eq_card hp)]
  simp only [card_filter]
  exact sum_comm

/-- Each sifted `a` with `q ∣ a` is counted in `S(A_q, P, N^{1/11})`. -/
lemma filter_subset_Asift (N : ℕ) (θ : ℝ) (q : ℕ) :
    (Pset N θ).filter (fun p => q ∣ N - p) ⊆ Asift N θ q := by
  classical
  intro p hp
  rw [mem_filter] at hp
  obtain ⟨hpN, hpp, hpθ, _, hlow⟩ := mem_Pset hp.1
  simp only [Asift, mem_filter, mem_range]
  refine ⟨hpN, hpp, hpθ, hp.2, fun r hr hrz => ?_⟩
  exact absurd (hlow r hr) (not_le.mpr hrz)

/-- `Σ_{a sifted} ρ₁(a) ≤ S₁`. -/
theorem sum_rho1_le_S1 (N : ℕ) (θ : ℝ) :
    ∑ p ∈ Pset N θ, rho1 (z1 N) (z2 N) (N - p) ≤ S1 N θ := by
  rw [sum_rho1_eq, S1]
  exact sum_le_sum fun q _ => card_le_card (filter_subset_Asift N θ q)

/-- The summed weight is `S - Σρ₁/2 - S₂/2 - S₃`. -/
lemma sum_wt_eq (N : ℕ) (θ : ℝ) :
    ∑ p ∈ Pset N θ, wt N (N - p) =
      (Ssift N θ : ℝ) - (∑ p ∈ Pset N θ, rho1 (z1 N) (z2 N) (N - p) : ℕ) / 2 -
        (S2 N θ : ℝ) / 2 - (S3 N θ : ℝ) := by
  unfold wt Ssift S2 S3
  push_cast
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← sum_div, ← sum_div]
  simp

/-- (4.1) of Cai 2002 with the loss explicit: for `N ≥ 2048` and `m = ⌊N^{1/11}⌋`,
`S(N, θ) ≥ S - S₁/2 - S₂/2 - S₃ - N/(m - 1)`. The paper writes the loss as `O(N^{10/11})`. -/
theorem eq41 (N : ℕ) (θ : ℝ) (hN : 2048 ≤ N) :
    (Ssift N θ : ℝ) - (S1 N θ : ℝ) / 2 - (S2 N θ : ℝ) / 2 - (S3 N θ : ℝ) -
      (N : ℝ) / ((⌊z1 N⌋₊ : ℝ) - 1) ≤ (S N θ : ℝ) := by
  have h := lemma5_explicit N θ hN
  rw [sum_wt_eq] at h
  have h1 : ((∑ p ∈ Pset N θ, rho1 (z1 N) (z2 N) (N - p) : ℕ) : ℝ) ≤ (S1 N θ : ℝ) := by
    exact_mod_cast sum_rho1_le_S1 N θ
  linarith

/-- The loss is `O(N^{10/11})` in the paper's sense: `N/(⌊N^{1/11}⌋ - 1) ≤ 3 N^{10/11}`
once `N^{1/11} ≥ 3`, so (4.1) holds as printed. -/
lemma loss_le (N : ℕ) (hz : 3 ≤ z1 N) :
    (N : ℝ) / ((⌊z1 N⌋₊ : ℝ) - 1) ≤ 3 * (N : ℝ) ^ (10 / 11 : ℝ) := by
  have hz0 : 0 ≤ z1 N := by linarith
  have hfl : z1 N - 1 < (⌊z1 N⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hden : z1 N / 3 ≤ (⌊z1 N⌋₊ : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
    have : z1 N = 0 := by
      unfold z1; rw [this, Real.zero_rpow (by norm_num)]
    linarith
  have hsplit : (N : ℝ) = (N : ℝ) ^ (10 / 11 : ℝ) * z1 N := by
    unfold z1; rw [← Real.rpow_add hN0]; norm_num
  have hpos : 0 < z1 N / 3 := by linarith
  calc (N : ℝ) / ((⌊z1 N⌋₊ : ℝ) - 1) ≤ (N : ℝ) / (z1 N / 3) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) hpos hden
    _ = 3 * (N : ℝ) ^ (10 / 11 : ℝ) := by
        conv_lhs => rw [hsplit]
        field_simp

/-- (4.1) in the printed `O(N^{10/11})` form, constant 3, for `N ≥ 3¹¹ = 177147`. -/
theorem eq41_printed (N : ℕ) (θ : ℝ) (hN : 177147 ≤ N) :
    (Ssift N θ : ℝ) - (S1 N θ : ℝ) / 2 - (S2 N θ : ℝ) / 2 - (S3 N θ : ℝ) -
      3 * (N : ℝ) ^ (10 / 11 : ℝ) ≤ (S N θ : ℝ) := by
  have hz : 3 ≤ z1 N := by
    unfold z1
    have h3 : (3 : ℝ) = ((3 : ℝ) ^ (11 : ℝ)) ^ (1 / 11 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h3]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : (177147 : ℝ) ≤ N := by exact_mod_cast hN
    have h11 : (3 : ℝ) ^ (11 : ℝ) = 177147 := by norm_num
    linarith
  have h := eq41 N θ (by omega)
  have := loss_le N hz
  linarith

end

end LeanLab.Cai2002

-- Repo encoding of P0070 from cloud runs, copied under namespace B by PC run 20261020T0603Z-352, unit U-1182, unchanged otherwise.
/-
P0070 Perelli-Pintz 1992: the Corollary from the Theorem by counting, page 356, and a check of
the printed identity `Ψ(N, 2k) = Ψ₂(2N, 2k) - Ψ₂(N + 2k, 2k)` on page 356.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach and the twin prime conjecture are OPEN.
-/
import Mathlib
import LeanLab.PerelliPintz1992.B.Statements

namespace LeanLab.PerelliPintz1992.B
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- **The Corollary from the Theorem**, zero sorry as an implication: apply (3) with
`A' = 2A + B`; each exception has `Δ² > N² L^{-2A}`, so their number is at most
`K H N² L^{-2A-B} / (N² L^{-2A}) = K H L^{-B}`. Here `C₁ = 1`. -/
theorem corollary_of (h : Theorem) : Corollary := by
  intro ε hε hε2 A B hA hB
  obtain ⟨K, N₀, hK⟩ := h ε hε hε2 (2 * A + B) (by linarith)
  refine ⟨1, max K 0, max N₀ 3, fun N hN H V h1 h2 h3 h4 => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  set ex := (Ks V H).filter (fun k => 1 * (N : ℝ) * L ^ (-A) < |Delta N k|) with hex
  have hsum := hK N hN0 H V h1 h2 h3 h4
  have ht : (N : ℝ) ^ 2 * L ^ (-(2 * A)) > 0 := by positivity
  -- each exception contributes more than `N² L^{-2A}`
  have hsq : ∀ k ∈ ex, (N : ℝ) ^ 2 * L ^ (-(2 * A)) ≤ Delta N k ^ 2 := by
    intro k hk
    rw [hex, Finset.mem_filter] at hk
    have h0 : 0 ≤ (N : ℝ) * L ^ (-A) := by positivity
    have := hk.2
    rw [one_mul] at this
    have hlt : ((N : ℝ) * L ^ (-A)) ^ 2 ≤ |Delta N k| ^ 2 := by
      exact pow_le_pow_left₀ h0 this.le 2
    rw [sq_abs] at hlt
    calc (N : ℝ) ^ 2 * L ^ (-(2 * A)) = ((N : ℝ) * L ^ (-A)) ^ 2 := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ (-A)), ← Real.rpow_mul hL.le]
          push_cast; ring_nf
      _ ≤ Delta N k ^ 2 := hlt
  have hcount : (ex.card : ℝ) * ((N : ℝ) ^ 2 * L ^ (-(2 * A))) ≤
      ∑ k ∈ Ks V H, Delta N k ^ 2 := by
    calc (ex.card : ℝ) * ((N : ℝ) ^ 2 * L ^ (-(2 * A)))
        = ∑ _k ∈ ex, (N : ℝ) ^ 2 * L ^ (-(2 * A)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ ex, Delta N k ^ 2 := Finset.sum_le_sum hsq
      _ ≤ ∑ k ∈ Ks V H, Delta N k ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)
  have hsplit : L ^ (-(2 * A + B)) = L ^ (-(2 * A)) * L ^ (-B) := by
    rw [← Real.rpow_add hL]; ring_nf
  have hH : 0 < H := lt_trans (by positivity) h1
  have hmain : (ex.card : ℝ) * ((N : ℝ) ^ 2 * L ^ (-(2 * A))) ≤
      (max K 0 * H * L ^ (-B)) * ((N : ℝ) ^ 2 * L ^ (-(2 * A))) := by
    calc _ ≤ K * H * (N : ℝ) ^ 2 * L ^ (-(2 * A + B)) := le_trans hcount hsum
      _ ≤ max K 0 * H * (N : ℝ) ^ 2 * L ^ (-(2 * A + B)) := by
          gcongr; exact le_max_left _ _
      _ = (max K 0 * H * L ^ (-B)) * ((N : ℝ) ^ 2 * L ^ (-(2 * A))) := by
          rw [hsplit]; ring
  exact le_of_mul_le_mul_right hmain ht

/-- The difference between the two sides of the printed identity on page 356 is exactly the one
term `m = N`: `Ψ(N, 2k) = Ψ₂(2N, 2k) - Ψ₂(N + 2k, 2k) + Λ(N) Λ(N + 2k)` for `k ≥ 1`, `2k ≤ N`.
The printed identity drops the last term. It is a slip without effect on the results. -/
theorem psi_eq_psi2 (N k : ℕ) (hk : 1 ≤ k) (h2k : 2 * k ≤ N) :
    Psi N k = Psi2 (2 * N) k - Psi2 (N + 2 * k) k + Λ N * Λ (N + 2 * k) := by
  -- both sides are sums over `n = m + 2k` with `N ≤ m ≤ 2N - 2k`
  have hL : Psi N k = ∑ m ∈ Icc N (2 * N - 2 * k), Λ m * Λ (m + 2 * k) := by
    unfold Psi
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hR : Psi2 (2 * N) k - Psi2 (N + 2 * k) k =
      ∑ m ∈ Ioc N (2 * N - 2 * k), Λ m * Λ (m + 2 * k) := by
    unfold Psi2
    have hsplit : Ioc (2 * k) (2 * N) = Ioc (2 * k) (N + 2 * k) ∪ Ioc (N + 2 * k) (2 * N) :=
      (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
    rw [hsplit, Finset.sum_union (Finset.disjoint_left.2 (fun a ha hb => by
      simp only [Finset.mem_Ioc] at ha hb; omega)), add_sub_cancel_left]
    apply Finset.sum_nbij' (fun n => n - 2 * k) (fun m => m + 2 * k)
    · intro n hn; simp only [Finset.mem_coe, Finset.mem_Ioc] at hn ⊢; omega
    · intro m hm; simp only [Finset.mem_coe, Finset.mem_Ioc] at hm ⊢; omega
    · intro n hn; simp only [Finset.mem_coe, Finset.mem_Ioc] at hn; omega
    · intro m _; simp
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      rw [mul_comm, Nat.sub_add_cancel (by omega)]
  rw [hL, hR]
  have hI : Icc N (2 * N - 2 * k) = insert N (Ioc N (2 * N - 2 * k)) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hI, Finset.sum_insert (by simp), add_comm]

/-- So the printed identity fails whenever `N` and `N + 2k` are both prime powers: at `N = 3`,
`k = 1`, `Ψ(3, 2) = Λ(3)Λ(5) + Λ(4)Λ(6) = log 3 log 5`, while `Ψ₂(6, 2) - Ψ₂(5, 2) = Λ(6)Λ(4) = 0`. -/
theorem printed_identity_fails : Psi 3 1 ≠ Psi2 (2 * 3) 1 - Psi2 (3 + 2 * 1) 1 := by
  rw [psi_eq_psi2 3 1 le_rfl (by norm_num)]
  have h3 : Λ 3 = Real.log 3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have h5 : Λ 5 = Real.log 5 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  have hpos : 0 < Λ 3 * Λ (3 + 2 * 1) := by
    rw [show 3 + 2 * 1 = 5 by norm_num, h3, h5]
    exact mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  intro h; linarith

end LeanLab.PerelliPintz1992.B


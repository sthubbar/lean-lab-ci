import LeanLab.PNTPort.BVMax.TauGoldbach
import LeanLab.PNTSieve.BrunTitchmarshAP

/-!
# The divisor analogue of binary Goldbach, the upper bound

Lab proof, unit U-5307, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

* `card_divisors_le`: `τ(n) ≤ 2 #{d ∣ n : d² ≤ n}`;
* `tauSum_le_count`: `Σ_{p<N} τ(N - p) ≤ 2 Σ_{d ≤ √N} #{p < N : d ∣ N - p}`;
* `tauSum_le`: `Σ_{p<N} τ(N - p) ≤ C N` for all large `N`, from `brunTitchmarsh_ap` with
  `z = N^{1/6}` for every `d ≤ √N`; no Bombieri-Vinogradov needed for the upper bound.
With `tauSum_ge_totient` this pins the sum between `φ(N)/16` and `C N`, and `N/φ(N) ≪ log log N`.
-/

namespace LeanLab.PNTPort.BVMax

open Finset Real Filter

/-- `τ(n) ≤ 2 #{d ∣ n : d² ≤ n}`. -/
lemma card_divisors_le (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ 2 * (n.divisors.filter (fun d => d * d ≤ n)).card := by
  have hsplit := card_filter_add_card_filter_not (s := n.divisors) (fun d => d * d ≤ n)
  have hinj : (n.divisors.filter (fun d => ¬ d * d ≤ n)).card ≤
      (n.divisors.filter (fun d => d * d ≤ n)).card := by
    apply card_le_card_of_injOn (fun d => n / d)
    · intro d hd
      simp only [coe_filter, Set.mem_setOf_eq, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hn⟩, ?_⟩
      have hlt : n / d < d := (Nat.div_lt_iff_lt_mul (Nat.pos_of_dvd_of_pos hd.1.1
        (Nat.pos_of_ne_zero hn) |> fun h => by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · subst h0; simp at hd
          · exact h0)).mpr (by push Not at hd; linarith [hd.2])
      calc n / d * (n / d) ≤ n / d * d := Nat.mul_le_mul_left _ hlt.le
        _ ≤ n := Nat.div_mul_le_self n d
    · intro d1 h1 d2 h2 he
      simp only [coe_filter, Set.mem_setOf_eq, Nat.mem_divisors] at h1 h2
      simp only at he
      rw [← Nat.div_div_self h1.1.1 hn, he, Nat.div_div_self h2.1.1 hn]
  omega

/-- `Σ_{p<N} τ(N - p) ≤ 2 Σ_{d ≤ √N} #{p < N prime : d ∣ N - p}`. -/
lemma tauSum_le_count (N : ℕ) :
    tauSum N ≤ 2 * ∑ d ∈ Icc 1 (Nat.sqrt N),
      ((((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card : ℝ) := by
  unfold tauSum
  have key : ∑ p ∈ (range N).filter Nat.Prime, (N - p).divisors.card ≤
      2 * ∑ d ∈ Icc 1 (Nat.sqrt N), (((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card := by
    rw [show ∑ d ∈ Icc 1 (Nat.sqrt N), (((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card
        = ∑ p ∈ (range N).filter Nat.Prime, ((Icc 1 (Nat.sqrt N)).filter (fun d => d ∣ N - p)).card
        from sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun d p => d ∣ N - p), mul_sum]
    apply sum_le_sum
    intro p hp
    simp only [mem_filter, mem_range] at hp
    have hn : N - p ≠ 0 := by omega
    refine (card_divisors_le (N - p) hn).trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
    intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨Nat.pos_of_dvd_of_pos hd.1.1 (by omega), ?_⟩, hd.1.1⟩
    rw [Nat.le_sqrt]
    exact hd.2.trans (Nat.sub_le N p)
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this
  exact this

/-- `Σ_{p<N} τ(N - p) ≤ C N` for all large `N`. -/
theorem tauSum_le : ∃ C : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → tauSum N ≤ C * N := by
  obtain ⟨C, hC, hCsum⟩ := BV.sum_inv_totient_le
  have hev : ∀ᶠ x in atTop, 32 * Real.log x ^ (3 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0 : ℝ) < 1 / 3 by norm_num)).bound
      (show (0 : ℝ) < 1 / 32 by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) ((1 : ℝ) / 3))] at hx
    have := le_abs_self (Real.log x ^ (3 : ℝ))
    linarith
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    (hev.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  refine ⟨2 * (24 * C + 1), max ⌈X0⌉₊ 3, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_right hN
  have hNX : X0 ≤ N := (Nat.le_ceil X0).trans (by exact_mod_cast le_of_max_le_left hN)
  obtain ⟨hpow, hL1⟩ := hX0 N hNX
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL0 : 0 < L := by linarith
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 6) with hz
  have hz1 : 1 < z := Real.one_lt_rpow (by linarith) (by norm_num)
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z = L / 6 := by
    rw [hz, Real.log_rpow hN0]; ring
  -- each d by Brun-Titchmarsh on [1, N - 1]
  have hd : ∀ d ∈ Icc 1 (Nat.sqrt N),
      ((((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card : ℝ) ≤
        12 * N / (d.totient * L) + 4 * z * (1 + L) ^ 3 := by
    intro d hd
    rw [mem_Icc] at hd
    have hbt := LeanLab.PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap 1 ((N : ℝ) - 2) z d N
      one_pos (by linarith) hz1 (by omega)
    have hA : ⌈(1 : ℝ)⌉₊ = 1 := Nat.ceil_one
    have hB : ⌊(1 : ℝ) + ((N : ℝ) - 2)⌋₊ = N - 1 := by
      rw [show (1 : ℝ) + ((N : ℝ) - 2) = ((N - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega)]; push_cast; ring]
      exact Nat.floor_natCast _
    rw [hA, hB] at hbt
    have hsub : ((range N).filter Nat.Prime).filter (fun p => d ∣ N - p) ⊆
        (Icc 1 (N - 1)).filter (fun p => p.Prime ∧ p % d = N % d) := by
      intro p hp
      simp only [mem_filter, mem_range, mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.2.one_lt.le, by omega⟩, hp.1.2, (Nat.modEq_iff_dvd' (by omega)).mpr hp.2⟩
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have h1 : ((((range N).filter Nat.Prime).filter (fun p => d ∣ N - p)).card : ℝ) ≤
        (((Icc 1 (N - 1)).filter (fun p => p.Prime ∧ p % d = N % d)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    refine h1.trans (hbt.trans ?_)
    rw [hlz]
    apply add_le_add
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 * ((N : ℝ) - 2)) * (d.totient * L) ≤ 2 * N * (d.totient * L) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [mul_pos hφ hL0]
    · have : (1 + L / 6) ^ 3 ≤ (1 + L) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity) (by linarith)
      nlinarith [this, hz0]
  -- sum over d ≤ √N
  have hsq : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hsqN : ((Nat.sqrt N : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sqrt_le_self N
  have hsum := sum_le_sum hd
  rw [sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum
  have hmain : ∑ d ∈ Icc 1 (Nat.sqrt N), 12 * (N : ℝ) / (d.totient * L) ≤ 24 * C * N := by
    have e : ∑ d ∈ Icc 1 (Nat.sqrt N), 12 * (N : ℝ) / (d.totient * L) =
        12 * N / L * ∑ d ∈ Icc 1 (Nat.sqrt N), (1 : ℝ) / d.totient := by
      rw [mul_sum]; refine sum_congr rfl (fun d _ => ?_); field_simp
    rw [e]
    have hc := hCsum (Nat.sqrt N)
    have hlog : Real.log (Nat.sqrt N) ≤ L := by
      rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | hpos
      · rw [h0]; simp; linarith
      · exact Real.log_le_log (by exact_mod_cast hpos) hsqN
    calc 12 * (N : ℝ) / L * ∑ d ∈ Icc 1 (Nat.sqrt N), (1 : ℝ) / d.totient
        ≤ 12 * N / L * (C * (1 + L)) :=
          mul_le_mul_of_nonneg_left (hc.trans (by nlinarith)) (by positivity)
      _ ≤ 12 * N / L * (C * (2 * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hC.le) (by positivity)
      _ = 24 * C * N := by field_simp; ring
  have herr : ((Nat.sqrt N : ℕ) : ℝ) * (4 * z * (1 + L) ^ 3) ≤ N := by
    have h1 : (1 + L) ^ 3 ≤ 8 * L ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have : 1 + L ≤ 2 * L := by linarith
      calc (1 + L) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 8 * L ^ 3 := by ring
    have h2 : Real.sqrt N * z * (N : ℝ) ^ ((1 : ℝ) / 3) = N := by
      rw [Real.sqrt_eq_rpow, hz, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      norm_num
    have hz' : 0 ≤ Real.sqrt N * z := by positivity
    calc ((Nat.sqrt N : ℕ) : ℝ) * (4 * z * (1 + L) ^ 3)
        ≤ Real.sqrt N * (4 * z * (8 * L ^ (3 : ℝ))) := by
          apply mul_le_mul hsq _ (by positivity) (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.sqrt N * z * (32 * L ^ (3 : ℝ)) := by ring
      _ ≤ Real.sqrt N * z * (N : ℝ) ^ ((1 : ℝ) / 3) := mul_le_mul_of_nonneg_left hpow hz'
      _ = N := h2
  have hcount := tauSum_le_count N
  linarith

end LeanLab.PNTPort.BVMax

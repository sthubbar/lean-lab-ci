import LeanLab.PNTPort.BVMax.TauGoldbachUpper
import LeanLab.PNTPort.BVMax.TauGoldbachMain

/-!
# The Titchmarsh divisor problem in order of magnitude

Lab proof, unit U-5315, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics:
Titchmarsh 1930 on GRH, Linnik 1961 and, by Bombieri-Vinogradov, Rodriquez and Halberstam 1965 to
1967 for the asymptotic `Σ_{p ≤ x} τ(p - 1) ~ (ζ(2)ζ(3)/ζ(6)) x`. This file proves the two bounds of
the right order, the shifted prime twin of `tauSum_ge_totient` and `tauSum_le`:

* `titchSum N = Σ_{p ≤ N} τ(p - 1)`;
* `titchSum_ge`: `titchSum N ≥ N/16` for all large `N`, from `bvPi` with the residue `1`;
* `titchSum_le`: `titchSum N ≤ C N` for all large `N`, from `brunTitchmarsh_ap`.
-/

namespace LeanLab.PNTPort.BVMax

open Finset Real Filter

/-- `Σ_{p ≤ N, p prime} τ(p - 1)`. -/
noncomputable def titchSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, ((p - 1).divisors.card : ℝ)

lemma dvd_sub_one_iff {p d : ℕ} (hp : 1 ≤ p) : d ∣ p - 1 ↔ p % d = 1 % d :=
  ⟨fun h => ((Nat.modEq_iff_dvd' hp).mpr h).symm, fun h => (Nat.modEq_iff_dvd' hp).mp h.symm⟩

/-- Double counting: `Σ_{d ≤ D} π(N; d, 1) ≤ titchSum N`. -/
lemma sum_piN_le_titchSum (N D : ℕ) : ∑ d ∈ Icc 1 D, piN N d 1 ≤ titchSum N := by
  unfold piN titchSum
  have key : ∑ d ∈ Icc 1 D, ((Icc 1 N).filter (fun n => n % d = 1 % d ∧ n.Prime)).card ≤
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, (p - 1).divisors.card := by
    calc ∑ d ∈ Icc 1 D, ((Icc 1 N).filter (fun n => n % d = 1 % d ∧ n.Prime)).card
        = ∑ d ∈ Icc 1 D, (((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card := by
          refine sum_congr rfl (fun d _ => congrArg card ?_)
          ext n
          simp only [mem_filter, mem_Icc]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, (dvd_sub_one_iff h1.1).mpr h2⟩
          · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, (dvd_sub_one_iff h1.1).mp h2, h3⟩
      _ = ∑ p ∈ (Icc 1 N).filter Nat.Prime, ((Icc 1 D).filter (fun d => d ∣ p - 1)).card :=
          sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun d p => d ∣ p - 1)
      _ ≤ _ := by
          refine sum_le_sum (fun p hp => card_le_card ?_)
          intro d hd
          simp only [mem_filter, mem_Icc] at hp hd
          exact Nat.mem_divisors.mpr ⟨hd.2, by have := hp.2.two_le; omega⟩
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast at this
  exact this

/-- `Σ_{p ≤ N} τ(p - 1) ≥ N/16` for all large `N`, unconditional, ineffective. -/
theorem titchSum_ge : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (N : ℝ) / 16 ≤ titchSum N := by
  obtain ⟨B, hB, K, hK⟩ := bvPi 2 (by norm_num)
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hll : ∀ᶠ x in atTop, B * Real.log (Real.log x) ≤ Real.log x / 4 := by
    have ho := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (show (0 : ℝ) < 1 / (4 * B) by positivity)
    filter_upwards [ho, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hx0
    simp only [Function.comp, id, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg hx0] at hx
    have := le_abs_self (Real.log (Real.log x))
    have h2 : B * Real.log (Real.log x) ≤ B * (1 / (4 * B) * Real.log x) :=
      mul_le_mul_of_nonneg_left (this.trans hx) hB.le
    calc _ ≤ _ := h2
      _ = Real.log x / 4 := by field_simp
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    (hll.and (Real.tendsto_log_atTop.eventually_ge_atTop (32 * K' + 2)))
  refine ⟨max ⌈X0⌉₊ 4, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := le_of_max_le_right hN
  have hNX : X0 ≤ N := (Nat.le_ceil X0).trans (by exact_mod_cast le_of_max_le_left hN)
  obtain ⟨h1, h2⟩ := hX0 N hNX
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  set Q := ⌊Real.sqrt N / L ^ B⌋₊ with hQ
  have hlogQ : L / 4 ≤ Real.log ((Q : ℝ) + 1) := by
    have hQ1 : Real.sqrt N / L ^ B < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpos : 0 < Real.sqrt N / L ^ B :=
      div_pos (Real.sqrt_pos.mpr hN0) (Real.rpow_pos_of_pos hL0 B)
    have hl : Real.log (Real.sqrt N / L ^ B) = L / 2 - B * Real.log L := by
      rw [Real.log_div (Real.sqrt_pos.mpr hN0).ne' (Real.rpow_pos_of_pos hL0 B).ne',
        Real.log_sqrt hN0.le, Real.log_rpow hL0]
    have := Real.log_le_log hpos hQ1.le
    linarith
  -- Bombieri-Vinogradov at y = N with the residue 1
  have hbv := hK N (by linarith) (fun _ => 1) (fun q => Nat.coprime_one_left q) (fun _ => (N : ℝ))
    (fun _ => ⟨hN0.le, le_rfl⟩)
  have hfl : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hterm : ∀ d ∈ Icc 1 Q, liD (N : ℝ) * ((1 : ℝ) / d.totient) ≤
      piN N d 1 + |piAP (N : ℝ) d 1 - liD (N : ℝ) / d.totient| := by
    intro d _
    have hp : piAP (N : ℝ) d 1 = piN N d 1 := by unfold piAP; rw [hfl]
    rw [hp, mul_one_div]
    have := le_abs_self (liD (N : ℝ) / d.totient - piN N d 1)
    rw [abs_sub_comm] at this
    linarith
  have hs := sum_le_sum hterm
  rw [← mul_sum, sum_add_distrib] at hs
  have hcount := sum_piN_le_titchSum N Q
  -- the main term
  have hharm : Real.log ((Q : ℝ) + 1) ≤ ∑ d ∈ Icc 1 Q, (1 : ℝ) / d.totient := by
    have := log_add_one_le_harmonic Q
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    refine this.trans (sum_le_sum (fun d hd => ?_))
    rw [mem_Icc] at hd
    have h1d : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by exact_mod_cast Nat.totient_le d)
  have hli : ((N : ℝ) - 2) / L ≤ liD (N : ℝ) := by
    have h := liD_ge (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have hup : Real.log ((N : ℝ) + 1) ≤ L + 1 / N := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by positivity) hN0.ne'] at h1
      have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    have hlo : L ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hN0 (by linarith)
    refine le_trans ?_ h
    push_cast
    rw [div_le_div_iff₀ hL0 (by linarith)]
    have hNinv : ((N : ℝ) - 2) * (1 / N) ≤ 1 := by
      rw [mul_one_div, div_le_one hN0]; linarith
    have := mul_le_mul_of_nonneg_left hup (show (0 : ℝ) ≤ (N : ℝ) - 2 by linarith)
    nlinarith
  have hmain : (N : ℝ) / 8 ≤ liD (N : ℝ) * ∑ d ∈ Icc 1 Q, (1 : ℝ) / d.totient := by
    have hli0 : 0 ≤ ((N : ℝ) - 2) / L := div_nonneg (by linarith) hL0.le
    calc (N : ℝ) / 8 ≤ ((N : ℝ) - 2) / L * (L / 4) := by
          have e : ((N : ℝ) - 2) / L * (L / 4) = ((N : ℝ) - 2) / 4 := by field_simp
          rw [e]; linarith
      _ ≤ liD (N : ℝ) * ∑ d ∈ Icc 1 Q, (1 : ℝ) / d.totient :=
          mul_le_mul hli (hlogQ.trans hharm) (by positivity) (hli0.trans hli)
  have herr : K * N / L ^ (2 : ℝ) ≤ (N : ℝ) / 16 := by
    have hL2 : L ^ (2 : ℝ) = L * L := by rw [Real.rpow_two, sq]
    rw [hL2, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hKN : K * N ≤ K' * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN0.le
    have : 16 * K' ≤ L * L := by nlinarith
    nlinarith
  linarith

/-- `Σ_{p ≤ N} τ(p - 1) ≤ C N` for all large `N`. -/
theorem titchSum_le : ∃ C : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → titchSum N ≤ C * N := by
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
  have hlz : Real.log z = L / 6 := by rw [hz, Real.log_rpow hN0]; ring
  -- τ(p - 1) ≤ 2 #{d ≤ √N : d ∣ p - 1}, then count by d
  have hcount : titchSum N ≤ 2 * ∑ d ∈ Icc 1 (Nat.sqrt N),
      ((((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card : ℝ) := by
    unfold titchSum
    have key : ∑ p ∈ (Icc 1 N).filter Nat.Prime, (p - 1).divisors.card ≤
        2 * ∑ d ∈ Icc 1 (Nat.sqrt N), (((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card := by
      rw [show ∑ d ∈ Icc 1 (Nat.sqrt N), (((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card
          = ∑ p ∈ (Icc 1 N).filter Nat.Prime, ((Icc 1 (Nat.sqrt N)).filter (fun d => d ∣ p - 1)).card
          from sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun d p => d ∣ p - 1), mul_sum]
      apply sum_le_sum
      intro p hp
      simp only [mem_filter, mem_Icc] at hp
      have h2 := hp.2.two_le
      have hn : p - 1 ≠ 0 := by omega
      refine (card_divisors_le (p - 1) hn).trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
      intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨Nat.pos_of_dvd_of_pos hd.1.1 (by omega), ?_⟩, hd.1.1⟩
      rw [Nat.le_sqrt]
      exact hd.2.trans (by omega)
    have := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at this
    exact this
  have hd : ∀ d ∈ Icc 1 (Nat.sqrt N),
      ((((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card : ℝ) ≤
        12 * N / (d.totient * L) + 4 * z * (1 + L) ^ 3 := by
    intro d hd
    rw [mem_Icc] at hd
    have hbt := LeanLab.PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap 1 ((N : ℝ) - 1) z d 1
      one_pos (by linarith) hz1 (by omega)
    have hA : ⌈(1 : ℝ)⌉₊ = 1 := Nat.ceil_one
    have hB : ⌊(1 : ℝ) + ((N : ℝ) - 1)⌋₊ = N := by
      rw [show (1 : ℝ) + ((N : ℝ) - 1) = (N : ℝ) by ring]; exact Nat.floor_natCast _
    rw [hA, hB] at hbt
    have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1) ⊆
        (Icc 1 N).filter (fun p => p.Prime ∧ p % d = 1 % d) := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp ⊢
      exact ⟨hp.1.1, hp.1.2, (dvd_sub_one_iff hp.1.1.1).mp hp.2⟩
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have h1 : ((((Icc 1 N).filter Nat.Prime).filter (fun p => d ∣ p - 1)).card : ℝ) ≤
        (((Icc 1 N).filter (fun p => p.Prime ∧ p % d = 1 % d)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    refine h1.trans (hbt.trans ?_)
    rw [hlz]
    apply add_le_add
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 * ((N : ℝ) - 1)) * (d.totient * L) ≤ 2 * N * (d.totient * L) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [mul_pos hφ hL0]
    · have : (1 + L / 6) ^ 3 ≤ (1 + L) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity) (by linarith)
      nlinarith [this, hz0]
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
  linarith

end LeanLab.PNTPort.BVMax

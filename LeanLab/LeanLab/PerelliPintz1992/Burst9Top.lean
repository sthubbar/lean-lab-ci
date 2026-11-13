/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 9, 2026-11-12. The new top level `perelliPintz_p3 : MainTheorem`, the
type of `perelliPintz`, with no sorry of its own. The glue below repeats the proofs of
`minor_block_bound`, `reduction27A_wide_of_split` and `estimate7Wide_of_p2` of
`Burst8P2b.lean` line for line, with `rpart_block_bound_p3` in place of the leaf
`rpart_block_bound`.

Leaves of `perelliPintz_p3`:
* CITED, sorry: `siegel_walfisz_uniform`, `shiu_d2`, classical theorems the paper cites.
* LEAF, sorry: `Decomp1624.energy_decayA`, Section 6.
* The Section 5 leaf `rpart_block_bound` is replaced by `rpart_block_bound_p3`, PROVED: display
  13, Gallagher, Cauchy and Schwarz, the Parseval cost and the end averaging are all proved.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Main

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2 LeanLab.PerelliPintz1992.Burst4Split

noncomputable section

/-- **One dyadic block, displays 23 to 27, p. 364**: the block is at most
`C N (L^c energyA + L^{-A-2})`, from `block_le_R_T`, the `R` part `rpart_block_bound_p3` and
the `T` part bound `Tpart_le`. PROVED, no sorry. -/
theorem minor_block_bound_p3 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
        (M : ℝ) ≤ Q N →
        blockInt N ε ξ A M ≤ C * N * (L N ^ c * energyA N ε ξ M + L N ^ (-(A + 2))) := by
  obtain ⟨ε₁, hε₁, hR⟩ := rpart_block_bound_p3
  refine ⟨ε₁, hε₁, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, c, N₀, hC, hc, hRb⟩ := hR ε hε hεε A hA
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ N ∧ 2 * L N ^ (3 * Bexp A / 2) < N ∧ (∀ q ∈ Decomp1519.Qs N A,
        Decomp1519.wq N A q ≤ 1 / 2) ∧ 1 ≤ L N ^ (Bexp A / 2)) ∧ 16 ≤ N ∧ 1 ≤ L N ∧
      L N ^ Bexp A ≤ √(N : ℝ) / 4 ∧ L N ^ (A + 3) ≤ (N : ℝ) ^ ε ∧ N₀ ≤ N := by
    filter_upwards [Decomp1519.estimate6_hyps_vacuity hA, eventually_ge_atTop 16,
      hLtop.eventually_ge_atTop 1, Decomp1519.logpow_le_sqrt_div4 (Bexp A),
      logpow_le_eps (A + 3) ε hε, tendsto_natCast_atTop_atTop.eventually_ge_atTop N₀]
      with N h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨2 * C + 576, c, N1, by positivity, hc, fun N hN ξ M hM1 hMQ => ?_⟩
  have hNN1 : N1 ≤ N := by exact_mod_cast hN
  obtain ⟨⟨-, -, hw2, -⟩, hN16, hℓ1, hLB, hLε, hN0⟩ := hN1 N hNN1
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hsqrt : √(N : ℝ) ≤ H N ε := by
    unfold H; rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hLH : ℓ ^ Bexp A ≤ H N ε := by
    have : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    linarith
  have hT := Tpart_le (ε := ε) (ξ := ξ) hN16 hA hℓ1 hw2 hLH hM1 hMQ
  have hRp := hRb N hN0 ξ M hM1 hMQ
  have hblk := block_le_R_T N ε ξ A M
  -- the `T` part in powers of `ℓ`
  have hu : 0 < ℓ ^ (A + 3) := Real.rpow_pos_of_pos hℓ0 _
  have hQH : Q N / H N ε ≤ 1 / ℓ ^ (A + 3) := by
    have he : Q N / H N ε = 1 / (2 * (N : ℝ) ^ ε) := by
      unfold Q H
      rw [Real.rpow_add hNpos]
      have : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
      have : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      field_simp
    rw [he]
    have hNε : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
    exact one_div_le_one_div_of_le hu (by linarith)
  have hLBu : 1 / ℓ ^ (Bexp A / 2) ≤ 1 / ℓ ^ (A + 3) :=
    one_div_le_one_div_of_le hu
      (Real.rpow_le_rpow_of_exponent_le hℓ1 (by unfold Bexp; linarith))
  have hTu : Tpart N ε ξ A M ≤ 288 * ℓ * N * (1 / ℓ ^ (A + 3)) := by
    refine hT.trans ?_
    have h1 : Q N / H N ε + 1 / ℓ ^ (Bexp A / 2) ≤ 2 * (1 / ℓ ^ (A + 3)) := by linarith
    have h2 : (1 + ℓ) * ((N : ℝ) + 1) ≤ 4 * ℓ * N := by nlinarith
    have h3 : 0 ≤ Q N / H N ε + 1 / ℓ ^ (Bexp A / 2) := by
      have : 0 < Q N := by unfold Q; positivity
      have : 0 < H N ε := Real.rpow_pos_of_pos hNpos _
      positivity
    calc 36 * (1 + ℓ) * (N + 1) * (Q N / H N ε + 1 / ℓ ^ (Bexp A / 2))
        = 36 * ((1 + ℓ) * (N + 1)) * (Q N / H N ε + 1 / ℓ ^ (Bexp A / 2)) := by ring
      _ ≤ 36 * (4 * ℓ * N) * (2 * (1 / ℓ ^ (A + 3))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 h3 (by positivity)
      _ = 288 * ℓ * N * (1 / ℓ ^ (A + 3)) := by ring
  have hpow : ℓ * (1 / ℓ ^ (A + 3)) = ℓ ^ (-(A + 2)) := by
    rw [show A + 3 = (A + 2) + 1 by ring, Real.rpow_add_one hℓ0.ne', Real.rpow_neg hℓ0.le]
    field_simp
  have hTu' : Tpart N ε ξ A M ≤ 288 * N * ℓ ^ (-(A + 2)) := by
    rw [← hpow]; linarith
  have hE0 : 0 ≤ ℓ ^ c * energyA N ε ξ M :=
    mul_nonneg (Real.rpow_nonneg hℓ0.le _) (energyA_nonneg N ε ξ M)
  have hL0 : 0 ≤ ℓ ^ (-(A + 2)) := Real.rpow_nonneg hℓ0.le _
  calc blockInt N ε ξ A M ≤ 2 * Rpart N ε ξ A M + 2 * Tpart N ε ξ A M := hblk
    _ ≤ 2 * (C * N * (ℓ ^ c * energyA N ε ξ M + ℓ ^ (-(A + 2)))) +
        2 * (288 * N * ℓ ^ (-(A + 2))) := by linarith
    _ ≤ (2 * C + 576) * N * (ℓ ^ c * energyA N ε ξ M + ℓ ^ (-(A + 2))) := by
        have : 0 ≤ (N : ℝ) * (ℓ ^ c * energyA N ε ξ M) := mul_nonneg hNpos.le hE0
        nlinarith


/-- **The leaf `Burst4Split.reduction27A_wide`**, same type, from `window_le_blocks` and the
block bound `minor_block_bound_p3`, summing `J + 1 ≤ L` dyadic blocks. PROVED, no sorry. -/
theorem reduction27A_wide_p3 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, hb⟩ := minor_block_bound_p3
  refine ⟨ε₁, hε₁, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, c, N₀, hC, hc, hB⟩ := hb ε hε hεε A hA
  refine ⟨C, c + 1, max N₀ 64, hC, by linarith, fun N hN ξ E hE0 hE => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN64 : 64 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hL := L_pos hN2
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hJ := Jn_succ_le hN64
  have hblock : ∀ j ∈ Finset.range (Jn N + 1),
      blockInt N ε ξ A (2 ^ j) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 2))) := by
    intro j hj
    have hjJ : j ≤ Jn N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hM1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hMQ : ((2 ^ j : ℕ) : ℝ) ≤ Q N := by
      have hQ1 := Q_ge_one (by omega : 4 ≤ N)
      have h1 : 2 ^ j ≤ ⌊Q N⌋₊ :=
        (Nat.pow_le_pow_right (by norm_num) hjJ).trans (Nat.pow_log_le_self 2
          (by have : 1 ≤ ⌊Q N⌋₊ := Nat.le_floor (by exact_mod_cast hQ1); omega))
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
    refine (hB N hN0 ξ (2 ^ j) hM1 hMQ).trans ?_
    have h1 : L N ^ c * energyA N ε ξ (2 ^ j) ≤ L N ^ c * E :=
      mul_le_mul_of_nonneg_left (hE _ hM1 hMQ) (Real.rpow_nonneg hL.le _)
    have h2 : 0 ≤ C * N := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  refine (window_le_blocks (by omega) ε ξ A).trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hX : 0 ≤ C * N * (L N ^ c * E + L N ^ (-(A + 2))) := by positivity
  have h1 : ((Jn N : ℝ) + 1) * (C * N * (L N ^ c * E + L N ^ (-(A + 2)))) ≤
      L N * (C * N * (L N ^ c * E + L N ^ (-(A + 2)))) := mul_le_mul_of_nonneg_right hJ hX
  refine h1.trans (le_of_eq ?_)
  have e1 : L N ^ (c + 1) = L N ^ c * L N := Real.rpow_add_one hL.ne' c
  have e2 : L N ^ (-(A + 1)) = L N ^ (-(A + 2)) * L N := by
    rw [← Real.rpow_add_one hL.ne']; congr 1; ring
  rw [e1, e2]; ring

/-- 7 for every real centre, `Estimate7Wide`, from `reduction27A_wide_of_split` and
`Decomp1624.energy_decayA`; the proof of `Burst4Split.estimate7Wide_of_split` with the split
reduction. CONDITIONAL ON `energy_decayA`. -/
theorem estimate7Wide_p3 : Estimate7Wide := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27A_wide_p3
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decayA ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have hξ0 : 0 ≤ clamp01 ξ := le_max_left _ _
  have hξ1 : clamp01 ξ ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N →
      energyA N ε ξ M ≤ K * L N ^ (-(A + 1 + c)) := fun M hM1 hM2 =>
    (energyA_le_clamp (by omega) ε ξ M).trans (hdecay N hN₁ (clamp01 ξ) hξ0 hξ1 M hM1 hM2)
  have he := hbound N hN₀ ξ (K * L N ^ (-(A + 1 + c))) (by positivity) hE
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

/-- **Perelli and Pintz 1992, the Theorem, p. 356**, same type as `perelliPintz`: Section 2 by
`mainTheorem_of_wide`, Section 4 by `estimate6Wide_of_split`, Sections 5 and 6 by
`estimate7Wide_p3`. CONDITIONAL ON `siegel_walfisz_uniform`, `shiu_d2`,
`Decomp1624.energy_decayA`. No sorry in this proof. -/
theorem perelliPintz_p3 : MainTheorem :=
  mainTheorem_of_wide estimate6Wide_of_split estimate7Wide_p3

#check (perelliPintz_p3 : MainTheorem)

#print axioms minor_block_bound_p3
#print axioms reduction27A_wide_p3
#print axioms estimate7Wide_p3
#print axioms perelliPintz_p3

end
end LeanLab.PerelliPintz1992.Burst9

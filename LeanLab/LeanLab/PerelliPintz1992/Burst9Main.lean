/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 9, 2026-11-12, step `rpart_block_bound`.

* `rpart_block_bound_p3`: the exact type of the leaf `Burst8P2.rpart_block_bound`, the `R` part
  of one dyadic block, Section 5, pp. 363 and 364, display 13, Gallagher's lemma, Cauchy and
  Schwarz, giving `energyA`. PROVED, from `parseval_cost_proved` of `Burst9Parseval.lean` and
  `clip_average_proved` of `Burst9Clip5.lean`. The pieces: `arc_to_eta`, `qr_bound`,
  `card_aWin_le_two`, `Ex_sum_le`, and the totient bound of `Burst8P2b`.
* `perelliPintz_p3 : MainTheorem`, the type of `perelliPintz`, with no sorry of its own: the
  proof of `Burst8P2.perelliPintz_p2` with `rpart_block_bound_p3` in place of
  `rpart_block_bound`; the glue `minor_block_bound_p3`, `reduction27A_wide_p3`,
  `estimate7Wide_p3` repeats the proofs of `Burst8P2b.lean` line for line.

The leaves of `perelliPintz_p3`: the cited classical theorems `siegel_walfisz_uniform` and
`shiu_d2`, the Section 6 step `Decomp1624.energy_decayA`; the Section 5 leaf `rpart_block_bound` is gone.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Arc
import LeanLab.PerelliPintz1992.Burst9Parseval
import LeanLab.PerelliPintz1992.Burst9Clip5

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2 LeanLab.PerelliPintz1992.Burst4Split

noncomputable section

/-! ### Elementary bounds -/

theorem log_two_mul_le {N : ℕ} (hN : 2 ≤ N) : Real.log (2 * N) ≤ 2 * L N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold L
  rw [Real.log_mul (by norm_num) (by linarith)]
  have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  linarith

theorem natlog_succ_le {N : ℕ} (hN : 2 ≤ N) (hℓ : 1 ≤ L N) :
    ((Nat.log 2 (2 * N) : ℕ) : ℝ) + 1 ≤ 4 * L N := by
  have h1 : 2 ^ Nat.log 2 (2 * N) ≤ 2 * N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 (2 * N) : ℕ) : ℝ) * Real.log 2 ≤ Real.log (2 * N) := by
    have := Real.log_le_log (by positivity) (show ((2 ^ Nat.log 2 (2 * N) : ℕ) : ℝ) ≤
      ((2 * N : ℕ) : ℝ) by exact_mod_cast h1)
    push_cast at this
    rwa [Real.log_pow] at this
  have h3 := log_two_mul_le hN
  have hl2 : (2 / 3 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h0 : (0 : ℝ) ≤ (Nat.log 2 (2 * N) : ℕ) := Nat.cast_nonneg _
  nlinarith

theorem Q_sq (N : ℕ) : Q N ^ 2 = N / 4 := by
  unfold Q
  rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num

theorem Q_le_sqrt (N : ℕ) : Q N ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  unfold Q
  have : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  linarith

theorem Q_ge_four {N : ℕ} (hN : 64 ≤ N) : 4 ≤ Q N := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Q; rw [← Real.sqrt_eq_rpow]
  have : (8 : ℝ) ≤ √(N : ℝ) := by
    rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  linarith

/-- The moduli of `Y(M)`: `M ≤ q ≤ 2M`, `q ≤ Q`. PROVED. -/
theorem mem_Y_facts {N : ℕ} {ε ξ : ℝ} {M : ℕ} {q : ℕ+} (hq : q ∈ Y N ε ξ M) (hQ : 0 ≤ Q N) :
    M ≤ (q : ℕ) ∧ (q : ℕ) ≤ 2 * M ∧ ((q : ℕ) : ℝ) ≤ Q N := by
  obtain ⟨hqim, hMq, hqM, -⟩ := of_mem_filter hq
  obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
  have hqI := (Finset.mem_Icc.mp q0.property)
  have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
  have hqQf : (q : ℕ) ≤ ⌊Q N⌋₊ := by rw [hqval]; exact hqI.2
  exact ⟨hMq, hqM, (Nat.cast_le.mpr hqQf).trans (Nat.floor_le hQ)⟩

theorem card_Y_le (N : ℕ) (ε ξ : ℝ) (M : ℕ) (hQ : 0 ≤ Q N) :
    ((Y N ε ξ M).card : ℝ) ≤ Q N := by
  have h1 : (Y N ε ξ M).card ≤ ⌊Q N⌋₊ := by
    unfold Y
    refine (card_filter_le_of _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_attach, Nat.card_Icc]; omega
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hQ)

/-- The end block length `K₀ = ⌈N L^{-K}⌉`. PROVED. -/
theorem K0_facts {N : ℕ} {K : ℝ} (hK : 1 ≤ K) (hN : 64 ≤ N) (hℓ : 8 ≤ L N)
    (hLN : L N ^ K ≤ N) :
    1 ≤ ⌈(N : ℝ) / L N ^ K⌉₊ ∧ 4 * ⌈(N : ℝ) / L N ^ K⌉₊ ≤ N ∧
      (N : ℝ) / L N ^ K ≤ ⌈(N : ℝ) / L N ^ K⌉₊ ∧
      (⌈(N : ℝ) / L N ^ K⌉₊ : ℝ) ≤ 2 * N / L N ^ K := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 < L N := by linarith
  have hLK : 8 ≤ L N ^ K := by
    calc (8 : ℝ) ≤ L N := hℓ
      _ = L N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L N ^ K := Real.rpow_le_rpow_of_exponent_le (by linarith) hK
  have hpos : 0 < (N : ℝ) / L N ^ K := by positivity
  have h1 : (N : ℝ) / L N ^ K ≤ N / 8 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hLK
  have hge1 : 1 ≤ (N : ℝ) / L N ^ K := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hc := Nat.ceil_lt_add_one hpos.le
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith), ?_, Nat.le_ceil _, ?_⟩
  · have : ((4 * ⌈(N : ℝ) / L N ^ K⌉₊ : ℕ) : ℝ) ≤ N := by
      push_cast; linarith
    exact_mod_cast this
  · have : 2 * (N : ℝ) / L N ^ K = (N : ℝ) / L N ^ K + (N : ℝ) / L N ^ K := by ring
    linarith

theorem T1_le (C₁ : ℝ) (hC₁ : 0 < C₁) (N : ℕ) (Om lam LK u φ : ℝ) (hl : lam ≤ LK)
    (hlam : 0 ≤ lam) (hu : 1 / φ ^ 2 ≤ u) :
    16 * π ^ 2 * C₁ * lam * N * Om ^ 2 / φ ^ 2 ≤ 16 * π ^ 2 * C₁ * LK * N * Om ^ 2 * u := by
  have hA0 : 0 ≤ 16 * π ^ 2 * C₁ * N * Om ^ 2 := by positivity
  have hu0 : 0 ≤ 1 / φ ^ 2 := by positivity
  calc 16 * π ^ 2 * C₁ * lam * N * Om ^ 2 / φ ^ 2
      = (16 * π ^ 2 * C₁ * N * Om ^ 2) * lam * (1 / φ ^ 2) := by ring
    _ ≤ (16 * π ^ 2 * C₁ * N * Om ^ 2) * LK * u :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl hA0) hu hu0
          (mul_nonneg hA0 (hlam.trans hl))
    _ = _ := by ring

theorem T2_le {N : ℕ} (hN : 64 ≤ N) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    16 * π ^ 2 * C₁ * (Real.log (2 * N) + 1) ^ 2 / Q N ^ 2 ≤
      144 * π ^ 2 * C₁ * L N ^ 2 / Q N ^ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := log_two_mul_le (by omega : 2 ≤ N)
  have hl20 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hℓ : 1 ≤ L N := by
    unfold L
    have : Real.log 64 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h64 : (1 : ℝ) ≤ Real.log 64 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have h9 : (Real.log (2 * N) + 1) ^ 2 ≤ 9 * L N ^ 2 := by nlinarith
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have : 0 ≤ 16 * π ^ 2 * C₁ := by positivity
  nlinarith

theorem T3_le {N : ℕ} (hN : 64 ≤ N) (hℓ1 : 1 ≤ L N) (q : ℕ+) (hqQ : ((q : ℕ) : ℝ) ≤ Q N) :
    8 * (1 / (((q : ℕ) : ℝ) * Q N)) *
        (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ^ 2 ≤
      8 * (8 * L N ^ 2) ^ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ0 : 0 < Q N := by have := Q_ge_four hN; linarith
  have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
  set B := 8 * L N ^ 2 with hB
  set E := ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n with hEdef
  have hE := Ex_sum_le N q
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  have hnl := natlog_succ_le (by omega : 2 ≤ N) hℓ1
  have hl2 := log_two_mul_le (by omega : 2 ≤ N)
  have hl20 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hE' : E ≤ ((q : ℕ) : ℝ) * B := by
    refine hE.trans ?_
    rw [hB, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc (((Nat.log 2 (2 * N) : ℕ) : ℝ) + 1) * Real.log (2 * N) ≤ (4 * L N) * (2 * L N) :=
          mul_le_mul hnl hl2 hl20 (by linarith)
      _ = 8 * L N ^ 2 := by ring
  have hE2 := pow_le_pow_left₀ hE0 hE' 2
  rw [show 8 * (1 / (((q : ℕ) : ℝ) * Q N)) * E ^ 2 = 8 * E ^ 2 / (((q : ℕ) : ℝ) * Q N) by ring]
  rw [div_le_iff₀ (by positivity)]
  have hB0 : 0 ≤ B := by positivity
  have hqq : ((q : ℕ) : ℝ) ^ 2 ≤ ((q : ℕ) : ℝ) * Q N := by nlinarith
  calc 8 * E ^ 2 ≤ 8 * ((((q : ℕ) : ℝ) * B) ^ 2) := by linarith
    _ = 8 * B ^ 2 * ((q : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ 8 * B ^ 2 * (((q : ℕ) : ℝ) * Q N) :=
        mul_le_mul_of_nonneg_left hqq (by positivity)

/-! ### The `R` part of one dyadic block -/

set_option maxHeartbeats 2000000 in
/-- **The leaf `Burst8P2.rpart_block_bound`, same type**, Section 5, pp. 363 and 364:
display 13, Gallagher's lemma, Cauchy and Schwarz, giving `energyA`, through the end averaging
route of `Decomp1624.reduction27A`, with `K₀ = ⌈N L^{-(A+4)}⌉` and `c = A + 6`.
PROVED, from `parseval_cost_proved` and `clip_average_proved`. -/
theorem rpart_block_bound_p3 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
        (M : ℝ) ≤ Q N →
        Rpart N ε ξ A M ≤ C * N * (L N ^ c * energyA N ε ξ M + L N ^ (-(A + 2))) := by
  obtain ⟨C₀, N₁, hC₀, hpc⟩ := parseval_cost_proved
  obtain ⟨C₁, hC₁, hcl⟩ := clip_average_proved
  refine ⟨1, one_pos, fun ε hε _ A hA => ?_⟩
  set K : ℝ := A + 4 with hKdef
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop, 64 ≤ N ∧ 8 ≤ L N ∧
      L N ^ (A + 6) ≤ (N : ℝ) ^ (1 / 2 : ℝ) ∧ N₁ ≤ N := by
    filter_upwards [eventually_ge_atTop 64, hLtop.eventually_ge_atTop 8,
      logpow_le_eps (A + 6) (1 / 2) (by norm_num),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop N₁] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hev
  set Cm : ℝ := 512 * π ^ 2 * C₁ with hCm
  set Ce : ℝ := 288 * π ^ 2 * C₁ + 1024 + 8 * C₀ with hCe
  refine ⟨Cm + Ce, A + 6, N2, by positivity, by linarith, fun N hN ξ M hM1 hMQ => ?_⟩
  have hNN2 : N2 ≤ N := by exact_mod_cast hN
  obtain ⟨hN64, hℓ8, hpow, hN1⟩ := hN2 N hNN2
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hQ4 := Q_ge_four hN64
  have hQ0 : 0 < Q N := by linarith
  have hsqrtN : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
    rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hNpos.le] at this
  have hKA6 : ℓ ^ K ≤ ℓ ^ (A + 6) := Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
  have hLN : ℓ ^ K ≤ N := hKA6.trans (hpow.trans hsqrtN)
  obtain ⟨hK1, hK4, hKlo, hKhi⟩ := K0_facts (K := K) (by linarith) hN64 hℓ8 hLN
  set K0 := ⌈(N : ℝ) / ℓ ^ K⌉₊ with hK0def
  have hK0r : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hLK0 : 0 < ℓ ^ K := Real.rpow_pos_of_pos hℓ0 _
  have hLK1 : 1 ≤ ℓ ^ K := Real.one_le_rpow hℓ1 (by linarith)
  -- the per modulus facts
  have hlam : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N → max 1 (gallagherWindow N q / K0) ≤ ℓ ^ K := by
    intro q hqQ
    refine max_le hLK1 ?_
    have hh : gallagherWindow N q ≤ N / 8 := by
      unfold gallagherWindow
      have := Q_sq N
      have h1 : ((q : ℕ) : ℝ) * Q N ≤ Q N * Q N := mul_le_mul_of_nonneg_right hqQ hQ0.le
      nlinarith
    rw [div_le_iff₀ hK0r]
    have : (N : ℝ) ≤ ℓ ^ K * K0 := by
      rw [div_le_iff₀ hLK0] at hKlo; linarith
    nlinarith
  have hclipq : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N → ∀ χ : DirichletCharacter ℂ (q : ℕ),
      (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ Aset N K0, ∑ b ∈ Bset N K0,
          (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) (gallagherWindow N q) x‖ ^ 2) ≤
        C₁ * (windowMean N χ (gallagherWindow N q) + (1 / (K0 : ℝ)) *
          (∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2) := by
    intro q hqQ χ
    have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
    refine hcl N K0 hN64 hK1 hK4 q χ _ ?_ ?_
    · unfold gallagherWindow; nlinarith
    · unfold gallagherWindow
      have := Q_sq N
      have h1 : ((q : ℕ) : ℝ) * Q N ≤ Q N * Q N := mul_le_mul_of_nonneg_right hqQ hQ0.le
      nlinarith
  -- the bound for each arc
  set δ : ℕ+ → ℝ := fun q => 1 / (((q : ℕ) : ℝ) * Q N) with hδ
  set Dt : ℕ+ → ℕ → ℝ := fun q r => (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ Pset N K0,
    (∫ η in (-δ q)..(δ q), ‖Rx (Dset N p) q r η‖ ^ 2) with hDt
  set B : ℝ := 8 * ℓ ^ 2 with hB
  set X : ℕ+ → ℝ := fun q =>
    16 * π ^ 2 * C₁ * ℓ ^ K * N * Om N q ^ 2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) +
      144 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 8 * B ^ 2 with hX
  have harc : ∀ q ∈ Y N ε ξ M, ∀ r ∈ aWin N ε ξ (q : ℕ),
      (∫ α in arcM N A q r, ‖Decomp1519.R N q r (α - (r : ℝ) / q)‖ ^ 2) ≤ Dt q r + X q := by
    intro q hq r hr
    obtain ⟨hMq, -, hqQ⟩ := mem_Y_facts hq hQ0.le
    have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
    have hqM : (M : ℝ) ≤ (q : ℕ) := by exact_mod_cast hMq
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hcop : Nat.Coprime r q := (Finset.mem_filter.mp (of_mem_filter hr).1).2
    have h1 := arc_to_eta N A q r (by positivity)
    have h2 := qr_bound hK1 hK4 q hQ0 hcop C₁ hC₁ (hclipq q hqQ)
    refine h1.trans (h2.trans ?_)
    have hlq : Real.log ((q : ℕ) : ℝ) ≤ ℓ := by
      simp only [hℓdef, L]
      exact Real.log_le_log (by linarith) (hqQ.trans ((Q_le_sqrt N).trans hsqrtN))
    have hinvφ := inv_totient_sq_le q.pos hlq hM0 hqM
    have hT1 := T1_le C₁ hC₁ N (Om N q) _ _ _ _ (hlam q hqQ)
      (le_trans zero_le_one (le_max_left _ _)) hinvφ
    have hT2 := T2_le hN64 C₁ hC₁
    have hT3 := T3_le hN64 hℓ1 q hqQ
    show _ ≤ Dt q r + X q
    simp only [hDt, hX, hδ, hB]
    linarith
  -- sum over the arcs
  have hsum1 : Rpart N ε ξ A M ≤ ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), (Dt q r + X q) := by
    unfold Rpart
    exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => harc q hq r hr
  -- the `D` part
  have hDsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) ≤ 4 * C₀ * K0 * ℓ ^ 2 := by
    have e1 : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) =
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ Pset N K0, ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx (Dset N p) q r η‖ ^ 2) := by
      simp only [hDt]
      simp_rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_congr rfl fun q _ => Finset.sum_comm).trans Finset.sum_comm
    rw [e1]
    have e1' : (∑ p ∈ Pset N K0, ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx (Dset N p) q r η‖ ^ 2)) ≤
        ∑ _p ∈ Pset N K0, C₀ * (2 * K0) * ℓ ^ 2 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := hpc N (by exact_mod_cast hN1) ε ξ hε M hM1 hMQ (Dset N p) (Dset_sub N p)
      refine this.trans ?_
      have hc : ((Dset N p).card : ℝ) ≤ 2 * K0 := by exact_mod_cast card_Dset_le hK4 hp
      have := mul_le_mul_of_nonneg_left hc hC₀.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    rw [Finset.sum_const, card_Pset N K0 (by omega), nsmul_eq_mul] at e1'
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    calc (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ Pset N K0, ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx (Dset N p) q r η‖ ^ 2)
        ≤ (2 / (K0 : ℝ) ^ 2) * (((K0 * K0 : ℕ) : ℝ) * (C₀ * (2 * K0) * ℓ ^ 2)) :=
          mul_le_mul_of_nonneg_left e1' (by positivity)
      _ = 4 * C₀ * K0 * ℓ ^ 2 := by push_cast; field_simp; ring
  -- the `X` part
  have hX0 : ∀ q, 0 ≤ X q := fun q => by simp only [hX]; positivity
  have hXsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), X q) ≤
      ∑ q ∈ Y N ε ξ M, 2 * X q := by
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, -, hqQ⟩ := mem_Y_facts hq hQ0.le
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((aWin N ε ξ (q : ℕ)).card : ℝ) ≤ 2 := by
      exact_mod_cast card_aWin_le_two hN64 hε ξ q.pos hqQ
    exact mul_le_mul_of_nonneg_right hc (hX0 q)
  have hEA : energyA N ε ξ M = (1 / (M : ℝ) ^ 2) * ∑ q ∈ Y N ε ξ M, Om N q ^ 2 := rfl
  have hXsum2 : (∑ q ∈ Y N ε ξ M, 2 * X q) ≤
      128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M +
        (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2) := by
    have hYc := card_Y_le N ε ξ M hQ0.le
    simp only [hX]
    rw [Finset.sum_congr rfl fun q _ => (show 2 * (16 * π ^ 2 * C₁ * ℓ ^ K * N * Om N q ^ 2 *
        (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) + 144 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 8 * B ^ 2) =
        (128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N) * ((1 / (M : ℝ) ^ 2) * Om N q ^ 2) +
          (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) by ring),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hEA, Finset.sum_const,
      nsmul_eq_mul]
    have h1 : ((Y N ε ξ M).card : ℝ) * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) ≤
        Q N * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) :=
      mul_le_mul_of_nonneg_right hYc (by positivity)
    have h2 : Q N * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) =
        288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 := by
      field_simp
    linarith
  -- the final comparison
  have hE0 : 0 ≤ energyA N ε ξ M := energyA_nonneg N ε ξ M
  have hmain : 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M ≤
      Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by
    have h1 : (1 + ℓ) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have h2 : ℓ ^ K * ℓ ^ 2 = ℓ ^ (A + 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hℓ0]
      congr 1
      rw [hKdef]; push_cast; ring
    have hA0 : 0 ≤ 128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M := by positivity
    calc 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M
        = (128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M) * (1 + ℓ) ^ 2 := by ring
      _ ≤ (128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M) * (4 * ℓ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hA0
      _ = 512 * π ^ 2 * C₁ * N * ((ℓ ^ K * ℓ ^ 2) * energyA N ε ξ M) := by ring
      _ = Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by rw [h2, hCm]
  -- the small terms
  have hsmall_base : (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 ≤ N * ℓ ^ (-(A + 2)) := by
    have e : (N : ℝ) * ℓ ^ (-(A + 2)) * ℓ ^ (A + 6) = N * ℓ ^ 4 := by
      rw [mul_assoc, ← Real.rpow_add hℓ0, show -(A + 2) + (A + 6) = ((4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hp0 : 0 < ℓ ^ (A + 6) := Real.rpow_pos_of_pos hℓ0 _
    have hs0 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
    have hss : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hNpos]; norm_num
    rw [← mul_le_mul_iff_left₀ hp0, e]
    have h4 : 0 ≤ ℓ ^ 4 := by positivity
    calc (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * ℓ ^ (A + 6)
        ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) * ℓ ^ 4 := by ring
      _ = N * ℓ ^ 4 := by rw [hss]
  have hsmall : 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2 ≤
      Ce * N * ℓ ^ (-(A + 2)) := by
    have hQ1 : 1 ≤ Q N := by linarith
    have hl24 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have hs1 : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hQs := Q_le_sqrt N
    have t1 : 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ≤ 288 * π ^ 2 * C₁ * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) := by
      rw [div_le_iff₀ hQ0]
      have : ℓ ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * Q N := by
        have : (1 : ℝ) * ℓ ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * Q N := by
          have := mul_le_mul hs1 hl24 (by positivity) (by positivity)
          nlinarith
        linarith
      have hc : 0 ≤ 288 * π ^ 2 * C₁ := by positivity
      nlinarith
    have t2 : 16 * Q N * B ^ 2 ≤ 1024 * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) := by
      rw [hB]
      have : 16 * Q N * (8 * ℓ ^ 2) ^ 2 = 1024 * (Q N * ℓ ^ 4) := by ring
      rw [this]
      have h4 : 0 ≤ ℓ ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right hQs h4
      linarith
    have t3 : 4 * C₀ * K0 * ℓ ^ 2 ≤ 8 * C₀ * (N * ℓ ^ (-(A + 2))) := by
      have hsK : ℓ ^ K = ℓ ^ (A + 2) * ℓ ^ 2 := by
        rw [← Real.rpow_natCast ℓ 2, ← Real.rpow_add hℓ0]
        congr 1
        rw [hKdef]; push_cast; ring
      have hA2 : 0 < ℓ ^ (A + 2) := Real.rpow_pos_of_pos hℓ0 _
      have e : (2 * N / ℓ ^ K) * ℓ ^ 2 = 2 * (N * ℓ ^ (-(A + 2))) := by
        rw [hsK, Real.rpow_neg hℓ0.le]
        field_simp
      have := mul_le_mul_of_nonneg_right hKhi (by positivity : 0 ≤ ℓ ^ 2)
      rw [e] at this
      nlinarith
    have hsb := hsmall_base
    have hc1 : 0 ≤ 288 * π ^ 2 * C₁ + 1024 := by positivity
    calc 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2
        ≤ (288 * π ^ 2 * C₁ + 1024) * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) +
            8 * C₀ * (N * ℓ ^ (-(A + 2))) := by linarith
      _ ≤ (288 * π ^ 2 * C₁ + 1024) * (N * ℓ ^ (-(A + 2))) + 8 * C₀ * (N * ℓ ^ (-(A + 2))) := by
          have := mul_le_mul_of_nonneg_left hsb hc1
          linarith
      _ = Ce * N * ℓ ^ (-(A + 2)) := by rw [hCe]; ring
  -- assemble
  have hsplit : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), (Dt q r + X q)) =
      (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) +
        ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), X q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_add_distrib
  have hfin := hsum1.trans (le_of_eq hsplit)
  have hL0 : 0 ≤ ℓ ^ (-(A + 2)) := Real.rpow_nonneg hℓ0.le _
  have hE6 : 0 ≤ Ce * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by
    have : 0 ≤ Ce := by positivity
    positivity
  have hCm6 : 0 ≤ Cm * N * ℓ ^ (-(A + 2)) := by
    have : 0 ≤ Cm := by positivity
    positivity
  calc Rpart N ε ξ A M
      ≤ 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M +
          (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2) := by
        linarith
    _ ≤ Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) + Ce * N * ℓ ^ (-(A + 2)) := by linarith
    _ ≤ (Cm + Ce) * N * (ℓ ^ (A + 6) * energyA N ε ξ M + ℓ ^ (-(A + 2))) := by nlinarith

#print axioms log_two_mul_le
#print axioms natlog_succ_le
#print axioms Q_sq
#print axioms mem_Y_facts
#print axioms card_Y_le
#print axioms K0_facts
#print axioms inv_totient_sq_le
#print axioms T1_le
#print axioms T2_le
#print axioms T3_le
#print axioms rpart_block_bound_p3

end
end LeanLab.PerelliPintz1992.Burst9

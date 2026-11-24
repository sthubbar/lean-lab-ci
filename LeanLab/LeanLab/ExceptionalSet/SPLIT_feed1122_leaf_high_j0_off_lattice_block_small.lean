import LeanLab.ExceptionalSet.SPLIT_leaf_high_j0_large_phase_strip

/-!
Burst burst-20261122 feed1122, session S89. Split of `Decomp553b.leaf_high_j0_off_lattice_block_small`
of `SPLIT_leaf_high_j0_large_phase_strip.lean`, P0082 Brüdern and Perelli 1998, page 370, the
proof of Lemma 9: displays 40 and 41 detect the parity of `[F(n)]` by the shifted sums
`Φ(α - h/2)`, and the last paragraph of page 370 bounds every shifted sum by Theorem 2,
page 354.

Leaves:
* `leaf_high_j0_parity_expansion`, HARD: the parity filtered block sum over the upper block
  `(3N/4, N]` is at most a constant times `N/H` plus the shifted plain sums `S(t - h/2)`,
  `|h| ≤ H`, plus the plain sums `S(k)`, `1 ≤ k ≤ H`, at the integer frequencies that carry
  the truncation error near the jumps of the parity indicator. This is the truncated Fourier
  expansion of displays 40 and 41 in majorant form.
* `leaf_high_j0_block_theorem2`, HARD: Theorem 2 of page 354 for the plain sum over the block
  `(3N/4, N]` on the range `F^(-c) ≤ |α| ≤ F^C`.
* `leaf_high_j0_off_lattice_bookkeeping`, the eventual size comparisons of `E`, `⌈E⌉` and
  `F^C` and the final absorption into `N E^(-5/6)`, pure real analysis.

The assembly `leaf_high_j0_off_lattice_block_small_split` uses these and the proved
`leaf_high_j0_strip_index_bounded`, which shows that every half integer with index above
`E^(3/4)` is automatically off the strips. No existing file is edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF: P0082 page 370, displays 40 and 41, the truncated Fourier detection of the parity
of `[F(n)]` on the upper block, in majorant form. HARD. For a constant `C`, every `N`, every
`H ≥ 1` and every `t`, the parity filtered block sum is at most `C` times `N/H` plus the
shifted plain sums `S(t - h/2)` with `|h| ≤ H` plus the plain sums `S(k)` with `1 ≤ k ≤ H`,
where `S(α) = Σ_{3N/4 < n ≤ N} e(α F(n))`. -/
theorem leaf_high_j0_parity_expansion (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N H : ℕ, 1 ≤ H → ∀ t : ℝ,
      ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) t‖ ≤
        C * ((N : ℝ) / H +
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
            ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((t - (h : ℝ) / 2) * F γ n)‖ +
          ∑ k ∈ Finset.Icc (1 : ℕ) H,
            ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((k : ℝ) * F γ n)‖) := by
  sorry

/-- LEAF: P0082 page 354, Theorem 2, for the plain sum over the block `(3N/4, N]`, as used
in the last paragraph of page 370. HARD. For `0 < c < 1` and `0 < C' < γ - 1` there are
`κ' > 0` and `A ≥ 0` with `|S(α)| ≤ A N exp(-κ' (log N)^(3-2γ))` whenever
`F(N)^(-c) ≤ |α| ≤ F(N)^C'` and `N ≥ 1`. -/
theorem leaf_high_j0_block_theorem2 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' →
          ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC (α * F γ n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- The eventual size comparisons and the final absorption for the assembly: once `N` is
large, `E ≥ 1`, `3E ≤ F^C'`, and `C (N/⌈E⌉ + (3⌈E⌉ + 1) A N exp(-κ' (log N)^(3-2γ)))` is at
most `N E^(-5/6)` when `κ ≤ κ'/4`. Proved. -/
theorem leaf_high_j0_off_lattice_bookkeeping (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (C' κ' C A : ℝ) (hC' : 0 < C') (hκ' : 0 < κ') (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ κ : ℝ, 0 < κ → κ ≤ κ' / 4 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ calE γ κ N ∧ 3 * calE γ κ N ≤ F γ N ^ C' ∧
      C * ((N : ℝ) / (⌈calE γ κ N⌉₊ : ℝ) +
        (3 * (⌈calE γ κ N⌉₊ : ℝ) + 1) * (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))))
        ≤ (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  intro κ hκ hκle
  have hp : 0 < 3 - 2 * γ := by linarith
  have tL : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have tM : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 * γ - 3))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 3 * γ - 3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  set K : ℝ := C * (1 + 7 * A) with hKdef
  obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp
    (tL.eventually_ge_atTop (6 * Real.log K / κ))
  obtain ⟨Nb, hNb⟩ := Filter.eventually_atTop.mp
    (tL.eventually_ge_atTop (Real.log 3 / κ))
  obtain ⟨Nc, hNc⟩ := Filter.eventually_atTop.mp
    (tM.eventually_ge_atTop (2 * κ / C'))
  refine ⟨max (max (max Na Nb) Nc) 2, fun N hN => ?_⟩
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hNc' : Nc ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set Lp : ℝ := Real.log (N : ℝ) ^ (3 - 2 * γ) with hLpdef
  have hLp0 : 0 ≤ Lp := Real.rpow_nonneg hL.le _
  set u : ℝ := κ * Lp with hudef
  have hu0 : 0 ≤ u := mul_nonneg hκ.le hLp0
  have hE : calE γ κ N = Real.exp u := rfl
  have hEr : ∀ r : ℝ, calE γ κ N ^ r = Real.exp (u * r) := by
    intro r
    rw [hE, ← Real.exp_mul]
  have hua : 6 * Real.log K ≤ u := by
    have := hNa N hNa'
    rw [div_le_iff₀ hκ] at this
    rw [hudef]; linarith
  have hub : Real.log 3 ≤ u := by
    have := hNb N hNb'
    rw [div_le_iff₀ hκ] at this
    rw [hudef]; linarith
  have huc : 2 * κ ≤ C' * Real.log (N : ℝ) ^ (3 * γ - 3) := by
    have := hNc N hNc'
    rw [div_le_iff₀ hC'] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]; exact Real.one_le_exp hu0
  · have hFC : F γ N ^ C' = Real.exp (Real.log (N : ℝ) ^ γ * C') := by
      rw [F, ← Real.exp_mul]
    have hsplit : Real.log (N : ℝ) ^ γ = Lp * Real.log (N : ℝ) ^ (3 * γ - 3) := by
      rw [hLpdef, ← Real.rpow_add hL]
      ring_nf
    rw [hFC, hE]
    have h3 : (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
    rw [h3, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hsplit]
    have : Lp * (2 * κ) ≤ Lp * (C' * Real.log (N : ℝ) ^ (3 * γ - 3)) :=
      mul_le_mul_of_nonneg_left huc hLp0
    nlinarith
  · rw [hEr, hE]
    set e : ℝ := Real.exp u with hedef
    have he1 : 1 ≤ e := Real.one_le_exp hu0
    have hepos : 0 < e := Real.exp_pos u
    set H : ℕ := ⌈e⌉₊ with hHdef
    have hHge : e ≤ (H : ℝ) := Nat.le_ceil _
    have hHle : (H : ℝ) ≤ e + 1 := (Nat.ceil_lt_add_one hepos.le).le
    have hHpos : 0 < (H : ℝ) := lt_of_lt_of_le hepos hHge
    have hX : Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) ≤ Real.exp (-u) ^ 4 := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      rw [hudef]
      push_cast
      nlinarith
    have hem : Real.exp (-u) * e = 1 := by rw [hedef, ← Real.exp_add]; simp
    set m : ℝ := Real.exp (-u) with hmdef
    have hm0 : 0 < m := Real.exp_pos _
    have hm1 : m ≤ 1 := by rw [hmdef]; exact Real.exp_le_one_iff.mpr (by linarith)
    have hK : K ≤ Real.exp (u / 6) := by
      rcases le_or_gt K 0 with hK0 | hK0
      · exact hK0.trans (Real.exp_pos _).le
      · calc K = Real.exp (Real.log K) := (Real.exp_log hK0).symm
          _ ≤ Real.exp (u / 6) := Real.exp_le_exp.mpr (by linarith)
    have hrhs : Real.exp (u * (-(5 / 6 : ℝ))) = Real.exp (u / 6) * m := by
      rw [hmdef, ← Real.exp_add]; ring_nf
    rw [hrhs]
    -- bound the two terms
    have ht1 : (N : ℝ) / H ≤ N * m := by
      rw [div_le_iff₀ hHpos]
      have : (N : ℝ) * m * e ≤ N * m * H := by
        apply mul_le_mul_of_nonneg_left hHge; positivity
      have h' : (N : ℝ) * m * e = N := by rw [mul_assoc, hem, mul_one]
      linarith
    have hm4 : m ^ 4 * e ≤ m := by
      have : m ^ 4 * e = m ^ 3 * (m * e) := by ring
      rw [this, hem, mul_one]
      have : m ^ 3 ≤ m ^ 1 := pow_le_pow_of_le_one hm0.le hm1 (by norm_num)
      simpa using this
    have h3H : 3 * (H : ℝ) + 1 ≤ 7 * e := by linarith
    have ht2 : (3 * (H : ℝ) + 1) * (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
        ≤ 7 * A * N * m := by
      have hAN : 0 ≤ A * N := by positivity
      calc (3 * (H : ℝ) + 1) * (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
          ≤ (7 * e) * (A * N * m ^ 4) := by
            apply mul_le_mul h3H (mul_le_mul_of_nonneg_left hX hAN) (by positivity)
              (by positivity)
        _ = 7 * (A * N) * (m ^ 4 * e) := by ring
        _ ≤ 7 * (A * N) * m := by
            apply mul_le_mul_of_nonneg_left hm4; positivity
        _ = 7 * A * N * m := by ring
    calc C * ((N : ℝ) / H + (3 * (H : ℝ) + 1) *
          (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))))
        ≤ C * (N * m + 7 * A * N * m) := by
          apply mul_le_mul_of_nonneg_left _ hC.le; linarith
      _ = K * (N * m) := by rw [hKdef]; ring
      _ ≤ Real.exp (u / 6) * (N * m) := by
          apply mul_le_mul_of_nonneg_right hK; positivity
      _ = N * (Real.exp (u / 6) * m) := by ring

/-- `leaf_high_j0_off_lattice_block_small`, statement verbatim, from the two HARD leaves, the
bookkeeping and the proved `leaf_high_j0_strip_index_bounded`. -/
theorem leaf_high_j0_off_lattice_block_small_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨C, hC, hP⟩ := leaf_high_j0_parity_expansion γ h1 h2
  obtain ⟨δb, hδb, hidx⟩ := leaf_high_j0_strip_index_bounded γ h1 h2
  refine ⟨min δb 1, lt_min hδb one_pos, fun δ hδ hδs => ?_⟩
  have hδb' : δ < δb := hδs.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := hδs.trans_le (min_le_right _ _)
  set C' : ℝ := (γ - 1) / 2 with hC'def
  have hC' : 0 < C' := by rw [hC'def]; linarith
  have hC'γ : C' < γ - 1 := by rw [hC'def]; linarith
  obtain ⟨κ', A, hκ', hA, hT⟩ :=
    leaf_high_j0_block_theorem2 γ h1 h2 (1 - δ) C' (by linarith) (by linarith) hC' hC'γ
  obtain ⟨κb, hκb, hidx⟩ := hidx δ hδ hδb'
  refine ⟨min κb (κ' / 4), lt_min hκb (by linarith), fun κ hκ hκs => ?_⟩
  have hκb' : κ ≤ κb := hκs.trans (min_le_left _ _)
  have hκle : κ ≤ κ' / 4 := hκs.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hidx κ hκ hκb'
  obtain ⟨N₂, hN₂⟩ :=
    leaf_high_j0_off_lattice_bookkeeping γ h1 h2 C' κ' C A hC' hκ' hC hA κ hκ hκle
  refine ⟨max (max N₁ N₂) 1, fun N hN a ha b hb hoff => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNone : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hE1, hEF, habs⟩ := hN₂ N hN2
  set E := calE γ κ N with hEdef
  set H : ℕ := ⌈E⌉₊ with hHdef
  set X : ℝ := A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hHge : E ≤ (H : ℝ) := Nat.le_ceil _
  have hHle : (H : ℝ) ≤ 2 * E := by
    have := Nat.ceil_lt_add_one (le_trans zero_le_one hE1)
    rw [← hHdef] at this
    linarith
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ (H : ℝ) := le_trans hE1 hHge
    exact_mod_cast this
  have hFone : 1 ≤ F γ N := by
    rw [F]
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hNone)) _)
  have hlow : F γ N ^ (-(1 - δ)) = F γ N ^ (δ - 1) := by ring_nf
  -- every half integer is off the strips
  have hall : ∀ h : ℤ, F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2| := by
    intro h
    by_cases hh : (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ)
    · exact hoff h hh
    · by_contra hle
      exact hh (hN₁ N hN1 a ha b hb h (le_of_not_gt hle))
  -- the window bound on `b - a`
  have hE23 : E ^ (2 / 3 : ℝ) ≤ E := by
    have := Real.rpow_le_rpow_of_exponent_le hE1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    simpa using this
  have hba : |b - a| ≤ 2 * E := by
    simp only [oddDomain, Set.mem_inter_iff, Set.mem_Icc] at ha hb
    rw [abs_le]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  -- shifted sums
  have hshift : ∀ h ∈ Finset.Icc (-(H : ℤ)) H,
      ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC (((b - a) - (h : ℝ) / 2) * F γ n)‖ ≤ X := by
    intro h hmem
    rw [Finset.mem_Icc] at hmem
    have habsh : (|h| : ℝ) ≤ H := by
      have : |h| ≤ (H : ℤ) := abs_le.mpr hmem
      exact_mod_cast this
    have hup : |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ C' := by
      have htri : |(b - a) - (h : ℝ) / 2| ≤ |b - a| + |(h : ℝ) / 2| := abs_sub _ _
      have hh2 : |(h : ℝ) / 2| = (|h| : ℝ) / 2 := by
        rw [abs_div, abs_two]
      rw [hh2] at htri
      linarith
    refine hT N hNone _ ?_ hup
    rw [hlow]
    exact (hall h).le
  -- integer frequency sums
  have hint : ∀ k ∈ Finset.Icc (1 : ℕ) H,
      ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((k : ℝ) * F γ n)‖ ≤ X := by
    intro k hmem
    rw [Finset.mem_Icc] at hmem
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hmem.1
    have hkH : (k : ℝ) ≤ H := by exact_mod_cast hmem.2
    have hkabs : |(k : ℝ)| = k := abs_of_nonneg (by positivity)
    refine hT N hNone _ ?_ ?_
    · rw [hkabs, hlow]
      have : F γ N ^ (δ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hFone (by linarith)
      linarith
    · rw [hkabs]
      linarith
  have hsum1 : ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
      ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC (((b - a) - (h : ℝ) / 2) * F γ n)‖ ≤
        (2 * (H : ℝ) + 1) * X := by
    refine (Finset.sum_le_card_nsmul _ _ X hshift).trans ?_
    rw [nsmul_eq_mul, Int.card_Icc]
    have : ((((H : ℤ) + 1 - -(H : ℤ)).toNat : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by
      have h' : ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
      rw [h']
      push_cast
      ring
    rw [this]
  have hsum2 : ∑ k ∈ Finset.Icc (1 : ℕ) H,
      ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((k : ℝ) * F γ n)‖ ≤ (H : ℝ) * X := by
    refine (Finset.sum_le_card_nsmul _ _ X hint).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    simp
  have hmain := hP N H hH1 (b - a)
  calc ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖
      ≤ C * ((N : ℝ) / H + (2 * (H : ℝ) + 1) * X + (H : ℝ) * X) := by
        refine hmain.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith
    _ = C * ((N : ℝ) / H + (3 * (H : ℝ) + 1) * X) := by ring
    _ ≤ (N : ℝ) * E ^ (-(5 / 6 : ℝ)) := habs

#print axioms leaf_high_j0_off_lattice_bookkeeping
#print axioms leaf_high_j0_off_lattice_block_small_split

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_high_j0_off_lattice_block_small_split =
    type_of% @leaf_high_j0_off_lattice_block_small := rfl

end LeanLab.ExceptionalSet.Decomp553b

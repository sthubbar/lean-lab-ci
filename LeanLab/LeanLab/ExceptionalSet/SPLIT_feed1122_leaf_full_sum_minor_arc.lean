/-
Split of the LEAF statement `leaf_full_sum_minor_arc` of
`LeanLab.ExceptionalSet.SPLIT_leaf_gap_core`, unit U-1539, P0082 Bruedern and Perelli 1998.

The parent asks for the full exponential sum `Σ_{N/2 < n ≤ N} e(α F(n))` to be at most
`N ℰ^(-1/3) / 8` for `F γ N ^ (δ - 1) < |α| ≤ F γ N ^ δ`.  In the paper this is Theorem 2,
p. 354, transported from the dyadic block `[M, 2M]` to the block `(N/2, N]`.  Theorem 2 only
covers `F(M)^(-c) ≤ |α| ≤ F(M)^C` with `c < 1` and `C < γ - 1`, so the range of `α` is cut at
`F γ N ^ δ'` with `δ' = min δ ((γ - 1) / 2)`:

* the lower range `F γ N ^ (δ - 1) < |α| ≤ F γ N ^ δ'` is proved here from the lab's
  existing statement `theorem2` of `State1539`, Theorem 2 of the paper, through the proved
  dyadic transport of the block, the two proved comparisons of the range
  ends, and the proved comparison of the saving `exp(-κ (log M)^(3-2γ))` with `ℰ^(-1/3) / 8`;
* the upper range `F γ N ^ ((γ - 1) / 2) < |α| ≤ F γ N ^ δ` is the LEAF
  `leaf_fsm_large_alpha`.  It is empty when `δ ≤ (γ - 1) / 2`.  The paper never needs it,
  since its `δ` in Lemma 9 is small; the parent asks for every `δ < 1` because the assembly
  of `leaf_gap_core_split` chose `δ₀ = 1`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_gap_core

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Dyadic transport of the block, the passage from the paper's `[M, 2M]` in Theorem 2,
p. 354, to the block `(N/2, N]` of display (36), p. 368, with `M = N / 2`.  The two blocks
differ by the term `n = M` and by at most the one term `n = N` when `N` is odd, each of
modulus one.  Proved. -/
theorem leaf_fsm_dyadic_transport (γ α : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖ ≤ ‖expSumF γ α (N / 2)‖ + 2 := by
  set M := N / 2 with hM
  set f : ℕ → ℂ := fun n => eC (α * F γ n) with hf
  have h1 : M ≤ 2 * M := by omega
  have h2 : 2 * M ≤ N := by omega
  have hsplit : ∑ n ∈ Finset.Ioc M N, f n =
      ∑ n ∈ Finset.Ioc M (2 * M), f n + ∑ n ∈ Finset.Ioc (2 * M) N, f n :=
    (Finset.sum_Ioc_consecutive f h1 h2).symm
  have hicc : ∑ n ∈ Finset.Ioc M (2 * M), f n + f M = expSumF γ α M := by
    unfold expSumF
    exact Finset.sum_Ioc_add_eq_sum_Icc h1
  have hR : ‖∑ n ∈ Finset.Ioc (2 * M) N, f n‖ ≤ 1 := by
    calc ‖∑ n ∈ Finset.Ioc (2 * M) N, f n‖ ≤ ∑ n ∈ Finset.Ioc (2 * M) N, ‖f n‖ :=
          norm_sum_le _ _
      _ = (Finset.Ioc (2 * M) N).card := by simp [hf, norm_eC]
      _ ≤ 1 := by
          rw [Nat.card_Ioc]; exact_mod_cast (by omega : N - 2 * M ≤ 1)
  have hfM : ‖f M‖ = 1 := norm_eC _
  have heq : ∑ n ∈ Finset.Ioc M N, f n =
      expSumF γ α M - f M + ∑ n ∈ Finset.Ioc (2 * M) N, f n := by
    rw [hsplit, ← hicc]; ring
  show ‖∑ n ∈ Finset.Ioc M N, f n‖ ≤ _
  rw [heq]
  calc ‖expSumF γ α M - f M + ∑ n ∈ Finset.Ioc (2 * M) N, f n‖
      ≤ ‖expSumF γ α M - f M‖ + ‖∑ n ∈ Finset.Ioc (2 * M) N, f n‖ := norm_add_le _ _
    _ ≤ (‖expSumF γ α M‖ + ‖f M‖) + 1 := add_le_add (norm_sub_le _ _) hR
    _ = ‖expSumF γ α M‖ + 2 := by rw [hfM]; ring

/-- Eventually `θ log N ≤ log (N / 2)` for any `θ < 1`, with `N / 2` the natural floor. -/
private theorem log_half_ge (θ : ℝ) (hθ : θ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N ∧ θ * Real.log N ≤ Real.log ((N / 2 : ℕ) : ℝ) := by
  refine ⟨⌈Real.exp (Real.log 4 / (1 - θ))⌉₊ + 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  refine ⟨hN2, ?_⟩
  have h1θ : 0 < 1 - θ := by linarith
  have hNe : Real.exp (Real.log 4 / (1 - θ)) ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp (Real.log 4 / (1 - θ)))
    have h' : (⌈Real.exp (Real.log 4 / (1 - θ))⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log 4 / (1 - θ) ≤ Real.log N := by
    rw [← Real.log_exp (Real.log 4 / (1 - θ))]
    exact Real.log_le_log (Real.exp_pos _) hNe
  have hlog4 : Real.log 4 ≤ (1 - θ) * Real.log N := by
    rw [div_le_iff₀ h1θ] at hlogN; linarith
  have hM : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
    have : N ≤ 4 * (N / 2) := by omega
    have : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hlogM : Real.log ((N : ℝ) / 4) ≤ Real.log ((N / 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hM
  rw [Real.log_div hNpos.ne' (by norm_num)] at hlogM
  linarith

/-- For `1 < γ` and `0 ≤ a < b`, eventually `(log N) ^ γ * a ≤ (log (N / 2)) ^ γ * b`. -/
private theorem log_pow_half_compare (γ a b : ℝ) (hγ : 1 < γ) (ha : 0 ≤ a) (hb : a < b) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N ∧
      Real.log (N : ℝ) ^ γ * a ≤ Real.log ((N / 2 : ℕ) : ℝ) ^ γ * b := by
  have hbpos : 0 < b := lt_of_le_of_lt ha hb
  have hγpos : 0 < γ := by linarith
  set θ : ℝ := 1 - (b - a) / (2 * γ * b) with hθ
  have hd : 0 < (b - a) / (2 * γ * b) := div_pos (by linarith) (by positivity)
  have hd1 : (b - a) / (2 * γ * b) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hθ1 : θ < 1 := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  obtain ⟨N₀, hN₀⟩ := log_half_ge θ hθ1
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hN2, hlog⟩ := hN₀ N hN
  refine ⟨hN2, ?_⟩
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hbern : 1 + γ * (θ - 1) ≤ (1 + (θ - 1)) ^ γ :=
    one_add_mul_self_le_rpow_one_add (by linarith) hγ.le
  have hθγ : a ≤ b * θ ^ γ := by
    have h' : (1 + (θ - 1)) = θ := by ring
    rw [h'] at hbern
    have hk : γ * (θ - 1) = -((b - a) / (2 * b)) := by
      rw [hθ]; field_simp; ring
    rw [hk] at hbern
    have : b * (1 - (b - a) / (2 * b)) = (b + a) / 2 := by field_simp; ring
    nlinarith
  have hpow : (θ * Real.log N) ^ γ ≤ Real.log ((N / 2 : ℕ) : ℝ) ^ γ :=
    Real.rpow_le_rpow (mul_nonneg hθ0 hlogN0) hlog hγpos.le
  rw [Real.mul_rpow hθ0 hlogN0] at hpow
  have hLγ : 0 ≤ Real.log (N : ℝ) ^ γ := Real.rpow_nonneg hlogN0 γ
  nlinarith [mul_le_mul_of_nonneg_left hθγ hLγ]

/-- The lower end of the range of Theorem 2, p. 354.  For `1 < γ`, `0 < δ < 1` and
`1 - δ < c`, eventually `F(2M) ^ (-c) ≤ F(N) ^ (δ - 1)` with `M = N / 2`, because
`log F(2M) / log F(N) = (log 2M / log N) ^ γ` tends to one.  Proved. -/
theorem leaf_fsm_low_end (γ δ c : ℝ) (hγ : 1 < γ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hc : 1 - δ < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      F γ (2 * ((N / 2 : ℕ) : ℝ)) ^ (-c) ≤ F γ N ^ (δ - 1) := by
  obtain ⟨N₀, hN₀⟩ := log_pow_half_compare γ (1 - δ) c hγ (by linarith) hc
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hN2, hcmp⟩ := hN₀ N hN
  have hM1 : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N / 2)
  have hlogM0 : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) := Real.log_nonneg hM1
  have hlog2M : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log (2 * ((N / 2 : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hpow : Real.log ((N / 2 : ℕ) : ℝ) ^ γ ≤ Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ :=
    Real.rpow_le_rpow hlogM0 hlog2M (by linarith)
  have hc0 : 0 < c := by linarith
  have key : Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ * (-c) ≤ Real.log (N : ℝ) ^ γ * (δ - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hpow hc0.le]
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  rw [← Real.exp_mul, ← Real.exp_mul]
  exact Real.exp_le_exp.mpr key

/-- The upper end of the range of Theorem 2, p. 354.  For `1 < γ` and `0 ≤ δ < C`,
eventually `F(N) ^ δ ≤ F(M) ^ C` with `M = N / 2`.  Proved. -/
theorem leaf_fsm_high_end (γ δ C : ℝ) (hγ : 1 < γ) (hδ : 0 ≤ δ) (hC : δ < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → F γ N ^ δ ≤ F γ ((N / 2 : ℕ) : ℝ) ^ C := by
  obtain ⟨N₀, hN₀⟩ := log_pow_half_compare γ δ C hγ hδ hC
  refine ⟨N₀, fun N hN => ?_⟩
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  rw [← Real.exp_mul, ← Real.exp_mul]
  exact Real.exp_le_exp.mpr (hN₀ N hN).2

/-- The saving of Theorem 2, p. 354, against the threshold of Lemma 9, p. 368.  For
`1 < γ < 3/2`, `0 < κ ≤ 1` and any `B`, eventually, for every `0 < κ' ≤ κ`,
`B M exp(-κ (log M)^(3-2γ)) + 2 ≤ N ℰ^(-1/3) / 8` with `M = N / 2` and `ℰ` taken at `κ'`.
This holds since `(log M)^(3-2γ) / (log N)^(3-2γ)` tends to one, `(log N)^(3-2γ)` tends to
infinity, and `κ' / 3 < κ`.  Proved. -/
theorem leaf_fsm_saving (γ κ B : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2) (hκ : 0 < κ)
    (hκ₁ : κ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ κ' : ℝ, 0 < κ' → κ' ≤ κ →
      B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) + 2
        ≤ (N : ℝ) * calE γ κ' N ^ (-(1 / 3 : ℝ)) / 8 := by
  set g : ℝ := 3 - 2 * γ with hg
  have hg0 : 0 < g := by linarith
  have hg1 : g ≤ 1 := by linarith
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set A : ℝ := max (max 1 (3 / 2 * Real.log 32)) (((6 / κ) * Real.log (8 * B' + 1)) ^ g⁻¹)
    with hA
  obtain ⟨N₁, hN₁⟩ := log_half_ge (1 / 2) (by norm_num)
  refine ⟨N₁ + ⌈Real.exp A⌉₊ + 2, ?_⟩
  intro N hN κ' hκ' hκ'le
  obtain ⟨hN2, hhalf⟩ := hN₁ N (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNA : Real.exp A ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp A)
    have h' : (⌈Real.exp A⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hlogA : A ≤ Real.log N := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hNA
  set lN := Real.log (N : ℝ) with hlN
  set lM := Real.log ((N / 2 : ℕ) : ℝ) with hlM
  have hA1 : 1 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA32 : 3 / 2 * Real.log 32 ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAT : ((6 / κ) * Real.log (8 * B' + 1)) ^ g⁻¹ ≤ A := le_max_right _ _
  have hlN1 : 1 ≤ lN := le_trans hA1 hlogA
  have hlN0 : 0 ≤ lN := by linarith
  have hlM0 : 0 ≤ lM := le_trans (by nlinarith) hhalf
  set L := lN ^ g with hL
  set LM := lM ^ g with hLM
  have hL0 : 0 ≤ L := Real.rpow_nonneg hlN0 g
  -- LM ≥ L / 2
  have hLM : L / 2 ≤ LM := by
    have h1 : (1 / 2 * lN) ^ g ≤ LM := Real.rpow_le_rpow (by positivity) hhalf hg0.le
    rw [Real.mul_rpow (by norm_num) hlN0] at h1
    have h2 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ g :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hg1
    rw [Real.rpow_one] at h2
    nlinarith
  -- L ≤ lN
  have hLle : L ≤ lN := by
    have := Real.rpow_le_rpow_of_exponent_le hlN1 hg1
    rwa [Real.rpow_one] at this
  -- L ≥ (6/κ) log(8B'+1)
  have hlog8 : 0 ≤ Real.log (8 * B' + 1) := Real.log_nonneg (by linarith)
  have hLT : (6 / κ) * Real.log (8 * B' + 1) ≤ L := by
    have hT0 : 0 ≤ (6 / κ) * Real.log (8 * B' + 1) := by positivity
    have h1 : (((6 / κ) * Real.log (8 * B' + 1)) ^ g⁻¹) ^ g ≤ L :=
      Real.rpow_le_rpow (Real.rpow_nonneg hT0 _) (le_trans hAT hlogA) hg0.le
    rwa [Real.rpow_inv_rpow hT0 hg0.ne'] at h1
  have hexp6 : 8 * B' + 1 ≤ Real.exp (κ * L / 6) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < 8 * B' + 1)]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hLT hκ.le
    have h6 : κ * ((6 / κ) * Real.log (8 * B' + 1)) = 6 * Real.log (8 * B' + 1) := by
      field_simp
    nlinarith
  -- the right side
  have hcal : calE γ κ' N ^ (-(1 / 3 : ℝ)) = Real.exp (-(κ' * L) / 3) := by
    unfold calE
    rw [← Real.exp_mul]; congr 1; rw [hL, hlN]; ring
  set E3 := Real.exp (-(κ * L) / 3) with hE3
  have hRHS : E3 ≤ calE γ κ' N ^ (-(1 / 3 : ℝ)) := by
    rw [hcal]; apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hκ'le hL0
    linarith
  -- first term
  have hM : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    have : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
    have : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hM0 : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE1 : Real.exp (-κ * LM) ≤ E3 * Real.exp (-(κ * L / 6)) := by
    rw [hE3, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith
  have hE6 : (8 * B' + 1) * Real.exp (-(κ * L / 6)) ≤ 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]; linarith
  have hE3pos : 0 < E3 := Real.exp_pos _
  have hterm1 : B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κ * LM) ≤ (N : ℝ) * E3 / 16 := by
    have hx : 0 ≤ Real.exp (-(κ * L / 6)) := (Real.exp_pos _).le
    have hB1 : B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κ * LM)
        ≤ B' * ((N : ℝ) / 2) * (E3 * Real.exp (-(κ * L / 6))) := by
      have h1 : B * ((N / 2 : ℕ) : ℝ) ≤ B' * ((N : ℝ) / 2) :=
        le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
          (mul_le_mul_of_nonneg_left hM hB'0)
      calc B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κ * LM)
          ≤ B' * ((N : ℝ) / 2) * Real.exp (-κ * LM) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hE1 (by positivity)
    have hB2 : B' * Real.exp (-(κ * L / 6)) ≤ 1 / 8 := by nlinarith
    calc B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κ * LM)
        ≤ B' * ((N : ℝ) / 2) * (E3 * Real.exp (-(κ * L / 6))) := hB1
      _ = ((N : ℝ) * E3 / 2) * (B' * Real.exp (-(κ * L / 6))) := by ring
      _ ≤ ((N : ℝ) * E3 / 2) * (1 / 8) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
      _ = (N : ℝ) * E3 / 16 := by ring
  -- second term
  have hterm2 : 2 ≤ (N : ℝ) * E3 / 16 := by
    have hE3' : Real.exp (-lN / 3) ≤ E3 := by
      rw [hE3]; apply Real.exp_le_exp.mpr
      have : κ * L ≤ lN := by nlinarith
      linarith
    have hNe : (N : ℝ) = Real.exp lN := (Real.exp_log hNpos).symm
    have h32 : (32 : ℝ) ≤ (N : ℝ) * Real.exp (-lN / 3) := by
      rw [hNe, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      apply Real.exp_le_exp.mpr
      have := le_trans hA32 hlogA
      linarith
    have := mul_le_mul_of_nonneg_left hE3' hNpos.le
    linarith
  have hfin : (N : ℝ) * E3 / 8 ≤ (N : ℝ) * calE γ κ' N ^ (-(1 / 3 : ℝ)) / 8 := by
    have := mul_le_mul_of_nonneg_left hRHS hNpos.le
    linarith
  linarith

/-- LEAF: the full exponential sum in the range beyond Theorem 2.  For `1 < γ < 3/2` and
`0 < δ < 1`, if `F γ N ^ ((γ - 1) / 2) < |α| ≤ F γ N ^ δ` then
`‖Σ_{N/2 < n ≤ N} e(α F(n))‖ ≤ N ℰ ^ (-1/3) / 8`, uniformly in every sufficiently small `κ`.
This is the part of the parent that lies outside the range `C < γ - 1` of Theorem 2,
p. 354, and of Karacuba's Lemma 10, p. 370; it is empty for `δ ≤ (γ - 1) / 2`, and the
paper's Lemma 9 never uses it.  HARD: an exponential sum estimate for large `α`. -/
private theorem leaf_fsm_large_alpha_range_empty (γ δ : ℝ) (hγ₁ : 1 < γ)
    (hδ : δ ≤ (γ - 1) / 2) {N : ℕ} (hN : 2 ≤ N) {α : ℝ}
    (hlo : F γ N ^ ((γ - 1) / 2) < |α|) (hhi : |α| ≤ F γ N ^ δ) : False := by
  have hN1 : (1 : ℝ) ≤ N := by
    have hN1n : 1 ≤ N := by omega
    exact_mod_cast hN1n
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hpow0 : 0 ≤ Real.log (N : ℝ) ^ γ := Real.rpow_nonneg hlogN0 γ
  have hF1 : 1 ≤ F γ N := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    exact Real.one_le_exp hpow0
  have hmono : F γ N ^ δ ≤ F γ N ^ ((γ - 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hF1 hδ
  have hα : |α| ≤ F γ N ^ ((γ - 1) / 2) := hhi.trans hmono
  exact (not_lt_of_ge hα) hlo

theorem leaf_fsm_large_alpha (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        F γ N ^ ((γ - 1) / 2) < |α| → |α| ≤ F γ N ^ δ →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
          ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 3 : ℝ)) / 8 := by
  by_cases hδ : δ ≤ (γ - 1) / 2
  · refine ⟨1, one_pos, ?_⟩
    intro κ hκ hκle
    refine ⟨2, ?_⟩
    intro N hN α hlo hhi
    exact False.elim (leaf_fsm_large_alpha_range_empty γ δ hγ₁ hδ hN hlo hhi)
  · by_cases hδC : δ < γ - 1
    · set C : ℝ := (δ + (γ - 1)) / 2 with hC
      have hC0 : 0 < C := by
        unfold C
        linarith
      have hCγ : C < γ - 1 := by
        unfold C
        linarith
      have hδC' : δ < C := by
        unfold C
        linarith
      obtain ⟨κT, B, hκT, hT⟩ := theorem2 γ hγ₁ hγ₂ (1 / 2) C
        (by norm_num) (by norm_num) hC0 hCγ
      set κ₁ : ℝ := min κT 1 with hκ₁
      have hκ₁pos : 0 < κ₁ := lt_min hκT one_pos
      refine ⟨1, one_pos, ?_⟩
      intro κ hκ hκle
      obtain ⟨N₁, hN₁⟩ := leaf_fsm_high_end γ δ C hγ₁ hδ₀ hδC'
      obtain ⟨N₂, hN₂⟩ := leaf_fsm_saving γ κ₁ (max B 0) hγ₁ hγ₂ hκ₁pos
        (min_le_right _ _)
      refine ⟨N₁ + N₂ + 2, ?_⟩
      intro N hN α hlo hhi
      have hN2 : 2 ≤ N := by omega
      have hM1 : 1 ≤ N / 2 := by omega
      have hF2 : 1 ≤ F γ (2 * ((N / 2 : ℕ) : ℝ)) := by
        unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
        apply Real.one_le_exp
        apply Real.rpow_nonneg
        apply Real.log_nonneg
        have hM1r : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hM1
        linarith
      have hlow1 : 1 ≤ F γ N ^ ((γ - 1) / 2) := by
        unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
        rw [← Real.exp_mul]
        apply Real.one_le_exp
        have hpow0 : 0 ≤ Real.log (N : ℝ) ^ γ := by
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN2
          exact hN1r
        positivity
      have hαgt1 : 1 < |α| := lt_of_lt_of_le hlo hlow1
      have hα1 : F γ (2 * ((N / 2 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ |α| := by
        have hpow0 : 0 ≤ Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ := by
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          have hM1r : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hM1
          linarith
        unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
        rw [← Real.exp_mul]
        have he : Real.exp (Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ * (-(1 / 2 : ℝ))) ≤ 1 := by
          apply Real.exp_le_one.mpr
          nlinarith
        simpa only [neg_mul, mul_comm] using he
      have hα2 : |α| ≤ F γ ((N / 2 : ℕ) : ℝ) ^ C :=
        hhi.trans (hN₁ N (by omega))
      have hTb := hT (N / 2) hM1 α hα1 hα2
      have hL : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ) := by
        apply Real.rpow_nonneg
        apply Real.log_nonneg
        exact_mod_cast hM1
      have hM0 : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hexp : Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
          ≤ Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
        apply Real.exp_le_exp.mpr
        have hκ₁le : κ₁ ≤ κT := min_le_left _ _
        nlinarith
      have hB : B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
          ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
              Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
        have h1 : B * ((N / 2 : ℕ) : ℝ) ≤ max B 0 * ((N / 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
        have h2 : 0 ≤ max B 0 * ((N / 2 : ℕ) : ℝ) := mul_nonneg (le_max_right _ _) hM0
        calc B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
            ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
                Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp h2
      have hS := hN₂ N (by omega) κ hκ
        (le_trans hκle (min_le_right _ _))
      have hD := leaf_fsm_dyadic_transport γ α N
      have hTb' : ‖expSumF γ α (N / 2)‖ ≤ B * ((N / 2 : ℕ) : ℝ) *
          Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
        simpa using hTb
      linarith
    · sorry

/-- `leaf_full_sum_minor_arc` from Theorem 2 of the paper, the proved dyadic transport, range comparisons and saving comparison, and the
large range leaf. -/
theorem leaf_full_sum_minor_arc_split (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        F γ N ^ (δ - 1) < |α| → |α| ≤ F γ N ^ δ →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
          ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 3 : ℝ)) / 8 := by
  set δ' : ℝ := min δ ((γ - 1) / 2) with hδ'
  have hγ1 : 0 < γ - 1 := by linarith
  have hδ'0 : 0 ≤ δ' := le_min hδ₀.le (by linarith)
  have hδ'C : δ' < 3 * (γ - 1) / 4 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨κT, B, hκT, hT⟩ := theorem2 γ hγ₁ hγ₂ (1 - δ / 2) (3 * (γ - 1) / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  set κ₁ : ℝ := min κT 1 with hκ₁
  have hκ₁pos : 0 < κ₁ := lt_min hκT one_pos
  obtain ⟨κ₂, hκ₂pos, hlarge⟩ := leaf_fsm_large_alpha γ δ hγ₁ hγ₂ hδ₀ hδ₁
  refine ⟨min κ₁ κ₂, lt_min hκ₁pos hκ₂pos, ?_⟩
  intro κ hκ hκle
  obtain ⟨N₁, hN₁⟩ := hlarge κ hκ (le_trans hκle (min_le_right _ _))
  obtain ⟨N₂, hN₂⟩ := leaf_fsm_low_end γ δ (1 - δ / 2) hγ₁ hδ₀ hδ₁ (by linarith)
  obtain ⟨N₃, hN₃⟩ := leaf_fsm_high_end γ δ' (3 * (γ - 1) / 4) hγ₁ hδ'0 hδ'C
  obtain ⟨N₄, hN₄⟩ := leaf_fsm_saving γ κ₁ (max B 0) hγ₁ hγ₂ hκ₁pos (min_le_right _ _)
  refine ⟨N₁ + N₂ + N₃ + N₄ + 2, ?_⟩
  intro N hN α hlow hhigh
  by_cases hcase : |α| ≤ F γ N ^ δ'
  · -- the range of Theorem 2
    have hM1 : 1 ≤ N / 2 := by omega
    have hα1 : F γ (2 * ((N / 2 : ℕ) : ℝ)) ^ (-(1 - δ / 2)) ≤ |α| :=
      le_trans (hN₂ N (by omega)) hlow.le
    have hα2 : |α| ≤ F γ ((N / 2 : ℕ) : ℝ) ^ (3 * (γ - 1) / 4) :=
      le_trans hcase (hN₃ N (by omega))
    have hTb := hT (N / 2) hM1 α hα1 hα2
    have hL : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ) := by
      apply Real.rpow_nonneg
      apply Real.log_nonneg
      exact_mod_cast hM1
    have hM0 : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
        ≤ Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      apply Real.exp_le_exp.mpr
      have : κ₁ ≤ κT := min_le_left _ _
      nlinarith
    have hB : B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
        ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
            Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      have h1 : B * ((N / 2 : ℕ) : ℝ) ≤ max B 0 * ((N / 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
      have h2 : 0 ≤ max B 0 * ((N / 2 : ℕ) : ℝ) := mul_nonneg (le_max_right _ _) hM0
      calc B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
          ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
              Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp h2
    have hS := hN₄ N (by omega) κ hκ (le_trans hκle (min_le_left _ _))
    have hD := leaf_fsm_dyadic_transport γ α N
    have hTb' : ‖expSumF γ α (N / 2)‖ ≤ B * ((N / 2 : ℕ) : ℝ) *
        Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      simpa using hTb
    linarith
  · -- the range beyond Theorem 2
    push_neg at hcase
    rcases le_total δ ((γ - 1) / 2) with hle | hle
    · exfalso
      have : δ' = δ := min_eq_left hle
      rw [this] at hcase
      linarith
    · have : δ' = (γ - 1) / 2 := min_eq_right hle
      rw [this] at hcase
      exact hN₁ N (by omega) α hcase hhigh

end LeanLab.ExceptionalSet.U1539

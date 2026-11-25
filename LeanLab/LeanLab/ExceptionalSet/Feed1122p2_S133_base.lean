import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_high_j0_off_lattice_block_small

/-!
Burst burst-20261122, session S133, wave 13, proving the HARD leaves. Split of `Decomp553b.leaf_high_j0_parity_expansion` of `SPLIT_feed1122_leaf_high_j0_off_lattice_block_small.lean`.

Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst.
Fourier 48 (1998), section 7 page 370, the proof of Lemma 9, displays 40 and 41, and
Theorem 2 on page 354 with its proof from Karacuba's Lemma 10 on page 370.

Every split theorem below has the statement of its parent verbatim, checked by `type_of%`, and
its proof uses only these new leaves:
* `leaf_parity_detector_S133base`, MEDIUM: display 40 in majorant form, a statement about one real
  variable. The indicator of `[x]` even has a trigonometric approximant of period `2` and degree
  `H` with bounded coefficients, whose error is majorized by a real trigonometric polynomial of
  period `1` with mean at most `C/H`. Selberg's polynomials give it with `C = 2`, Vaaler, Bull.
  Amer. Math. Soc. 12 (1985), Theorem 6; Montgomery, Ten Lectures, chapter 1.
Everything else is proved here: the expansion of the parity condition, the truncation at
`H = ⌈ℰ⌉`, the coverage of the integer frequencies `1 ≤ k ≤ H` and of the shifts by Theorem 2,
and the absorption of every constant into `ℰ^(-5/6)` or `ℰ^(-2)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF: P0082 page 370, display 40, the smoothed periodic detector of the parity of `[x]`,
in majorant form. Class MEDIUM. There is `C` such that for every `H ≥ 1` there are coefficients
`a h`, `|h| ≤ H`, and `q₀`, `b k`, `1 ≤ k ≤ H`, all bounded by `C`, with `q₀ ≤ C / H`, such that
for every real `x` the indicator of `[x]` even differs from
`P(x) = Σ_{|h| ≤ H} a h e(-h x / 2)` by at most `q₀ + Re Σ_{1 ≤ k ≤ H} b k e(k x)`.
Selberg's polynomials for the interval `[0, 1/2)` modulo `1` in the variable `x/2` give this
with `C = 2`: their difference is `(F_H(x/2) + F_H(x/2 - 1/2))/(H + 1)` with `F_H` the Fejér
kernel, which contains only the even frequencies, Vaaler 1985 Theorem 6. -/
theorem leaf_parity_detector_S133base :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re := by
  sorry

namespace Feed1122p2S133base

/-- `M ≤ s (log N)^p` for all large `N`, when `p > 0` and `s > 0`. Proved. -/
theorem eventually_le_log_rpow (p s M : ℝ) (hp : 0 < p) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → M ≤ s * Real.log N ^ p := by
  have tL : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ p) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (tL.eventually_ge_atTop (M / s))
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  rw [div_le_iff₀ hs] at this
  linarith

/-- `F(N)^r = exp(r (log N)^γ)`. -/
theorem F_rpow (γ r : ℝ) (N : ℕ) : F γ N ^ r = Real.exp (r * Real.log N ^ γ) := by
  rw [LeanLab.ExceptionalSet.BrudernPerelli1998.F, ← Real.exp_mul]; ring_nf

/-- `ℰ^r = exp(r κ (log N)^(3 - 2γ))`. -/
theorem calE_rpow (γ κ r : ℝ) (N : ℕ) :
    calE γ κ N ^ r = Real.exp (r * (κ * Real.log N ^ (3 - 2 * γ))) := by
  rw [LeanLab.ExceptionalSet.U1539.calE, ← Real.exp_mul]; ring_nf

/-- The bookkeeping of the reduction, proved. Given Theorem 2 on sub-blocks, for a fixed
sub-block `(u N, v N]` of `(N/2, N]`, a lower range `F(N)^(δ - 1) < |β|` and an upper range
`|β| ≤ m ℰ^p` or `|β| ≤ m X^δ`, the bound `N ℰ^(-q)` holds for small `κ`. Here the upper range is
encoded by its logarithm `log m + w` with `w ≤ (C'/2) (log N)^γ`. -/
theorem reduce (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (u v : ℕ → ℕ)
    (hu : ∀ N, N / 2 ≤ u N) (hv : ∀ N, v N ≤ N)
    (hT : ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ u v : ℕ, N / 2 ≤ u → v ≤ N →
        ∀ α : ℝ, F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' →
          ‖∑ n ∈ Finset.Ioc u v, eC (α * F γ n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
    (q : ℝ) (hq : 0 < q) (hq2 : q ≤ 2) (m : ℝ) (hm : 0 < m)
    (W : ℝ → ℝ → ℕ → ℝ)
    (hW : ∀ δ κ, 0 < δ → δ < (γ - 1) / 4 → 0 < κ → κ ≤ (γ - 1) / 16 → ∀ N : ℕ, 3 ≤ N →
      W δ κ N ≤ ((γ - 1) / 4) * Real.log N ^ γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
          F γ N ^ (δ - 1) < |β| → |β| ≤ m * Real.exp (W δ κ N) →
            ‖∑ n ∈ Finset.Ioc (u N) (v N), eC (β * F γ n)‖ ≤
              (N : ℝ) * calE γ κ N ^ (-q) := by
  have hγ : 0 < γ - 1 := by linarith
  refine ⟨(γ - 1) / 4, by linarith, fun δ hδ hδ0 => ?_⟩
  have hδ1 : δ < 1 := by linarith
  set C' : ℝ := (γ - 1) / 2 with hC'
  obtain ⟨κ', A, hκ', hA, hB⟩ := hT (1 - δ) C' (by linarith) (by linarith) (by linarith)
    (by linarith)
  refine ⟨min (κ' / 4) ((γ - 1) / 16), lt_min (by linarith) (by linarith),
    fun κ hκ hκ0 => ?_⟩
  have hκa : κ ≤ κ' / 4 := hκ0.trans (min_le_left _ _)
  have hκb : κ ≤ (γ - 1) / 16 := hκ0.trans (min_le_right _ _)
  obtain ⟨Na, hNa⟩ := eventually_le_log_rpow (3 - 2 * γ) (κ' / 2) (Real.log (max A 1))
    (by linarith) (by linarith)
  obtain ⟨Nb, hNb⟩ := eventually_le_log_rpow γ ((γ - 1) / 4) (Real.log m)
    (by linarith) (by linarith)
  refine ⟨max (max Na Nb) 3, fun N hN β hlo hhi => ?_⟩
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  set L : ℝ := Real.log N ^ (3 - 2 * γ) with hLdef
  have hL : 0 ≤ L := Real.rpow_nonneg hL0 _
  set G : ℝ := Real.log N ^ γ with hGdef
  -- lower range
  have hlow : F γ N ^ (-(1 - δ)) ≤ |β| := by
    have : (-(1 - δ)) = δ - 1 := by ring
    rw [this]; exact hlo.le
  -- upper range
  have hup : |β| ≤ F γ N ^ C' := by
    refine hhi.trans ?_
    rw [F_rpow]
    have hw := hW δ κ hδ hδ0 hκ hκb N hN2
    have hmm := hNb N hNb'
    calc m * Real.exp (W δ κ N) = Real.exp (Real.log m + W δ κ N) := by
          rw [Real.exp_add, Real.exp_log hm]
      _ ≤ Real.exp (C' * G) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hC']; linarith
  have hmain := hB N (by omega) (u N) (v N) (hu N) (hv N) β hlow hup
  refine hmain.trans ?_
  -- absorption
  have hA1 : A ≤ Real.exp ((κ' / 2) * L) := by
    have h := hNa N hNa'
    calc A ≤ max A 1 := le_max_left _ _
      _ = Real.exp (Real.log (max A 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ Real.exp ((κ' / 2) * L) := Real.exp_le_exp.mpr h
  rw [calE_rpow]
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc A * N * Real.exp (-κ' * L) ≤ Real.exp ((κ' / 2) * L) * N * Real.exp (-κ' * L) := by
        gcongr
    _ = N * Real.exp (-(κ' / 2) * L) := by
        rw [mul_comm (Real.exp _) (N : ℝ), mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ N * Real.exp (-q * (κ * L)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hNn
        have : q * κ ≤ κ' / 2 := by nlinarith
        nlinarith

/-- `1 ≤ log N` for `N ≥ 3`. -/
theorem one_le_log {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The upper range `X^δ`, proved. -/
theorem W_F (γ : ℝ) (h1 : 1 < γ) : ∀ δ κ : ℝ, 0 < δ → δ < (γ - 1) / 4 → 0 < κ →
    κ ≤ (γ - 1) / 16 → ∀ N : ℕ, 3 ≤ N → δ * Real.log N ^ γ ≤ ((γ - 1) / 4) * Real.log N ^ γ := by
  intro δ κ _ hδ _ _ N hN
  exact mul_le_mul_of_nonneg_right hδ.le
    (Real.rpow_nonneg (by linarith [one_le_log hN]) _)

/-- The upper range `ℰ^p`, `p ≤ 2`, proved. -/
theorem W_E (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∀ δ κ : ℝ, 0 < δ → δ < (γ - 1) / 4 → 0 < κ →
    κ ≤ (γ - 1) / 16 → ∀ N : ℕ, 3 ≤ N →
      p * (κ * Real.log N ^ (3 - 2 * γ)) ≤ ((γ - 1) / 4) * Real.log N ^ γ := by
  intro δ κ _ _ hκ hκb N hN
  have hl := one_le_log hN
  have hLG : Real.log N ^ (3 - 2 * γ) ≤ Real.log N ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  have hL0 : 0 ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  have hpk : p * κ ≤ (γ - 1) / 4 := by nlinarith
  have hpk0 : 0 ≤ p * κ := by positivity
  calc p * (κ * Real.log N ^ (3 - 2 * γ)) = (p * κ) * Real.log N ^ (3 - 2 * γ) := by ring
    _ ≤ (p * κ) * Real.log N ^ γ := mul_le_mul_of_nonneg_left hLG hpk0
    _ ≤ ((γ - 1) / 4) * Real.log N ^ γ :=
        mul_le_mul_of_nonneg_right hpk (by linarith [hL0, hLG])

/-- The upper block `(3N/4, N]` as a filter of `(N/2, N]`. -/
theorem upper_block (N : ℕ) :
    (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4) = Finset.Ioc (3 * N / 4) N := by
  ext n; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega

/-- The lower block `(N/2, 3N/4]` as a filter of `(N/2, N]`. -/
theorem lower_block (N : ℕ) :
    (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) = Finset.Ioc (N / 2) (3 * N / 4) := by
  ext n; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega

end Feed1122p2S133base

namespace Feed1122p2S133base

/-- `e(a + b) = e(a) e(b)`. -/
theorem eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  simp only [eC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `‖e(x)‖ = 1`. -/
theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  simp only [eC]
  rw [show (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The detector inserted into a block sum, proved, P0082 page 370 displays 40 and 41: for the
even parity of `[x n]` on any finite block `B` with at most `N` elements. -/
theorem parity_even_of_detector
    (hdet : ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset ℕ) (x : ℕ → ℝ) (N H : ℕ), B.card ≤ N → 1 ≤ H → ∀ t : ℝ,
      ‖∑ n ∈ B.filter (fun n => Even ⌊x n⌋), eC (t * x n)‖ ≤
        C * ((N : ℝ) / H +
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ +
          ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖) := by
  obtain ⟨C, hC, hD⟩ := hdet
  refine ⟨C, hC, fun B x N H hcard hH t => ?_⟩
  obtain ⟨a, q₀, b, ha, hq0, hq, hb, hx⟩ := hD H hH
  set ind : ℕ → ℂ := fun n => if Even ⌊x n⌋ then (1 : ℂ) else 0 with hinddef
  set P : ℕ → ℂ := fun n =>
    ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x n) with hPdef
  have hphase : ∑ n ∈ B.filter (fun n => Even ⌊x n⌋), eC (t * x n) =
      ∑ n ∈ B, ind n * eC (t * x n) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hinddef]
    split_ifs <;> simp
  have hsplit : ∑ n ∈ B, ind n * eC (t * x n) =
      ∑ n ∈ B, (ind n - P n) * eC (t * x n) + ∑ n ∈ B, P n * eC (t * x n) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  have hmain : ∑ n ∈ B, P n * eC (t * x n) =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * ∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n) := by
    simp only [hPdef, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_assoc, ← eC_add]
    congr 2
    ring
  have hmain_le : ‖∑ n ∈ B, P n * eC (t * x n)‖ ≤
      C * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ := by
    rw [hmain, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ha h) (norm_nonneg _)
  have herr_pt : ∀ n ∈ B, ‖(ind n - P n) * eC (t * x n)‖ ≤
      q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x n)).re := by
    intro n _
    rw [norm_mul, norm_eC, mul_one]
    exact hx (x n)
  have herr : ‖∑ n ∈ B, (ind n - P n) * eC (t * x n)‖ ≤
      B.card * q₀ + ∑ k ∈ Finset.Icc (1 : ℕ) H, C * ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum herr_pt).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    refine add_le_add le_rfl ?_
    rw [← Complex.re_sum, Finset.sum_comm]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k _ => ?_)))
    rw [← Finset.mul_sum, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)
  have hcard' : (B.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hq' : (B.card : ℝ) * q₀ ≤ C * ((N : ℝ) / H) := by
    calc (B.card : ℝ) * q₀ ≤ N * (C / H) :=
          mul_le_mul hcard' hq hq0 (Nat.cast_nonneg _)
      _ = C * ((N : ℝ) / H) := by ring
  rw [hphase, hsplit]
  refine (norm_add_le _ _).trans ?_
  have e1 := herr
  rw [← Finset.mul_sum] at e1
  have e2 := hmain_le
  nlinarith [e1, e2, hq']

/-- Both parities, proved: the odd parity is the full block minus the even parity, and the
full block is the term `h = 0` of the shifted sums. -/
theorem parity_of_detector
    (hdet : ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ), (j = 0 ∨ j = 1) →
      ∀ (B : Finset ℕ) (x : ℕ → ℝ) (N H : ℕ), B.card ≤ N → 1 ≤ H → ∀ t : ℝ,
      ‖∑ n ∈ B.filter (fun n => Even (⌊x n⌋ + j)), eC (t * x n)‖ ≤
        C * ((N : ℝ) / H +
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ +
          ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖) := by
  obtain ⟨C, hC, hE⟩ := parity_even_of_detector hdet
  refine ⟨C + 1, by linarith, fun j hj B x N H hcard hH t => ?_⟩
  set R : ℝ := (N : ℝ) / H +
    ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ +
    ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ with hRdef
  have hE' := hE B x N H hcard hH t
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have : (0 : ℝ) ≤ (N : ℝ) / H := by positivity
    have h2 : 0 ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h3 : 0 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  rcases hj with rfl | rfl
  · simp only [add_zero]
    calc _ ≤ C * R := hE'
      _ ≤ (C + 1) * R := by nlinarith
  · -- the full block is the `h = 0` term
    have h0 : ‖∑ n ∈ B, eC (t * x n)‖ ≤
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ := by
      have hmem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by
        rw [Finset.mem_Icc]; constructor <;> omega
      have := Finset.single_le_sum (f := fun h : ℤ => ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖)
        (fun _ _ => norm_nonneg _) hmem
      simpa using this
    have hsplit : ∑ n ∈ B.filter (fun n => Even (⌊x n⌋ + 1)), eC (t * x n) =
        ∑ n ∈ B, eC (t * x n) - ∑ n ∈ B.filter (fun n => Even ⌊x n⌋), eC (t * x n) := by
      rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not B (fun n => Even ⌊x n⌋),
        add_comm]
      congr 1
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext n
      simp only [Finset.mem_filter, Int.even_add_one]
    rw [hsplit]
    have hR1 : ‖∑ n ∈ B, eC (t * x n)‖ ≤ R := by
      rw [hRdef]
      have : (0 : ℝ) ≤ (N : ℝ) / H := by positivity
      have h3 : 0 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      linarith
    calc _ ≤ ‖∑ n ∈ B, eC (t * x n)‖ +
          ‖∑ n ∈ B.filter (fun n => Even ⌊x n⌋), eC (t * x n)‖ := norm_sub_le _ _
      _ ≤ R + C * R := add_le_add hR1 hE'
      _ = (C + 1) * R := by ring

end Feed1122p2S133base

namespace Feed1122p2S133base

/-- The parity filtered block phase is small once every shifted sum and every integer frequency
sum up to `2 ℰ` is at most `N ℰ^(-2)`, with `ℰ = exp u`. Proved bookkeeping of P0082 page 370,
the last paragraph of section 7, with the truncation `H = ⌈ℰ⌉`. -/
theorem parity_absorb (Cd : ℝ) (hCd : 0 < Cd)
    (hP : ∀ (j : ℤ), (j = 0 ∨ j = 1) →
      ∀ (B : Finset ℕ) (x : ℕ → ℝ) (N H : ℕ), B.card ≤ N → 1 ≤ H → ∀ t : ℝ,
      ‖∑ n ∈ B.filter (fun n => Even (⌊x n⌋ + j)), eC (t * x n)‖ ≤
        Cd * ((N : ℝ) / H +
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ +
          ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖))
    (j : ℤ) (hj : j = 0 ∨ j = 1) (B : Finset ℕ) (x : ℕ → ℝ) (N : ℕ) (hB : B.card ≤ N)
    (t u : ℝ) (hu : 0 ≤ u) (hK : 8 * Cd ≤ Real.exp (u / 6))
    (hshift : ∀ h : ℤ, (|h| : ℝ) ≤ 2 * Real.exp u →
      ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ ≤ N * Real.exp (-2 * u))
    (hint : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 2 * Real.exp u →
      ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ ≤ N * Real.exp (-2 * u)) :
    ‖∑ n ∈ B.filter (fun n => Even (⌊x n⌋ + j)), eC (t * x n)‖ ≤
      N * Real.exp (-(5 / 6) * u) := by
  set e : ℝ := Real.exp u with hedef
  have he1 : 1 ≤ e := Real.one_le_exp hu
  have hepos : 0 < e := Real.exp_pos u
  set H : ℕ := ⌈e⌉₊ with hHdef
  have hHge : e ≤ (H : ℝ) := Nat.le_ceil _
  have hHle : (H : ℝ) ≤ e + 1 := (Nat.ceil_lt_add_one hepos.le).le
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := le_trans he1 hHge
    exact_mod_cast this
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
  set m : ℝ := Real.exp (-u) with hmdef
  have hm0 : 0 < m := Real.exp_pos _
  have hme : m * e = 1 := by rw [hmdef, hedef, ← Real.exp_add]; simp
  have hm2 : Real.exp (-2 * u) = m * m := by
    rw [hmdef, ← Real.exp_add]; ring_nf
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set X : ℝ := (N : ℝ) * Real.exp (-2 * u) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hS1 : ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ ≤
      (2 * (H : ℝ) + 1) * X := by
    have hb : ∀ h ∈ Finset.Icc (-(H : ℤ)) H,
        ‖∑ n ∈ B, eC ((t - (h : ℝ) / 2) * x n)‖ ≤ X := by
      intro h hh
      rw [Finset.mem_Icc] at hh
      refine hshift h ?_
      have : |h| ≤ (H : ℤ) := abs_le.mpr hh
      have : (|h| : ℝ) ≤ H := by exact_mod_cast this
      linarith
    refine (Finset.sum_le_card_nsmul _ _ X hb).trans ?_
    rw [nsmul_eq_mul, Int.card_Icc]
    have h' : ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
    rw [h']; push_cast; exact le_rfl
  have hS2 : ∑ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ ≤ (H : ℝ) * X := by
    have hb : ∀ k ∈ Finset.Icc (1 : ℕ) H, ‖∑ n ∈ B, eC ((k : ℝ) * x n)‖ ≤ X := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      refine hint k hk.1 ?_
      have : (k : ℝ) ≤ H := by exact_mod_cast hk.2
      linarith
    refine (Finset.sum_le_card_nsmul _ _ X hb).trans ?_
    rw [nsmul_eq_mul, Nat.card_Icc]; simp
  have hmain := hP j hj B x N H hB hH1 t
  have hNH : (N : ℝ) / H ≤ N * m := by
    rw [div_le_iff₀ hHpos]
    have : (N : ℝ) * m * e ≤ N * m * H := mul_le_mul_of_nonneg_left hHge (by positivity)
    have h' : (N : ℝ) * m * e = N := by rw [mul_assoc, hme, mul_one]
    linarith
  have hX : (3 * (H : ℝ) + 1) * X ≤ 7 * N * m := by
    have h7 : 3 * (H : ℝ) + 1 ≤ 7 * e := by linarith
    calc (3 * (H : ℝ) + 1) * X ≤ (7 * e) * X := mul_le_mul_of_nonneg_right h7 hX0
      _ = 7 * N * m * (m * e) := by rw [hXdef, hm2]; ring
      _ = 7 * N * m := by rw [hme, mul_one]
  have hrhs : Real.exp (-(5 / 6) * u) = Real.exp (u / 6) * m := by
    rw [hmdef, ← Real.exp_add]; ring_nf
  rw [hrhs]
  calc _ ≤ Cd * ((N : ℝ) / H + (2 * (H : ℝ) + 1) * X + (H : ℝ) * X) := by
        refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hCd.le)
        linarith
    _ ≤ Cd * (8 * (N * m)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCd.le
        nlinarith
    _ = (8 * Cd) * (N * m) := by ring
    _ ≤ Real.exp (u / 6) * (N * m) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = N * (Real.exp (u / 6) * m) := by ring

end Feed1122p2S133base

namespace Feed1122p2S133base

/-- The block phase with phase `x n - j` has the norm of the block phase with phase `x n`. -/
theorem blockPhase_shift_norm (s : Finset ℕ) (x : ℕ → ℝ) (j : ℤ) (t : ℝ) :
    ‖blockPhase s (fun n => x n - (j : ℝ)) t‖ = ‖∑ n ∈ s, eC (t * x n)‖ := by
  have : blockPhase s (fun n => x n - (j : ℝ)) t = (∑ n ∈ s, eC (t * x n)) * eC (-(t * j)) := by
    rw [blockPhase, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← eC_add]; congr 1; ring
  rw [this, norm_mul, norm_eC, mul_one]

/-- The parity condition and a block condition commute. -/
theorem filter_parity_comm (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (γ : ℝ) (j : ℤ) :
    (S.filter (fun n => Even (nu γ n + j))).filter p =
      (S.filter p).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + j)) := by
  ext n
  simp only [Finset.mem_filter]
  have hnu : nu γ n = ⌊F γ (n : ℝ)⌋ := rfl
  rw [hnu]
  tauto

/-- `2 ℰ ≤ ℰ^2` once `ℰ ≥ 2`, and `2 ℰ ≤ X^δ` once `κ ≤ δ/2` and `N` is large. -/
theorem two_E_le_F (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₁ : ℕ, ∀ κ : ℝ, 0 < κ → κ ≤ δ / 2 → ∀ N : ℕ, N₁ ≤ N →
      2 * calE γ κ N ≤ F γ N ^ δ := by
  obtain ⟨Na, hNa⟩ := eventually_le_log_rpow γ (δ / 2) (Real.log 2) (by linarith) (by linarith)
  refine ⟨max Na 3, fun κ hκ hκδ N hN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hl := one_le_log hN3
  have hLG : Real.log N ^ (3 - 2 * γ) ≤ Real.log N ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  have hL0 : 0 ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  have h2' := hNa N (le_trans (le_max_left _ _) hN)
  rw [F_rpow, LeanLab.ExceptionalSet.U1539.calE]
  calc 2 * Real.exp (κ * Real.log N ^ (3 - 2 * γ))
      = Real.exp (Real.log 2 + κ * Real.log N ^ (3 - 2 * γ)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (δ * Real.log N ^ γ) := by
        refine Real.exp_le_exp.mpr ?_
        have : κ * Real.log N ^ (3 - 2 * γ) ≤ (δ / 2) * Real.log N ^ γ :=
          mul_le_mul hκδ hLG hL0 (by linarith)
        linarith

/-- The common analytic core of the parity leaves, proved from the detector and the sub-block
Theorem 2: if every shifted sum `S(t - h/2)`, `|h| ≤ 2 ℰ`, over the block is at most `N ℰ^(-2)`,
then the parity filtered block phase is at most `N ℰ^(-5/6)`. P0082 page 370. -/
theorem parity_core (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (u v : ℕ → ℕ)
    (hu : ∀ N, N / 2 ≤ u N) (hv : ∀ N, v N ≤ N)
    (hT : ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ u v : ℕ, N / 2 ≤ u → v ≤ N →
        ∀ α : ℝ, F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' →
          ‖∑ n ∈ Finset.Ioc u v, eC (α * F γ n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
    (hdet : ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re)
    (j : ℤ) (hj : j = 0 ∨ j = 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
          (∀ h : ℤ, (|h| : ℝ) ≤ 2 * calE γ κ N →
            ‖∑ n ∈ Finset.Ioc (u N) (v N), eC ((t - (h : ℝ) / 2) * F γ n)‖ ≤
              (N : ℝ) * calE γ κ N ^ (-2 : ℝ)) →
          ‖∑ n ∈ (Finset.Ioc (u N) (v N)).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + j)),
              eC (t * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-(5 / 6) : ℝ) := by
  obtain ⟨Cd, hCd, hP⟩ := parity_of_detector hdet
  obtain ⟨δ₀, hδ₀, R⟩ := reduce γ h1 h2 u v hu hv hT 2 (by norm_num) le_rfl 2 (by norm_num)
    (fun _ κ N => 1 * (κ * Real.log N ^ (3 - 2 * γ)))
    (W_E γ h1 h2 1 (by norm_num) (by norm_num))
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ hδl => ?_⟩
  obtain ⟨κ₀, hκ₀, R2⟩ := R δ hδ (hδl.trans_le (min_le_left _ _))
  have hδ1 : δ < 1 := hδl.trans_le (min_le_right _ _)
  refine ⟨κ₀, hκ₀, fun κ hκ hκl => ?_⟩
  obtain ⟨N₁, R3⟩ := R2 κ hκ hκl
  obtain ⟨N₂, hN₂⟩ := eventually_le_log_rpow (3 - 2 * γ) (κ / 6) (Real.log (max (8 * Cd) 1))
    (by linarith) (by linarith)
  refine ⟨max (max N₁ N₂) 3, fun N hN t hshift => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hl := one_le_log hN3
  set L : ℝ := Real.log N ^ (3 - 2 * γ) with hLdef
  have hL0 : 0 ≤ L := Real.rpow_nonneg (by linarith) _
  have hE : calE γ κ N = Real.exp (κ * L) := rfl
  have hcard : ((Finset.Ioc (u N) (v N))).card ≤ N := by
    rw [Nat.card_Ioc]; have := hv N; omega
  have hK : 8 * Cd ≤ Real.exp (κ * L / 6) := by
    have h := hN₂ N hN2
    calc 8 * Cd ≤ max (8 * Cd) 1 := le_max_left _ _
      _ = Real.exp (Real.log (max (8 * Cd) 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ Real.exp (κ * L / 6) := Real.exp_le_exp.mpr (by rw [hLdef]; linarith)
  have hF1 : F γ N ^ (δ - 1) < 1 := by
    have hF : 1 < F γ N := by
      rw [LeanLab.ExceptionalSet.BrudernPerelli1998.F]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (Real.rpow_pos_of_pos (by linarith) _)
    exact Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  have key := parity_absorb Cd hCd hP j hj (Finset.Ioc (u N) (v N)) (fun n => F γ n) N hcard t
    (κ * L) (by positivity) hK ?_ ?_
  · rw [calE_rpow, ← hLdef]
    exact key
  · intro h hh
    have := hshift h (by rw [hE]; exact hh)
    rw [calE_rpow, ← hLdef] at this
    exact this
  · intro k hk1 hk2
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have := R3 N hN1 (k : ℝ) (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [abs_of_nonneg (by linarith)]; simpa [hLdef] using hk2)
    rw [calE_rpow, ← hLdef] at this
    exact this

end Feed1122p2S133base

/-- `leaf_high_j0_parity_expansion`, statement verbatim, from the detector leaf
`leaf_parity_detector_S133base` through the proved `Feed1122p2S133base.parity_of_detector`. -/
theorem leaf_high_j0_parity_expansion_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N H : ℕ, 1 ≤ H → ∀ t : ℝ,
      ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) t‖ ≤
        C * ((N : ℝ) / H +
          ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
            ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((t - (h : ℝ) / 2) * F γ n)‖ +
          ∑ k ∈ Finset.Icc (1 : ℕ) H,
            ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((k : ℝ) * F γ n)‖) := by
  obtain ⟨C, hC, hP⟩ := Feed1122p2S133base.parity_of_detector leaf_parity_detector_S133base
  refine ⟨C, hC, fun N H hH t => ?_⟩
  rw [Feed1122p2S133base.blockPhase_shift_norm (indices_high_j0 γ N) (fun n => F γ n) 0 t,
    indices_high_j0, Feed1122p2S133base.filter_parity_comm, Feed1122p2S133base.upper_block]
  have hcard : (Finset.Ioc (3 * N / 4) N).card ≤ N := by rw [Nat.card_Ioc]; omega
  exact hP 0 (Or.inl rfl) (Finset.Ioc (3 * N / 4) N) (fun n => F γ n) N H hcard hH t

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_high_j0_parity_expansion_split =
    type_of% @leaf_high_j0_parity_expansion := rfl

#print axioms Feed1122p2S133base.parity_core
#print axioms Feed1122p2S133base.reduce
#print axioms Feed1122p2S133base.parity_absorb

end LeanLab.ExceptionalSet.Decomp553b

import LeanLab.ExceptionalSet.Feed1122_high_j0_off_lattice_block_small

/-!
Burst burst-20261122, session S133, wave 13, proving the HARD leaves. Split of `leaf_feed1122_high_j0_full_block_small` and `leaf_feed1122_high_j0_twisted_block_small` of `Feed1122_high_j0_off_lattice_block_small.lean`.

Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst.
Fourier 48 (1998), section 7 page 370, the proof of Lemma 9, displays 40 and 41, and
Theorem 2 on page 354 with its proof from Karacuba's Lemma 10 on page 370.

Every split theorem below has the statement of its parent verbatim, checked by `type_of%`, and
its proof uses only these new leaves:
* `leaf_parity_detector_S133w3`, MEDIUM: display 40 in majorant form, a statement about one real
  variable. The indicator of `[x]` even has a trigonometric approximant of period `2` and degree
  `H` with bounded coefficients, whose error is majorized by a real trigonometric polynomial of
  period `1` with mean at most `C/H`. Selberg's polynomials give it with `C = 2`, Vaaler, Bull.
  Amer. Math. Soc. 12 (1985), Theorem 6; Montgomery, Ten Lectures, chapter 1.
* `leaf_theorem2_subblock_S133w3`, HARD, cited: Theorem 2 of page 354 for the plain sum over any
  sub-interval of `(N/2, N]`, with no `δ`, `κ` or `ℰ` in it. The library form `U1539.Theorem2`
  covers only `[N, 2N]`, and `U1539.Lemma10` only `(N, 2N]`.
Everything else is proved here: the expansion of the parity condition, the truncation at
`H = ⌈ℰ⌉`, the coverage of the integer frequencies `1 ≤ k ≤ H` and of the shifts by Theorem 2,
and the absorption of every constant into `ℰ^(-5/6)` or `ℰ^(-2)`. A leaf not used by a split
of this file is still stated once, so that every branch of this wave carries the same two
leaves under its own suffix.

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
theorem leaf_parity_detector_S133w3 :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re := by
  sorry

/-- LEAF: P0082 Theorem 2 on page 354, from Karacuba's Lemma 10 on page 370, in the
sub-block form used on page 370 after display 41. Class HARD, a cited analytic theorem.
For `1 < γ < 3/2`, `0 < c < 1` and `0 < C' < γ - 1` there are `κ' > 0` and `A ≥ 0` such that
for every `N ≥ 1`, every sub-interval `(u, v]` of `(N/2, N]` and every `α` with
`F(N)^(-c) ≤ |α| ≤ F(N)^C'`, the sum `Σ_{u < n ≤ v} e(α F(n))` is at most
`A N exp(-κ' (log N)^(3 - 2γ))`. -/
theorem leaf_theorem2_subblock_S133w3 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ u v : ℕ, N / 2 ≤ u → v ≤ N →
        ∀ α : ℝ, F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' →
          ‖∑ n ∈ Finset.Ioc u v, eC (α * F γ n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := by
  sorry

namespace Feed1122p2S133w3

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

end Feed1122p2S133w3

namespace Feed1122p2S133w3

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

end Feed1122p2S133w3

namespace Feed1122p2S133w3

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

end Feed1122p2S133w3

namespace Feed1122p2S133w3

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

end Feed1122p2S133w3

/-- `leaf_feed1122_high_j0_full_block_small`, statement verbatim, from the sub-block Theorem 2
leaf `leaf_theorem2_subblock_S133w3` and the proved bookkeeping `Feed1122p2S133w3.reduce`: the strip
condition at `h = 0` gives `X^(δ-1) < |b - a|`, and the odd domain gives `|b - a| ≤ 2 ℰ`. -/
theorem leaf_feed1122_high_j0_full_block_small_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖∑ n ∈ feed1122_highFull N, eC ((b - a) * F γ n)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, H⟩ := Feed1122p2S133w3.reduce γ h1 h2 (fun N => 3 * N / 4) (fun N => N)
    (fun N => by omega) (fun N => le_rfl) (leaf_theorem2_subblock_S133w3 γ h1 h2) (5 / 6)
    (by norm_num) (by norm_num) 2 (by norm_num)
    (fun _ κ N => 1 * (κ * Real.log N ^ (3 - 2 * γ)))
    (Feed1122p2S133w3.W_E γ h1 h2 1 (by norm_num) (by norm_num))
  refine ⟨δ₀, hδ₀, fun δ hδ hδl => ?_⟩
  obtain ⟨κ₀, hκ₀, K⟩ := H δ hδ hδl
  refine ⟨κ₀, hκ₀, fun κ hκ hκl => ?_⟩
  obtain ⟨N₀, hN⟩ := K κ hκ hκl
  refine ⟨N₀, fun N hN0 a ha b hb hoff => ?_⟩
  have hE1 : 1 ≤ calE γ κ N := by
    rw [LeanLab.ExceptionalSet.U1539.calE]
    exact Real.one_le_exp (mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
  have hE23 : calE γ κ N ^ (2 / 3 : ℝ) ≤ calE γ κ N := by
    have := Real.rpow_le_rpow_of_exponent_le hE1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    simpa using this
  have hba : |b - a| ≤ 2 * calE γ κ N := by
    simp only [oddDomain, Set.mem_inter_iff, Set.mem_Icc] at ha hb
    rw [abs_le]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  have h0 := hoff 0 (by simp; positivity)
  simp only [Int.cast_zero, zero_div, sub_zero] at h0
  rw [feed1122_highFull, Feed1122p2S133w3.upper_block]
  refine hN N hN0 (b - a) h0 ?_
  simp only [one_mul]
  exact hba

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_feed1122_high_j0_full_block_small_split =
    type_of% @leaf_feed1122_high_j0_full_block_small := rfl

/-- `leaf_feed1122_high_j0_twisted_block_small`, statement verbatim, from the detector leaf
`leaf_parity_detector_S133w3` and the sub-block Theorem 2 leaf `leaf_theorem2_subblock_S133w3`. The
twist `(-1)^ν` is the even parity sum minus the odd parity sum, P0082 page 370 display 41; each
is bounded by the proved `Feed1122p2S133w3.parity_core` at the scale `2κ`, so with `ℰ^2` in place of
`ℰ`. The shifts with `|h| ≤ ℰ^(3/4)` are off the strips by hypothesis, the larger ones because
`|b - a| ≤ 2 ℰ^(2/3)`; the two bounds `N ℰ^(-5/3)` add up to at most `N ℰ^(-5/6)`. -/
theorem leaf_feed1122_high_j0_twisted_block_small_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖∑ n ∈ feed1122_highFull N, eC ((b - a) * F γ n) * (-1 : ℂ) ^ (nu γ n)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨d0, hd0, P0⟩ := Feed1122p2S133w3.parity_core γ h1 h2 (fun N => 3 * N / 4) (fun N => N)
    (fun N => by omega) (fun N => le_rfl) (leaf_theorem2_subblock_S133w3 γ h1 h2)
    leaf_parity_detector_S133w3 0 (Or.inl rfl)
  obtain ⟨d1, hd1, P1⟩ := Feed1122p2S133w3.parity_core γ h1 h2 (fun N => 3 * N / 4) (fun N => N)
    (fun N => by omega) (fun N => le_rfl) (leaf_theorem2_subblock_S133w3 γ h1 h2)
    leaf_parity_detector_S133w3 1 (Or.inr rfl)
  obtain ⟨dR, hdR, R⟩ := Feed1122p2S133w3.reduce γ h1 h2 (fun N => 3 * N / 4) (fun N => N)
    (fun N => by omega) (fun N => le_rfl) (leaf_theorem2_subblock_S133w3 γ h1 h2) 2 (by norm_num)
    le_rfl 3 (by norm_num) (fun _ κ N => 1 * (κ * Real.log N ^ (3 - 2 * γ)))
    (Feed1122p2S133w3.W_E γ h1 h2 1 (by norm_num) (by norm_num))
  refine ⟨min (min d0 d1) (min dR 1), lt_min (lt_min hd0 hd1) (lt_min hdR one_pos),
    fun δ hδ hδl => ?_⟩
  have hδ0 : δ < d0 := lt_of_lt_of_le hδl ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ < d1 := lt_of_lt_of_le hδl ((min_le_left _ _).trans (min_le_right _ _))
  have hδR : δ < dR := lt_of_lt_of_le hδl ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1' : δ < 1 := lt_of_lt_of_le hδl ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨k0, hk0, Q0⟩ := P0 δ hδ hδ0
  obtain ⟨k1, hk1, Q1⟩ := P1 δ hδ hδ1
  obtain ⟨kR, hkR, QR⟩ := R δ hδ hδR
  refine ⟨min (min k0 k1) kR / 2, by positivity, fun κ hκ hκl => ?_⟩
  have hκ2 : 0 < 2 * κ := by linarith
  have m1 := min_le_left (min k0 k1) kR
  have m2 := min_le_right (min k0 k1) kR
  have m3 := min_le_left k0 k1
  have m4 := min_le_right k0 k1
  obtain ⟨M0, S0⟩ := Q0 (2 * κ) hκ2 (by linarith)
  obtain ⟨M1, S1⟩ := Q1 (2 * κ) hκ2 (by linarith)
  obtain ⟨MR, SR⟩ := QR (2 * κ) hκ2 (by linarith)
  obtain ⟨M2, hM2⟩ := Feed1122p2S133w3.eventually_le_log_rpow (3 - 2 * γ) (κ / 12) (Real.log 6)
    (by linarith) (by linarith)
  refine ⟨max (max (max M0 M1) MR) (max M2 3), fun N hN a ha b hb hoff => ?_⟩
  have hN0 : M0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hN
  have hN1 : M1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hN
  have hNR : MR ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : M2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hl := Feed1122p2S133w3.one_le_log hN3
  have hL0 : 0 ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  set u : ℝ := κ * Real.log N ^ (3 - 2 * γ) with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu12 : Real.log 6 ≤ u / 12 := by
    have := hM2 N hN2; rw [hudef]; linarith
  have h6 : 6 ≤ Real.exp (u / 12) := by
    calc (6 : ℝ) = Real.exp (Real.log 6) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (u / 12) := Real.exp_le_exp.mpr hu12
  have r34 : calE γ κ N ^ (3 / 4 : ℝ) = Real.exp ((3 / 4) * u) := by
    rw [Feed1122p2S133w3.calE_rpow]
  have r23 : calE γ κ N ^ (2 / 3 : ℝ) = Real.exp ((2 / 3) * u) := by
    rw [Feed1122p2S133w3.calE_rpow]
  have hx1 : 1 ≤ Real.exp ((2 / 3) * u) := Real.one_le_exp (by positivity)
  have e3 : 6 * Real.exp ((2 / 3) * u) ≤ Real.exp ((3 / 4) * u) := by
    have : Real.exp ((3 / 4) * u) = Real.exp (u / 12) * Real.exp ((2 / 3) * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; exact mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
  have e4 : Real.exp ((2 / 3) * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have hba : |b - a| ≤ 2 * Real.exp ((2 / 3) * u) := by
    simp only [oddDomain, Set.mem_inter_iff, Set.mem_Icc] at ha hb
    rw [r23] at ha hb
    rw [abs_le]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  have hF1 : F γ N ^ (δ - 1) < 1 := by
    have hF : 1 < F γ N := by
      rw [LeanLab.ExceptionalSet.BrudernPerelli1998.F, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (Real.rpow_pos_of_pos (by linarith) _)
    exact Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  have hE2 : calE γ (2 * κ) N = Real.exp (2 * u) := by
    rw [LeanLab.ExceptionalSet.U1539.calE, hudef]; ring_nf
  have hshift : ∀ h : ℤ, (|h| : ℝ) ≤ 2 * calE γ (2 * κ) N →
      ‖∑ n ∈ Finset.Ioc (3 * N / 4) N, eC (((b - a) - (h : ℝ) / 2) * F γ n)‖ ≤
        (N : ℝ) * calE γ (2 * κ) N ^ (-2 : ℝ) := by
    intro h hh
    have hcast : (|h| : ℝ) = |(h : ℝ)| := by simp [Int.cast_abs]
    have hh2 : |(h : ℝ) / 2| = |(h : ℝ)| / 2 := by rw [abs_div, abs_two]
    have htri : |(h : ℝ) / 2| ≤ |b - a| + |(b - a) - (h : ℝ) / 2| := by
      calc |(h : ℝ) / 2| = |(b - a) - ((b - a) - (h : ℝ) / 2)| := by ring_nf
        _ ≤ |b - a| + |(b - a) - (h : ℝ) / 2| := abs_sub _ _
    have htri2 : |(b - a) - (h : ℝ) / 2| ≤ |b - a| + |(h : ℝ) / 2| := abs_sub _ _
    refine SR N hNR ((b - a) - (h : ℝ) / 2) ?_ ?_
    · by_cases hs : (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ)
      · exact hoff h hs
      · rw [not_le, r34] at hs
        rw [hcast] at hs
        have : 1 ≤ |(b - a) - (h : ℝ) / 2| := by linarith
        linarith
    · show |(b - a) - (h : ℝ) / 2| ≤ 3 * Real.exp (1 * ((2 * κ) * Real.log N ^ (3 - 2 * γ)))
      have hW : 1 * ((2 * κ) * Real.log N ^ (3 - 2 * γ)) = 2 * u := by rw [hudef]; ring
      rw [hW]
      rw [hE2, hcast] at hh
      linarith
  have hev := S0 N hN0 (b - a) (fun h hh => hshift h hh)
  have hod := S1 N hN1 (b - a) (fun h hh => hshift h hh)
  rw [feed1122_highFull, Feed1122p2S133w3.upper_block]
  have hodd : (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => ¬ Even (⌊F γ (n : ℝ)⌋ + 0)) =
      (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 1)) := by
    ext n; simp only [Finset.mem_filter, add_zero, Int.even_add_one]
  have hid : ∑ n ∈ Finset.Ioc (3 * N / 4) N, eC ((b - a) * F γ n) * (-1 : ℂ) ^ (nu γ n) =
      ∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 0)),
        eC ((b - a) * F γ n) -
      ∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 1)),
        eC ((b - a) * F γ n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc (3 * N / 4) N)
      (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 0)), hodd]
    have hX : ∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 0)),
        eC ((b - a) * F γ n) * (-1 : ℂ) ^ (nu γ n) =
        ∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 0)),
          eC ((b - a) * F γ n) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_filter, add_zero] at hn
      have hnu : nu γ n = ⌊F γ (n : ℝ)⌋ := rfl
      rw [hnu, hn.2.neg_one_zpow, mul_one]
    have hY : ∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 1)),
        eC ((b - a) * F γ n) * (-1 : ℂ) ^ (nu γ n) =
        -∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 1)),
          eC ((b - a) * F γ n) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_filter, Int.even_add_one, Int.not_even_iff_odd] at hn
      have hnu : nu γ n = ⌊F γ (n : ℝ)⌋ := rfl
      rw [hnu, hn.2.neg_one_zpow]; ring
    rw [hX, hY]; ring
  rw [hid]
  have hc1 : calE γ (2 * κ) N ^ (-(5 / 6) : ℝ) = Real.exp (-(5 / 6) * (2 * u)) := by
    rw [hE2, ← Real.exp_mul]; ring_nf
  have hc2 : calE γ κ N ^ (-(5 / 6 : ℝ)) = Real.exp (-(5 / 6) * u) := by
    rw [Feed1122p2S133w3.calE_rpow]
  rw [hc1] at hev hod
  rw [hc2]
  have hfin : 2 * Real.exp (-(5 / 6) * (2 * u)) ≤ Real.exp (-(5 / 6) * u) := by
    have hsplit : Real.exp (-(5 / 6) * u) = Real.exp ((5 / 6) * u) * Real.exp (-(5 / 6) * (2 * u)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have h2 : 2 ≤ Real.exp ((5 / 6) * u) := by
      have : Real.exp (u / 12) ≤ Real.exp ((5 / 6) * u) := Real.exp_le_exp.mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc _ ≤ ‖∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 0)),
        eC ((b - a) * F γ n)‖ +
      ‖∑ n ∈ (Finset.Ioc (3 * N / 4) N).filter (fun n : ℕ => Even (⌊F γ (n : ℝ)⌋ + 1)),
        eC ((b - a) * F γ n)‖ := norm_sub_le _ _
    _ ≤ (N : ℝ) * Real.exp (-(5 / 6) * (2 * u)) + (N : ℝ) * Real.exp (-(5 / 6) * (2 * u)) :=
        add_le_add hev hod
    _ = (N : ℝ) * (2 * Real.exp (-(5 / 6) * (2 * u))) := by ring
    _ ≤ (N : ℝ) * Real.exp (-(5 / 6) * u) := mul_le_mul_of_nonneg_left hfin hNn

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_feed1122_high_j0_twisted_block_small_split =
    type_of% @leaf_feed1122_high_j0_twisted_block_small := rfl

#print axioms Feed1122p2S133w3.parity_core
#print axioms Feed1122p2S133w3.reduce
#print axioms Feed1122p2S133w3.parity_absorb

end LeanLab.ExceptionalSet.Decomp553b

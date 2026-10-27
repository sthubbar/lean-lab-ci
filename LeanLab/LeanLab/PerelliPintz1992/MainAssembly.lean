/-
P0070 Perelli-Pintz 1992: the Theorem, p. 356, assembled from (6) and (7), p. 359.

* `Estimate6Wide`: (6) for block starts `0 ≤ V < N/2`, which the paper's "clearly sufficient
  to prove the case `H = N^{1/2+ε}`", p. 358, needs, since blocks of `[V, V + H]` start up to
  `V + H < N/2`.
* `Estimate7Wide`: (7) uniformly for every real `ξ`, which the reduction by (5) needs, since
  `𝔪 ⊆ (1/Q, 1 + 1/Q]` reaches past 1; see QUESTION Q-P0070-7 in STATEMENTS.md.
* `mainTheorem_of_wide`: `Estimate6Wide → Estimate7Wide → MainTheorem`. So the Theorem is
  CONDITIONAL ON these two cited estimates only; every other step is proved, through
  `main_explicit`.

Helpers: `eventually_logpow_le`, `majorArcs_subset`, `psi0_le`, `block_bound`,
`kRange_subset_blocks`.

KNOWN mathematics. AI-written Lean code, Claude, PC run 20261020T0603Z-352, unit U-1178.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.MainExplicit

namespace LeanLab.PerelliPintz1992
open Real ArithmeticFunction MeasureTheory Set Filter

/-- (6) for block starts `V < N/2`. -/
def Estimate6Wide : Prop :=
  ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N V : ℕ,
    N0 ≤ N → (V : ℝ) < N / 2 →
    ∑ k ∈ (Finset.Icc V (V + ⌊(N : ℝ) ^ (1 / 2 + ε)⌋₊)).filter (1 ≤ ·),
      ‖(∫ α in majorArcs N A, ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤
      C * (N : ℝ) ^ (1 / 2 + ε) * N ^ 2 / L N ^ A

/-- (7) uniformly for every real `ξ`. -/
def Estimate7Wide : Prop :=
  ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N : ℕ,
    N0 ≤ N → ∀ ξ : ℝ,
    ∫ α in Set.Ioo (ξ - 1 / (N : ℝ) ^ (1 / 2 + ε)) (ξ + 1 / (N : ℝ) ^ (1 / 2 + ε)) ∩
        minorArcs N A, ‖S N α‖ ^ 2 ≤ C * N / L N ^ (A + 1)

/-- The wide forms imply the printed forms. -/
lemma estimate6_of_wide (h : Estimate6Wide) : Estimate6 := by
  obtain ⟨ε1, hε1, h⟩ := h
  refine ⟨ε1, hε1, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, N0, hC⟩ := h ε hε hεε A hA
  exact ⟨C, N0, fun N V hN hV => hC N V hN (by linarith [show (0 : ℝ) ≤ N / 4 by positivity])⟩

lemma estimate7_of_wide (h : Estimate7Wide) : Estimate7 := by
  obtain ⟨ε1, hε1, h⟩ := h
  refine ⟨ε1, hε1, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, N0, hC⟩ := h ε hε hεε A hA
  exact ⟨C, N0, fun N hN ξ _ _ => hC N hN ξ⟩

/-- Any fixed power of `log N` is eventually at most `√N / 4`. -/
lemma eventually_logpow_le (P : ℝ) :
    ∀ᶠ N : ℕ in atTop, L N ^ P ≤ √(N : ℝ) / 4 := by
  have h := (isLittleO_log_rpow_rpow_atTop P (by norm_num : (0 : ℝ) < 1 / 2)).def
    (by norm_num : (0 : ℝ) < 1 / 4)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with N hN hN1
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl : 0 ≤ Real.log N := Real.log_nonneg hx
  simp only [Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hl _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hN
  unfold L; linarith

/-- For `N ≥ 16` with `L^B ≤ √N/4`, the major arcs lie in `(1/Q, 1 + 1/Q]`, `Q = N^{1/2}/2`. -/
lemma majorArcs_subset {N : ℕ} {A : ℝ} (hN : 16 ≤ N)
    (hLB : L N ^ Bexp A ≤ √(N : ℝ) / 4) :
    majorArcs N A ⊆ Ioc (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2))
      (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2) + 1) := by
  intro x hx
  simp only [majorArcs, mem_iUnion, mem_setOf_eq, mem_Ioo] at hx
  obtain ⟨q, ⟨hq1, hq2⟩, a, ⟨ha1, ha2, _⟩, hx1, hx2⟩ := hx
  have hN' : (16 : ℝ) ≤ N := by exact_mod_cast hN
  set s := √(N : ℝ) with hs
  have hss : s * s = N := Real.mul_self_sqrt (by linarith)
  have hs4 : 4 ≤ s := by
    rw [hs, show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN'
  have hrp : (N : ℝ) ^ (1 / 2 : ℝ) = s := by rw [hs, Real.sqrt_eq_rpow]
  rw [hrp]
  have hLpos : 0 < L N := by
    unfold L; exact Real.log_pos (by linarith)
  set u := L N ^ (Bexp A / 2) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hLpos.le _
  have huu : u * u = L N ^ Bexp A := by
    rw [hu, ← Real.rpow_add hLpos]; congr 1; ring
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha2' : (a : ℝ) ≤ q := by exact_mod_cast ha2
  have hqpos : (0 : ℝ) < q := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  set b := L N ^ Bexp A with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hLpos.le _
  have hqq : (q : ℝ) * q ≤ s / 4 := by
    have := mul_le_mul hq2 hq2 hqpos.le hu0
    linarith
  have hc : 1 / (s / 2) = 2 / s := by field_simp
  rw [hc]
  -- b / (q N) ≤ 1/(4 s q)
  have hbN : b / (q * N) ≤ 1 / (4 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [← hss]; nlinarith [hLB]
  constructor
  · -- 2/s < a/q - b/(qN)
    have h1 : (1 : ℝ) / q ≤ a / q := by
      rw [div_le_div_iff₀ hqpos hqpos]; nlinarith
    have h2 : 2 / s < 1 / q - 1 / (4 * s) := by
      rw [div_lt_iff₀ (by linarith)]
      have : (1 / q - 1 / (4 * s)) * s = s / q - 1 / 4 := by field_simp
      rw [this]
      rw [lt_sub_iff_add_lt, lt_div_iff₀ hqpos]
      nlinarith [hqq]
    have : 1 / (q : ℝ) * 1 ≤ 1 / (q : ℝ) * 1 := le_rfl
    linarith
  · -- a/q + b/(qN) ≤ 2/s + 1
    have h1 : (a : ℝ) / q ≤ 1 := by rw [div_le_one hqpos]; exact ha2'
    have h2 : 1 / (4 * s) ≤ 2 / s := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith

/-- `Ψ(N, 0) = Σ_{n=N}^{2N} Λ(n)² ≤ 8 N L²` for `N ≥ 2`. -/
lemma psi0_le {N : ℕ} (hN : 2 ≤ N) : Psi N 0 ≤ 8 * N * L N ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : Real.log (2 * N) ≤ 2 * Real.log N := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (N : ℝ) ^ (2 : ℝ) = N * N by norm_num [sq]]; nlinarith
  have hl0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hterm : ∀ m ∈ (Finset.Icc N (2 * N)).filter (fun m => m + 2 * 0 ≤ 2 * N),
      Λ m * Λ (m + 2 * 0) ≤ (2 * Real.log N) ^ 2 := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    simp only [mul_zero, add_zero]
    have hm1 : Λ m ≤ Real.log (2 * N) := by
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hm2 : (m : ℝ) ≤ 2 * N := by exact_mod_cast hm.1.2
      exact vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hm2)
    have h0 : 0 ≤ Λ m := vonMangoldt_nonneg
    nlinarith
  calc Psi N 0 ≤ ∑ m ∈ (Finset.Icc N (2 * N)).filter (fun m => m + 2 * 0 ≤ 2 * N),
        (2 * Real.log N) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ((N + 1 : ℕ) : ℝ) * (2 * Real.log N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have := Finset.card_filter_le (Finset.Icc N (2 * N)) (fun m => m + 2 * 0 ≤ 2 * N)
        rw [Nat.card_Icc] at this
        exact_mod_cast (by omega : _ ≤ N + 1)
    _ ≤ 8 * N * L N ^ 2 := by
        unfold L; push_cast; nlinarith [sq_nonneg (Real.log N)]

/-- The window integral over `𝔪 = (c, c+1] \ 𝔐` equals the one over the paper's
`minorArcs = (c, 1 + c) \ 𝔐`: the two sets differ by the point `c + 1`. -/
lemma window_congr (N : ℕ) (A ξ w : ℝ) :
    ∫ α in Ioo (ξ - w) (ξ + w) ∩ (Ioc (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2))
      (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2) + 1) \ majorArcs N A), ‖S N α‖ ^ 2 =
    ∫ α in Ioo (ξ - w) (ξ + w) ∩ minorArcs N A, ‖S N α‖ ^ 2 := by
  apply setIntegral_congr_set
  unfold minorArcs
  rw [add_comm (1 : ℝ) (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2))]
  exact Filter.EventuallyEqSet.inter (Filter.Eventually.of_forall fun _ => rfl)
    (Filter.EventuallyEqSet.diff (Ioo_ae_eq_Ioc (μ := volume)).symm
      (Filter.Eventually.of_forall fun _ => rfl))

/-- **One block of length `H₀ = ⌊N^{1/2+ε}⌋`.** With `A' = 2A + 5`, the bounds `C₆`, `C₇` of
(6) and (7) at level `A'`, and `N` large in the three explicit senses below:
`Σ_{k ∈ [V, V + H₀], k ≥ 1} |Ψ(N,2k) - 𝔖(2k)(N-2k)|² ≤ (640 C₇ + 32 + 2 C₆) N^{1/2+ε} N² L^{-A}`. -/
lemma block_bound {N V : ℕ} {ε A C6 C7 : ℝ} (hA : 0 < A) (hN : 16 ≤ N)
    (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7) (hL1 : 1 ≤ L N)
    (hLB : L N ^ Bexp (2 * A + 5) ≤ √(N : ℝ) / 4)
    (hδ : L N ^ (A + 4) ≤ (N : ℝ) ^ (1 / 2 + ε) / 2)
    (h6 : ∑ k ∈ (Finset.Icc V (V + ⌊(N : ℝ) ^ (1 / 2 + ε)⌋₊)).filter (1 ≤ ·),
      ‖(∫ α in majorArcs N (2 * A + 5), ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤
      C6 * (N : ℝ) ^ (1 / 2 + ε) * N ^ 2 / L N ^ (2 * A + 5))
    (h7 : ∀ ξ : ℝ,
      ∫ α in Set.Ioo (ξ - 1 / (N : ℝ) ^ (1 / 2 + ε)) (ξ + 1 / (N : ℝ) ^ (1 / 2 + ε)) ∩
        minorArcs N (2 * A + 5), ‖S N α‖ ^ 2 ≤ C7 * N / L N ^ (2 * A + 5 + 1)) :
    ∑ k ∈ kRange V ⌊(N : ℝ) ^ (1 / 2 + ε)⌋₊, err N k ^ 2 ≤
      (640 * C7 + 32 + 2 * C6) * ((N : ℝ) ^ (1 / 2 + ε) * N ^ 2 / L N ^ A) := by
  set h0 := (N : ℝ) ^ (1 / 2 + ε) with hh0
  set Lg := L N with hLg
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hLpos : 0 < Lg := by linarith
  have hh0pos : 0 < h0 := Real.rpow_pos_of_pos hNpos _
  set P := Lg ^ A with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hA.le
  have hPpos : 0 < P := by linarith
  have hA4 : Lg ^ (A + 4) = P * Lg ^ 4 := by
    rw [Real.rpow_add hLpos, hP]; norm_cast
  have hA5 : Lg ^ (2 * A + 5) = P * P * Lg ^ 5 := by
    rw [show 2 * A + 5 = A + A + 5 by ring, Real.rpow_add hLpos, Real.rpow_add hLpos, hP]
    norm_cast
  have hA6 : Lg ^ (2 * A + 5 + 1) = P * P * Lg ^ 6 := by
    rw [show 2 * A + 5 + 1 = A + A + 6 by ring, Real.rpow_add hLpos, Real.rpow_add hLpos, hP]
    norm_cast
  have hL4 : 1 ≤ Lg ^ 4 := one_le_pow₀ hL1
  have hL5 : 1 ≤ Lg ^ 5 := one_le_pow₀ hL1
  set δ := Lg ^ (A + 4) / h0 with hδdef
  set w := 1 / h0 with hwdef
  have hδpos : 0 < δ := div_pos (by rw [hA4]; positivity) hh0pos
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_iff₀ hh0pos]; linarith
  have hwpos : 0 < w := by positivity
  have hM := majorArcs_subset hN hLB
  set E6 := C6 * h0 * N ^ 2 / Lg ^ (2 * A + 5) with hE6
  set E7 := C7 * N / Lg ^ (2 * A + 5 + 1) with hE7
  have h7' : ∀ ξ : ℝ, ∫ α in Ioo (ξ - w) (ξ + w) ∩ (Ioc (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2))
      (1 / ((N : ℝ) ^ (1 / 2 : ℝ) / 2) + 1) \ majorArcs N (2 * A + 5)), ‖S N α‖ ^ 2 ≤ E7 := by
    intro ξ; rw [window_congr]; exact h7 ξ
  have hmain := main_explicit N V ⌊h0⌋₊ (2 * A + 5) _ δ w E6 E7 hδpos hδ2 hwpos hM h6 h7'
  refine hmain.trans ?_
  -- bounds on the pieces
  have hPsi : Psi N 0 ≤ 8 * N * Lg ^ 2 := psi0_le (N := N) (by omega)
  have hPsi0 : 0 ≤ Psi N 0 := Psi_nonneg N 0
  have hH0 : ((⌊h0⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * h0 := by
    have := Nat.floor_le hh0pos.le
    have h01 : 1 ≤ h0 := Real.one_le_rpow (by
      have : (16 : ℝ) ≤ N := by exact_mod_cast hN
      linarith) (by
      have : (0 : ℝ) ≤ ε ∨ ε < 0 := le_or_gt 0 ε
      -- 1/2 + ε ≥ 0 since h0 ≥ 2 L^{A+4} ≥ 2 forces it; argue directly
      by_contra hneg
      push_neg at hneg
      have : h0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by
        have : (16 : ℝ) ≤ N := by exact_mod_cast hN
        linarith) hneg
      have : 1 ≤ Lg ^ (A + 4) := by rw [hA4]; nlinarith
      linarith)
    linarith
  have hn : ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) ≤ 4 * (P * Lg ^ 4) := by
    have h2 : 2 * δ / w = 2 * (P * Lg ^ 4) := by
      rw [hδdef, hwdef, hA4]; field_simp
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * δ / w by positivity)
    push_cast
    rw [h2] at hc ⊢
    have : 1 ≤ P * Lg ^ 4 := one_le_mul_of_one_le_of_one_le hP1 hL4
    linarith
  have hE70 : 0 ≤ E7 := by positivity
  -- term 1
  have hprod : Psi N 0 * (((⌊h0⌋₊ : ℕ) : ℝ) + 1) * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) ≤
      (8 * N * Lg ^ 2) * (2 * h0) * (4 * (P * Lg ^ 4)) := by
    apply mul_le_mul (mul_le_mul hPsi hH0 (by positivity) (by positivity)) hn
      (by positivity) (by positivity)
  have hT1 : 2 * (Psi N 0 * ((((⌊h0⌋₊ : ℕ) : ℝ) + 1) * (5 * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) * E7))) ≤
      640 * C7 * (h0 * N ^ 2 / P) := by
    have heq : 2 * (Psi N 0 * ((((⌊h0⌋₊ : ℕ) : ℝ) + 1) * (5 * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) * E7)))
        = 10 * (Psi N 0 * (((⌊h0⌋₊ : ℕ) : ℝ) + 1) * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ)) * E7 := by ring
    rw [heq]
    calc 10 * (Psi N 0 * (((⌊h0⌋₊ : ℕ) : ℝ) + 1) * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ)) * E7
        ≤ 10 * ((8 * N * Lg ^ 2) * (2 * h0) * (4 * (P * Lg ^ 4))) * E7 := by gcongr
      _ = 640 * C7 * (h0 * N ^ 2 / P) := by
        rw [hE7, hA6]; field_simp; ring
  -- term 2
  have hT2 : 2 * (Psi N 0 * (Psi N 0 / (4 * δ))) ≤ 32 * (h0 * N ^ 2 / P) := by
    have hsq : Psi N 0 * Psi N 0 ≤ (8 * N * Lg ^ 2) * (8 * N * Lg ^ 2) :=
      mul_le_mul hPsi hPsi hPsi0 (by positivity)
    have heq : 2 * (Psi N 0 * (Psi N 0 / (4 * δ))) = (Psi N 0 * Psi N 0) / (2 * δ) := by
      field_simp; ring
    rw [heq, div_le_iff₀ (by positivity)]
    calc Psi N 0 * Psi N 0 ≤ (8 * N * Lg ^ 2) * (8 * N * Lg ^ 2) := hsq
      _ = 32 * (h0 * N ^ 2 / P) * (2 * δ) := by
        rw [hδdef, hA4]; field_simp; ring
  -- term 3
  have hT3 : 2 * E6 ≤ 2 * C6 * (h0 * N ^ 2 / P) := by
    rw [hE6, hA5]
    have : C6 * h0 * N ^ 2 / (P * P * Lg ^ 5) ≤ C6 * (h0 * N ^ 2 / P) := by
      rw [div_le_iff₀ (by positivity)]
      have hX : 0 ≤ C6 * (h0 * N ^ 2 / P) := by positivity
      have : 1 ≤ P * Lg ^ 5 := one_le_mul_of_one_le_of_one_le hP1 hL5
      calc C6 * h0 * N ^ 2 = C6 * (h0 * N ^ 2 / P) * P := by field_simp
        _ ≤ C6 * (h0 * N ^ 2 / P) * (P * (P * Lg ^ 5)) := by
          gcongr; nlinarith
        _ = C6 * (h0 * N ^ 2 / P) * (P * P * Lg ^ 5) := by ring
    linarith
  have : 2 * (Psi N 0 * ((((⌊h0⌋₊ : ℕ) : ℝ) + 1) * (5 * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) * E7) +
      Psi N 0 / (4 * δ))) + 2 * E6 =
      2 * (Psi N 0 * ((((⌊h0⌋₊ : ℕ) : ℝ) + 1) * (5 * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) * E7))) +
      2 * (Psi N 0 * (Psi N 0 / (4 * δ))) + 2 * E6 := by ring
  rw [this]
  have : (640 * C7 + 32 + 2 * C6) * (h0 * N ^ 2 / P) =
      640 * C7 * (h0 * N ^ 2 / P) + 32 * (h0 * N ^ 2 / P) + 2 * C6 * (h0 * N ^ 2 / P) := by ring
  rw [this]
  linarith

/-- The `k ∈ [V, V + H]` split into `H/(H₀+1) + 1` blocks of length `H₀`. -/
lemma kRange_subset_blocks (V H H0 : ℕ) :
    kRange V H ⊆ (Finset.range (H / (H0 + 1) + 1)).biUnion
      (fun i => kRange (V + i * (H0 + 1)) H0) := by
  intro k hk
  simp only [kRange, Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  simp only [Finset.mem_biUnion, Finset.mem_range, kRange, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨(k - V) / (H0 + 1), ?_, ⟨?_, ?_⟩, h3⟩
  · have : (k - V) / (H0 + 1) ≤ H / (H0 + 1) := Nat.div_le_div_right (by omega)
    omega
  · have := Nat.div_mul_le_self (k - V) (H0 + 1)
    omega
  · have h := Nat.div_add_mod (k - V) (H0 + 1)
    have hm := Nat.mod_lt (k - V) (show 0 < H0 + 1 by omega)
    have : (H0 + 1) * ((k - V) / (H0 + 1)) = (k - V) / (H0 + 1) * (H0 + 1) := Nat.mul_comm _ _
    omega

/-- Union bound for finite sums of nonnegative terms over `(range n).biUnion t`. -/
lemma sum_biUnion_range_le {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (t : ℕ → Finset ℕ) (n : ℕ) :
    ∑ k ∈ (Finset.range n).biUnion t, f k ≤ ∑ i ∈ Finset.range n, ∑ k ∈ t i, f k := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have hui := Finset.sum_union_inter (s₁ := t n) (s₂ := (Finset.range n).biUnion t) (f := f)
    have h0 : 0 ≤ ∑ k ∈ t n ∩ (Finset.range n).biUnion t, f k :=
      Finset.sum_nonneg fun k _ => hf k
    linarith

/-- **The Theorem of Perelli and Pintz from the wide forms of (6) and (7).** -/
theorem mainTheorem_of_wide (h6 : Estimate6Wide) (h7 : Estimate7Wide) : MainTheorem := by
  intro ε hε hε2 A hA
  obtain ⟨ε1, hε1, h6⟩ := h6
  obtain ⟨ε2, hε2', h7⟩ := h7
  set ε' := min ε (min ε1 ε2) / 2 with hε'
  have hm1 : min ε (min ε1 ε2) ≤ ε := min_le_left _ _
  have hm2 : min ε (min ε1 ε2) ≤ ε1 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : min ε (min ε1 ε2) ≤ ε2 := (min_le_right _ _).trans (min_le_right _ _)
  have hmpos : 0 < min ε (min ε1 ε2) := lt_min hε (lt_min hε1 hε2')
  have he'pos : 0 < ε' := by rw [hε']; linarith
  have he'1 : ε' < ε1 := by rw [hε']; linarith
  have he'2 : ε' < ε2 := by rw [hε']; linarith
  have he'e : ε' ≤ ε := by rw [hε']; linarith
  have hA' : 0 < 2 * A + 5 := by linarith
  obtain ⟨C6, N6, hC6⟩ := h6 ε' he'pos he'1 (2 * A + 5) hA'
  obtain ⟨C7, N7, hC7⟩ := h7 ε' he'pos he'2 (2 * A + 5) hA'
  have hev : ∀ᶠ N : ℕ in atTop, 16 ≤ N ∧ L N ^ Bexp (2 * A + 5) ≤ √(N : ℝ) / 4 ∧
      L N ^ (A + 4) ≤ √(N : ℝ) / 4 :=
    (eventually_ge_atTop 16).and ((eventually_logpow_le _).and (eventually_logpow_le _))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  set K := 640 * max C7 0 + 32 + 2 * max C6 0 with hK
  refine ⟨2 * K, max (max (N1 : ℝ) N6) N7, fun N H V hN hH1 hH2 hV => ?_⟩
  have hNN1 : N1 ≤ N := by
    have : (N1 : ℝ) ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
    exact_mod_cast this
  obtain ⟨hN16, hLB, hLδ⟩ := hN1 N hNN1
  have hN6 : N6 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN7 : N7 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ L N := by
    unfold L
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  set h0 := (N : ℝ) ^ (1 / 2 + ε') with hh0
  have hsq : √(N : ℝ) ≤ h0 := by
    rw [Real.sqrt_eq_rpow, hh0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hh0pos : 0 < h0 := Real.rpow_pos_of_pos hNpos _
  have hδ : L N ^ (A + 4) ≤ h0 / 2 := by
    have : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    linarith
  have hh0H : h0 < H := by
    refine lt_of_le_of_lt ?_ hH1
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set H0 := ⌊h0⌋₊ with hH0
  set P := L N ^ A with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hK0 : 0 ≤ K := by positivity
  -- each block
  have hblock : ∀ i ∈ Finset.range (H / (H0 + 1) + 1),
      ∑ k ∈ kRange (V + i * (H0 + 1)) H0, err N k ^ 2 ≤ K * (h0 * N ^ 2 / P) := by
    intro i hi
    have hiH : i * (H0 + 1) ≤ H := by
      have : i ≤ H / (H0 + 1) := by simp only [Finset.mem_range] at hi; omega
      calc i * (H0 + 1) ≤ H / (H0 + 1) * (H0 + 1) := Nat.mul_le_mul_right _ this
        _ ≤ H := Nat.div_mul_le_self H (H0 + 1)
    have hVi : ((V + i * (H0 + 1) : ℕ) : ℝ) < N / 2 := by
      have : ((V + i * (H0 + 1) : ℕ) : ℝ) ≤ V + H := by exact_mod_cast (by omega : V + i * (H0 + 1) ≤ V + H)
      linarith
    have hX : 0 ≤ h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5) := by
      have : 0 < L N ^ (2 * A + 5) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have hb6 := hC6 N (V + i * (H0 + 1)) hN6 hVi
    have hb6' : ∑ k ∈ (Finset.Icc (V + i * (H0 + 1)) (V + i * (H0 + 1) + ⌊(N : ℝ) ^ (1 / 2 + ε')⌋₊)).filter (1 ≤ ·),
      ‖(∫ α in majorArcs N (2 * A + 5), ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))) -
        (S2k k * ((N : ℝ) - 2 * k) : ℝ)‖ ^ 2 ≤
      max C6 0 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) := by
      refine hb6.trans ?_
      have e1 : C6 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) =
          C6 * (h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5)) := by rw [hh0]; ring
      have e2 : max C6 0 * (N : ℝ) ^ (1 / 2 + ε') * N ^ 2 / L N ^ (2 * A + 5) =
          max C6 0 * (h0 * (N : ℝ) ^ 2 / L N ^ (2 * A + 5)) := by rw [hh0]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    have hb7 : ∀ ξ : ℝ,
        ∫ α in Set.Ioo (ξ - 1 / (N : ℝ) ^ (1 / 2 + ε')) (ξ + 1 / (N : ℝ) ^ (1 / 2 + ε')) ∩
          minorArcs N (2 * A + 5), ‖S N α‖ ^ 2 ≤ max C7 0 * N / L N ^ (2 * A + 5 + 1) := by
      intro ξ
      refine (hC7 N hN7 ξ).trans ?_
      have : 0 < L N ^ (2 * A + 5 + 1) := Real.rpow_pos_of_pos (by linarith) _
      rw [div_le_div_iff_of_pos_right this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hNpos.le
    exact block_bound hA hN16 (le_max_right _ _) (le_max_right _ _) hL1 hLB hδ hb6' hb7
  -- sum over blocks
  have hnonneg : ∀ k, 0 ≤ err N k ^ 2 := fun k => sq_nonneg _
  have hsum := (Finset.sum_le_sum_of_subset_of_nonneg (kRange_subset_blocks V H H0)
    (fun k _ _ => hnonneg k)).trans (sum_biUnion_range_le hnonneg _ _)
  refine hsum.trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- count of blocks
  have hnb : ((H / (H0 + 1) + 1 : ℕ) : ℝ) ≤ 2 * H / h0 := by
    push_cast
    have h1 : ((H / (H0 + 1) : ℕ) : ℝ) ≤ (H : ℝ) / ((H0 : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := H) (n := H0 + 1)
      push_cast at this; exact this
    have h2 : (H : ℝ) / ((H0 : ℝ) + 1) ≤ H / h0 := by
      apply div_le_div_of_nonneg_left (by positivity) hh0pos
      exact (Nat.lt_floor_add_one h0).le
    have h3 : 1 ≤ (H : ℝ) / h0 := by rw [le_div_iff₀ hh0pos]; linarith
    have : (2 : ℝ) * H / h0 = H / h0 + H / h0 := by ring
    linarith
  calc ((H / (H0 + 1) + 1 : ℕ) : ℝ) * (K * (h0 * N ^ 2 / P))
      ≤ 2 * H / h0 * (K * (h0 * N ^ 2 / P)) := by
        apply mul_le_mul_of_nonneg_right hnb; positivity
    _ = 2 * K * H * N ^ 2 / P := by field_simp

/-- **Perelli-Pintz 1992, the Theorem, CONDITIONAL ON the wide forms of (6) and (7).**
`perelliPintz` in Statements.lean stays a cited `sorry`; this is the lab's route to it. -/
theorem perelliPintz_of_wide (h6 : Estimate6Wide) (h7 : Estimate7Wide) : MainTheorem :=
  mainTheorem_of_wide h6 h7

/-- The Corollary, p. 356, CONDITIONAL ON the same two estimates. -/
theorem corollary_of_wide (h6 : Estimate6Wide) (h7 : Estimate7Wide) : Corollary :=
  corollary_of_mainTheorem (mainTheorem_of_wide h6 h7)

#print axioms window_congr
#print axioms majorArcs_subset
#print axioms psi0_le
#print axioms block_bound
#print axioms kRange_subset_blocks
#print axioms mainTheorem_of_wide
#print axioms corollary_of_wide

end LeanLab.PerelliPintz1992

/-
The chain from the PRINTED Proposition 8.1 of P0029 Bhowmik, Grimmelt, The exceptional set of the
Goldbach problem, arXiv 2607.27282v2, pages 30 to 32, to Theorem 8.2 with `X^{7/12}` exceptions,
unit U-1335, track T1. New module; BG2026Prop81MPR.lean (U-1322) and BG2026Prop81Print.lean
(U-1331) are imported and not changed.

Part 1. The U-1322 exception form `Prop81` from the printed (8.3) plus the second half of display
(8.1), `𝔖(χ̃, χ̃, N) = χ̃(-1) 𝔖(N)` for `r̃ ∣ N`, page 30, following the page 32 proof of Theorem 8.2:
the three error terms of (8.3) are at most `δ/4 𝔖(N) N` once `c` is small and `r̃` is large, using
`(δ̃L)^{c'} ≤ c^{c'}`, `r̃/φ(r̃)² → 0` and `X^{1-ε₀} = o(X)`, and `B(β̃, β̃) N^{-2δ̃} = 1 + O(c)` from
continuity of `Γ` at 1 and 2 and `N^{-2δ̃} ≥ e^{-2c}`.

Quantifier point, F-1335a: the page 32 argument chooses `c = c(δ)` BEFORE `A`, and `ε = ε(A)`, so it
needs the implied constant `C` of (8.3) uniform in `ε`. U-1331's `Prop81PrintFix` puts `C` after
`ε`; that is weaker than needed. The print `Prop81Print` and the parts proof both give `C` before
`ε` with only `ε₀` and `K` after `ε`: `Prop81PrintUnif` below. Derivation is from `Prop81PrintUnif`.

Part 2. `MinorL2` from `MinorArcSup` by Parseval, as in Lemma 4.2, page 16, in a DISCRETE circle
method: `M = 2L` points `j/M`, `L = ⌊X⌋ + 1`, `S_j = S(j/M)` of length `L`. Then for `N < L`,
`r₂(N) = M⁻¹ Σ_j S_j² e(-Nj/M)` exactly, `r2_eq_discrete`, since `S²` has degree `< M`. The minor
part `rMinD X N = M⁻¹ Σ_{j/M ∈ 𝔪(R)} S_j² e(-Nj/M)` satisfies
`Σ_N |rMinD|² ≤ M⁻¹ Σ_{𝔪} |S_j|⁴ ≤ sup_𝔪 |S|² · Σ_{n<L} Λ(n)²`, two uses of finite Parseval.

Part 3. Theorem 8.2 at `X^{7/12}`, CONDITIONAL ON `MajorFormula81 GS (5/12) (rMajR (5/12))`,
`Display81Mult GS` and `MPRTheorem11`, where `rMajR X N` is the real part of the DISCRETE major arc
sum `M⁻¹ Σ_{j/M ∉ 𝔪(R)} S_j² e(-Nj/M)` for `N < L`, `rMajR_eq`. CAVEAT: Pintz [20, Thm 1] and the
page 31 Sketch state the major arc formula for the CONTINUOUS integral `∫_𝔐 S² e(-Nα) dα`. The two
differ by `r_𝔪^{cont} - r_𝔪^{disc}`, small in mean square but not pointwise, so `MajorFormula81` at
`rMajR` is a discrete variant of the printed input, NOT the printed input. The general
`prop81PrintUnif_of_parts` takes any split, so a continuous `MinorL2`, Parseval on `AddCircle` or
the limit `M → ∞` of the discrete bound, would remove the caveat; not done.

AI wrote this Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.BG2026Prop81Print
import LeanLab.VanDerCorput1939.Totient

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-! ### Part 1: `Prop81` from the printed (8.3) and display (8.1) -/

/-- Proposition 8.1 with `h`, `c'` and the implied constant `C` depending on `ϑ` only, and `ε₀`, `K`
chosen after `ε`. This is what the page 31 Sketch proves and what page 32 uses. -/
def Prop81PrintUnif (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (ϑ σ : ℝ) : Prop :=
  ∃ h c' C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ ε0 K : ℝ, 0 < ε0 ∧ 0 < K ∧
    ∀ X : ℝ, 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ),
    Siegel81 ϑ h X r χ δt → ∃ B : Finset ℕ, (B.card : ℝ) ≤ K * X ^ (σ + ε) ∧
      ∀ N ∈ evenWin X, N ∉ B → |r2 N - main83 GS r χ δt N| ≤ C * err83 c' ε0 X r δt N

/-- Second half of display (8.1), page 30, CITED from Pintz's Main Lemma: at a primitive real
`χ̃` mod `r̃` and even `N` with `r̃ ∣ N`, `𝔖(χ̃, χ̃, N) = χ̃(-1) 𝔖(N)`. -/
def Display81Mult (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    ∀ N : ℕ, Even N → r ∣ N → GS r χ N = (χ (-1)).re * Sing N

theorem prop81PrintUnif_of_print {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ σ : ℝ}
    (h : Prop81Print GS ϑ σ) : Prop81PrintUnif GS ϑ σ := by
  obtain ⟨hh, c', ε0, C, hh0, hc', hε0, hC, hK⟩ := h
  refine ⟨hh, c', C, hh0, hc', hC, fun ε hε => ?_⟩
  obtain ⟨K, hK0, hb⟩ := hK ε hε
  exact ⟨ε0, K, hε0, hK0, hb⟩

theorem prop81PrintFix_of_unif {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ σ : ℝ}
    (h : Prop81PrintUnif GS ϑ σ) : Prop81PrintFix GS ϑ σ := by
  obtain ⟨hh, c', C, hh0, hc', hC, hK⟩ := h
  refine ⟨hh, c', hh0, hc', fun ε hε => ?_⟩
  obtain ⟨ε0, K, hε0, hK0, hb⟩ := hK ε hε
  exact ⟨ε0, C, K, hε0, hC, hK0, hb⟩

/-- The parts proof of U-1331 gives the uniform order. CONDITIONAL ON `MajorFormula81 GS ϑ rMaj`
and `MinorL2 ϑ κ rMin`. -/
theorem prop81PrintUnif_of_parts {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ κ σ : ℝ}
    {rMaj rMin : ℝ → ℕ → ℝ} (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N)
    (hσ : max (1 - ϑ) (2 * κ - 1) ≤ σ)
    (hM : MajorFormula81 GS ϑ rMaj) (hm : MinorL2 ϑ κ rMin) : Prop81PrintUnif GS ϑ σ := by
  obtain ⟨h, c', ε0, C, hh, hc', hε0, hC, hMaj⟩ := hM
  refine ⟨h, c', C + 1, hh, hc', by linarith, fun ε hε => ?_⟩
  set e := min ε0 (ε / 4) with he
  have he0 : 0 < e := lt_min hε0 (by linarith)
  have hee : e ≤ ε / 4 := min_le_right _ _
  have heε0 : e ≤ ε0 := min_le_left _ _
  obtain ⟨K, hK, hcnt⟩ := minor_count_threshold hm (e := e) (ε' := ε / 2) (by linarith)
  refine ⟨e, K, he0, hK, fun X hX r _ χ δt hS => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  set B := (evenWin X).filter (fun N => X ^ (1 - e) < |rMin X N|)
  refine ⟨B, ?_, fun N hN hNB => ?_⟩
  · refine (hcnt X hX1).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  · have hmin : |rMin X N| ≤ X ^ (1 - e) := by
      by_contra hc; push Not at hc
      exact hNB (mem_filter.mpr ⟨hN, hc⟩)
    have hmaj := hMaj X hX r χ δt hS N hN
    have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hpow : X ^ (1 - ε0) ≤ X ^ (1 - e) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hEE : err83 c' ε0 X r δt N ≤ err83 c' e X r δt N := by
      unfold err83; linarith
    have hE1 : X ^ (1 - e) ≤ err83 c' e X r δt N := by
      unfold err83
      have hs := Sing_pos N
      have h1 : 0 ≤ (δt * Real.log X) ^ c' := Real.rpow_nonneg (mul_nonneg hS.2.2.2.1.le hL) _
      have h2 : 0 ≤ Sing N * X * (δt * Real.log X) ^ c' := by positivity
      have h3 : 0 ≤ Sing N * N * (r / (Nat.totient r : ℝ) ^ 2) := by positivity
      linarith
    rw [hsplit X N]
    calc |rMaj X N + rMin X N - main83 GS r χ δt N|
        = |(rMaj X N - main83 GS r χ δt N) + rMin X N| := by ring_nf
      _ ≤ |rMaj X N - main83 GS r χ δt N| + |rMin X N| := abs_add_le _ _
      _ ≤ C * err83 c' e X r δt N + err83 c' e X r δt N := by
          have := mul_le_mul_of_nonneg_left hEE hC.le
          linarith
      _ = (C + 1) * err83 c' e X r δt N := by ring

/-- `B(s, s) → 1` as `s → 1`, from continuity of `Γ` at 1 and 2, `Γ(1) = Γ(2) = 1`. -/
theorem betaFactor_near_one {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s - 1| < ρ → |betaFactor s s - 1| < η := by
  have h1 : ContinuousAt Real.Gamma 1 :=
    (Real.differentiableAt_Gamma (fun m => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).continuousAt
  have h2 : ContinuousAt Real.Gamma 2 :=
    (Real.differentiableAt_Gamma (fun m => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).continuousAt
  have h2' : ContinuousAt (fun s : ℝ => Real.Gamma (s + s)) 1 := by
    have hc : ContinuousAt (fun s : ℝ => s + s) 1 := continuousAt_id.add continuousAt_id
    have h2'' : ContinuousAt Real.Gamma ((fun s : ℝ => s + s) 1) := by norm_num; exact h2
    exact ContinuousAt.comp (g := Real.Gamma) h2'' hc
  have hG2 : Real.Gamma (1 + 1) ≠ 0 := by norm_num [Real.Gamma_two]
  have hcont : ContinuousAt (fun s : ℝ => betaFactor s s) 1 := by
    unfold betaFactor
    exact (h1.mul h1).div h2' hG2
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ, hρ, hb⟩ := hcont η hη
  refine ⟨ρ, hρ, fun s hs => ?_⟩
  have := hb (x := s) (by rw [Real.dist_eq]; exact hs)
  rw [Real.dist_eq] at this
  have hv : betaFactor 1 1 = 1 := by
    unfold betaFactor; norm_num [Real.Gamma_one, Real.Gamma_two]
  rwa [hv] at this

/-- `r/φ(r)² ≤ η` once `r ≥ 16/η²`, from van der Corput's `r³ ≤ 16 φ(r)⁴`, VanDerCorput1939/Totient.lean. -/
theorem r_div_totient_sq_le {η : ℝ} (hη : 0 < η) {r : ℕ} (hr0 : 0 < r) (hr : 16 / η ^ 2 ≤ r) :
    (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ η := by
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr0
  have h3 : ((r : ℝ)) ^ 3 ≤ 16 * (Nat.totient r : ℝ) ^ 4 := by
    exact_mod_cast LeanLab.VanDerCorput1939.cube_le_totient_pow4 r hr0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  rw [div_le_iff₀ (by positivity)]
  have h16 : 16 ≤ η ^ 2 * r := by rwa [div_le_iff₀ (by positivity), mul_comm] at hr
  -- r² ≤ η² φ⁴ since r³ ≤ 16 φ⁴ ≤ η² r φ⁴
  have hsq : (r : ℝ) ^ 2 ≤ (η * (Nat.totient r : ℝ) ^ 2) ^ 2 := by
    have : (r : ℝ) ^ 3 ≤ η ^ 2 * r * (Nat.totient r : ℝ) ^ 4 := by
      have := mul_le_mul_of_nonneg_right h16 (by positivity : (0 : ℝ) ≤ (Nat.totient r : ℝ) ^ 4)
      linarith
    have e : (r : ℝ) ^ 3 = r * r ^ 2 := by ring
    have e2 : η ^ 2 * r * (Nat.totient r : ℝ) ^ 4 = r * (η * (Nat.totient r : ℝ) ^ 2) ^ 2 := by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_left this hrR
  exact (pow_le_pow_iff_left₀ hrR.le (by positivity) two_ne_zero).mp hsq

/-- `N^{2(1-δ̃)-1}/N = N^{-2δ̃} ∈ (1 - 2c, 1]` for `1 ≤ N ≤ X`, `δ̃ log X < c`, `δ̃ ≥ 0`. -/
theorem pow_factor_near_one {N X δt c : ℝ} (hN : 1 ≤ N) (hNX : N ≤ X) (hδ : 0 ≤ δt)
    (hc : δt * Real.log X < c) :
    1 - 2 * c < N ^ (2 * (1 - δt) - 1) / N ∧ N ^ (2 * (1 - δt) - 1) / N ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have e : N ^ (2 * (1 - δt) - 1) / N = N ^ (-(2 * δt)) := by
    rw [← Real.rpow_sub_one hN0.ne']; ring_nf
  rw [e]
  constructor
  · have hlog : Real.log N ≤ Real.log X := Real.log_le_log hN0 hNX
    have hl : -(2 * δt) * Real.log N > -(2 * c) := by nlinarith
    rw [Real.rpow_def_of_pos hN0]
    have := Real.add_one_le_exp (Real.log N * -(2 * δt))
    nlinarith
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- `evenMult r X ⊆ evenWin X`. -/
theorem evenMult_sub_evenWin (r : ℕ) (X : ℝ) : evenMult r X ⊆ evenWin X := by
  intro N hN
  simp only [evenMult, evenWin, mem_filter] at hN ⊢
  exact ⟨hN.1, hN.2.1⟩

/-- The U-1322 exception form `Prop81 ϑ σ` from the printed (8.3) with uniform constant and the
second half of (8.1), along the page 32 argument. CONDITIONAL ON `Prop81PrintUnif GS ϑ σ` and
`Display81Mult GS`. -/
theorem prop81_of_printUnif {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ σ : ℝ}
    (hP : Prop81PrintUnif GS ϑ σ) (hD : Display81Mult GS) : Prop81 ϑ σ := by
  intro δ hδ hδ1
  obtain ⟨h, c', C, hh, hc', hC, hU⟩ := hP
  obtain ⟨ρ, hρ, hbeta⟩ := betaFactor_near_one (η := δ / 8) (by linarith)
  set c₁ := (δ / (24 * C)) ^ c'⁻¹ with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set c := min (min h (δ / 16)) (min ρ c₁) with hcd
  have hc0 : 0 < c := lt_min (lt_min hh (by linarith)) (lt_min hρ hc₁0)
  have hch : c ≤ h := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcδ : c ≤ δ / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcρ : c ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcpow : c ^ c' ≤ δ / (24 * C) := by
    have := Real.rpow_le_rpow hc0.le hcc₁ hc'.le
    rwa [hc₁, Real.rpow_inv_rpow (by positivity) hc'.ne'] at this
  refine ⟨c, hc0, fun A hA hAϑ τ hτ => ?_⟩
  set ε := (τ - σ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨ε0, K, hε00, hK, hB⟩ := hU ε hε0
  have hC0 := C0_pos
  obtain ⟨x1, hx11, hx1⟩ := eventually_le_rpow (a := σ + ε) (b := τ) (K := K) (by linarith) hK
  obtain ⟨x2, -, hx2⟩ := eventually_le_rpow (a := 1 - ε0) (b := 1) (K := 12 * C / (δ * C0))
    (by linarith) (by positivity)
  set x0 := max (max x1 x2) (Real.exp 1 + 2)
  set η' := δ / (12 * C) with hη'
  have hη'0 : 0 < η' := by positivity
  refine ⟨max ⌈x0 ^ A⁻¹⌉₊ ⌈16 / η' ^ 2⌉₊, fun r _ hr χ hprim hreal hzero => ?_⟩
  obtain ⟨β, hβ1, hβ2, hβL⟩ := hzero
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  set X := (r : ℝ) ^ A with hXdef
  have hx0pos : 0 < x0 := by
    have := Real.exp_pos 1
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hXx : x0 ≤ X := by
    have hrx : x0 ^ A⁻¹ ≤ r := (Nat.ceil_le).mp (le_of_max_le_left hr)
    have h := Real.rpow_le_rpow (by positivity) hrx hA.le
    rwa [Real.rpow_inv_rpow hx0pos.le hA.ne'] at h
  have hX1x : x1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXx
  have hX2x : x2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXx
  have hXe : Real.exp 1 + 2 ≤ X := le_trans (le_max_right _ _) hXx
  have hX2 : 2 ≤ X := by have := Real.exp_pos 1; linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlog0 : 0 < Real.log X := by linarith
  set δt := 1 - β with hδt
  have hδt0 : 0 < δt := by rw [hδt]; linarith
  have hδtc : δt * Real.log X < c := by
    have := hβ1; rw [hXdef] at this
    have h' : δt < c / Real.log X := by rw [hδt]; linarith
    rwa [lt_div_iff₀ hlog0] at h'
  have hδtlt : δt < c := by nlinarith
  -- the Siegel setting of (8.3)
  have hS : Siegel81 ϑ h X r χ δt := by
    refine ⟨?_, hprim, hreal, hδt0, ?_, ?_⟩
    · have e : X ^ A⁻¹ = r := by rw [hXdef, Real.rpow_rpow_inv hrR.le hA.ne']
      have hX1 : 1 ≤ X := by linarith
      calc (r : ℝ) = X ^ A⁻¹ := e.symm
        _ ≤ X ^ ϑ := Real.rpow_le_rpow_of_exponent_le hX1 (by rw [← one_div]; exact hAϑ.le)
    · rw [lt_div_iff₀ hlog0]; nlinarith
    · have : ((1 - δt : ℝ) : ℂ) = (β : ℂ) := by rw [hδt]; push_cast; ring
      rw [this]; exact hβL
  obtain ⟨B, hBc, hBN⟩ := hB X hX2 r χ δt hS
  refine ⟨B, ?_, fun N hN hNB => ?_⟩
  · exact hBc.trans (hx1 X hX1x)
  · have hNw := evenMult_sub_evenWin r X hN
    have hbound := hBN N hNw hNB
    simp only [evenMult, mem_filter, mem_Icc] at hN
    obtain ⟨⟨hN1, hN2⟩, hNe, hrN⟩ := hN
    have hNX2 : X / 2 ≤ N := (Nat.ceil_le).mp hN1
    have hNX : (N : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp hN2
    have hN1R : (1 : ℝ) ≤ N := by linarith
    have hN0 : (0 : ℝ) < N := by linarith
    have hGS := hD r χ hprim hreal N hNe hrN
    set s := (χ (-1)).re
    set p := (N : ℝ) ^ (2 * (1 - δt) - 1) / N with hp
    set bf := betaFactor (1 - δt) (1 - δt)
    set E := r2 N - main83 GS r χ δt N with hE
    refine ⟨bf * p, E, ?_, ?_, ?_⟩
    · obtain ⟨hp1, hp2⟩ := pow_factor_near_one hN1R hNX hδt0.le hδtc
      have hbf : |bf - 1| < δ / 8 := hbeta _ (by
        rw [show 1 - δt - 1 = -δt by ring, abs_neg, abs_of_pos hδt0]; linarith)
      have hp0 : 0 ≤ p := by rw [hp]; positivity
      have : |bf * p - 1| ≤ |bf - 1| * p + |p - 1| := by
        calc |bf * p - 1| = |(bf - 1) * p + (p - 1)| := by ring_nf
          _ ≤ |(bf - 1) * p| + |p - 1| := abs_add_le _ _
          _ = |bf - 1| * p + |p - 1| := by rw [abs_mul, abs_of_nonneg hp0]
      have hp1' : |p - 1| ≤ 2 * c := by rw [abs_le]; constructor <;> linarith
      have : |bf - 1| * p ≤ δ / 8 := by
        calc |bf - 1| * p ≤ |bf - 1| * 1 := mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
          _ ≤ δ / 8 := by linarith
      linarith
    · -- the three error terms of (8.3)
      have hSN := Sing_ge N
      have hSpos := Sing_pos N
      have hbound' : |E| ≤ C * err83 c' ε0 X r δt N := hbound
      unfold err83 at hbound'
      have t1 : (δt * Real.log X) ^ c' ≤ δ / (24 * C) :=
        le_trans (Real.rpow_le_rpow (by positivity) hδtc.le hc'.le) hcpow
      have t2 : (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ η' := by
        apply r_div_totient_sq_le hη'0 hrpos
        exact (Nat.ceil_le).mp (le_of_max_le_right hr)
      have t3 : 12 * C / (δ * C0) * X ^ (1 - ε0) ≤ X := by
        have := hx2 X hX2x; rwa [Real.rpow_one] at this
      have t3' : C * X ^ (1 - ε0) ≤ δ / 12 * (C0 * X) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at t3
        have e1 : 12 * C * X ^ (1 - ε0) = 12 * (C * X ^ (1 - ε0)) := by ring
        have e2 : δ / 12 * (C0 * X) = (X * (δ * C0)) / 12 := by ring
        rw [e1] at t3; rw [e2]; linarith
      have hSNX : C0 * X ≤ Sing N * N := by
        have := mul_le_mul hSN hNX2 (by positivity) (by positivity)
        linarith
      have hA1 : C * (Sing N * X * (δt * Real.log X) ^ c') ≤ δ / 12 * (Sing N * N) := by
        have hq : 0 ≤ (δt * Real.log X) ^ c' := by positivity
        have : Sing N * X * (δt * Real.log X) ^ c' ≤ Sing N * (2 * N) * (δ / (24 * C)) := by
          apply mul_le_mul _ t1 hq (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hSpos.le
        calc C * (Sing N * X * (δt * Real.log X) ^ c')
            ≤ C * (Sing N * (2 * N) * (δ / (24 * C))) := mul_le_mul_of_nonneg_left this hC.le
          _ = δ / 12 * (Sing N * N) := by field_simp; ring
      have hA2 : C * (Sing N * N * (r / (Nat.totient r : ℝ) ^ 2)) ≤ δ / 12 * (Sing N * N) := by
        calc C * (Sing N * N * (r / (Nat.totient r : ℝ) ^ 2))
            ≤ C * (Sing N * N * η') := by
              apply mul_le_mul_of_nonneg_left _ hC.le
              exact mul_le_mul_of_nonneg_left t2 (by positivity)
          _ = δ / 12 * (Sing N * N) := by rw [hη']; field_simp
      have hsum : C * (Sing N * X * (δt * Real.log X) ^ c' + Sing N * N * (r / (Nat.totient r : ℝ) ^ 2)
          + X ^ (1 - ε0)) = C * (Sing N * X * (δt * Real.log X) ^ c')
            + C * (Sing N * N * (r / (Nat.totient r : ℝ) ^ 2)) + C * X ^ (1 - ε0) := by ring
      rw [hsum] at hbound'
      have t4 : δ / 12 * (C0 * X) ≤ δ / 12 * (Sing N * N) :=
        mul_le_mul_of_nonneg_left hSNX (by positivity)
      linarith
    · rw [hE]
      have hm : main83 GS r χ δt N = Sing N * N + s * Sing N * (bf * p) * N := by
        unfold main83
        rw [hGS, hp]
        field_simp
        simp only [bf]
        ring
      rw [hm]; ring

/-- Vacuity test for `Display81Mult`: the choice `GS r χ N = χ(-1) 𝔖(N)` satisfies it. -/
theorem vacuity_display81 :
    Display81Mult (fun r χ N => ((χ : DirichletCharacter ℂ r) (-1)).re * Sing N) :=
  fun _ _ _ _ _ _ _ _ => rfl

/-! ### Part 2: a discrete circle method and Parseval -/

open ComplexConjugate

/-- Orthogonality of the powers of a primitive `M`-th root of unity. -/
theorem orth_root {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) {a b : ℕ}
    (ha : a < M) (hb : b < M) :
    ∑ j ∈ range M, (ζ ^ a * ζ⁻¹ ^ b) ^ j = if a = b then (M : ℂ) else 0 := by
  have hz : ζ ≠ 0 := hζ.ne_zero hM.ne'
  split_ifs with hab
  · subst hab
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz)]
    simp
  · have hu : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      have : ζ ^ a * ζ⁻¹ ^ b * ζ ^ b = ζ ^ b := by rw [h, one_mul]
      rwa [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hz), mul_one] at this
    rw [geom_sum_eq hu]
    have : (ζ ^ a * ζ⁻¹ ^ b) ^ M = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a M, mul_comm b M, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [this]; simp

/-- Finite Parseval for a primitive `M`-th root of unity: frequencies `J ⊆ [0, M)`. -/
theorem parseval_root {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, j < M) (g : ℕ → ℂ) :
    ∑ N ∈ range M, ‖∑ j ∈ J, g j * ζ ^ (N * j)‖ ^ 2 = M * ∑ j ∈ J, ‖g j‖ ^ 2 := by
  have hn : ‖ζ‖ = 1 := hζ.norm'_eq_one hM.ne'
  have hc : conj ζ = ζ⁻¹ := (Complex.inv_eq_conj hn).symm
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj']
  have key : ∀ N : ℕ, (∑ j ∈ J, g j * ζ ^ (N * j)) * conj (∑ j ∈ J, g j * ζ ^ (N * j)) =
      ∑ j ∈ J, ∑ j' ∈ J, (g j * conj (g j')) * (ζ ^ j * ζ⁻¹ ^ j') ^ N := by
    intro N
    rw [map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl (fun j _ => sum_congr rfl (fun j' _ => ?_))
    rw [map_mul, map_pow, hc, mul_pow, ← pow_mul, ← pow_mul, mul_comm j N, mul_comm j' N]
    ring
  rw [sum_congr rfl (fun N _ => key N)]
  calc ∑ N ∈ range M, ∑ j ∈ J, ∑ j' ∈ J, g j * conj (g j') * (ζ ^ j * ζ⁻¹ ^ j') ^ N
      = ∑ j ∈ J, ∑ j' ∈ J, g j * conj (g j') * ∑ N ∈ range M, (ζ ^ j * ζ⁻¹ ^ j') ^ N := by
        rw [sum_comm]
        refine sum_congr rfl (fun j _ => ?_)
        rw [sum_comm]
        refine sum_congr rfl (fun j' _ => ?_)
        rw [mul_sum]
    _ = ∑ j ∈ J, ∑ j' ∈ J, g j * conj (g j') * (if j = j' then (M : ℂ) else 0) := by
        refine sum_congr rfl (fun j hj => sum_congr rfl (fun j' hj' => ?_))
        rw [orth_root hM hζ (hJ j hj) (hJ j' hj')]
    _ = ∑ j ∈ J, g j * conj (g j) * M := by
        refine sum_congr rfl (fun j hj => ?_)
        simp only [mul_ite, mul_zero]
        rw [sum_ite_eq]
        simp [hj]
    _ = (M : ℂ) * ∑ j ∈ J, g j * conj (g j) := by
        rw [mul_sum]; refine sum_congr rfl (fun j _ => ?_); ring

/-- `e(1/M)`. -/
def eM (M : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / M)

theorem eM_prim {M : ℕ} (hM : 0 < M) : IsPrimitiveRoot (eM M) M :=
  Complex.isPrimitiveRoot_exp M hM.ne'

/-- `S(j/M) = Σ_{n<L} Λ(n) e(1/M)^{jn}`. -/
theorem SΛ_root (L M j : ℕ) :
    SΛ L ((j : ℝ) / (M : ℝ)) = ∑ n ∈ range L, (Λ n : ℂ) * eM M ^ (j * n) := by
  unfold SΛ eM
  refine sum_congr rfl (fun n _ => ?_)
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The discrete scale: length `L = ⌊X⌋ + 1`, `M = 2L` points. -/
def Ld (X : ℝ) : ℕ := ⌊X⌋₊ + 1

def Md (X : ℝ) : ℕ := 2 * Ld X

theorem Md_pos (X : ℝ) : 0 < Md X := by unfold Md Ld; omega

/-- `S_j = S(j/M)` of length `L`. -/
def Sd (X : ℝ) (j : ℕ) : ℂ := SΛ (Ld X) ((j : ℝ) / (Md X : ℝ))

open Classical in
/-- The points `j/M` on the minor arcs `𝔪(R)`, `R = X^ϑ`, of length `L`. -/
noncomputable def minorJ (ϑ X : ℝ) : Finset ℕ :=
  (range (Md X)).filter (fun j => Minor (Ld X) (X ^ ϑ) ((j : ℝ) / (Md X : ℝ)))

theorem minorJ_lt {ϑ X : ℝ} {j : ℕ} (hj : j ∈ minorJ ϑ X) : j < Md X := by
  classical
  unfold minorJ at hj
  convert mem_range.mp (mem_filter.mp hj).1

theorem mem_minorJ {ϑ X : ℝ} {j : ℕ} (hj : j ∈ minorJ ϑ X) :
    Minor (Ld X) (X ^ ϑ) ((j : ℝ) / (Md X : ℝ)) := by
  classical
  unfold minorJ at hj
  convert (mem_filter.mp hj).2

/-- The discrete minor arc integral `M⁻¹ Σ_{j/M ∈ 𝔪} S_j² e(-Nj/M)`. -/
def rMinC (ϑ X : ℝ) (N : ℕ) : ℂ :=
  (Md X : ℂ)⁻¹ * ∑ j ∈ minorJ ϑ X, Sd X j ^ 2 * (eM (Md X))⁻¹ ^ (N * j)

/-- The discrete major arc integral, over `j/M ∉ 𝔪(R)`. -/
def rMajC (ϑ X : ℝ) (N : ℕ) : ℂ :=
  (Md X : ℂ)⁻¹ * ∑ j ∈ range (Md X) \ minorJ ϑ X, Sd X j ^ 2 * (eM (Md X))⁻¹ ^ (N * j)

/-- Real parts; `rMajR` is defined so that `r₂ = rMajR + rMinR` holds by definition, and equals the
real part of the major arc integral for `N ≤ X`, `rMajR_eq`. -/
def rMinR (ϑ : ℝ) (X : ℝ) (N : ℕ) : ℝ := (rMinC ϑ X N).re

def rMajR (ϑ : ℝ) (X : ℝ) (N : ℕ) : ℝ := r2 N - rMinR ϑ X N

theorem split_R (ϑ : ℝ) : ∀ X N, r2 N = rMajR ϑ X N + rMinR ϑ X N := by
  intro X N; unfold rMajR; ring

/-- Parseval for `S`: `Σ_{j<M} |S_j|² = M Σ_{n<L} Λ(n)²`. -/
theorem sum_Sd_sq (X : ℝ) :
    ∑ j ∈ range (Md X), ‖Sd X j‖ ^ 2 = Md X * ∑ n ∈ range (Ld X), (Λ n) ^ 2 := by
  have hM := Md_pos X
  have h := parseval_root hM (eM_prim hM) (range (Ld X))
    (fun n hn => by rw [mem_range] at hn; unfold Md; omega) (fun n => (Λ n : ℂ))
  have e : ∀ j, Sd X j = ∑ n ∈ range (Ld X), (Λ n : ℂ) * eM (Md X) ^ (j * n) := fun j => by
    unfold Sd; rw [SΛ_root]
  simp_rw [e]
  rw [h]
  congr 1
  refine sum_congr rfl (fun n _ => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Bessel for the minor part: `Σ_{N<M} |rMinC N|² = M⁻¹ Σ_{𝔪} |S_j|⁴`. -/
theorem sum_rMinC_sq (ϑ X : ℝ) :
    ∑ N ∈ range (Md X), ‖rMinC ϑ X N‖ ^ 2 = (Md X : ℝ)⁻¹ * ∑ j ∈ minorJ ϑ X, ‖Sd X j‖ ^ 4 := by
  have hM := Md_pos X
  have hMR : (0 : ℝ) < Md X := by exact_mod_cast hM
  have h := parseval_root hM (eM_prim hM).inv (minorJ ϑ X)
    (fun j hj => minorJ_lt hj)
    (fun j => Sd X j ^ 2)
  have e : ∀ N, ‖rMinC ϑ X N‖ ^ 2 =
      (Md X : ℝ)⁻¹ ^ 2 * ‖∑ j ∈ minorJ ϑ X, Sd X j ^ 2 * (eM (Md X))⁻¹ ^ (N * j)‖ ^ 2 := by
    intro N
    unfold rMinC
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  simp_rw [e]
  rw [← mul_sum, h]
  have e2 : ∀ j, ‖Sd X j ^ 2‖ ^ 2 = ‖Sd X j‖ ^ 4 := fun j => by rw [norm_pow]; ring
  simp_rw [e2]
  field_simp

/-- `MinorL2` from `MinorArcSup` by Parseval, as in the proof of Lemma 4.2, page 16, in the
discrete circle method: `Σ_N |r_𝔪(N)|² ≤ sup_𝔪 |S|² Σ_{n<L} Λ(n)²`. CONDITIONAL ON `MinorArcSup κ`. -/
theorem minorL2_of_sup {ϑ κ : ℝ} (hϑ : 0 ≤ ϑ) (hκ : 0 ≤ κ) (hS : MinorArcSup κ) :
    MinorL2 ϑ κ (rMinR ϑ) := by
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by positivity
  obtain ⟨Cs, hCs, hsup⟩ := hS e he0
  refine ⟨2 * Cs ^ 2 / e ^ 2 * 2 ^ ε * (8 + 2 ^ (2 * κ + 1)), by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set L := Ld X with hLd
  set M := Md X with hMd
  have hL1 : 1 ≤ L := by rw [hLd]; unfold Ld; omega
  have hLR1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLR0 : (0 : ℝ) < L := by linarith
  have hL2X : (L : ℝ) ≤ 2 * X := by
    rw [hLd]; unfold Ld; push_cast
    have := Nat.floor_le hX0.le; linarith
  set R := X ^ ϑ with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hX hϑ
  have hR0 : 0 < R := by linarith
  set Q := Cs * (L : ℝ) ^ e * (L / Real.sqrt R + (L : ℝ) ^ κ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hpt : ∀ j ∈ minorJ ϑ X, ‖Sd X j‖ ≤ Q := by
    intro j hj
    exact hsup L R _ hL1 hR1 (mem_minorJ hj)
  have stepA : ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinR ϑ X N ^ 2 ≤
      ∑ N ∈ range M, ‖rMinC ϑ X N‖ ^ 2 := by
    calc ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinR ϑ X N ^ 2
        ≤ ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, ‖rMinC ϑ X N‖ ^ 2 := by
          apply sum_le_sum; intro N _
          unfold rMinR
          have := Complex.abs_re_le_norm (rMinC ϑ X N)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ ≤ ∑ N ∈ range M, ‖rMinC ϑ X N‖ ^ 2 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro N hN; rw [mem_Icc] at hN; rw [mem_range, hMd]; unfold Md Ld; omega
          · intros; positivity
  have stepB : ∑ N ∈ range M, ‖rMinC ϑ X N‖ ^ 2 ≤ Q ^ 2 * ∑ n ∈ range L, (Λ n) ^ 2 := by
    rw [hMd, sum_rMinC_sq]
    have hMR : (0 : ℝ) < Md X := by exact_mod_cast Md_pos X
    calc (Md X : ℝ)⁻¹ * ∑ j ∈ minorJ ϑ X, ‖Sd X j‖ ^ 4
        ≤ (Md X : ℝ)⁻¹ * ∑ j ∈ minorJ ϑ X, Q ^ 2 * ‖Sd X j‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum; intro j hj
          have h2 : ‖Sd X j‖ ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hpt j hj) 2
          have : ‖Sd X j‖ ^ 4 = ‖Sd X j‖ ^ 2 * ‖Sd X j‖ ^ 2 := by ring
          rw [this]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ (Md X : ℝ)⁻¹ * ∑ j ∈ range (Md X), Q ^ 2 * ‖Sd X j‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum_of_subset_of_nonneg
          · intro j hj; exact mem_range.mpr (minorJ_lt hj)
          · intros; positivity
      _ = Q ^ 2 * ∑ n ∈ range L, (Λ n) ^ 2 := by
          rw [← mul_sum, sum_Sd_sq]; field_simp; rfl
  have hlog : Real.log L ≤ (L : ℝ) ^ e / e := Real.log_le_rpow_div hLR0.le he0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hLR1
  have stepC : ∑ n ∈ range L, (Λ n) ^ 2 ≤ L * ((L : ℝ) ^ e / e) ^ 2 := by
    calc ∑ n ∈ range L, (Λ n) ^ 2 ≤ ∑ n ∈ range L, ((L : ℝ) ^ e / e) ^ 2 := by
          apply sum_le_sum; intro n hn
          rw [mem_range] at hn
          have h1 : Λ n ≤ Real.log L := by
            refine vonMangoldt_le_log.trans ?_
            rcases Nat.eq_zero_or_pos n with h | h
            · subst h; simpa using hlog0
            · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hn.le)
          exact pow_le_pow_left₀ vonMangoldt_nonneg (h1.trans hlog) 2
      _ = L * ((L : ℝ) ^ e / e) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  set P := (L : ℝ) ^ e with hP
  have hP0 : 0 ≤ P := by positivity
  set K := (L : ℝ) ^ κ with hK
  have hK0 : 0 ≤ K := by positivity
  have claim1 : Q ^ 2 ≤ 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) := by
    have hsq : (L / Real.sqrt R) ^ 2 = L ^ 2 / R := by
      rw [div_pow, Real.sq_sqrt hR0.le]
    have : (L / Real.sqrt R + K) ^ 2 ≤ 2 * ((L / Real.sqrt R) ^ 2 + K ^ 2) := by
      nlinarith [sq_nonneg (L / Real.sqrt R - K)]
    rw [hsq] at this
    calc Q ^ 2 = Cs ^ 2 * P ^ 2 * (L / Real.sqrt R + K) ^ 2 := by rw [hQ]; ring
      _ ≤ Cs ^ 2 * P ^ 2 * (2 * (L ^ 2 / R + K ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) := by ring
  have claim2 : P ^ 4 ≤ 2 ^ ε * X ^ ε := by
    have e4 : P ^ 4 = (L : ℝ) ^ ε := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hLR0.le, he]; norm_num
    rw [e4, ← Real.mul_rpow (by norm_num) hX0.le]
    exact Real.rpow_le_rpow hLR0.le hL2X hε.le
  have claim3 : (L : ℝ) ^ 3 / R ≤ 8 * X ^ (3 - ϑ) := by
    rw [Real.rpow_sub hX0, div_le_iff₀ hR0]
    have : X ^ (3 : ℝ) = X ^ 3 := by norm_cast
    rw [this, hR]
    have hL3 : (L : ℝ) ^ 3 ≤ (2 * X) ^ 3 := pow_le_pow_left₀ hLR0.le hL2X 3
    have : 8 * (X ^ 3 / X ^ ϑ) * X ^ ϑ = 8 * X ^ 3 := by
      field_simp
    rw [this]; nlinarith
  have claim4 : (L : ℝ) * K ^ 2 ≤ 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1) := by
    have e1 : (L : ℝ) * K ^ 2 = (L : ℝ) ^ (2 * κ + 1) := by
      rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hLR0.le, Real.rpow_add hLR0, Real.rpow_one]
      push_cast; ring
    rw [e1, ← Real.mul_rpow (by norm_num) hX0.le]
    exact Real.rpow_le_rpow hLR0.le hL2X (by linarith)
  have hX3 : 0 ≤ X ^ (3 - ϑ) := by positivity
  have hX4 : 0 ≤ X ^ (2 * κ + 1) := by positivity
  have hXε : 0 ≤ X ^ ε := by positivity
  have h2κ : 0 ≤ (2 : ℝ) ^ (2 * κ + 1) := by positivity
  have h2ε : 0 ≤ (2 : ℝ) ^ ε := by positivity
  calc ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinR ϑ X N ^ 2
      ≤ Q ^ 2 * (L * (P / e) ^ 2) :=
        stepA.trans (stepB.trans (mul_le_mul_of_nonneg_left stepC (by positivity)))
    _ ≤ 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) * (L * (P / e) ^ 2) :=
        mul_le_mul_of_nonneg_right claim1 (by positivity)
    _ = 2 * Cs ^ 2 / e ^ 2 * P ^ 4 * ((L : ℝ) ^ 3 / R + L * K ^ 2) := by
        field_simp
    _ ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
          (8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left claim2 (by positivity)) (by linarith)
          (by positivity) (by positivity)
    _ ≤ 2 * Cs ^ 2 / e ^ 2 * 2 ^ ε * (8 + 2 ^ (2 * κ + 1)) * X ^ ε *
          (X ^ (3 - ϑ) + X ^ (2 * κ + 1)) := by
        have : 8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1) ≤
            (8 + 2 ^ (2 * κ + 1)) * (X ^ (3 - ϑ) + X ^ (2 * κ + 1)) := by nlinarith
        have hc : 0 ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) := by positivity
        calc 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
              (8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1))
            ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
              ((8 + 2 ^ (2 * κ + 1)) * (X ^ (3 - ϑ) + X ^ (2 * κ + 1))) :=
              mul_le_mul_of_nonneg_left this hc
          _ = _ := by ring

/-- The discrete circle method is exact: for `N < L`, `M⁻¹ Σ_{j<M} S_j² e(-Nj/M) = r₂(N)`, since
`S²` has frequencies `n + m ≤ 2L - 2 < M`. PROVED. -/
theorem r2_eq_discrete (X : ℝ) {N : ℕ} (hN : N < Ld X) :
    (Md X : ℂ)⁻¹ * ∑ j ∈ range (Md X), Sd X j ^ 2 * (eM (Md X))⁻¹ ^ (N * j) = (r2 N : ℂ) := by
  set L := Ld X with hLd
  set M := Md X with hMd
  have hML : M = 2 * L := rfl
  have hM := Md_pos X
  have hMR : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set ω := eM M with hω
  have hprim : IsPrimitiveRoot ω M := eM_prim hM
  have e1 : ∀ j, Sd X j ^ 2 * ω⁻¹ ^ (N * j) =
      ∑ n ∈ range L, ∑ m ∈ range L, (Λ n : ℂ) * Λ m * (ω ^ (n + m) * ω⁻¹ ^ N) ^ j := by
    intro j
    have : Sd X j = ∑ n ∈ range L, (Λ n : ℂ) * ω ^ (j * n) := by unfold Sd; rw [SΛ_root]
    rw [this, sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl (fun n _ => ?_)
    rw [sum_mul]
    refine sum_congr rfl (fun m _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_mul, show (n + m) * j = j * n + j * m by ring, pow_add,
      mul_comm N j]
    ring
  rw [sum_congr rfl (fun j _ => e1 j), sum_comm]
  have e2 : ∀ n ∈ range L, ∑ j ∈ range M, ∑ m ∈ range L,
      (Λ n : ℂ) * Λ m * (ω ^ (n + m) * ω⁻¹ ^ N) ^ j =
      if n ≤ N then (Λ n : ℂ) * Λ (N - n) * M else 0 := by
    intro n hn
    rw [mem_range] at hn
    rw [sum_comm]
    have e3 : ∀ m ∈ range L, ∑ j ∈ range M, (Λ n : ℂ) * Λ m * (ω ^ (n + m) * ω⁻¹ ^ N) ^ j =
        (Λ n : ℂ) * Λ m * (if n + m = N then (M : ℂ) else 0) := by
      intro m hm
      rw [mem_range] at hm
      rw [← mul_sum, orth_root hM hprim (by omega) (by omega)]
    rw [sum_congr rfl e3]
    split_ifs with hnN
    · rw [sum_eq_single (N - n)]
      · rw [if_pos (by omega)]
      · intro b _ hb; rw [if_neg (by omega)]; simp
      · intro h; exfalso; rw [mem_range] at h; omega
    · apply sum_eq_zero; intro m _; rw [if_neg (by omega)]; simp
  rw [sum_congr rfl e2, ← sum_filter]
  have hf : (range L).filter (fun n => n ≤ N) = range (N + 1) := by
    ext n; simp only [mem_filter, mem_range]; omega
  rw [hf, ← sum_mul]
  unfold r2
  push_cast
  field_simp

/-- For `N ≤ X` the split `rMajR = r₂ - rMinR` is the real part of the discrete major arc
integral. PROVED. -/
theorem rMajR_eq (ϑ X : ℝ) {N : ℕ} (hN : N < Ld X) : rMajR ϑ X N = (rMajC ϑ X N).re := by
  have hsub : minorJ ϑ X ⊆ range (Md X) := fun j hj => mem_range.mpr (minorJ_lt hj)
  have hfull := r2_eq_discrete X hN
  rw [← sum_sdiff hsub, mul_add] at hfull
  have : rMajC ϑ X N = (r2 N : ℂ) - rMinC ϑ X N := by
    unfold rMajC rMinC; rw [← hfull]; ring
  unfold rMajR rMinR
  rw [this, Complex.sub_re, Complex.ofReal_re]

/-! ### Part 3: the chain -/

/-- Theorem 8.2 with `X^{7/12}` exceptions, `A > 12/5`. CONDITIONAL ON `MajorFormula81 GS (5/12)`
for the DISCRETE major arc part `rMajR (5/12)`, a variant of the printed continuous input, see the
header CAVEAT, on `Display81Mult GS` and on `MPRTheorem11`. -/
theorem theorem82σ_seven_twelfths_chain {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ}
    (hM : MajorFormula81 GS (5 / 12) (rMajR (5 / 12))) (hD : Display81Mult GS)
    (hMPR : MPRTheorem11) : Theorem82σ (7 / 12) := by
  have hm : MinorL2 (5 / 12) (19 / 24) (rMinR (5 / 12)) :=
    minorL2_of_sup (by norm_num) (by norm_num) (minorArcSup_of_MPR hMPR)
  have hU : Prop81PrintUnif GS (5 / 12) (7 / 12) :=
    prop81PrintUnif_of_parts (split_R _) (by norm_num) hM hm
  exact theorem82σ_of_prop81σ _ (prop81AtMultiplesσ_of_prop81 (by norm_num) (by norm_num)
    (prop81_of_printUnif hU hD))

/-- The paper's own page 32 proof: Theorem 8.2 as printed, `X^{3/5}`, `A > 5/2`, from the printed
Proposition 8.1 at `ϑ = 2/5` and (8.1). CONDITIONAL ON `Prop81Print GS (2/5) (3/5)` and
`Display81Mult GS`. -/
theorem theorem82_of_print {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ}
    (hP : Prop81Print GS (2 / 5) (3 / 5)) (hD : Display81Mult GS) : Theorem82 := by
  rw [← theorem82σ_three_fifths]
  exact theorem82σ_of_prop81σ _ (prop81AtMultiplesσ_of_prop81 (by norm_num) (by norm_num)
    (prop81_of_printUnif (prop81PrintUnif_of_print hP) hD))

/-- Theorem 8.2 at `X^{7/12}` from a printed-form Proposition 8.1 at `ϑ = 5/12`, `σ = 7/12`.
CONDITIONAL ON `Prop81Print GS (5/12) (7/12)` and `Display81Mult GS`. -/
theorem theorem82σ_seven_twelfths_of_print {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ}
    (hP : Prop81Print GS (5 / 12) (7 / 12)) (hD : Display81Mult GS) : Theorem82σ (7 / 12) :=
  theorem82σ_of_prop81σ _ (prop81AtMultiplesσ_of_prop81 (by norm_num) (by norm_num)
    (prop81_of_printUnif (prop81PrintUnif_of_print hP) hD))

/-- Vacuity test for `minorJ`: at `X = 4`, `ϑ = 0`, so `L = 5`, `M = 10`, `R = 1`, the point `j = 3`,
`α = 3/10`, is on `𝔪(1)`: `1/5 < |3/10 - a|` for every integer `a`. -/
theorem vacuity_minorJ : 3 ∈ minorJ 0 4 := by
  classical
  have hL : Ld 4 = 5 := by unfold Ld; norm_num
  have hM : Md 4 = 10 := by unfold Md; rw [hL]
  have hmin : Minor (Ld 4) ((4 : ℝ) ^ (0 : ℝ)) (((3 : ℕ) : ℝ) / (Md 4 : ℝ)) := by
    rw [hL, hM, Real.rpow_zero]
    intro q a hq hqR
    have hq1 : q = 1 := by
      have : (q : ℝ) ≤ 1 := hqR
      have : q ≤ 1 := by exact_mod_cast this
      omega
    subst hq1
    norm_num
    rcases le_or_gt a 0 with h | h
    · have : (a : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ a := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
  unfold minorJ
  exact mem_filter.mpr ⟨by rw [hM]; simp, hmin⟩

end

end LeanLab.ExceptionalSet.BG2026

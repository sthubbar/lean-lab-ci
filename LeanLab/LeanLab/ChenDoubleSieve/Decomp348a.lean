import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Section3

/-!
Supply split for the lower sieve bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, pages 6, 38 and 39.
The finite level retains the logarithmic loss from Lemma 2.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The filter of sufficiently large even natural numbers. -/
def evenAtTop : Filter ℕ := atTop ⊓ principal {N | Even N}

/-- The local Euler product V at the fixed lower sifting level. -/
def lowerDensity (N : ℕ) : ℝ :=
  ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))

/-- The normalized Euler product used in equations 10.2 and 10.5. -/
def scaledDensity (N : ℕ) : ℝ := log N * lowerDensity N / CN N

/-- The residual logarithmic level after fixing a divisor d. -/
def lowerLevel (B : ℝ) (N d : ℕ) : ℝ :=
  log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / d) /
    log ((N : ℝ) ^ kappa1)

/-- The finite level main term before the normalization in equation 10.2. -/
def main0 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * f (lowerLevel B N 1)

/-- The finite logarithmic loss has this exact form at divisor one. -/
theorem lowerLevel_one (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    lowerLevel B N 1 = 6 - 12 * B * (log (log N) / log N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold lowerLevel
  simp only [Nat.cast_one, div_one]
  rw [log_div (rpow_pos_of_pos hpos _).ne' (rpow_pos_of_pos hlog _).ne',
    log_rpow hpos, log_rpow hlog, log_rpow hpos]
  norm_num [kappa1]
  field_simp
  <;> ring

/-- The residual level at divisor one tends to six for each fixed loss B. -/
theorem lowerLevel_one_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => lowerLevel B N 1) atTop (𝓝 6) := by
  have hsmall : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun N : ℕ => 6 - 12 * B * (log (log N) / log N))
      atTop (𝓝 6) := by
    simpa using (tendsto_const_nhds (x := (6 : ℝ))).sub
      ((hsmall.comp hlog).const_mul (12 * B))
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (lowerLevel_one B hN).symm

/-- Divide the finite main term by the exact normalizer. -/
theorem main0_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main0 f B N / Θ N = scaledDensity N * f (lowerLevel B N 1) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main0 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']

/-- LEAF. Wu 2004 page 38, the Euler product asymptotic before equation 10.2.
Only the local density is normalized. No sieve count occurs here. -/
theorem scaledDensity_tendsto :
    Tendsto scaledDensity evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) := by
  sorry

/-- LEAF. Wu 2004 page 38, Lemmas 2.2 and 2.3 before equation 10.2.
The finite level lower sieve estimate precedes the Euler product normalization.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main0_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main0 f B N - η * Θ N ≤ sieveTerms N 0 := by
  sorry

/-- The finite main term has the required coefficient limit.
CONDITIONAL ON the OPEN Euler product asymptotic and IsLinearSieve. -/
theorem main0_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N => main0 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 0)) := by
  have hc : ContinuousAt f (6 : ℝ) := h.2.1.continuousAt (Ioi_mem_nhds (by norm_num))
  have hf : Tendsto (fun N => f (lowerLevel B N 1)) evenAtTop (𝓝 (f 6)) :=
    hc.tendsto.comp (tendsto_inf_left (lowerLevel_one_tendsto B))
  have ht := scaledDensity_tendsto.mul hf
  have ht' : Tendsto (fun N => scaledDensity N * f (lowerLevel B N 1))
      evenAtTop (𝓝 (integralTerms F f ω 0)) := by
    convert ht using 1
    change 𝓝 (2 * f (1 / (2 * kappa1)) / (kappa1 * exp eulerMascheroniConstant)) = _
    congr 1
    rw [show (1 / (2 * kappa1) : ℝ) = 6 by norm_num [kappa1]]
    ring
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main0_ratio f B hN).symm

/-- Two independent half epsilon errors give the final normalized lower bound.
This is an elementary assembly with the analytic inputs explicit. -/
theorem lower_of_main (c : ℝ) (u : ℕ → ℝ) (main : ℝ → ℕ → ℝ)
    (hsieve : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → main B N - η * Θ N ≤ u N)
    (hlimit : ∀ B : ℝ, 0 < B →
      Tendsto (fun N => main B N / Θ N) evenAtTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (c - ε) * Θ N ≤ u N := by
  intro ε hε
  obtain ⟨B, hB, M, hM⟩ := hsieve (ε / 2) (by positivity)
  have he : ∀ᶠ N in evenAtTop, c - ε / 2 < main B N / Θ N :=
    (hlimit B hB).eventually (eventually_gt_nhds (by linarith : c - ε / 2 < c))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨max 2 (max M K), ?_⟩
  intro N hEven hN
  have ht := Θ_pos (show 2 ≤ N by omega)
  have hc := (lt_div_iff₀ ht).1 (hK N (by omega) hEven)
  have hs := hM N hEven (by omega)
  nlinarith

/-- The exact lower_F0 conclusion follows from two strictly smaller leaves.
OPEN through main0_lower and scaledDensity_tendsto. -/
theorem lower_F0_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 := by
  exact lower_of_main _ _ (main0 f) (main0_lower F f h)
    (fun B _ => main0_tendsto F f ω h B)

end LeanLab.ChenDoubleSieve.Task348

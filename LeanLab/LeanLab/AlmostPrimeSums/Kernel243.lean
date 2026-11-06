import LeanLab.AlmostPrimeSums.Prime243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The moving upper sieve coefficient is bounded by the explicit prime integral.
This route needs only an upper limit and does not invoke primeCoefficient_limit.
Source: BJS https://arxiv.org/abs/2207.09452 p. 54 equations 173 to 174.
-/

namespace LeanLab.AlmostPrimeSums.Kernel243

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a
open LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Prime243

noncomputable section

/-- The level logarithm divided by log N. BJS p. 54 equation 173. -/
def levelRatio (N : ℕ) (B : ℝ) : ℝ := log (sieveLevel N B) / log N

/-- The normalized explicit prime integral upper envelope, including its
Mertens error and q minus one correction. Derived from BJS p. 54 equation 173. -/
def kernelEnvelope (N : ℕ) (B : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant *
    ((N : ℝ) ^ ((1 : ℝ) / 8) / ((N : ℝ) ^ ((1 : ℝ) / 8) - 1)) *
    ((log (8 / 3 : ℝ) + log ((levelRatio N B - 1 / 8) / (levelRatio N B - 1 / 3))) /
      (8 * levelRatio N B) + 6 / ((levelRatio N B - 1 / 3) * log N))

/-- The normalized level tends to one half for every fixed logarithmic loss.
Derived parameter limit for BJS p. 54 equation 173. -/
theorem levelRatio_limit (B : ℝ) :
    Tendsto (fun N : ℕ => levelRatio N B) atTop (𝓝 (1 / 2 : ℝ)) := by
  simpa only [levelRatio, sieveLevel, rpow_one, mul_one] using
    chen_sieve_parameter_tendsto 1 B (by norm_num)

/-- The explicit kernel envelope has the required upper prime coefficient.
Derived limit evaluation of BJS p. 54 equation 173. -/
theorem kernelEnvelope_limit (B : ℝ) :
    Tendsto (fun N : ℕ => kernelEnvelope N B) atTop
      (𝓝 (exp eulerMascheroniConstant * log 6 / 2)) := by
  have hk := levelRatio_limit B
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop
  have hzsub : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hz
  have hratio : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8) /
      ((N : ℝ) ^ ((1 : ℝ) / 8) - 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (hzsub.const_div_atTop (1 : ℝ))
    norm_num only [add_zero] at h
    apply h.congr'
    filter_upwards [hz.eventually_ge_atTop 2] with N hN
    have hn : (N : ℝ) ^ ((1 : ℝ) / 8) - 1 ≠ 0 := by linarith
    field_simp
    <;> ring
  have hq := ((hk.sub_const (1 / 8)).div (hk.sub_const (1 / 3)) (by norm_num)).log (by norm_num)
  have hmain := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => log (8 / 3 : ℝ))
    atTop (𝓝 (log (8 / 3 : ℝ)))).add hq).div (hk.const_mul 8) (by norm_num)
  have hden := (hk.sub_const (1 / 3)).pos_mul_atTop (by norm_num) hlog
  have herr := hden.const_div_atTop (6 : ℝ)
  have h := (hratio.const_mul (2 * exp eulerMascheroniConstant)).mul (hmain.add herr)
  have hlogs : log (8 / 3 : ℝ) + log (9 / 4 : ℝ) = log 6 := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num only at h
  rw [hlogs] at h
  convert h using 1 <;> try funext N
  all_goals try dsimp [kernelEnvelope]
  all_goals ring

/-- The finite prime coefficient is eventually at most the explicit envelope.
Derived application of the proved Abel bound in BJS p. 54 equation 173. -/
theorem primeCoefficient_le_envelope (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, primeCoefficient N B ≤ kernelEnvelope N B := by
  have hk := (levelRatio_limit B).eventually (lt_mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2))
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 1,
    hz.eventually_ge_atTop 2, hk] with N hN hlog1 hz2 hkN
  let k := levelRatio N B
  let l := log (N : ℝ)
  let z := (N : ℝ) ^ ((1 : ℝ) / 8)
  let y := (N : ℝ) ^ ((1 : ℝ) / 3)
  let L := log (sieveLevel N B)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < l := by dsimp [l]; linarith
  have hD : 0 < sieveLevel N B := by dsimp [sieveLevel]; positivity
  have hzlog : log z = l / 8 := by dsimp [z, l]; rw [log_rpow hNp]; ring
  have hylog : log y = l / 3 := by dsimp [y, l]; rw [log_rpow hNp]; ring
  have hL : L = k * l := by dsimp [L, k, l, levelRatio]; field_simp [hl.ne']
  have hk3 : 0 < k - 1 / 3 := by dsimp [k]; linarith
  have hk8 : 0 < k - 1 / 8 := by linarith
  have hk0 : 0 < k := by linarith
  have hhalf : L ≤ 4 * log z := by
    dsimp [L, sieveLevel]
    rw [log_div (sqrt_pos_of_pos hNp).ne' (rpow_pos_of_pos hl B).ne',
      log_sqrt hNp.le, log_rpow hl, hzlog]
    have hh : 0 ≤ B * log l := mul_nonneg hB.le (log_nonneg hlog1)
    change log (N : ℝ) / 2 - B * log (log N) ≤ 4 * (l / 8)
    dsimp [l] at *
    linarith
  have hupper : log y < L := by rw [hylog, hL]; nlinarith
  have hbound := primeCoefficient_bound N B hN hz2 hhalf hupper
  have heq :
      2 * exp eulerMascheroniConstant * log z * (z / (z - 1)) *
        (((log (log y) - log (L - log y)) -
          (log (log z) - log (L - log z))) / L + 6 / (log z * (L - log y))) =
        kernelEnvelope N B := by
    rw [hzlog, hylog, hL,
      show k * l - l / 3 = (k - 1 / 3) * l by ring,
      show k * l - l / 8 = (k - 1 / 8) * l by ring,
      log_div hl.ne' (by norm_num), log_div hl.ne' (by norm_num),
      log_mul hk3.ne' hl.ne', log_mul hk8.ne' hl.ne']
    dsimp [kernelEnvelope]
    change _ = 2 * exp eulerMascheroniConstant * (z / (z - 1)) *
      ((log (8 / 3 : ℝ) + log ((k - 1 / 8) / (k - 1 / 3))) / (8 * k) + 6 / ((k - 1 / 3) * l))
    rw [log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num), log_div hk8.ne' hk3.ne']
    have hz1 : z - 1 ≠ 0 := by dsimp [z]; linarith
    field_simp [hl.ne', hk0.ne', hk3.ne', hz1]
    <;> ring
  change primeCoefficient N B ≤ _ at hbound
  exact hbound.trans_eq heq

/-- The prime sum has the upper coefficient needed by sumSAq_upper.
No open prime sum theorem occurs in this proof. BJS p. 54 equation 173. -/
theorem primeCoefficient_upper (B : ℝ) (hB : 0 < B) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      primeCoefficient N B ≤ exp eulerMascheroniConstant * log 6 / 2 + η := by
  filter_upwards [primeCoefficient_le_envelope B hB,
    (kernelEnvelope_limit B).eventually (gt_mem_nhds (lt_add_of_pos_right _ hη))] with N hN hlim
  exact hN.trans hlim.le


end
end LeanLab.AlmostPrimeSums.Kernel243

import Mathlib
import LeanLab.ExceptionalSet.KernelMomentSupplyJ200
import LeanLab.ExceptionalSet.LargePhiSupplyJ200
import LeanLab.ExceptionalSet.State1539

/-!
First level of the proof of `Display29Steps.leaf_even_kernel_moment`, P0082 pages 368 and 369.
Source: P0082, J. Bruedern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

Proved here, from the sorry-free `KernelMomentSupplyJ200`, `VaughanSupplyJ200` and
`LargePhiSupplyJ200`: the tail removal after display (34) at the cutoff `Y = ℰ`, not the paper's
`ℰ^{1/2}`, which fails at the inner `Δ = ℰ^{-2/3}`; the squaring (37) with `Φ_e` of display (36);
the split at `|Φ_e| = N ℰ(2κ)^{-2/3}`; the small part by the `L¹` bound (38) in the weaker form
`7 log 4 X log X Δ^{-1/2}`; the large part by Lemma 9 and display (39), with the proved real
minor arc Vaughan bound in place of a cited Vinogradov estimate. No sorry is left in this file.
The only open input is Lemma 9 of the paper, the existing open statement `U1539.lemma9`, so
`Display29Steps.leaf_even_kernel_moment` is CONDITIONAL ON Lemma 9.
The file name keeps the LEAF prefix of the split plan; it holds no LEAF.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.KernelMomentSteps

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp eC majorArcs nu calE Phie)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)
open LeanLab.ExceptionalSet.KernelMomentSupplyJ200

/-- P0082 page 369, the large `Φ_e` part of the squared out moment, from the use of
Lemma 9 to the end of display (39). With `X = F(N)`, `P = X^{6δ}`, `ℰ = ℰ(κ)`, the inner
`Δ = ℰ(2κ)^{-1/3} = ℰ^{-2/3}` and the truncated minor arcs `𝔫_Y = 𝔫 ∩ [-Y, Y]` with `Y = ℰ`:
the double integral of `|S(α)² K_e(α)| |S(β)² K_e(β)| |Φ_e(β - α)|` over the pairs in
`𝔫_Y × 𝔫_Y` with `|Φ_e(β - α)| > N ℰ(2κ)^{-2/3}` is `≪ N X² ℰ^{-1/3}`.
Formerly a LEAF of this split, now proved in `LargePhiSupplyJ200.even_gram_large_of_lemma9`
from Lemma 9, with `δ₀ = min(δ₉, 1/30)` and `κ₀ = κ₉/4`, and the proved real minor arc Vaughan
bound. CONDITIONAL ON Lemma 9 through the open statement `U1539.lemma9`, as `U1539.lemma4` is
used for display (33). -/
theorem even_gram_large (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∫ z : ℝ × ℝ,
            {z : ℝ × ℝ | (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) <
                ‖Phie γ N (z.2 - z.1)‖}.indicator (fun z : ℝ × ℝ =>
              ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.1 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.1‖ *
                ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.2 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.2‖ *
                ‖Phie γ N (z.2 - z.1)‖) z
            ∂(volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N))).prod
              (volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N)))) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
  LargePhiSupplyJ200.even_gram_large_of_lemma9 U1539.lemma9 γ h1 h2

/-- `X = F(N) ≥ 2` once `N ≥ 16`. Copy of `Display29Steps.two_le_F`, which sits in a file that
imports this one. -/
theorem two_le_F' (γ : ℝ) (h1 : 1 < γ) (N : ℕ) (hN : 16 ≤ N) : 2 ≤ F γ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have he := Real.exp_one_lt_d9
    have : (16 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hp : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hL (by linarith)
  have := Real.add_one_le_exp (Real.log (N : ℝ) ^ γ)
  simp only [F]
  linarith

/-- P0082 pages 368 and 369, from display (37) to the end of the proof of display (29),
the bound of the squared out moment by absolute values. With `X = F(N)`, `P = X^{6δ}`,
`ℰ = ℰ(κ)`, the inner `Δ = ℰ(2κ)^{-1/3} = ℰ^{-2/3}` and the truncated minor arcs
`𝔫_Y = 𝔫 ∩ [-Y, Y]` with `Y = ℰ`:
`∫∫_{𝔫_Y × 𝔫_Y} |S(α)² K_e(α)| |S(β)² K_e(β)| |Φ_e(β - α)| dα dβ ≪ N X² ℰ^{-1/3}`.
The paper's proof: the pairs with `|Φ_e(β - α)| ≤ N ℰ(2κ)^{-2/3}` cost that size times the square
of the `L¹` bound (38), which holds with a loss `log(1/Δ)` or, weaker, `Δ^{-1/2}`; for the others
`|β - α| ≤ 2Y ≤ X^δ` and Lemma 9 at its `κ₉`, valid once `4κ ≤ κ₉`, puts `β - α` near `h/2`
with `|h| ≤ ℰ(κ₉)^{2/3}`, and display (39) with Vinogradov's estimate
`S(β) ≪ X P^{-1/2} (log X)^4` on the minor arcs, a CITED input needing `δ ≤ 1/15`, gives a
power saving `X^{-5δ}`. PROVED here from the split at `N ℰ(2κ)^{-2/3}`, the `L¹` bound
`7 log 4 X log X Δ^{-1/2}` of `Decomp483d`, copied, and the exponent arithmetic, with the large
part `even_gram_large`, CONDITIONAL ON Lemma 9. -/
theorem even_gram_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∫ z : ℝ × ℝ,
            ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.1 ^ 2 *
                evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.1‖ *
              ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.2 ^ 2 *
                evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.2‖ *
              ‖Phie γ N (z.2 - z.1)‖
            ∂(volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N))).prod
              (volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N)))) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := even_gram_large γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ hκle
  obtain ⟨N₃, hN₃⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  refine ⟨49 * Real.log 4 ^ 2 + B, by positivity, max (max N₁ N₃) 16, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hX : 2 ≤ F γ N := two_le_F' γ h1 N hN16
  have hE1 : 1 ≤ calE γ κ N := by
    unfold calE
    exact Real.one_le_exp (mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _))
  have hE0 : 0 < calE γ κ N := by linarith
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  have hΔ0 : 0 < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) < 1 := by
    rw [hΔeq]
    have h4 : 1 < calE γ κ N := by
      unfold calE
      exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos
        (Real.log_pos (by exact_mod_cast (by omega : 1 < N))) _))
    exact Real.rpow_lt_one_of_one_lt_of_neg h4 (by norm_num)
  set P := F γ N ^ (6 * δ)
  set X := F γ N
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))
  set E := calE γ κ N
  set A := (majorArcs P X)ᶜ ∩ Set.Icc (-E) E
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * evenKernel Δ α‖
  let φ : ℝ × ℝ → ℝ := fun z => ‖Phie γ N (z.2 - z.1)‖
  have hPc : Continuous (Phie γ N) := by unfold Phie eC; fun_prop
  have hφc : Continuous φ := (hPc.comp (continuous_snd.sub continuous_fst)).norm
  have hgc : Continuous g :=
    (((by unfold Sp eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hgI : Integrable g := by
    simpa only [g, integrand, norm_mul, U1539.norm_eC, mul_one] using
      (total_integrable P X Δ 0 hΔ0 hΔ1).norm
  have hgi : Integrable g (volume.restrict A) := hgI.integrableOn
  have hcard : ∀ x, ‖Phie γ N x‖ ≤ N := by
    intro x
    unfold Phie
    refine (norm_sum_le _ _).trans ?_
    simp only [U1539.norm_eC, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hgg : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2)
      ((volume.restrict A).prod (volume.restrict A)) := hgi.mul_prod hgi
  have hint : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2 * φ z)
      ((volume.restrict A).prod (volume.restrict A)) := by
    refine (hgg.const_mul (N : ℝ)).mono'
      (((hgc.comp continuous_fst).mul (hgc.comp continuous_snd)).mul hφc).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    have hp : 0 ≤ g z.1 * g z.2 := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_left (hcard (z.2 - z.1)) hp
    change g z.1 * g z.2 * ‖Phie γ N (z.2 - z.1)‖ ≤ (N : ℝ) * (g z.1 * g z.2)
    linarith
  have hT₀ : 0 ≤ (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hsplit := gram_split (volume.restrict A) g φ (fun _ => norm_nonneg _)
    hφc.measurable hgi hint _ hT₀
  have hL1 : (∫ x, g x ∂(volume.restrict A)) ≤
      7 * (Real.log 4 * X * Real.log X) / Real.sqrt (E ^ (-(2 / 3 : ℝ))) := by
    rw [← hΔeq]
    exact (setIntegral_le_integral hgI (Filter.Eventually.of_forall
      (fun _ => norm_nonneg _))).trans (shifted_weighted_mass_sqrt P X Δ hX hΔ0 hΔ1)
  have hsmall := small_part_le N X E _ (Nat.cast_nonneg N) hX hE1 (hN₃ N hN3)
    (integral_nonneg (fun _ => norm_nonneg _)) hL1
  rw [← calE_two_mul_twothirds] at hsmall
  have hlarge := hN₁ N hN1
  calc _ ≤ _ := hsplit
    _ ≤ 49 * Real.log 4 ^ 2 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      refine add_le_add ?_ hlarge
      calc _ = (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) *
            (∫ x, g x ∂(volume.restrict A)) ^ 2 := by ring
        _ ≤ _ := hsmall
    _ = _ := by ring

/-- P0082 pages 368 and 369, the proof of display (29) from the right side of (32): the tail
removal after (34) at `Y = ℰ`, the squaring (37), and the exponent arithmetic of the tail term
at `Δ = ℰ^{-2/3}` are PROVED; the absolute double integral is `even_gram_bound`.
The conclusion is exactly the statement of `Display29Steps.leaf_even_kernel_moment`. -/
theorem even_kernel_moment_of_steps (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
              Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
                OddKernel467.evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) α *
                  eC (-(α * F γ n))‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := even_gram_bound γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ hκle
  obtain ⟨N₂, hN₂⟩ := four_le_calE γ κ h2 hκ
  obtain ⟨N₃, hN₃⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  refine ⟨2 * B + 128 * Real.log 4 ^ 2, by positivity, max (max N₁ N₂) (max N₃ 16),
    fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set E := calE γ κ N with hEdef
  set X := F γ N with hXdef
  set P := F γ N ^ (6 * δ) with hPdef
  have hE4 : 4 ≤ E := hN₂ N hN2
  have hX : 2 ≤ X := two_le_F' γ h1 N hN16
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = E ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) with hΔdef
  have hE0 : 0 < E := by linarith
  have hΔ0 : 0 < Δ := by rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := by
    rw [hΔeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  let s := (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n))
  have hmt := moment_tail_gram P X Δ E hX hΔ0 hΔ1 hE4 (majorArcs P X)ᶜ s (fun n => F γ n)
  have hgram := hN₁ N hN1
  have htail : (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * E)) ^ 2 ≤
      64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]
    exact tail_sq_le X E hX (by linarith) (hN₃ N hN3)
  have hcard : (s.card : ℝ) ≤ N := by
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hEn : 0 ≤ E ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hE0 _).le
  have hXn : 0 ≤ X ^ 2 := sq_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl4 : 0 ≤ Real.log 4 ^ 2 := sq_nonneg _
  have hτ0 : 0 ≤ (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * E)) ^ 2 := sq_nonneg _
  have hsum : (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ, Sp P X α ^ 2 * evenKernel Δ α *
      eC (-(α * F γ n))‖ ^ 2) ≤
      2 * (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        2 * N * (64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ))) := by
    refine hmt.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hgram (by norm_num)
    · have h3 := mul_le_mul hcard htail hτ0 hNn
      nlinarith [h3]
  calc _ ≤ 2 * (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        2 * N * (64 * Real.log 4 ^ 2 * X ^ 2 * E ^ (-(1 / 3 : ℝ))) := hsum
    _ = (2 * B + 128 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by ring

end LeanLab.ExceptionalSet.KernelMomentSteps

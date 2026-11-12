import Mathlib
import LeanLab.ExceptionalSet.EvenMinorSupplyJ200
import LeanLab.ExceptionalSet.LEAF_kernel_moment_steps

/-!
First level of the proof of displays (29) and (30) of P0082, pages 367 to 369.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

Page 367 to 368: Lemma 1 with the kernel `K_e` of (31) turns `R₂(ν_n + 1)` into the kernel
integral `∫_𝔫 S² K_e e(-αF(n)) dα` unless `{F(n)}` is within `Δ/2` of an integer, display (32);
those boundary `n` are counted by Lemma 4 and each costs at most `(X log X)²`, display (33).
Both steps are proved in `EvenMinorSupplyJ200`, the count CONDITIONAL ON Lemma 4.

What is left is one LEAF per parity: the second moment of the kernel integrals over the
paper's range `𝒩_e`, resp. `𝒩_o`, is `≪ N X² ℰ^{-1/3}`. On pages 368 and 369 the paper proves
this by the tail removal beyond `Y`, display (35), the squaring (37) with `Φ_e` of (36), the split
at `|Φ_e| ≤ N ℰ^{-2/3}`, the `L¹` bound (38), Lemma 9 and display (39) with Vinogradov's bound
`S(β) ≪ X P^{-1/2} (log X)^4` on the minor arcs.

Parameters. As printed, `Δ = ℰ^{-1/3}` of (34) leaves `R ≪ N X² (log X)² ℰ^{-1/3}` in (33),
a logarithm too many for the exact `ℰ^{-1/3}` of (29). Here the argument runs at the inner scale
`ℰ' = ℰ(2κ) = ℰ²`, with `Δ = ℰ'^{-1/3}` exactly as (34) at `ℰ'`, and the target bound
`N X² ℰ^{-1/3} = N X² ℰ'^{-1/6}` leaves a power `ℰ'^{1/6}` for every logarithm. The leaves
choose `κ` after `δ` with "there is `κ₀`, for all `κ ≤ κ₀`", as the targets do.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.Display29Steps

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp eC majorArcs nu calE Lemma4)
open LeanLab.ExceptionalSet.OddSupplyJ200 (R2)
open LeanLab.ExceptionalSet.EvenMinorSupplyJ200

/-- Formerly a LEAF. P0082 pages 368 and 369, from the right side of display (32) to the end of the proof
of display (29): with `X = F(N)`, `P = X^{6δ}`, `ℰ' = ℰ(2κ)` and `Δ = ℰ'^{-1/3}` as in (34),
`Σ_{n ∈ 𝒩_e} |∫_𝔫 S(α)² K_e(α) e(-αF(n)) dα|² ≪ N X² ℰ^{-1/3}`, where
`𝒩_e = {N/2 < n ≤ N : ν_n even}` is the index set of `Φ_e`, display (36).
The paper's proof: remove the tail beyond `Y` by the decay of `K_e`, display (35); square out,
display (37); the pairs with `|Φ_e(β - α)| ≤ N ℰ'^{-2/3}` cost `N ℰ'^{-2/3}` times the square of
the `L¹` bound (38); the others lie near `h/2` with `|h| ≤ ℰ^{2/3}` by Lemma 9 and are bounded
in (39) by Vinogradov's estimate `S(β) ≪ X P^{-1/2} (log X)^4`, a CITED input.
No longer a sorry: proved in `LEAF_kernel_moment_steps` from the tail removal at `Y = ℰ`, the
squaring, the split at the size of `Φ_e`, the `L¹` bound and display (39), all PROVED, with
Lemma 9 taken from the open statement `U1539.lemma9`. CONDITIONAL ON Lemma 9. -/
theorem leaf_even_kernel_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
              Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
                OddKernel467.evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) α *
                  eC (-(α * F γ n))‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
  KernelMomentSteps.even_kernel_moment_of_steps γ h1 h2

/-- LEAF. P0082 page 369 after (39), the cognate of `leaf_even_kernel_moment` for display (30):
`w_e(α)` is replaced by `w_o(α) = w_e(-α)`, whose inverse transform is
`EvenMinorSupplyJ200.oddKernel`, and `𝒩_e` by `𝒩_o = {N/2 < n ≤ N : ν_n odd}`. Same parameters,
same argument with `Φ_o(α) = Σ_{n ∈ 𝒩_o} e(αF(n))` in place of `Φ_e`. Open. -/
theorem leaf_odd_kernel_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ Even (nu γ n)),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ,
              Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
                oddKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) α *
                  eC (-(α * F γ n))‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- `X = F(N) ≥ 2` once `N ≥ 16`. -/
theorem two_le_F (γ : ℝ) (h1 : 1 < γ) (N : ℕ) (hN : 16 ≤ N) : 2 ≤ F γ N := by
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

/-- `0 < Δ < 1` for `Δ = ℰ(2κ)^{-1/3}` once `N ≥ 16`. -/
theorem delta_bounds (γ κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 16 ≤ N) :
    0 < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) ∧ calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) < 1 := by
  have hEgt : 1 < calE γ (2 * κ) N := by
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_lt_one_of_one_lt_of_neg hEgt (by norm_num)⟩

/-- P0082 page 367 display (29) on the lab window, from displays (32) and (33) and the leaf
`leaf_even_kernel_moment`. CONDITIONAL ON Lemma 4. -/
theorem even_minor_moment_of_steps (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter
                (fun n => Even (nu γ n)),
            ‖R2 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := leaf_even_kernel_moment γ h1 h2
  obtain ⟨κ₄, hκ₄, hb⟩ := boundary_moment_of_lemma4 h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨min κ₀ κ₄, lt_min hκ₀ hκ₄, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ (hκle.trans (min_le_left _ _))
  obtain ⟨C, hC, N₂, hN₂⟩ := hb κ hκ (hκle.trans (min_le_right _ _))
  refine ⟨B + C, by positivity, max (max N₁ N₂) 16, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hΔ0, hΔ1⟩ := delta_bounds γ κ hκ N hN16
  let s := (win γ N).filter (fun n => Even (nu γ n))
  have ht := moment_transfer (F γ N ^ (6 * δ)) (F γ N) (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)))
    (two_le_F γ h1 N hN16) hΔ0 hΔ1 s (fun n => F γ n)
  have hsub : s ⊆ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hw, he⟩
    exact Finset.mem_filter.mpr ⟨win_subset_Ioc γ h1 N hN16 hw, he⟩
  have hl := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity)).trans (hN₁ N hN1)
  have hbd := hN₂ N hN2 s (Finset.filter_subset _ _)
  have hfin := ht.trans (add_le_add hl hbd)
  calc _ = _ := rfl
    _ ≤ _ := hfin
    _ = _ := by ring

/-- P0082 page 367 display (30) on the lab window, from the cognates of (32) and (33) and the
leaf `leaf_odd_kernel_moment`. CONDITIONAL ON Lemma 4. -/
theorem odd_minor_moment_of_steps (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.range (2 * N + 1)).filter
              (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter
                (fun n => ¬ Even (nu γ n)),
            ‖R2 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hL⟩ := leaf_odd_kernel_moment γ h1 h2
  obtain ⟨κ₄, hκ₄, hb⟩ := boundary_moment_of_lemma4 h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  obtain ⟨κ₀, hκ₀, hL2⟩ := hL δ hδ hδ₀'
  refine ⟨min κ₀ κ₄, lt_min hκ₀ hκ₄, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₁, hN₁⟩ := hL2 κ hκ (hκle.trans (min_le_left _ _))
  obtain ⟨C, hC, N₂, hN₂⟩ := hb κ hκ (hκle.trans (min_le_right _ _))
  refine ⟨B + C, by positivity, max (max N₁ N₂) 16, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hΔ0, hΔ1⟩ := delta_bounds γ κ hκ N hN16
  let s := (win γ N).filter (fun n => ¬ Even (nu γ n))
  have ht := moment_transfer_odd (F γ N ^ (6 * δ)) (F γ N)
    (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) (two_le_F γ h1 N hN16) hΔ0 hΔ1 s (fun n => F γ n)
  have hsub : s ⊆ (Finset.Ioc (N / 2) N).filter (fun n => ¬ Even (nu γ n)) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hw, he⟩
    exact Finset.mem_filter.mpr ⟨win_subset_Ioc γ h1 N hN16 hw, he⟩
  have hl := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity)).trans (hN₁ N hN1)
  have hbd := hN₂ N hN2 s (Finset.filter_subset _ _)
  have hfin := ht.trans (add_le_add hl hbd)
  calc _ = _ := rfl
    _ ≤ _ := hfin
    _ = _ := by ring

end LeanLab.ExceptionalSet.Display29Steps

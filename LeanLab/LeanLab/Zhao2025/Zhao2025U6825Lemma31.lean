import Mathlib
import LeanLab.Pintz2018.Section9

/-!
# Zhao 2025, Lemma 3.1 arithmetic: the 19.62 of (3.13) and the 99.728 of (3.19)

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6825, CLOUD 20261021T0316Z-cloud57.  AI wrote the Lean code.

`B` is Zhao's (2.15) with `ϕ = 1/3`, `C` is his (3.5) with `t₁ = ϕ + x + y`, `t₂ = z`.
Proved unconditionally here: two-sided enclosures of `C` at the parameters of (3.13) and of
(3.18), so `19.61 ≤ C ≤ 19.62` and `99.72 ≤ C ≤ 99.73`, the prefactors `156` and the exponents
`k`; `10/3 - k = 3334/1500 < 2.226` at (3.18), a cosmetic misprint candidate.
Conditional: (3.13) itself, from Lemma 3.1 in the form (3.12) and the monotonicity of `C` in `Λ`
that Zhao uses (his Lemma 2.3), both as named hypotheses, with a vacuity instance.
Binary Goldbach is open.
-/

namespace LeanLab.Zhao2025.U6825

open LeanLab.Pintz2018

/-- Zhao (2.15), `ϕ = 1/3`. -/
noncomputable def B (t0 l l0 : ℝ) : ℝ :=
  1 / 3 / 2 * ((1 - Real.exp (-(2 * (l + l0) * t0))) / (l + l0)) +
    (1 - Real.exp (-(l * t0))) / (l * (l + l0)) +
    (Real.exp (-(2 * (l + l0) * t0)) - Real.exp (-(l * t0))) / ((l + l0) * (l + 2 * l0))

/-- Zhao (3.5), `ϕ = 1/3`. -/
noncomputable def C (x y z L l0 : ℝ) : ℝ :=
  1 / (x * z) * (1 / 2 + (1 / 3 + x) / y) * Real.sqrt (B (1 / 3 + x + y) L l0 * B z L l0)

theorem eb_up (a u : ℝ) (ha : 0 ≤ a) (h : ((T15 (a / 8)) ^ 8)⁻¹ ≤ u) : Real.exp (-a) ≤ u :=
  (expneg_upper a ha).trans h

theorem eb_lo (a v : ℝ) (ha : 0 ≤ a) (h8 : a ≤ 8)
    (h : v ≤ ((T15 (a / 8) + (a / 8) ^ 15 * (16 / ((Nat.factorial 15 : ℝ) * 15))) ^ 8)⁻¹) :
    v ≤ Real.exp (-a) :=
  h.trans (expneg_lower a ha h8)

/-! ### Exponential enclosures, width `10⁻¹⁰` -/

theorem e1 : 0.089397133 ≤ Real.exp (-(3622 / 1500)) ∧ Real.exp (-(3622 / 1500)) ≤ 0.0893971331 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem e2 : 0.4172790901 ≤ Real.exp (-(0.874)) ∧ Real.exp (-(0.874)) ≤ 0.4172790902 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem e3 : 0.5468030114 ≤ Real.exp (-(1811 / 3000)) ∧ Real.exp (-(1811 / 3000)) ≤ 0.5468030115 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem e4 : 0.8037234794 ≤ Real.exp (-(0.2185)) ∧ Real.exp (-(0.2185)) ≤ 0.8037234795 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem f1 : 0.0097404626 ≤ Real.exp (-(8684 / 1875)) ∧ Real.exp (-(8684 / 1875)) ≤ 0.0097404627 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem f2 : 0.098693782 ≤ Real.exp (-(4342 / 1875)) ∧ Real.exp (-(4342 / 1875)) ≤ 0.0986937821 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem f3 : 0.5822822402 ≤ Real.exp (-(0.5408)) ∧ Real.exp (-(0.5408)) ≤ 0.5822822403 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem f4 : 0.7630742036 ≤ Real.exp (-(0.2704)) ∧ Real.exp (-(0.2704)) ≤ 0.7630742037 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

/-! ### `B` enclosures -/

/-- `B(t₁, 1.311, 1/2)`, `t₁ = 2/3`, the first factor of (3.13). -/
theorem B313a : 0.25089682 ≤ B (1 / 3 + 1 / 12 + 1 / 4) 1.311 (1 / 2) ∧
    B (1 / 3 + 1 / 12 + 1 / 4) 1.311 (1 / 2) ≤ 0.25089683 := by
  unfold B
  rw [show (2 * (1.311 + 1 / 2) * (1 / 3 + 1 / 12 + 1 / 4) : ℝ) = 3622 / 1500 by norm_num,
    show (1.311 * (1 / 3 + 1 / 12 + 1 / 4) : ℝ) = 0.874 by norm_num]
  obtain ⟨a1, a2⟩ := e1; obtain ⟨b1, b2⟩ := e2
  generalize Real.exp (-(3622 / 1500)) = E at *
  generalize Real.exp (-0.874) = F at *
  constructor <;> norm_num <;> linarith

/-- `B(1/6, 1.311, 1/2)`, the second factor of (3.13). -/
theorem B313b : 0.06299011 ≤ B (1 / 6) 1.311 (1 / 2) ∧ B (1 / 6) 1.311 (1 / 2) ≤ 0.06299012 := by
  unfold B
  rw [show (2 * (1.311 + 1 / 2) * (1 / 6) : ℝ) = 1811 / 3000 by norm_num,
    show (1.311 * (1 / 6) : ℝ) = 0.2185 by norm_num]
  obtain ⟨a1, a2⟩ := e3; obtain ⟨b1, b2⟩ := e4
  generalize Real.exp (-(1811 / 3000)) = E at *
  generalize Real.exp (-0.2185) = F at *
  constructor <;> norm_num <;> linarith

/-- `B(t₁, 5.2, 0)`, `t₁ = 1/3 + 0.029 + 0.083`, the first factor of (3.19). -/
theorem B319a : 0.06178172 ≤ B (1 / 3 + 0.029 + 0.083) 5.2 0 ∧
    B (1 / 3 + 0.029 + 0.083) 5.2 0 ≤ 0.06178173 := by
  unfold B
  rw [show (2 * (5.2 + 0) * (1 / 3 + 0.029 + 0.083) : ℝ) = 8684 / 1875 by norm_num,
    show (5.2 * (1 / 3 + 0.029 + 0.083) : ℝ) = 4342 / 1875 by norm_num]
  obtain ⟨a1, a2⟩ := f1; obtain ⟨b1, b2⟩ := f2
  generalize Real.exp (-(8684 / 1875)) = E at *
  generalize Real.exp (-(4342 / 1875)) = F at *
  constructor <;> norm_num <;> linarith

/-- `B(0.052, 5.2, 0)`, the second factor of (3.19). -/
theorem B319b : 0.01546434 ≤ B 0.052 5.2 0 ∧ B 0.052 5.2 0 ≤ 0.01546435 := by
  unfold B
  rw [show (2 * (5.2 + 0) * 0.052 : ℝ) = 0.5408 by norm_num,
    show (5.2 * 0.052 : ℝ) = 0.2704 by norm_num]
  obtain ⟨a1, a2⟩ := f3; obtain ⟨b1, b2⟩ := f4
  generalize Real.exp (-0.5408) = E at *
  generalize Real.exp (-0.2704) = F at *
  constructor <;> norm_num <;> linarith

/-! ### `C` enclosures -/

theorem sqrt_enclose {P B1 B2 l1 u1 l2 u2 lo hi : ℝ} (hP : 0 < P) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (h1 : l1 ≤ B1 ∧ B1 ≤ u1) (h2 : l2 ≤ B2 ∧ B2 ≤ u2) (hlo : 0 ≤ lo) (hlo' : lo ^ 2 ≤ P ^ 2 * (l1 * l2))
    (hhi : 0 ≤ hi) (hhi' : P ^ 2 * (u1 * u2) ≤ hi ^ 2) :
    lo ≤ P * Real.sqrt (B1 * B2) ∧ P * Real.sqrt (B1 * B2) ≤ hi := by
  have hB1 : 0 ≤ B1 := hl1.trans h1.1
  have hB : l1 * l2 ≤ B1 * B2 := mul_le_mul h1.1 h2.1 hl2 hB1
  have hB' : B1 * B2 ≤ u1 * u2 := mul_le_mul h1.2 h2.2 (hl2.trans h2.1) (hB1.trans h1.2)
  have e : P * Real.sqrt (B1 * B2) = Real.sqrt (P ^ 2 * (B1 * B2)) := by
    rw [Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP.le]
  rw [e]
  constructor
  · calc lo = Real.sqrt (lo ^ 2) := (Real.sqrt_sq hlo).symm
      _ ≤ _ := Real.sqrt_le_sqrt (hlo'.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg P)))
  · calc Real.sqrt (P ^ 2 * (B1 * B2)) ≤ Real.sqrt (hi ^ 2) :=
          Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left hB' (sq_nonneg P)).trans hhi')
      _ = hi := Real.sqrt_sq hhi

/-- The prefactor of (3.5) at the parameters of (3.13) is `156`, the same as Pintz's. -/
theorem pref313 : (1 / ((1 / 12 : ℝ) * (1 / 6)) * (1 / 2 + (1 / 3 + 1 / 12) / (1 / 4))) = 156 := by
  norm_num

/-- (3.13): `C(1/12, 1/4, 1/6, 1.311, 1/2) ∈ [19.61, 19.62]`; Python gives `19.61139`, printed `19.62`. -/
theorem C313 : 19.61 ≤ C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2) ∧
    C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2) ≤ 19.62 := by
  unfold C
  exact sqrt_enclose (by norm_num) (by norm_num) (by norm_num) B313a B313b (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- (3.19): `C(0.029, 0.083, 0.052, 5.2, 0) ∈ [99.72, 99.73]`; Python `99.72832`, printed `99.728···`. -/
theorem C319 : 99.72 ≤ C 0.029 0.083 0.052 5.2 0 ∧ C 0.029 0.083 0.052 5.2 0 ≤ 99.73 := by
  unfold C
  exact sqrt_enclose (by norm_num) (by norm_num) (by norm_num) B319a B319b (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### Exponents -/

/-- (3.3), `M = O(1)` branch, at (3.18): `10/3 - k = 3334/1500 = 2.2226…`, below the printed
`2.226···`. Cosmetic misprint candidate; the proof of (3.16) only uses `2.22`. -/
theorem k319_exact : (10 / 3 : ℝ) - 2 * (1 / 3 + 3 * 0.029 + 0.083 + 0.052) = 3334 / 1500 ∧
    (3334 / 1500 : ℝ) < 2.226 := by
  constructor <;> norm_num

-- (3.3), general branch, at (3.13): `k = 8/3` is `LeanLab.Zhao2025.k_313` in Section4.lean, not repeated.

/-- (3.19) feeds (3.16) at `Λ = 5.2`: `99.73 · e^{-(3334/1500) · 5.2} ≤ 100 e^{-2.22 · 5.2}`. -/
theorem cor32_at_52 : 99.73 * Real.exp (-(3334 / 1500 * 5.2)) ≤ 100 * Real.exp (-(2.22 * 5.2)) := by
  have : Real.exp (-(3334 / 1500 * 5.2)) ≤ Real.exp (-(2.22 * 5.2)) :=
    Real.exp_le_exp.mpr (by norm_num)
  nlinarith [Real.exp_pos (-(3334 / 1500 * 5.2))]

/-! ### (3.13), conditional -/

/-- (3.13) CONDITIONAL ON two named inputs: `h312`, Zhao's (3.12), Lemma 3.1 counted as
`N(Λ) ≤ (1+ε) C(Λ) e^{kΛ}` with `k = 8/3`, and `hmono`, `C(Λ) ≤ C(1.311)` for `Λ ≥ 1.311`, the
monotonicity Zhao takes from Lemma 2.3. `Cf` is meant as `Λ ↦ C(1/12, 1/4, 1/6, Λ, 1/2)`. -/
theorem eq313_conditional (N Cf : ℝ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h312 : ∀ L, 1.311 ≤ L → N L ≤ (1 + ε) * Cf L * Real.exp (8 / 3 * L))
    (hmono : ∀ L, 1.311 ≤ L → Cf L ≤ Cf 1.311)
    (hval : Cf 1.311 = C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2)) :
    ∀ L, 1.311 ≤ L → N L ≤ (1 + ε) * 19.62 * Real.exp (8 / 3 * L) := by
  intro L hL
  have h1 := h312 L hL
  have h2 : Cf L ≤ 19.62 := (hmono L hL).trans (hval ▸ C313.2)
  have h3 : 0 < (1 + ε) * Real.exp (8 / 3 * L) := by positivity
  nlinarith

/-- Vacuity instance: the hypotheses of `eq313_conditional` are jointly satisfiable. -/
theorem eq313_vacuity : ∃ (N Cf : ℝ → ℝ),
    (∀ L, 1.311 ≤ L → N L ≤ (1 + 0) * Cf L * Real.exp (8 / 3 * L)) ∧
    (∀ L, 1.311 ≤ L → Cf L ≤ Cf 1.311) ∧ Cf 1.311 = C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2) := by
  refine ⟨fun _ => 0, fun _ => C (1 / 12) (1 / 4) (1 / 6) 1.311 (1 / 2), ?_, fun _ _ => le_rfl, rfl⟩
  intro L _
  have := C313.1
  have : 0 < Real.exp (8 / 3 * L) := Real.exp_pos _
  positivity

/-! ### The lambda0 lever in Zhao's critical case (4.24), arithmetic only

Inputs from numerics/zhao_U6825_split.out, AI-written Python: with `λ₀ = 0` in place of Zhao's
`λ₀ = 0.60, 0.91`, (3.27) and (3.15) give `max Tᵢ ≥ 0.1187`, `Σ Tᵢ ≥ 8.864`; with only the
`i ≥ 3` bound kept at `λ₀ = 0.702`, `max_{i≥3} Tᵢ ≥ 0.09724`. The printed `R` inputs `0.3`, `0.581`
are kept. These are the right side of (4.24), not a bound on Zhao's sum. -/

theorem split_lambda0_zero :
    1.364 < (0.3 : ℝ) * 0.581 + 0.1187 * (2 * 0.581 + 8.864) + 2 * ((0.1187 - 0.1187) * (2 * 0.3 + 0.1187)) := by
  norm_num

theorem split_i3_0702 :
    1.179 < (0.3 : ℝ) * 0.581 + 0.09724 * (2 * 0.581 + 8.864) + 2 * ((0.11871 - 0.09724) * (2 * 0.3 + 0.11871)) := by
  norm_num

end LeanLab.Zhao2025.U6825

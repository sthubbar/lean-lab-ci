import Mathlib
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.BoundarySupplyJ200
import LeanLab.ExceptionalSet.CoeffSupplyJ200
import LeanLab.ExceptionalSet.GammaOne465
import LeanLab.ExceptionalSet.GammaParameters465
import LeanLab.ExceptionalSet.GammaSplit465
import LeanLab.ExceptionalSet.GammaRanges465
import LeanLab.ExceptionalSet.NearWindow465
import LeanLab.ExceptionalSet.Arithmetic465
import LeanLab.ExceptionalSet.Growth465
import LeanLab.ExceptionalSet.Decomp465b
import LeanLab.HeathBrown1985.DivisorEps

/-!
Upstream supply of Lemma 5, display (22) and the counting part of Lemma 7 of P0082 for
`DecompJ200.leaf_major_even_coefficient`.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, pages 359 to 364, displays (14) to (22).

`DecompJ200` defines `window` and is imported by `Decomp371a`, `Endpoint465`, `Progressions465`,
`FarWindow465`, `GammaMean465`, `GammaTwoMean465`, `LargeGcd465`, `Decomp465a`, `Decomp465c` and
`Decomp467b`, so it cannot import their proved results. This file copies those proofs verbatim,
with `window` read as the literal window `BoundarySupplyJ200.windowSet`, definitionally
`DecompJ200.window`, and with the `Decomp371a` window lemmas read from their copies in
`BoundarySupplyJ200`. The files of the 465 chain that do not import `DecompJ200` are imported
directly. No statement is changed.

Every result here that uses the discrepancy estimate is CONDITIONAL ON `Lemma4`, an explicit
hypothesis, and the counting results are CONDITIONAL ON the explicit pointwise hypothesis
`hpoint` as well; no `sorry` occurs in this file.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu)

/-- The window of section 5, p. 366: `n ≤ 2N` with `X/2 < ν_n ≤ X`, `X = F(N)`, written out in
`BoundarySupplyJ200.windowSet`; definitionally `DecompJ200.window γ N`. -/
noncomputable abbrev window (γ : ℝ) (N : ℕ) : Finset ℕ := BoundarySupplyJ200.windowSet γ N

end LeanLab.ExceptionalSet.EvenSupplyJ200

-- Copied from `Endpoint465`, proof unchanged up to the window and namespace renaming.


namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 pages 358 and 362, range of the even integer in Lemma7.
Every interior window index has both adjacent integers below X. -/
theorem adjacent_le_X (γ : ℝ) (hγ : 1 < γ) (N n : ℕ) (hN : 16 ≤ N)
    (hn : n ∈ window γ N) (hnN : n < N) (j : ℤ) (hj : j ≤ 1) :
    (nu γ n + j : ℝ) ≤ F γ N := by
  have hi := mem_Ioc.mp (BoundarySupplyJ200.window_subset_Ioc γ hγ N hN hn)
  have hn8 : 8 ≤ n := by omega
  have hstep : (1 : ℝ) ≤ (N : ℝ) - n := by
    have hcast : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    linarith
  have hg := BoundarySupplyJ200.F_growth γ n N hγ (by exact_mod_cast hn8)
    (by exact_mod_cast hnN.le)
  have hmul := mul_le_mul_of_nonneg_left hstep (show 0 ≤ γ by linarith)
  have hfloor : (nu γ n : ℝ) ≤ F γ n := Int.floor_le _
  have hjR : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  linarith

/-- P0082 page 364, absorbing one endpoint into the exceptional count.
For kappa at most one and N at least eight, N E to minus one twelfth is at least one. -/
theorem one_le_count_scale (γ κ : ℝ) (hγ : 1 < γ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (N : ℕ) (hN : 8 ≤ N) :
    1 ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have h := Real.log_two_gt_d9
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hL : 1 ≤ Real.log (N : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hp : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show 3 - 2 * γ ≤ 1 by linarith)
  have hp0 : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  have hk : κ / 12 * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log N := by
    have h := mul_le_mul_of_nonneg_right (show κ / 12 ≤ 1 by linarith) hp0
    linarith
  rw [calE, ← Real.exp_mul, ← Real.exp_log hN0, ← Real.exp_add]
  apply Real.one_le_exp
  simp only [Real.log_exp]
  nlinarith

end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `Progressions465`, proof unchanged up to the window and namespace renaming.


namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page 360 before display16. A floor residue a modulo d
places the fractional part of x over d in the interval from a over d
to a plus one over d. Only this direction is needed for an upper count. -/
theorem floor_residue_fract (x : ℝ) (d : ℕ) (hd : 0 < d) (a : ℤ)
    (ha : 0 ≤ a) (had : a < d) (hdiv : (d : ℤ) ∣ ⌊x⌋ - a) :
    (a : ℝ) / d ≤ Int.fract (x / d) ∧
      Int.fract (x / d) < ((a : ℝ) + 1) / d := by
  obtain ⟨k, hk⟩ := hdiv
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hadR : (a : ℝ) + 1 ≤ d := by exact_mod_cast (show a + 1 ≤ d by omega)
  have hfloor : (⌊x⌋ : ℝ) - a = (d : ℝ) * k := by exact_mod_cast hk
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  let t := ((a : ℝ) + Int.fract x) / d
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hd0]
    linarith
  have hx : x / d = (k : ℝ) + t := by
    have he := Int.fract_add_floor x
    dsimp [t]
    field_simp
    linarith [Int.fract_add_floor x]
  rw [hx, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨ht0, ht1⟩]
  constructor
  · dsimp [t]
    exact div_le_div_of_nonneg_right (by linarith) hd0.le
  · dsimp [t]
    exact (div_lt_div_iff_of_pos_right hd0).mpr (by linarith)

end LeanLab.ExceptionalSet.EvenSupplyJ200

namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page360 display16 for either adjacent shift. CONDITIONAL ON
Lemma4 as an explicit hypothesis. This supplies divisibility progression
upper counts and does not assert any major coefficient estimate. -/
theorem progression_counts (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
                C * ((N : ℝ) / d + N / calE γ κ N) := by
  classical
  obtain ⟨κ₀, B, hκ₀, hdisc⟩ := h4 γ h1 h2
  refine ⟨1 / 12, by norm_num, fun δ hδ hδsmall =>
    ⟨κ₀, hκ₀, fun κ hκ hκsmall => ⟨|B| + 1, by positivity, 16, ?_⟩⟩⟩
  intro N hN d hd hdP j hj
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hX : 1 < F γ N := by
    apply Real.one_lt_exp_iff.mpr
    exact Real.rpow_pos_of_pos hL γ
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hdl : (d : ℝ) < F γ N ^ (1 / 2 : ℝ) := hdP.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hX (by linarith))
  have hαlow : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ) / d| := by
    rw [abs_of_pos (by positivity), Real.rpow_neg hX0.le]
    simpa only [one_div] using one_div_lt_one_div_of_lt hd0 hdl
  have hαhigh : |(1 : ℝ) / d| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hd0]
    exact hd1
  let a : ℤ := if j = 0 then 0 else (d : ℤ) - 1
  have ha : 0 ≤ a := by rcases hj with rfl | rfl <;> simp [a] <;> omega
  have had : a < d := by rcases hj with rfl | rfl <;> simp [a] <;> omega
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hadR : (a : ℝ) + 1 ≤ d := by exact_mod_cast (show a + 1 ≤ d by omega)
  let z₂ := (a : ℝ) / d
  let z₁ := ((a : ℝ) + 1) / d
  have hz₂ : 0 ≤ z₂ := by dsimp [z₂]; positivity
  have hzlt : z₂ < z₁ := by dsimp [z₁, z₂]; exact (div_lt_div_iff_of_pos_right hd0).mpr (by linarith)
  have hz₁ : z₁ ≤ 1 := by dsimp [z₁]; exact (div_le_one hd0).mpr hadR
  have hsub : (window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract ((1 / d : ℝ) * F γ n) ∧
        Int.fract ((1 / d : ℝ) * F γ n) < z₁) := by
    intro n hn
    obtain ⟨hnw, hnd⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨BoundarySupplyJ200.window_subset_Ioc γ h1 N hN hnw, ?_⟩
    have hdiv : (d : ℤ) ∣ nu γ n - a := by
      rcases hj with rfl | rfl
      · simpa [a] using hnd
      · have ht := dvd_sub hnd (dvd_refl (d : ℤ))
        convert ht using 1 <;> simp [a] <;> ring
    have hf := floor_residue_fract (F γ n) d (by omega) a ha had hdiv
    simpa only [z₁, z₂, one_div, mul_comm (d : ℝ)⁻¹, ← div_eq_mul_inv] using hf
  have hD := hdisc N (by omega) (1 / d) hαlow hαhigh z₁ z₂ hz₂ hzlt hz₁
  have hcount := (abs_le.mp hD).2
  have hcard : (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
      (((Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract ((1 / d : ℝ) * F γ n) ∧
        Int.fract ((1 / d : ℝ) * F γ n) < z₁)).card : ℝ) := by exact_mod_cast card_le_card hsub
  have hz : z₁ - z₂ = 1 / d := by dsimp [z₁, z₂]; ring
  have hmain : (z₁ - z₂) * (N : ℝ) / 2 ≤ (N : ℝ) / d := by
    rw [hz]
    have : 0 ≤ (N : ℝ) / d := by positivity
    rw [show (1 / (d : ℝ)) * (N : ℝ) / 2 = (N : ℝ) / d / 2 by ring]
    linarith
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hL.le _
  have hexp : Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤
      1 / calE γ κ N := by
    rw [calE, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hB : B * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤
      |B| * (N : ℝ) / calE γ κ N := by
    calc
      _ ≤ |B| * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)) (by positivity)
      _ ≤ |B| * N * (1 / calE γ κ N) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hq : 0 ≤ (N : ℝ) / d := by positivity
  have hqE : 0 ≤ (N : ℝ) / calE γ κ N := div_nonneg (Nat.cast_nonneg N) (show 0 ≤ calE γ κ N from (Real.exp_pos _).le)
  calc
    _ ≤ (z₁ - z₂) * (N : ℝ) / 2 +
        B * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by linarith
    _ ≤ (N : ℝ) / d + |B| * N / calE γ κ N := add_le_add hmain hB
    _ ≤ _ := by
      rw [show |B| * (N : ℝ) / calE γ κ N = |B| * ((N : ℝ) / calE γ κ N) by ring]
      nlinarith [mul_nonneg (abs_nonneg B) hq]

end LeanLab.ExceptionalSet.EvenSupplyJ200

namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page360 display16 in the strict square root modulus range.
CONDITIONAL ON the explicit Lemma4 discrepancy input. This wider range
is used for the finite part of the Gamma2 tail through X to one third. -/
theorem progression_counts_below_sqrt (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ C : ℝ, 0 < κ₀ ∧ 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∀ N : ℕ, 16 ≤ N → ∀ d : ℕ, 1 ≤ d → (d : ℝ) < F γ N ^ (1 / 2 : ℝ) →
        ∀ j : ℤ, (j = 0 ∨ j = 1) →
          (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
            C * ((N : ℝ) / d + N / calE γ κ N) := by
  classical
  obtain ⟨κ₀, B, hκ₀, hdisc⟩ := h4 γ h1 h2
  refine ⟨κ₀, |B| + 1, hκ₀, by positivity, fun κ hκ hκsmall N hN d hd hdl j hj => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hX : 1 < F γ N := by
    apply Real.one_lt_exp_iff.mpr
    exact Real.rpow_pos_of_pos hL γ
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hαlow : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ) / d| := by
    rw [abs_of_pos (by positivity), Real.rpow_neg hX0.le]
    simpa only [one_div] using one_div_lt_one_div_of_lt hd0 hdl
  have hαhigh : |(1 : ℝ) / d| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hd0]
    exact hd1
  let a : ℤ := if j = 0 then 0 else (d : ℤ) - 1
  have ha : 0 ≤ a := by rcases hj with rfl | rfl <;> simp [a] <;> omega
  have had : a < d := by rcases hj with rfl | rfl <;> simp [a] <;> omega
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hadR : (a : ℝ) + 1 ≤ d := by exact_mod_cast (show a + 1 ≤ d by omega)
  let z₂ := (a : ℝ) / d
  let z₁ := ((a : ℝ) + 1) / d
  have hz₂ : 0 ≤ z₂ := by dsimp [z₂]; positivity
  have hzlt : z₂ < z₁ := by dsimp [z₁, z₂]; exact (div_lt_div_iff_of_pos_right hd0).mpr (by linarith)
  have hz₁ : z₁ ≤ 1 := by dsimp [z₁]; exact (div_le_one hd0).mpr hadR
  have hsub : (window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract ((1 / d : ℝ) * F γ n) ∧
        Int.fract ((1 / d : ℝ) * F γ n) < z₁) := by
    intro n hn
    obtain ⟨hnw, hnd⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨BoundarySupplyJ200.window_subset_Ioc γ h1 N hN hnw, ?_⟩
    have hdiv : (d : ℤ) ∣ nu γ n - a := by
      rcases hj with rfl | rfl
      · simpa [a] using hnd
      · have ht := dvd_sub hnd (dvd_refl (d : ℤ))
        convert ht using 1 <;> simp [a] <;> ring
    have hf := floor_residue_fract (F γ n) d (by omega) a ha had hdiv
    simpa only [z₁, z₂, one_div, mul_comm (d : ℝ)⁻¹, ← div_eq_mul_inv] using hf
  have hD := hdisc N (by omega) (1 / d) hαlow hαhigh z₁ z₂ hz₂ hzlt hz₁
  have hcount := (abs_le.mp hD).2
  have hcard : (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
      (((Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract ((1 / d : ℝ) * F γ n) ∧
        Int.fract ((1 / d : ℝ) * F γ n) < z₁)).card : ℝ) := by exact_mod_cast card_le_card hsub
  have hz : z₁ - z₂ = 1 / d := by dsimp [z₁, z₂]; ring
  have hmain : (z₁ - z₂) * (N : ℝ) / 2 ≤ (N : ℝ) / d := by
    rw [hz]
    have : 0 ≤ (N : ℝ) / d := by positivity
    rw [show (1 / (d : ℝ)) * (N : ℝ) / 2 = (N : ℝ) / d / 2 by ring]
    linarith
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hL.le _
  have hexp : Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤
      1 / calE γ κ N := by
    rw [calE, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hB : B * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤
      |B| * (N : ℝ) / calE γ κ N := by
    calc
      _ ≤ |B| * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)) (by positivity)
      _ ≤ |B| * N * (1 / calE γ κ N) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hq : 0 ≤ (N : ℝ) / d := by positivity
  have hqE : 0 ≤ (N : ℝ) / calE γ κ N := div_nonneg (Nat.cast_nonneg N) (show 0 ≤ calE γ κ N from (Real.exp_pos _).le)
  calc
    _ ≤ (z₁ - z₂) * (N : ℝ) / 2 +
        B * N * Real.exp (-κ₀ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by linarith
    _ ≤ (N : ℝ) / d + |B| * N / calE γ κ N := add_le_add hmain hB
    _ ≤ _ := by
      rw [show |B| * (N : ℝ) / calE γ κ N = |B| * ((N : ℝ) / calE γ κ N) by ring]
      nlinarith [mul_nonneg (abs_nonneg B) hq]


end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `FarWindow465`, proof unchanged up to the window and namespace renaming.


namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page362 display19. A global divisor bound at exponent one
sixteenth gives a uniform squared divisor bound at each adjacent window integer.
CONDITIONAL ON the explicit arithmetic envelope. -/
theorem window_divisor_sq_le (γ : ℝ) (N n : ℕ) (hn : n ∈ window γ N)
    (j : ℤ) (hj : j = 0 ∨ j = 1) (hX : 1 ≤ F γ N) (D : ℝ) (hD : 0 ≤ D)
    (hτ : ∀ k : ℕ, 1 ≤ k → (k.divisors.card : ℝ) ≤ D * (k : ℝ) ^ (1 / 16 : ℝ)) :
    (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 ≤ 2 * D ^ 2 * F γ N ^ (1 / 8 : ℝ) := by
  let m := nu γ n + j
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hlo := (mem_filter.mp hn).2.1
  have hhi := (mem_filter.mp hn).2.2
  have hj0 : (0 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj1 : (j : ℝ) ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
  have hmpos : (0 : ℝ) < m := by dsimp [m]; push_cast; linarith
  have hmInt : 0 < m := by exact_mod_cast hmpos
  have hmNat : 1 ≤ m.natAbs := by have := Int.natAbs_pos.mpr hmInt.ne'; omega
  have habs : (m.natAbs : ℝ) = (m : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hmpos]
  have hmX : (m.natAbs : ℝ) ≤ 2 * F γ N := by rw [habs]; dsimp [m]; push_cast; linarith
  have ht := hτ m.natAbs hmNat
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg m.natAbs.divisors.card) ht 2
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg m.natAbs)] at hs
  norm_num only [show (1 / 16 : ℝ) * 2 = 1 / 8 by norm_num] at hs
  have hpow : (m.natAbs : ℝ) ^ (1 / 8 : ℝ) ≤ 2 * F γ N ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (2 * F γ N) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hmX (by norm_num)
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) * F γ N ^ (1 / 8 : ℝ) := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 2 * F γ N ^ (1 / 8 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0.le _)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 8 : ℝ) ≤ 1)
  calc
    _ ≤ D ^ 2 * (m.natAbs : ℝ) ^ (1 / 8 : ℝ) := hs
    _ ≤ D ^ 2 * (2 * F γ N ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = _ := by ring

/-- P0082 page362 display19, the far divisor envelope summed over the
floor window. The small delta condition makes its power at most X to
minus one eighth. No discrepancy or major arc estimate is assumed. -/
theorem far_gammaTwo_window_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (γ δ : ℝ), 1 < γ → 0 < δ → δ ≤ 1 / 100 →
      ∀ N : ℕ, 16 ≤ N → 2 ≤ F γ N ^ (1 / 3 : ℝ) →
        ∀ r : ℕ, (r : ℝ) ≤ F γ N ^ (6 * δ) → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          (r : ℝ) * ∑ n ∈ window γ N,
            4 * (6 + 2 * Real.log (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℕ)) *
              (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 /
                (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℕ) ≤
            B * N * (1 + Real.log (F γ N)) * F γ N ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨D, hD, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 16 (by norm_num)
  have hτ16 : ∀ k : ℕ, 1 ≤ k → (k.divisors.card : ℝ) ≤ D * (k : ℝ) ^ (1 / 16 : ℝ) := by simpa using hτ
  refine ⟨128 * D ^ 2, by positivity, fun γ δ hγ hδ hδsmall N hN hXthird r hr j hj => ?_⟩
  let X := F γ N
  let Y := ⌊X ^ (1 / 3 : ℝ)⌋₊
  let H := 1 + Real.log X
  have hX0 : 0 < X := Real.exp_pos _
  have hX : 1 ≤ X := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hY : 1 ≤ Y := Nat.le_floor (by dsimp [Y, X]; linarith)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hYhalf : X ^ (1 / 3 : ℝ) / 2 ≤ (Y : ℝ) := by
    have hf := Nat.lt_floor_add_one (X ^ (1 / 3 : ℝ))
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    dsimp [Y] at hY1 ⊢
    linarith
  have hYX : (Y : ℝ) ≤ X := by
    refine (Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le).trans ?_
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hCY : 0 ≤ 6 + 2 * Real.log (Y : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hY : (1 : ℝ) ≤ Y)
    linarith
  have hlogY : 6 + 2 * Real.log (Y : ℝ) ≤ 8 * H := by
    have := Real.log_le_log hY0 hYX
    dsimp [H]
    linarith
  have hpoint (n : ℕ) (hn : n ∈ window γ N) :
      (r : ℝ) * (4 * (6 + 2 * Real.log (Y : ℝ)) *
        (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) ≤
          128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ)) := by
    have ht := window_divisor_sq_le γ N n hn j hj hX D hD.le hτ16
    have hnum : 4 * (6 + 2 * Real.log (Y : ℝ)) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 ≤
        (4 * (8 * H)) * (2 * D ^ 2 * X ^ (1 / 8 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogY (by norm_num)) ht (sq_nonneg _) (by positivity)
    have hquot := (div_le_div_of_nonneg_right hnum hY0.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X ^ (1 / 3 : ℝ) / 2) hYhalf)
    calc
      _ ≤ X ^ (6 * δ) * ((4 * (8 * H)) * (2 * D ^ 2 * X ^ (1 / 8 : ℝ)) /
          (X ^ (1 / 3 : ℝ) / 2)) :=
        mul_le_mul hr hquot (by positivity) (Real.rpow_pos_of_pos hX0 _).le
      _ = (128 * D ^ 2 * H) * (X ^ (6 * δ) * X ^ (1 / 8 : ℝ) / X ^ (1 / 3 : ℝ)) := by ring
      _ = (128 * D ^ 2 * H) * X ^ (6 * δ + 1 / 8 - 1 / 3 : ℝ) := by
        rw [Real.rpow_sub hX0, Real.rpow_add hX0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)
  have hcard : ((window γ N).card : ℝ) ≤ N := by
    have hc := card_le_card (BoundarySupplyJ200.window_subset_Ioc γ hγ N hN)
    have hn : (Ioc (N / 2) N).card ≤ N := by rw [Nat.card_Ioc]; omega
    exact_mod_cast hc.trans hn
  calc
    _ = ∑ n ∈ window γ N, (r : ℝ) * (4 * (6 + 2 * Real.log (Y : ℝ)) *
        (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) := by rw [mul_sum]
    _ ≤ ∑ _n ∈ window γ N, 128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ)) := sum_le_sum hpoint
    _ = ((window γ N).card : ℝ) * (128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `GammaMean465`, proof unchanged up to the window and namespace renaming.


namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page360 Lemma5, the finite Gamma1 envelope on the literal floor
window. CONDITIONAL ON Lemma4 as an explicit input. It includes both
adjacent shifts and has no new admission. -/
theorem gammaOne_mean_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N, gammaOne r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmean⟩ := gammaOne_mean_log
  obtain ⟨δ₀, hδ₀, hp⟩ := progression_counts h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hp⟩ := hp δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨A, hA, Np, hp⟩ := hp κ hκ hκsmall
  obtain ⟨Ns, hs⟩ := gammaOne_parameters γ δ κ h1 h2 hδ hκ
  refine ⟨2 * K * A, by positivity, max 16 (max Np Ns), fun N hN r hr hrP j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hF : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hP : 1 ≤ F γ N ^ (6 * δ) := Real.one_le_rpow hF (by positivity)
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hprog : ∀ d : ℕ, 1 ≤ d → d ≤ ⌊F γ N ^ (6 * δ)⌋₊ →
      (((window γ N).filter (fun n => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        A * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd hdP
    have hdR : (d : ℝ) ≤ F γ N ^ (6 * δ) :=
      (by exact_mod_cast hdP : (d : ℝ) ≤ ⌊F γ N ^ (6 * δ)⌋₊).trans (Nat.floor_le (by linarith))
    exact hp N hNp d hd hdR j hj
  have hm := hmean (window γ N) (fun n => nu γ n + j) r (F γ N ^ (6 * δ))
    (calE γ κ N) A N hr hP hE hA.le hprog
  calc
    _ ≤ K * A * N * (1 + Real.log (F γ N ^ (6 * δ))) ^ 3 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N) := hm
    _ = (K * A * N) * ((1 + Real.log (F γ N ^ (6 * δ))) ^ 3 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N)) := by ring
    _ ≤ (K * A * N) * (2 * calE γ κ N ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hs N hNs) (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `GammaTwoMean465`, proof unchanged up to the window and namespace renaming.

namespace LeanLab.ExceptionalSet.EvenSupplyJ200
open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 pages361 and362 displays17 to19. The complete infinite Gamma2
average follows from the near progression estimate and the far divisor
bound. CONDITIONAL ON the explicit Lemma4 input. -/
theorem gammaTwo_mean_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N, (r : ℝ) * (∑' q : ℕ,
                if F γ N ^ (6 * δ) < (q : ℝ) ∧ r ∣ q then
                  1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ)) else 0) ≤
                C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨A, hA, hφ⟩ := totient_ratio_log
  obtain ⟨B, hB, hfar⟩ := far_gammaTwo_window_bound
  obtain ⟨κ₀, C, hκ₀, hC, hprog⟩ := progression_counts_below_sqrt h4 γ h1 h2
  refine ⟨1 / 100, by norm_num, fun δ hδ hδsmall => ?_⟩
  obtain ⟨D, hD, hτ⟩ := gammaTwo_divisor_envelope δ hδ
  obtain ⟨Nr, hranges⟩ := gammaTwo_ranges γ δ h1 hδ hδsmall.le
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Nn, hnearparam⟩ := gammaTwo_near_parameters γ δ κ h1 h2 hδ hκ
  obtain ⟨Nf, hfarparam⟩ := gammaTwo_far_parameters γ κ h1 h2 hκ
  refine ⟨2 * A ^ 2 * (4 * D + 1) * C + B, by positivity,
    max 16 (max Nr (max Nn Nf)), fun N hN r hr hrP j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNn : Nn ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNf : Nf ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hP, hthird, hPY, hYsqrt, hYX⟩ := hranges N hNr
  let X := F γ N
  let P := X ^ (6 * δ)
  let Y := ⌊X ^ (1 / 3 : ℝ)⌋₊
  let t := (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q)
  let K := A ^ 2 * (4 * D + 1) * C
  have hX0 : 0 < X := Real.exp_pos _
  have hX : 1 ≤ X := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hY : 1 ≤ Y := Nat.le_floor (by dsimp [Y, X]; linarith)
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hp : ∀ d : ℕ, 1 ≤ d → d ≤ Y →
      (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd hdY
    exact hprog κ hκ hκsmall N hN16 d hd
      ((by exact_mod_cast hdY : (d : ℝ) ≤ Y).trans_lt hYsqrt) j hj
  have htau : ∀ q ∈ Ioc ⌊P⌋₊ Y, (q.divisors.card : ℝ) ≤ D * P ^ (1 / 2 : ℝ) := by
    intro q hq
    have hqI := mem_Ioc.mp hq
    exact hτ X hX q (by have := hqI.1; omega)
      ((by exact_mod_cast hqI.2 : (q : ℝ) ≤ Y).trans hYX)
  have hnear := near_gammaTwo_window_log (window γ N) (fun n => nu γ n + j)
    r Y X P (calE γ κ N) C A D N hr hX hP hPY hYX hE hC.le hA.le hD.le hφ htau hp
  have hnear' : (r : ℝ) * ∑ q ∈ t, ∑ n ∈ window γ N,
      1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ)) ≤
      2 * K * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ K * N * ((1 + Real.log X) ^ 4 * (P ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N)) := by
        convert hnear using 1 <;> dsimp [K] <;> ring
      _ ≤ K * N * (2 * calE γ κ N ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hnearparam N hNn) (by dsimp [K]; positivity)
      _ = _ := by ring
  have hfar' : (r : ℝ) * ∑ n ∈ window γ N,
      4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y ≤
        B * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ B * N * (1 + Real.log X) * X ^ (-(1 / 8 : ℝ)) :=
        hfar γ δ h1 hδ hδsmall.le N hN16 hthird r hrP j hj
      _ = (B * N) * ((1 + Real.log X) * X ^ (-(1 / 8 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfarparam N hNf) (by positivity)
  have hsplit (n : ℕ) (hn : n ∈ window γ N) := by
    have hlo := (mem_filter.mp hn).2.1
    have hj0 : (0 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
    have hm : nu γ n + j ≠ 0 := by
      intro hm
      have hmR : (nu γ n : ℝ) + (j : ℝ) = 0 := by exact_mod_cast hm
      change X / 2 < (nu γ n : ℝ) at hlo
      linarith
    exact gammaTwo_split_bound r P (by positivity) (nu γ n + j) hm Y hY
  calc
    _ ≤ ∑ n ∈ window γ N,
        ((r : ℝ) * (∑ q ∈ t, 1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ))) +
          (r : ℝ) * (4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y)) :=
      sum_le_sum hsplit
    _ = (r : ℝ) * (∑ q ∈ t, ∑ n ∈ window γ N,
          1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ))) +
        (r : ℝ) * (∑ n ∈ window γ N,
          4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
    _ ≤ 2 * K * N * calE γ κ N ^ (-(1 / 2 : ℝ)) + B * N * calE γ κ N ^ (-(1 / 2 : ℝ)) :=
      add_le_add hnear' hfar'
    _ = _ := by dsimp [K]; ring
end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `LargeGcd465`, proof unchanged up to the window and namespace renaming.


namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.Supply465

/-- P0082 page364 display22 and the next sentence. This has the exact
new large gcd leaf statement, with Lemma4 as an explicit input.
CONDITIONAL ON that discrepancy estimate. No new admission is used. -/
theorem large_gcd_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              (((window γ N).filter (fun n =>
                (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨D, hD, hτ⟩ := divisor_count_ratio
  obtain ⟨δ₀, hδ₀, hp⟩ := progression_counts h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hp⟩ := hp δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨C, hC, Np, hp⟩ := hp κ hκ hκsmall
  obtain ⟨Ng, hg⟩ := logarithmic_error_absorbed γ δ κ h1 h2 hδ hκ
  refine ⟨24 * C * (D + 1), by positivity, max 16 (max Np Ng), fun N hN r hr hrP hlarge j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNg : Ng ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hrNat : 0 < r := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    apply mul_nonneg hκ.le
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hprog : ∀ d ∈ r.divisors,
      (((window γ N).filter (fun n => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdr : d ≤ r := Nat.le_of_dvd hrNat (Nat.mem_divisors.mp hd).1
    exact hp N hNp d hd1 ((by exact_mod_cast hdr : (d : ℝ) ≤ r).trans hrP) j hj
  have hcount := large_gcd_of_progressions (window γ N) (fun n => nu γ n + j)
    r hrNat C (calE γ κ N) N hE hprog
  have hτr := hτ (calE γ κ N) hE1 r hr hlarge
  have hlogr : Real.log r ≤ 6 * δ * Real.log (F γ N) := by
    calc
      _ ≤ Real.log (F γ N ^ (6 * δ)) := Real.log_le_log hr0 hrP
      _ = _ := Real.log_rpow hX _
  have hsigma : ((∑ d ∈ r.divisors, (d : ℝ)) / r) / calE γ κ N ≤
      calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    refine (div_le_div_of_nonneg_right ((divisor_sum_ratio r hrNat).trans ?_) hE.le).trans (hg N hNg)
    linarith
  calc
    _ ≤ 24 * (C * N * r.divisors.card + C * N / calE γ κ N * ∑ d ∈ r.divisors, (d : ℝ)) / r := hcount
    _ = (24 * C * N) * ((r.divisors.card : ℝ) / r +
        ((∑ d ∈ r.divisors, (d : ℝ)) / r) / calE γ κ N) := by ring
    _ ≤ (24 * C * N) * (D * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        calE γ κ N ^ (-(1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hτr hsigma) (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.EvenSupplyJ200


-- Copied from `Decomp465c` and `Decomp465a`: the two divisor envelopes and their sum.
namespace LeanLab.ExceptionalSet.EvenSupplyJ200

open Real Finset

/-- Copy of `Supply465.gammaTwo`, P0082 page 359 display (15), the positive envelope for Γ₂. -/
noncomputable def gammaTwo (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

/-- Copy of `Supply465.divisorError`: the sum of the explicit positive envelopes for Γ₁ and Γ₂,
P0082 page 359 displays (14) and (15). -/
noncomputable def divisorError (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) / P *
    ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
      (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) +
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

/-- Copy of `Supply465.divisorError_nonneg`: displays (14) and (15) are nonnegative. -/
theorem divisorError_nonneg (r : ℕ) (P : ℝ) (m : ℤ) (hP : 0 ≤ P) :
    0 ≤ divisorError r P m := by
  unfold divisorError
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact sum_nonneg (fun q _ => by positivity)
  · apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun q => by split_ifs <;> positivity)

end LeanLab.ExceptionalSet.EvenSupplyJ200

-- Copied from `Decomp467b`, proof unchanged up to the window and namespace renaming.
namespace LeanLab.ExceptionalSet.EvenSupplyJ200
open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE Lemma4)
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.CoeffSupplyJ200 (evenAdjacent)

/-- P0082 pages360 to362, Lemma5. The two divisor means add.
CONDITIONAL ON the explicit discrepancy input h4. -/
theorem error_mean_raw (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                (gammaOne r (F γ N ^ (6 * δ)) (nu γ n + j) +
                  gammaTwo r (F γ N ^ (6 * δ)) (nu γ n + j)) ≤
                    C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨δa, hδa, ha⟩ := gammaOne_mean_from_lemma4 h4 γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := gammaTwo_mean_from_lemma4 h4 γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ca, hCa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Cb, hCb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ca + Cb, add_pos hCa hCb, max Na Nb, fun N hN r hr hrP j hj => ?_⟩
  rw [sum_add_distrib]
  have haN := ha N ((le_max_left _ _).trans hN) r hr hrP j hj
  have hbN := hb N ((le_max_right _ _).trans hN) r hr hrP j hj
  calc
    _ ≤ Ca * N * calE γ κ N ^ (-(1 / 2 : ℝ)) +
        Cb * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := add_le_add haN hbN
    _ = _ := by ring

/-- P0082 page362, completion of Lemma5 for the positive error envelope.
CONDITIONAL ON the explicit discrepancy input h4. -/
theorem error_mean (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                  C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  simpa only [divisorError, gammaOne, gammaTwo] using error_mean_raw h4 γ h1 h2

section CharacterCases

variable (hpoint : ∀ (γ : ℝ), 1 < γ → γ < 3 / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j))
variable (h4 : Lemma4)
include hpoint h4

/-- P0082 pages362 to364, Lemma7. The pointwise character cases, the
divisor mean and the large gcd count control each adjacent shift. CONDITIONAL. -/
theorem adjacent_count_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            ((((window γ N).filter (fun n => Even (nu γ n + j))).filter (fun n =>
              (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δp, hδp, hp⟩ := hpoint γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := error_mean h4 γ h1 h2
  obtain ⟨δg, hδg, hg⟩ := large_gcd_from_lemma4 h4 γ h1 h2
  refine ⟨min δp (min δm δg), lt_min hδp (lt_min hδm hδg), fun δ hδ hδsmall => ?_⟩
  obtain ⟨κp, hκp, hp⟩ := hp δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨κg, hκg, hg⟩ := hg δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨min 1 (min κp (min κm κg)), lt_min zero_lt_one (lt_min hκp (lt_min hκm hκg)),
    fun κ hκ hκsmall => ?_⟩
  have hκ1 : κ ≤ 1 := hκsmall.trans (min_le_left _ _)
  have hκrest : κ ≤ min κp (min κm κg) := hκsmall.trans (min_le_right _ _)
  obtain ⟨c, A, hc, hA, Np, hp⟩ := hp κ hκ (hκrest.trans (min_le_left _ _))
  obtain ⟨C, hC, Nm, hm⟩ := hm κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨B, hB, Ng, hg⟩ := hg κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c / 2, B + 1 + 2 * A * C / c, by positivity, by positivity,
    max 16 (max Np (max Nm Ng)), fun N hN j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNm : Nm ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNg : Ng ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨r, hr, hrP, hp⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let s := (window γ N).filter (fun n => Even (nu γ n + j))
  let g := fun n => divisorError r P (nu γ n + j)
  let rare := if (r : ℝ) ≤ E ^ (1 / 7 : ℝ) then ∅ else
    (window γ N).filter (fun n => (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))
  let t := rare ∪ {N}
  have hX : 0 < X := Real.exp_pos _
  have hE : 1 ≤ E := by
    apply Real.one_le_exp
    apply mul_nonneg hκ.le
    apply Real.rpow_nonneg
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hg0 : ∀ n ∈ window γ N, 0 ≤ g n := fun n _ =>
    divisorError_nonneg r P _ (Real.rpow_nonneg hX.le _)
  have hmean : ∑ n ∈ s, g n ≤ C * N * E ^ (-(1 / 2 : ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hg0 n hn)).trans
      (hm N hNm r hr hrP j hj)
  have hrare : (rare.card : ℝ) ≤ B * N * E ^ (-(1 / 12 : ℝ)) := by
    dsimp only [rare]
    split_ifs with hsmall
    · simp only [card_empty, Nat.cast_zero]
      positivity
    · exact hg N hNg r hr hrP (lt_of_not_ge hsmall) j hj
  have ht : (t.card : ℝ) ≤ (B + 1) * N * E ^ (-(1 / 12 : ℝ)) := by
    have hu : (t.card : ℝ) ≤ (rare.card : ℝ) + 1 := by
      exact_mod_cast (card_union_le rare {N}).trans_eq (by simp)
    have hscale := one_le_count_scale γ κ h1 hκ.le hκ1 N (by omega)
    change 1 ≤ (N : ℝ) * E ^ (-(1 / 12 : ℝ)) at hscale
    nlinarith
  apply count_coefficient s t
    (fun n => (R1 P X (nu γ n + j)).re) g c A C (B + 1) X E N
    hc hA hC.le hX hE (fun n hn => hg0 n (mem_filter.mp hn).1) hmean ht
  intro n hn hnt
  obtain ⟨hnw, hne⟩ := mem_filter.mp hn
  have hnnot : n ≠ N := by
    intro heq
    apply hnt
    exact mem_union.mpr (Or.inr (mem_singleton.mpr heq))
  have hnN : n < N := lt_of_le_of_ne (BoundarySupplyJ200.window_upper γ h1 N (by omega) n hnw) hnnot
  have hrange := adjacent_le_X γ h1 N n hN16 hnw hnN j (by rcases hj with rfl | rfl <;> norm_num)
  apply hp j hj n hnw hne (by exact_mod_cast hrange)
  by_cases hsmall : (r : ℝ) ≤ E ^ (1 / 7 : ℝ)
  · exact Or.inl hsmall
  · apply Or.inr
    have : ¬ (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ) := by
      intro hlarge
      apply hnt
      apply mem_union.mpr
      apply Or.inl
      dsimp only [rare]
      rw [if_neg hsmall]
      exact mem_filter.mpr ⟨hnw, hlarge⟩
    exact lt_of_not_ge this

/-- P0082 pages362 to364, Lemma7. One parity specialization of the
adjacent count with its discrepancy and character case inputs explicit. CONDITIONAL. -/
theorem even_index_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs hpoint h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [add_zero] using h N hN 0 (Or.inl rfl)

/-- P0082 pages362 to364, Lemma7. One parity specialization of the
adjacent count with its discrepancy and character case inputs explicit. CONDITIONAL. -/
theorem odd_index_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs hpoint h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [Int.even_add_one, Int.not_even_iff_odd] using h N hN 1 (Or.inr rfl)

/-- P0082 pages362 to364, Lemma7. Combining the disjoint index parities
gives the even coefficient bound. CONDITIONAL ON the explicit inputs. -/
theorem even_coefficient_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := even_index_from_inputs hpoint h4 γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := odd_index_from_inputs hpoint h4 γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨ce, Be, hce, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨co, Bo, hco, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨min ce co, Be + Bo, lt_min hce hco, add_pos hBe hBo, max Ne No, fun N hN => ?_⟩
  have hNe : Ne ≤ N := (le_max_left _ _).trans hN
  have hNo : No ≤ N := (le_max_right _ _).trans hN
  have hF : 0 ≤ F γ N := (Real.exp_pos _).le
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hR : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
  have hstepE : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hF) hR
  have hstepO : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hF) hR
  have hA : ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Be * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
            ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepE⟩
    exact (Nat.cast_le.mpr hsub).trans (he N hNe)
  have hB : ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Bo * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
            co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : ¬ Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n + 1 := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepO⟩
    exact (Nat.cast_le.mpr hsub).trans (ho N hNo)
  have hpart : (window γ N).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) =
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) ∪
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnw, hb⟩
      by_cases hpar : Even (nu γ n)
      · exact Or.inl ⟨⟨hnw, hpar⟩, hb⟩
      · exact Or.inr ⟨⟨hnw, hpar⟩, hb⟩
    · rintro (⟨⟨hnw, _⟩, hb⟩ | ⟨⟨hnw, _⟩, hb⟩)
      · exact ⟨hnw, hb⟩
      · exact ⟨hnw, hb⟩
  have hdisj : Disjoint
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  push_cast
  refine (add_le_add hA hB).trans_eq ?_
  ring


end CharacterCases

end LeanLab.ExceptionalSet.EvenSupplyJ200

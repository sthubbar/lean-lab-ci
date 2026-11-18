import LeanLab.HeathBrown1985.Lemma1
import LeanLab.ExceptionalSet.BG2026Prop81Chain
import LeanLab.PNTPort.DirichletZF.Siegel
import LeanLab.ExceptionalSet.UpJ200.Decomp559b
import LeanLab.ExceptionalSet.UpJ200.Decomp559a
import LeanLab.ExceptionalSet.UpJ200.Decomp371a
import LeanLab.ExceptionalSet.GammaOne465
import LeanLab.ExceptionalSet.GammaParameters465
import LeanLab.ExceptionalSet.NearWindow465
import LeanLab.ExceptionalSet.GammaSplit465
import LeanLab.ExceptionalSet.GammaRanges465
import LeanLab.ExceptionalSet.Decomp465b

/-!
P0082 pages359 to364. Upstream character case and divisor mean helpers.
Source: https://doi.org/10.5802/aif.1621
Existing Supply465 arguments are reused with the upstream floor window.
No file in this import closure imports Decomp505a.
AI wrote the Lean code. Goldbach is open.
-/

/-! P0082 page 354. Preserve the paper growth name in downstream proofs.
The analytic import also defines a root scalar F. This export names the
existing paper function and introduces no new kernel declaration. -/
namespace LeanLab.ExceptionalSet
export BrudernPerelli1998 (F)
end LeanLab.ExceptionalSet

/-! Upstream reuse of Endpoint465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 pages 358 and 362, range of the even integer in Lemma7.
Every interior window index has both adjacent integers below X. -/
theorem adjacent_le_X (γ : ℝ) (hγ : 1 < γ) (N n : ℕ) (hN : 16 ≤ N)
    (hn : n ∈ window γ N) (hnN : n < N) (j : ℤ) (hj : j ≤ 1) :
    (nu γ n + j : ℝ) ≤ F γ N := by
  have hi := mem_Ioc.mp (LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ hγ N hN hn)
  have hn8 : 8 ≤ n := by omega
  have hstep : (1 : ℝ) ≤ (N : ℝ) - n := by
    have hcast : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    linarith
  have hg := LeanLab.ExceptionalSet.UpJ200.Decomp371a.F_growth γ n N hγ (by exact_mod_cast hn8)
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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/-! Upstream reuse of Progressions465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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
    refine ⟨LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN hnw, ?_⟩
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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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
    refine ⟨LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN hnw, ?_⟩
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


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section port-2.txt -/
/-! Upstream reuse of GammaMean465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section port-3.txt -/
/-! Upstream reuse of FarWindow465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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
    have hc := card_le_card (LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ hγ N hN)
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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section port-4.txt -/
/-! Upstream reuse of GammaTwoMean465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465
open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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
end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section port-5.txt -/
/-! Upstream reuse of LargeGcd465. All mathematical hypotheses are retained. -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

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

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section error.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 page359 display15. Positive infinite divisor envelope. -/
noncomputable def gammaTwo (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

/-- P0082 page 359 displays 14 and 15 are nonnegative error envelopes. -/
theorem divisorError_nonneg (r : ℕ) (P : ℝ) (m : ℤ) (hP : 0 ≤ P) :
    0 ≤ divisorError r P m := by
  unfold divisorError
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact sum_nonneg (fun q _ => by positivity)
  · apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun q => by split_ifs <;> positivity)


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


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section conductor.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Finset

/-- P0082 page363 case ii c. If every prime above three dividing an odd
squarefree u divides m, then u divides three m. -/
theorem odd_squarefree_dvd_three_mul (u m : ℕ) (hu : Odd u) (hs : Squarefree u)
    (hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m) : u ∣ 3 * m := by
  by_cases hm : m = 0
  · simp [hm]
  rw [← Nat.prod_primeFactors_of_squarefree hs]
  apply (Nat.prod_primeFactors_dvd_iff (by omega : 3 * m ≠ 0)).mpr
  intro p hpu
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpu
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpp, ?_, by omega⟩
  by_cases hp3 : p = 3
  · subst p
    exact dvd_mul_right 3 m
  · have hp2 : p ≠ 2 := by intro h; subst p; exact hu.not_two_dvd_nat hpd
    have hpgt : 3 < p := by have := hpp.two_le; omega
    exact dvd_mul_of_dvd_right (hp p hpp hpd hpgt) 3

/-- P0082 page363 case ii c. The printed conductor shape and empty
prime product imply r at most twenty four times gcd m r. CONDITIONAL ON
the explicit conductor shape, with no character classification supplied. -/
theorem conductor_large_gcd (r m k u : ℕ) (hr : r = 2 ^ k * u) (hk : k ≤ 3)
    (hu : Odd u) (hs : Squarefree u)
    (hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m) :
    r ≤ 24 * Nat.gcd m r := by
  have hud := odd_squarefree_dvd_three_mul u m hu hs hp
  have htwo : 2 ^ k ∣ 8 := by
    refine ⟨2 ^ (3 - k), ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hk]
    norm_num
  have hrdiv : r ∣ 24 * m := by
    rw [hr]
    convert mul_dvd_mul htwo hud using 1 <;> ring
  have hg : r ∣ 24 * Nat.gcd m r := by
    obtain ⟨c, hc⟩ := dvd_mul_gcd_of_dvd_mul hrdiv
    exact ⟨c, by simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using hc⟩
  have hrpos : 0 < r := by rw [hr]; exact mul_pos (by positivity) (Nat.pos_of_ne_zero hs.ne_zero)
  have hgp : 0 < Nat.gcd m r := Nat.gcd_pos_of_pos_right m hrpos
  exact Nat.le_of_dvd (by positivity) hg

/-- P0082 page363 display21 and its following paragraph. For a conductor
of the printed shape, gcd below r over twenty four forces a prime above
three in the conductor that does not divide m. CONDITIONAL ON that shape. -/
theorem conductor_prime_witness (r m k u : ℕ) (hr : r = 2 ^ k * u) (hk : k ≤ 3)
    (hu : Odd u) (hs : Squarefree u) (hsmall : 24 * Nat.gcd m r < r) :
    ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ p ∣ m := by
  by_contra hnone
  push_neg at hnone
  have hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m := by
    intro p hpp hpu hp3
    apply hnone p hpp
    · rw [hr]
      exact dvd_mul_of_dvd_right hpu _
    · exact hp3
  have := conductor_large_gcd r m k u hr hk hu hs hp
  omega
end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section source.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset

/-- P0082 page362 case i. A quarter of the uniform main coefficient
remains after an error at most a quarter of X times that coefficient.
The major arc expansion is an explicit premise. -/
theorem absent_character_lower (X m S a R e : ℝ)
    (hX : 0 ≤ X) (ha : 0 ≤ a) (hm : X / 2 ≤ m)
    (hS : a ≤ S) (he : e ≤ a * X / 4) (hR : m * S - e ≤ R) :
    a * X / 4 ≤ R := by
  have hm0 : 0 ≤ m := by linarith
  have hmul := mul_le_mul_of_nonneg_left hS hm0
  have hscale := mul_le_mul_of_nonneg_right hm ha
  linarith

/-- P0082 page363 display21. A nonempty product over primes above three
has value at most one third. Every other local factor is at most one. -/
theorem nonempty_prime_product_third (s : Finset ℕ) (hs : s.Nonempty)
    (hp : ∀ p ∈ s, p.Prime ∧ 3 < p) :
    (∏ p ∈ s, 1 / ((p : ℝ) - 2)) ≤ 1 / 3 := by
  obtain ⟨p, hps⟩ := hs
  have hfive (q : ℕ) (hq : q ∈ s) : (5 : ℝ) ≤ q := by
    have hh := hp q hq
    exact_mod_cast hh.1.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  have hnonneg (q : ℕ) (hq : q ∈ s) : 0 ≤ 1 / ((q : ℝ) - 2) := by
    have := hfive q hq
    exact div_nonneg (by norm_num) (by linarith)
  have hle (q : ℕ) (hq : q ∈ s) : 1 / ((q : ℝ) - 2) ≤ 1 := by
    have := hfive q hq
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀
    (Finset.singleton_subset_iff.mpr hps) hnonneg (fun q hq _ => hle q hq)
  have hpfive := hfive p hps
  have hlocal : 1 / ((p : ℝ) - 2) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hprod' : (∏ q ∈ s, 1 / ((q : ℝ) - 2)) ≤ 1 / ((p : ℝ) - 2) := by
    simpa only [Finset.prod_singleton] using hprod
  exact hprod'.trans hlocal

/-- P0082 page363 case ii b after display21. The exact one third
correction bound leaves two thirds of the main term. -/
theorem small_gcd_correction_lower (m S J T : ℝ) (hm : 0 ≤ m)
    (hJ : |J| ≤ m) (hT : |T| ≤ S / 3) :
    2 / 3 * m * S ≤ m * S + J * T := by
  have hprod : |J * T| ≤ m * (S / 3) := by
    rw [abs_mul]
    exact mul_le_mul hJ hT (abs_nonneg _) hm
  have hlow := (abs_le.mp hprod).1
  nlinarith

/-- P0082 page364 case ii d after display22. The conductor cutoff
converts its inverse square root into E to minus one fourteenth.
The zero gap estimate in display10 remains an explicit input. -/
theorem near_zero_conductor_gap (E r b L β : ℝ)
    (hE : 1 ≤ E) (hr : 1 < r) (hb : 0 ≤ b)
    (hrE : r ≤ E ^ (1 / 7 : ℝ)) (hL : Real.log r ≤ L)
    (hgap : b * r ^ (-(1 / 2 : ℝ)) / Real.log r ^ 2 ≤ 1 - β) :
    b * E ^ (-(1 / 14 : ℝ)) / L ^ 2 ≤ 1 - β := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hL0 : 0 < L := hlog.trans_le hL
  have hp : E ^ (-(1 / 14 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = (E ^ (1 / 7 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hE0.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) hrE (by norm_num)
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hb)
    (sq_nonneg L)).trans ?_
  refine (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlog)
    (pow_le_pow_left₀ hlog.le hL 2)).trans hgap

/-- P0082 page364 final sentence of case ii d. The logarithmic loss
fits in the exact exponent margin between one fourteenth and one tenth. -/
theorem near_zero_log_margin (E L : ℝ) (hE : 1 ≤ E) (hL : 0 < L)
    (hlog : L ^ 2 ≤ E ^ (1 / 35 : ℝ)) :
    E ^ (-(1 / 10 : ℝ)) ≤ E ^ (-(1 / 14 : ℝ)) / L ^ 2 := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  calc
    _ ≤ E ^ (-(1 / 10 : ℝ)) * E ^ (1 / 35 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hE0.le _)
    _ = _ := by rw [← Real.rpow_add hE0]; norm_num

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a

/-- P0082 page 358 display 9. Equal lifts of primitive characters have
identical levels and the original characters are heterogeneously equal. -/
theorem primitive_eq_of_lift_eq652 (r q M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hr : r ∣ M) (hq : q ∣ M)
    (heq : DirichletCharacter.changeLevel hr χ = DirichletCharacter.changeLevel hq ψ) :
    r = q ∧ HEq χ ψ := by
  have hlevel : r = q := by
    calc
      r = χ.conductor := hχ.symm
      _ = (DirichletCharacter.changeLevel hr χ).conductor :=
        (DirichletCharacter.conductor_changeLevel χ hr).symm
      _ = (DirichletCharacter.changeLevel hq ψ).conductor := congrArg _ heq
      _ = ψ.conductor := DirichletCharacter.conductor_changeLevel ψ hq
      _ = q := hψ
  subst q
  exact ⟨rfl, heq_of_eq (DirichletCharacter.changeLevel_injective hr heq)⟩


/-- P0082 page 358 display 9. A width at most one quarter puts the
whole selected interval strictly to the right of zero. -/
theorem selected_zero_pos652 (a P β : ℝ) (ha : a ≤ 1 / 4) (hP : 2 ≤ P)
    (hβ : 1 - a / Real.log P ≤ β) : 0 < β := by
  have hlog2 : (1 / 4 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlogP0 : 0 < Real.log P := by linarith
  have hlt : a / Real.log P < 1 := (div_lt_one hlogP0).mpr (by linarith)
  linarith


open LeanLab.PNTPort.DirichletZF

/-- P0082 page 358 display 9. A principal primitive character has no real
zero strictly between zero and one. -/
theorem primitive_principal_nonvanishing652 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) : χ = 1 → χ.LFunction β ≠ 0 := by
  intro heq hz
  have hq : q = 1 := by
    have hc : χ.conductor = q := hp
    rw [heq, DirichletCharacter.conductor_one] at hc
    exact hc.symm
  subst q
  have hneg := (riemannZeta_real_neg hβ0 hβ1).2
  rw [heq, DirichletCharacter.LFunction_modOne_eq] at hz
  rw [hz] at hneg
  simp at hneg


/-- P0082 page 358 display 9. The product modulus of two characters
below P has zero free logarithmic scale at most K log P. -/
theorem log_product_scale652 (M : ℕ) [NeZero M] (P : ℝ) (hP : 2 ≤ P)
    (hM : (M : ℝ) ≤ P ^ 2) :
    Real.log (Bt M 0) ≤ (Real.log (6 * Z) / Real.log 2 + 2) * Real.log P := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have h6 : (0 : ℝ) < 6 * Z := by have := one_le_Z; linarith
  have hL : 0 ≤ Real.log (6 * Z) := Real.log_nonneg (by have := one_le_Z; linarith)
  have hlogM : Real.log (M : ℝ) ≤ 2 * Real.log P := by
    have h := Real.log_le_log hM0 hM
    rwa [Real.log_pow] at h
  have hconstant : Real.log (6 * Z) ≤ Real.log (6 * Z) / Real.log 2 * Real.log P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogP hL
  have hb : Bt M 0 = (6 * Z) * M := by unfold Bt; simp; ring
  rw [hb, Real.log_mul h6.ne' hM0.ne']
  nlinarith only [hconstant, hlogM]


/-- P0082 page 358 display 9. The shared strip is inside the proved
zero free box at every product modulus bounded by P squared. -/
theorem selection_strip_inside652 (c a P β : ℝ) (hc : 0 < c) (ha0 : 0 ≤ a)
    (ha : a ≤ c / (2 * (Real.log (6 * Z) / Real.log 2 + 2)))
    (M : ℕ) [NeZero M] (hP : 2 ≤ P) (hM : (M : ℝ) ≤ P ^ 2)
    (hβ : 1 - a / Real.log P ≤ β) :
    1 - c / Real.log (Bt M 0) < β := by
  have hL : 0 ≤ Real.log (6 * Z) := Real.log_nonneg (by have := one_le_Z; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < Real.log (6 * Z) / Real.log 2 + 2 := by positivity
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogM : 0 < Real.log (Bt M 0) := by linarith [one_le_log_Bt (N := M) 0]
  have hbound := log_product_scale652 M P hP hM
  have hak : a * (Real.log (6 * Z) / Real.log 2 + 2) ≤ c / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (Real.log (6 * Z) / Real.log 2 + 2))).mp ha
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hbound ha0
  have hmul' := mul_le_mul_of_nonneg_right hak hlogP.le
  have hdiv : a / Real.log P < c / Real.log (Bt M 0) := by
    rw [div_lt_div_iff₀ hlogP hlogM]
    nlinarith only [hmul, hmul', mul_pos hc hlogP]
  linarith


open LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-- P0082 page 358 display 9. One absolute strip has either no
primitive real zero or exactly one zero of one primitive real character. -/
theorem selected_real_zero652 :
    ∃ a : ℝ, 0 < a ∧ ∀ P : ℝ, 2 ≤ P →
      ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ P ∧ SelectedRealZero a P r := by
  classical
  obtain ⟨c, c', hc, hc', H⟩ := zero_free_region_real
  let K := Real.log (6 * Z) / Real.log 2 + 2
  have hL : 0 ≤ Real.log (6 * Z) := Real.log_nonneg (by have := one_le_Z; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  let a := min (c / (2 * K)) (1 / 4)
  have ha : 0 < a := lt_min (div_pos hc (by positivity)) (by norm_num)
  have ha4 : a ≤ 1 / 4 := min_le_right _ _
  have hac : a ≤ c / (2 * K) := min_le_left _ _
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hpositive (β : ℝ) (hβ : 1 - a / Real.log P ≤ β) : 0 < β :=
    selected_zero_pos652 a P β ha4 hP hβ
  have hbox (M : ℕ) [NeZero M] (hM : (M : ℝ) ≤ P ^ 2)
      (β : ℝ) (hβ : 1 - a / Real.log P ≤ β) :
      1 - c / Real.log (Bt M 0) < β :=
    selection_strip_inside652 c a P β hc ha.le hac M hP hM hβ
  by_cases hfree : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
        ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ ≠ 0
  · exact ⟨1, le_rfl, by exact_mod_cast hP1, Or.inl ⟨rfl, hfree⟩⟩
  push Not at hfree
  obtain ⟨r, hrzero, χ, hr1, hrP, hp, β, hβ, hβ1, hz⟩ := hfree
  letI : NeZero r := hrzero
  have hχ : χ ≠ 1 := fun heq => primitive_principal_nonvanishing652 r χ hp β (hpositive β hβ) hβ1 heq hz
  have hβbox := hbox r (hrP.trans hP2) β hβ
  have hreal : χ ^ 2 = 1 := by
    rcases (H r χ hχ).1 (β : ℂ) hz with hleft | hright
    · simp only [Complex.ofReal_re, Complex.ofReal_im] at hleft
      exact False.elim (not_lt_of_ge hleft hβbox)
    · exact hright.2.2.1
  refine ⟨r, hr1, hrP, Or.inr ⟨hrzero, χ, β, hp, hreal, hχ,
    hpositive β hβ, hβ, hβ1, hz, ?_⟩⟩
  intro q hqzero ψ hq1 hqP hψ σ hσ hσ1 hσzero
  letI : NeZero q := hqzero
  have hψne : ψ ≠ 1 :=
    fun heq => primitive_principal_nonvanishing652 q ψ hψ σ (hpositive σ hσ) hσ1 heq hσzero
  let M := q * r
  haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  have hM : (M : ℝ) ≤ P ^ 2 := by
    dsimp [M]
    push_cast
    nlinarith only [mul_le_mul hqP hrP (Nat.cast_nonneg r) hP0.le]
  let dq : q ∣ M := Nat.dvd_mul_right q r
  let dr : r ∣ M := Nat.dvd_mul_left r q
  have hψlift : DirichletCharacter.changeLevel dq ψ ≠ 1 :=
    fun heq => hψne ((DirichletCharacter.changeLevel_eq_one_iff dq).mp heq)
  have hχlift : DirichletCharacter.changeLevel dr χ ≠ 1 :=
    fun heq => hχ ((DirichletCharacter.changeLevel_eq_one_iff dr).mp heq)
  have hσlift : (DirichletCharacter.changeLevel dq ψ).LFunction σ = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel dq ψ (Or.inl hψne), hσzero, zero_mul]
  have hβlift : (DirichletCharacter.changeLevel dr χ).LFunction β = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel dr χ (Or.inl hχ), hz, zero_mul]
  have hlogM : 0 < Real.log (Bt M 0) := by linarith [one_le_log_Bt (N := M) 0]
  obtain ⟨hlifts, hzeros⟩ := (H M (DirichletCharacter.changeLevel dq ψ) hψlift).2
    (DirichletCharacter.changeLevel dr χ) hχlift (σ : ℂ) (β : ℂ) hσlift hβlift
    (by simpa only [Complex.ofReal_re] using (hbox M hM σ hσ).le)
    (by simp only [Complex.ofReal_im, abs_zero]; positivity)
    (by simpa only [Complex.ofReal_re] using (hbox M hM β hβ).le)
    (by simp only [Complex.ofReal_im, abs_zero]; positivity)
  obtain ⟨hlevels, hcharacters⟩ := primitive_eq_of_lift_eq652 q r M ψ χ hψ hp dq dr hlifts
  exact ⟨hlevels, hcharacters, Complex.ofReal_injective hzeros⟩

/-- P0082 page 358 display 10. The proved Siegel bound gives an
absolute inverse square root zero free interval for real characters.
The constant is ineffective. No exceptional zero is assumed to exist. -/
theorem quadratic_zero_free_half652 :
    ∃ b : ℝ, 0 < b ∧ ∀ (r : ℕ) [NeZero r]
      (χ : DirichletCharacter ℂ r), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ β : ℝ, 1 - b * (r : ℝ) ^ (-(1 / 2 : ℝ)) < β → β ≤ 1 →
          χ.LFunction β ≠ 0 := by
  obtain ⟨c, hc, hs⟩ := siegel_zero (1 / 2 : ℝ) (by norm_num)
  refine ⟨c * (8 : ℝ) ^ (-(1 / 2 : ℝ)), by positivity, ?_⟩
  intro r hr χ hχ hχ2 β hβ hβ1 hz
  let M := 8 * r
  haveI : NeZero M := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne r)⟩
  have hM8 : 8 ≤ M := by have := Nat.pos_of_ne_zero (NeZero.ne r); omega
  have hd : r ∣ M := Dvd.intro_left 8 rfl
  have hzl : (DirichletCharacter.changeLevel hd χ).LFunction β = 0 := by
    rw [L_lift hd hχ, hz, zero_mul]
  have hb := hs M hM8 _ (lift_ne_one hd hχ) (lift_sq hd hχ2) β hβ1 hzl
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hMr : (M : ℝ) = 8 * r := by simp [M]
  rw [hMr, Real.mul_rpow (by norm_num) hr0.le] at hb
  nlinarith only [hb, hβ]

/-- P0082 page 363 case ii a. For every fixed width, a selected
nonprincipal conductor exceeds every fixed bound when the cutoff grows. -/
theorem selected_conductor_eventually_large652 (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ r : ℕ,
      SelectedRealZero a P r → r = 1 ∨ B ≤ (r : ℝ) := by
  obtain ⟨b, hb, H⟩ := quadratic_zero_free_half652
  have hB0 : 0 < B := by linarith
  let t := b * B ^ (-(1 / 2 : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  let L := a / t + 1
  refine ⟨max 2 (Real.exp L), le_max_left _ _, ?_⟩
  intro P hP r hs
  by_cases hr : r = 1
  · exact Or.inl hr
  right
  by_contra hsmall
  have hrB : (r : ℝ) < B := lt_of_not_ge hsmall
  obtain ⟨hrzero, χ, β, hp, hreal, hχ, hβ0, hβ, hβ1, hz, huniq⟩ :=
    hs.resolve_left (fun h => hr h.1)
  letI : NeZero r := hrzero
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hlog : L ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos L) ((le_max_right _ _).trans hP)
    simpa only [Real.log_exp] using h
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hdiv : a / Real.log P < t := by
    rw [div_lt_iff₀ hlogP]
    have hmul := mul_le_mul_of_nonneg_right hlog ht.le
    dsimp [L] at hmul
    have hid : (a / t + 1) * t = a + t := by field_simp [ht.ne']
    rw [hid] at hmul
    nlinarith only [hmul, ht]
  have hpows : B ^ (-(1 / 2 : ℝ)) ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr0 hrB.le (by norm_num)
  have hscale := mul_le_mul_of_nonneg_left hpows hb.le
  have hstrip : 1 - b * (r : ℝ) ^ (-(1 / 2 : ℝ)) < β := by
    dsimp [t] at hdiv
    linarith
  exact H r χ hχ hreal β hstrip hβ1.le hz

/-- P0082 page 363 case ii a. The coprime conductor ratio is uniformly
small for selected nonprincipal conductors at sufficiently large cutoffs. -/
theorem selected_totient_small652 (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ r : ℕ,
      SelectedRealZero a P r → r = 1 ∨ (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ η := by
  obtain ⟨P₀, hP₀, H⟩ := selected_conductor_eventually_large652 a
    (max 1 (16 / η ^ 2)) ha (le_max_left _ _)
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP r hs
  rcases H P hP r hs with hr | hlarge
  · exact Or.inl hr
  · right
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one
      ((le_max_left _ _).trans hlarge)
    exact LeanLab.ExceptionalSet.BG2026.r_div_totient_sq_le hη
      (by exact_mod_cast hrpos) ((le_max_right _ _).trans hlarge)

/-- P0082 page 364 case ii d. The small conductor cutoff gives an
ineffective zero free interval at the inverse fourteenth E scale. -/
theorem small_conductor_zero_free652 :
    ∃ b : ℝ, 0 < b ∧ ∀ E : ℝ, 1 ≤ E → ∀ (r : ℕ) [NeZero r]
      (χ : DirichletCharacter ℂ r), χ ≠ 1 → χ ^ 2 = 1 →
        (r : ℝ) ≤ E ^ (1 / 7 : ℝ) →
        ∀ β : ℝ, 1 - b * E ^ (-(1 / 14 : ℝ)) < β → β ≤ 1 →
          χ.LFunction β ≠ 0 := by
  obtain ⟨b, hb, H⟩ := quadratic_zero_free_half652
  refine ⟨b, hb, ?_⟩
  intro E hE r hr χ hχ hreal hrE β hβ hβ1
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hp : E ^ (-(1 / 14 : ℝ)) ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = (E ^ (1 / 7 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hE0.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hr0 hrE (by norm_num)
  have hscale := mul_le_mul_of_nonneg_left hp hb.le
  exact H r χ hχ hreal β (by linarith) hβ1

end LeanLab.ExceptionalSet.UpJ200.Decomp527a

/- task527 installed section pointwise.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- LEAF: P0082 page363 case ii c before display22.
The odd part of the conductor of a primitive real character is squarefree.
Only the odd local conductor obstruction is included. -/
theorem leaf_real_primitive_odd_part (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1)
    (k u : ℕ) (hr : r = 2 ^ k * u) (hu : Odd u) :
    Squarefree u := by
  exact LeanLab.ExceptionalSet.UpJ200.Decomp559a.real_primitive_odd_part
    r χ hprimitive hreal hnonprincipal k u hr hu

/-- LEAF: P0082 page363 case ii c before display22.
The power of two in a primitive real conductor has exponent at most three.
Only the two primary conductor obstruction is included. -/
theorem leaf_real_primitive_two_part (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1)
    (k u : ℕ) (hr : r = 2 ^ k * u) (hu : Odd u) :
    k ≤ 3 := by
  exact LeanLab.ExceptionalSet.UpJ200.Decomp559a.real_primitive_two_part
    r χ hprimitive hreal hnonprincipal k u hr hu

/-- P0082 page363 case ii c before display22. Mathlib supplies the odd
part decomposition. The two local real character inputs give the printed shape.
CONDITIONAL ON the odd and two primary conductor leaves. -/
theorem real_primitive_conductor (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hprimitive : χ.IsPrimitive)
    (hreal : χ ^ 2 = 1) (hnonprincipal : χ ≠ 1) :
    ∃ k u : ℕ, r = 2 ^ k * u ∧ k ≤ 3 ∧ Odd u ∧ Squarefree u := by
  obtain ⟨k, u, hu, hr⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne r)
  exact ⟨k, u, hr,
    leaf_real_primitive_two_part r χ hprimitive hreal hnonprincipal k u hr hu, hu,
    leaf_real_primitive_odd_part r χ hprimitive hreal hnonprincipal k u hr hu⟩

/-- LEAF: P0082 pages362 to364 Lemma7, displays20 and21.
One selected conductor supplies the four pointwise character cases.
They are absence, coprimality, a nonempty prime product and a near zero.
The selected primitive real character and both positive divisor errors remain.
No exceptional count or odd coefficient estimate is included. -/
theorem leaf_pointwise_major_character (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            (r = 1 ∨ ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r),
              χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              let Y := (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)
              (r = 1 → c * F γ N ≤ Y) ∧
              (r ≠ 1 → Int.gcd (nu γ n + j) r = 1 → c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                  c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                  c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y) := by
  obtain ⟨a, hapos, hselect⟩ := selected_real_zero652
  obtain ⟨δa, hδa, ha⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected γ h1 h2 a hapos
  obtain ⟨δb, hδb, hb⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected γ h1 h2 a hapos
  obtain ⟨δd, hδd, hd⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected γ h1 h2 a hapos
  obtain ⟨δe, hδe, he⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected γ h1 h2 a hapos
  refine ⟨min δa (min δb (min δd δe)), lt_min hδa (lt_min hδb (lt_min hδd hδe)), ?_⟩
  intro δ hδ hδsmall
  have hdeltas := lt_min_iff.mp hδsmall
  have hdeltas' := lt_min_iff.mp hdeltas.2
  have hdeltas'' := lt_min_iff.mp hdeltas'.2
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ hdeltas.1
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ hdeltas'.1
  obtain ⟨κd, hκd, hd⟩ := hd δ hδ hdeltas''.1
  obtain ⟨κe, hκe, he⟩ := he δ hδ hdeltas''.2
  refine ⟨min κa (min κb (min κd κe)), lt_min hκa (lt_min hκb (lt_min hκd hκe)), ?_⟩
  intro κ hκ hκsmall
  have hkappas := le_min_iff.mp hκsmall
  have hkappas' := le_min_iff.mp hkappas.2
  have hkappas'' := le_min_iff.mp hkappas'.2
  obtain ⟨ca, Aa, hca, hAa, Na, ha⟩ := ha κ hκ hkappas.1
  obtain ⟨cb, Ab, hcb, hAb, Nb, hb⟩ := hb κ hκ hkappas'.1
  obtain ⟨cd, Ad, hcd, hAd, Nd, hd⟩ := hd κ hκ hkappas''.1
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hkappas''.2
  let c := min ca (min cb (min cd ce))
  let A := Aa + Ab + Ad + Ae
  have hc : 0 < c := lt_min hca (lt_min hcb (lt_min hcd hce))
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Filter.Tendsto (fun N : ℕ => F γ N) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Filter.Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  obtain ⟨Np, hNp⟩ := Filter.eventually_atTop.mp (hP.eventually_ge_atTop 2)
  refine ⟨c, A, hc, hA, max Np (max Na (max Nb (max Nd Ne))), ?_⟩
  intro N hN
  have hNs := max_le_iff.mp hN
  have hNs' := max_le_iff.mp hNs.2
  have hNs'' := max_le_iff.mp hNs'.2
  have hNs''' := max_le_iff.mp hNs''.2
  obtain ⟨r, hr, hrP, hs⟩ := hselect _ (hNp N hNs.1)
  refine ⟨r, hr, hrP, LeanLab.ExceptionalSet.UpJ200.Decomp559b.selected_shape a _ r hs, ?_⟩
  intro j hj n hn heven hm
  dsimp only
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hca' : c ≤ ca := min_le_left _ _
  have hcb' : c ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have hcd' : c ≤ cd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hce' : c ≤ ce := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAa' : Aa ≤ A := by dsimp [A]; linarith
  have hAb' : Ab ≤ A := by dsimp [A]; linarith
  have hAd' : Ad ≤ A := by dsimp [A]; linarith
  have hAe' : Ae ≤ A := by dsimp [A]; linarith
  have transfer (ci Ai w : ℝ) (hw : 0 ≤ w) (hci : c ≤ ci) (hAi : Ai ≤ A)
      (h : ci * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)) :
      c * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    have hleft := mul_le_mul_of_nonneg_right hci (mul_nonneg hX hw)
    have hright := mul_le_mul_of_nonneg_right hAi (mul_nonneg hX hD)
    nlinarith only [hleft, hright, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcase
    have hh := ha N hNs'.1 r hr hrP hs j hj n hn heven hm hcase
    simpa only [mul_one] using transfer ca Aa 1 (by norm_num) hca' hAa' (by simpa using hh)
  · intro hcase hgcd
    have hh := hb N hNs''.1 r hr hrP hs j hj n hn heven hm hcase hgcd
    simpa only [mul_one] using transfer cb Ab 1 (by norm_num) hcb' hAb' (by simpa using hh)
  · intro hgcd hprime
    have hh := hd N hNs'''.1 r hr hrP hs j hj n hn heven hm hgcd hprime
    simpa only [mul_one] using transfer cd Ad 1 (by norm_num) hcd' hAd' (by simpa using hh)
  · intro hgcd hprime hsmall
    exact transfer ce Ae _ (Real.rpow_nonneg (Real.exp_pos _).le _) hce' hAe'
      (he N hNs'''.2 r hr hrP hs j hj n hn heven hm hgcd hprime hsmall)
end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section cases.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 pages363 and364 cases ii b to ii d. An empty prime product
forces the large gcd alternative for a conductor of the printed shape.
This is CONDITIONAL ON that explicit conductor shape. -/
theorem empty_product_large_gcd (r k u : ℕ) (m : ℤ)
    (hr : r = 2 ^ k * u) (hk : k ≤ 3) (hu : Odd u) (hs : Squarefree u)
    (hnone : ¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) :
    (r : ℝ) / 24 ≤ (Int.gcd m r : ℝ) := by
  have hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m.natAbs := by
    intro p hprime hpu hp3
    apply Int.natCast_dvd.mp
    by_contra hpm
    exact hnone ⟨p, hprime, by rw [hr]; exact dvd_mul_of_dvd_right hpu _, hp3, hpm⟩
  have hh := conductor_large_gcd r m.natAbs k u hr hk hu hs hp
  have hcast : (r : ℝ) ≤ 24 * (Int.gcd m r : ℝ) := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using
      (show (r : ℝ) ≤ 24 * (Nat.gcd m.natAbs r : ℝ) by exact_mod_cast hh)
  linarith

/-- P0082 pages362 to364 Lemma7. The four pointwise source cases
cover every conductor except the large conductor large gcd alternative.
The four coefficient estimates remain explicit inputs. -/
theorem four_case_lower (r k u : ℕ) (m : ℤ) (c X E Y : ℝ)
    (hshape : r = 1 ∨ (r = 2 ^ k * u ∧ k ≤ 3 ∧ Odd u ∧ Squarefree u))
    (hc : 0 ≤ c) (hX : 0 ≤ X) (hE : 1 ≤ E)
    (hgood : (r : ℝ) ≤ E ^ (1 / 7 : ℝ) ∨ (Int.gcd m r : ℝ) < (r : ℝ) / 24)
    (ha : r = 1 → c * X ≤ Y)
    (hb : r ≠ 1 → Int.gcd m r = 1 → c * X ≤ Y)
    (hd : 1 < Int.gcd m r →
      (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) → c * X ≤ Y)
    (he : 1 < Int.gcd m r →
      (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) →
      (r : ℝ) ≤ E ^ (1 / 7 : ℝ) → c * X * E ^ (-(1 / 10 : ℝ)) ≤ Y) :
    c * X * E ^ (-(1 / 10 : ℝ)) ≤ Y := by
  have hscale : c * X * E ^ (-(1 / 10 : ℝ)) ≤ c * X :=
    mul_le_of_le_one_right (mul_nonneg hc hX)
      (Real.rpow_le_one_of_one_le_of_nonpos hE (by norm_num))
  by_cases hr : r = 1
  · exact hscale.trans (ha hr)
  by_cases hg : Int.gcd m r = 1
  · exact hscale.trans (hb hr hg)
  have hrpos : 0 < r := by
    rcases hshape with h | ⟨h, _, _, hsq⟩
    · omega
    · rw [h]
      exact mul_pos (by positivity) (Nat.pos_of_ne_zero hsq.ne_zero)
  have hgpos : 0 < Int.gcd m r := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using Nat.gcd_pos_of_pos_right m.natAbs hrpos
  have hg1 : 1 < Int.gcd m r := by omega
  by_cases hp : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m
  · exact hscale.trans (hd hg1 hp)
  apply he hg1 hp
  rcases hgood with hsmall | hsmall
  · exact hsmall
  · obtain ⟨hrshape, hk, hu, hs⟩ := hshape.resolve_left hr
    exact False.elim (not_lt_of_ge (empty_product_large_gcd r k u m hrshape hk hu hs hp) hsmall)

/-- P0082 pages362 to364 Lemma7. The finite source case split gives
one pointwise estimate before the exceptional sets are counted.
CONDITIONAL ON the pointwise major estimate and real character classification. -/
theorem pointwise_lower_from_cases (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δ₀, hδ₀, h⟩ := leaf_pointwise_major_character γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, A, hc, hA, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, A, hc, hA, max 2 N₀, fun N hN => ?_⟩
  obtain ⟨r, hr, hrP, hcharacter, hcases⟩ := h N (by omega)
  obtain ⟨k, u, hshape⟩ : ∃ k u : ℕ,
      r = 1 ∨ (r = 2 ^ k * u ∧ k ≤ 3 ∧ Odd u ∧ Squarefree u) := by
    rcases hcharacter with habsent | ⟨hrzero, χ, hprimitive, hreal, hnonprincipal⟩
    · exact ⟨0, 1, Or.inl habsent⟩
    · letI := hrzero
      obtain ⟨k, u, h⟩ := real_primitive_conductor r χ hprimitive hreal hnonprincipal
      exact ⟨k, u, Or.inr h⟩
  refine ⟨r, hr, hrP, fun j hj n hn he hm hgood => ?_⟩
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  obtain ⟨ha, hb, hd, he⟩ := hcases j hj n hn he hm
  exact four_case_lower r k u (nu γ n + j) c (F γ N) (calE γ κ N) _
    hshape hc.le (Real.exp_pos _).le hE hgood ha hb hd he

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section count.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Finset
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Lemma4)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 page362 before Lemma6. The even adjacent integer. -/
noncomputable def evenMember (γ : ℝ) (n : ℕ) : ℤ :=
  if Even (nu γ n) then nu γ n else nu γ n + 1

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
  obtain ⟨δp, hδp, hp⟩ := pointwise_lower_from_cases γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := error_mean LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
  obtain ⟨δg, hδg, hg⟩ := large_gcd_from_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
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
  have hnN : n < N := lt_of_le_of_ne (LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_upper γ h1 N (by omega) n hnw) hnnot
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
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs γ h1 h2
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
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs γ h1 h2
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
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := even_index_from_inputs γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := odd_index_from_inputs γ h1 h2
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
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Be * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
            ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenMember γ n = nu γ n := by simp [evenMember, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepE⟩
    exact (Nat.cast_le.mpr hsub).trans (he N hNe)
  have hB : ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Bo * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
            co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : ¬ Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenMember γ n = nu γ n + 1 := by simp [evenMember, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepO⟩
    exact (Nat.cast_le.mpr hsub).trans (ho N hNo)
  have hpart : (window γ N).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) =
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) ∪
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
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
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenMember γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  push_cast
  refine (add_le_add hA hB).trans_eq ?_
  ring


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


/- task527 installed section zero-gap.txt -/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Real Filter Topology
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page364 final sentence of case ii d. The scalar logarithmic
loss is eventually absorbed by the margin between one fourteenth and one tenth.
This proves the asymptotic premise of near_zero_log_margin for the actual E. -/
theorem zero_gap_scale_absorbed (γ κ : ℝ) (hγ : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        calE γ κ N ^ (-(1 / 14 : ℝ)) / (Real.log (calE γ κ N)) ^ 2 := by
  let a := 3 - 2 * γ
  have ha : 0 < a := by dsimp [a]; linarith
  have ht : Tendsto (fun N : ℕ => κ * Real.log (N : ℝ) ^ a) atTop atTop :=
    ((tendsto_rpow_atTop ha).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hκ
  have hp := (isLittleO_rpow_exp_pos_mul_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 35)).bound
    (by norm_num : (0 : ℝ) < 1)
  apply eventually_atTop.mp
  filter_upwards [ht.eventually hp, ht.eventually_ge_atTop 1] with N hbound hlarge
  have hlog : Real.log (calE γ κ N) = κ * Real.log (N : ℝ) ^ a := by rw [calE, Real.log_exp]
  have hlogpos : 0 < Real.log (calE γ κ N) := by rw [hlog]; linarith
  have hsq : (Real.log (calE γ κ N)) ^ 2 ≤ calE γ κ N ^ (1 / 35 : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two,
      abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _), one_mul] at hbound
    rw [hlog, calE, ← Real.exp_mul]
    convert hbound using 1 <;> dsimp [a] <;> congr 1 <;> ring
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    have hN : 0 ≤ κ * Real.log (N : ℝ) ^ a := by linarith
    exact hN
  exact near_zero_log_margin _ _ hE hlogpos hsq

end LeanLab.ExceptionalSet.UpJ200.Decomp527a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Finset

/-- P0082 page 359 display 12. The first Euler product excludes all
prime divisors of the conductor times the positive frequency. -/
noncomputable def singularEulerFactor652 (r m : ℕ) : ℝ :=
  ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ r * m then
    1 - 1 / ((p : ℝ) - 1) ^ 2 else 1


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Finset

/-- P0082 page 359 display 12. Every local factor and the full first
Euler product lie between zero and one. -/
theorem singularEulerFactor_bounds652 (r m : ℕ) :
    0 ≤ singularEulerFactor652 r m ∧ singularEulerFactor652 r m ≤ 1 := by
  have hlocal (p : ℕ) :
      0 ≤ (if p.Prime ∧ ¬ p ∣ r * m then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ∧
      (if p.Prime ∧ ¬ p ∣ r * m then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
    split_ifs with hp
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
      have hd : 0 < (p : ℝ) - 1 := by linarith
      have hsq : 1 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hfrac : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 :=
        (div_le_one (sq_pos_of_pos hd)).mpr hsq
      exact ⟨sub_nonneg.mpr hfrac, sub_le_self _ (by positivity)⟩
    · norm_num
  unfold singularEulerFactor652
  exact ⟨tprod_nonneg (fun p => (hlocal p).1), tprod_le_of_prod_le' le_rfl (fun s =>
    Finset.prod_le_one₀ (fun p _ => (hlocal p).1) (fun p _ => (hlocal p).2))⟩


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Finset

/-- P0082 page 359 display 12. The real Euler expression for the
exceptional singular factor at a positive natural frequency. On the paper domain
the character value at minus one is real, so its real part gives the
printed sign. The values at conductor zero or frequency zero extend the formula.
No major arc expansion is asserted by this definition. -/
noncomputable def exceptionalSingular652 (r : ℕ) (χ : DirichletCharacter ℂ r)
    (m : ℕ) : ℝ :=
  (χ (-1 : ZMod r)).re * (ArithmeticFunction.moebius (r / Nat.gcd r m) : ℝ) *
    ((r : ℝ) / ((r.totient : ℝ) * ((r / Nat.gcd r m).totient : ℝ)) *
      singularEulerFactor652 r m *
      ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ r), (1 + 1 / ((p : ℝ) - 1)))


end LeanLab.ExceptionalSet.UpJ200.Decomp527a


namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a
open Finset

/-- P0082 page 363 case ii a from page 359 display 12. At a positive
frequency coprime to the conductor the explicit exceptional singular
factor is at most r over phi r squared times m over phi m in absolute value. -/
theorem exceptionalSingular_coprime_bound652 (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (m : ℕ) (hm : 1 ≤ m) (hcop : Nat.Coprime r m) :
    |exceptionalSingular652 r χ m| ≤
      (r : ℝ) / (r.totient : ℝ) ^ 2 * ((m : ℝ) / (m.totient : ℝ)) := by
  let s := m.primeFactors.filter (fun p => ¬ p ∣ r)
  let A := singularEulerFactor652 r m
  let B := ∏ p ∈ s, (1 + 1 / ((p : ℝ) - 1))
  let w := (r : ℝ) / ((r.totient : ℝ) * (r.totient : ℝ))
  have hfactor (p : ℕ) (hp : p ∈ m.primeFactors) : 1 ≤ (1 + 1 / ((p : ℝ) - 1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hd : 0 < (p : ℝ) - 1 := by linarith
    exact le_add_of_nonneg_right (by positivity)
  have hB0 : 0 ≤ B := Finset.prod_nonneg (fun p hp =>
    zero_le_one.trans (hfactor p (Finset.mem_filter.mp hp).1))
  have hB : B ≤ (m : ℝ) / (m.totient : ℝ) := by
    calc
      _ ≤ ∏ p ∈ m.primeFactors, (1 + 1 / ((p : ℝ) - 1)) :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
          (fun p hp => zero_le_one.trans (hfactor p (Finset.mem_filter.mp hp).1))
          (fun p hp _ => hfactor p hp)
      _ = ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hd : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hd]; ring
      _ = (m : ℝ) / (m.totient : ℝ) :=
        (LeanLab.HeathBrown1985.div_totient_eq_prod m hm).symm
  have hA : 0 ≤ A ∧ A ≤ 1 := singularEulerFactor_bounds652 r m
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hbig : 0 ≤ w * A * B := mul_nonneg (mul_nonneg hw hA.1) hB0
  have hχ : |(χ (-1 : ZMod r)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hμ : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
  have hcoef : |(χ (-1 : ZMod r)).re| * |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
    simpa only [mul_one] using mul_le_mul hχ hμ (abs_nonneg _) zero_le_one
  rw [exceptionalSingular652, hcop.gcd_eq_one, Nat.div_one, pow_two]
  change |(χ (-1 : ZMod r)).re * (ArithmeticFunction.moebius r : ℝ) * (w * A * B)| ≤
    w * ((m : ℝ) / (m.totient : ℝ))
  rw [abs_mul, abs_mul, abs_of_nonneg hbig]
  calc
    _ ≤ 1 * (w * A * B) := mul_le_mul_of_nonneg_right hcoef hbig
    _ = w * (A * B) := by ring
    _ ≤ w * (1 * ((m : ℝ) / (m.totient : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hA.2 hB hB0 zero_le_one) hw
    _ = _ := by ring

end LeanLab.ExceptionalSet.UpJ200.Decomp527a

import LeanLab.ExceptionalSet.Endpoint465

/-!
The floor residue step of P0082 page 360 display 16.
The discrepancy estimate is an explicit input. Its omitted proof on page359
is not supplied by this file. AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

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

end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

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
    refine ⟨Decomp371a.window_subset_Ioc γ h1 N hN hnw, ?_⟩
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

end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

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
    refine ⟨Decomp371a.window_subset_Ioc γ h1 N hN hnw, ?_⟩
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


end LeanLab.ExceptionalSet.Supply465

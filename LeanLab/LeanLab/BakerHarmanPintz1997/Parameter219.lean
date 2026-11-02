/-
Baker, Harman and Pintz 1997, page 21, final derivative test displays.
Numerical parameter estimates for the proved logarithmic derivative test.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.LogarithmicTest219

namespace LeanLab.BakerHarmanPintz1997.Parameter219
open Finset PortedVanDerCorput LogarithmicTest219

/-- Page 21. A terminal scale in the selected window gives a uniform second derivative bound. -/
theorem terminal_bound_of_window {N K c lam : ℝ} (hN : 1 ≤ N) (hK : 0 < K) (hc : 0 ≤ c)
    (hlo : K * N ^ (-3 / 2 : ℝ) ≤ lam) (hhi : lam ≤ K * N ^ (-1 / 4 : ℝ)) :
    8 * (c * (2 * N) * Real.sqrt lam + 1 / Real.sqrt lam) ≤
      8 * (2 * c * Real.sqrt K + 1 / Real.sqrt K) * N ^ (7 / 8 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hKsqrt : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsqrt (s : ℝ) : Real.sqrt (K * N ^ s) = Real.sqrt K * N ^ (s / 2) := by
    rw [Real.sqrt_mul hK.le]
    simp_rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hl : Real.sqrt K * N ^ (-3 / 4 : ℝ) ≤ Real.sqrt lam := by
    have hh := Real.sqrt_le_sqrt hlo
    rw [hsqrt] at hh
    norm_num at hh ⊢
    exact hh
  have hu : Real.sqrt lam ≤ Real.sqrt K * N ^ (-1 / 8 : ℝ) := by
    have hh := Real.sqrt_le_sqrt hhi
    rw [hsqrt] at hh
    norm_num at hh ⊢
    exact hh
  have hinv : 1 / Real.sqrt lam ≤ (1 / Real.sqrt K) * N ^ (3 / 4 : ℝ) := by
    have hh := one_div_le_one_div_of_le (mul_pos hKsqrt (Real.rpow_pos_of_pos hN0 _)) hl
    refine hh.trans_eq ?_
    rw [← one_div_mul_one_div]
    simp_rw [one_div]
    rw [← Real.rpow_neg hN0.le]
    norm_num
  have hp : N * N ^ (-1 / 8 : ℝ) = N ^ (7 / 8 : ℝ) := by
    nth_rw 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hN0]
    norm_num
  have hpow : N ^ (3 / 4 : ℝ) ≤ N ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  calc
    _ ≤ 8 * (c * (2 * N) * (Real.sqrt K * N ^ (-1 / 8 : ℝ)) +
      (1 / Real.sqrt K) * N ^ (3 / 4 : ℝ)) := by gcongr
    _ ≤ 8 * (c * (2 * N) * (Real.sqrt K * N ^ (-1 / 8 : ℝ)) +
      (1 / Real.sqrt K) * N ^ (7 / 8 : ℝ)) := by gcongr
    _ = _ := by
      have heq : c * (2 * N) * (Real.sqrt K * N ^ (-1 / 8 : ℝ)) =
          2 * c * Real.sqrt K * N ^ (7 / 8 : ℝ) := by
        calc
          _ = 2 * c * Real.sqrt K * (N * N ^ (-1 / 8 : ℝ)) := by ring
          _ = _ := by rw [hp]
      rw [heq]
      ring

/-- Page 21. A fixed constant is absorbed by every strictly larger positive base power eventually. -/
theorem constant_mul_rpow_le_eventually (C α β : ℝ) (hαβ : α < β) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ N : ℝ, X ≤ N → C * N ^ α ≤ N ^ β := by
  have hh : ∀ᶠ N : ℝ in Filter.atTop, C ≤ N ^ (β - α) :=
    (tendsto_rpow_atTop (by linarith : 0 < β - α)).eventually (Filter.eventually_ge_atTop C)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hh
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  calc
    _ ≤ N ^ (β - α) * N ^ α :=
      mul_le_mul_of_nonneg_right (hX N ((le_max_right _ _).trans hN)) (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- Page 21. The natural floor of the shift range loses a factor at most two. -/
theorem floor_shift_inverse {N δ : ℝ} (hN : 0 < N) (hbig : 2 ≤ N ^ δ) :
    1 ≤ ⌊N ^ δ⌋₊ ∧ 1 / (⌊N ^ δ⌋₊ : ℝ) ≤ 2 * N ^ (-δ) := by
  have hp : 0 < N ^ δ := Real.rpow_pos_of_pos hN _
  have hf := Nat.lt_floor_add_one (N ^ δ)
  have hhalf : N ^ δ / 2 ≤ (⌊N ^ δ⌋₊ : ℝ) := by linarith
  have hf1 : 1 ≤ (⌊N ^ δ⌋₊ : ℝ) := by linarith
  refine ⟨by exact_mod_cast hf1, ?_⟩
  calc
    _ ≤ 1 / (N ^ δ / 2) := one_div_le_one_div_of_le (by positivity) hhalf
    _ = _ := by rw [Real.rpow_neg hN.le]; ring

/-- Page 21. The chosen error parameter has enough power for the diagonal term. -/
theorem differencing_error_power {N δ : ℝ} (hN : 0 < N) (d : ℕ) :
    (2 * N ^ (-δ / (2 : ℝ) ^ d)) ^ (2 ^ d) =
      (2 : ℝ) ^ (2 ^ d) * N ^ (-δ) := by
  rw [mul_pow, ← Real.rpow_natCast (N ^ (-δ / (2 : ℝ) ^ d)) (2 ^ d), ← Real.rpow_mul hN.le]
  congr 1
  push_cast
  field_simp

/-- Page 21. At a fixed derivative order the logarithmic phase has a power saving. -/
theorem logarithmic_fixed_order (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8)
    (hδd : δ * d ≤ 1 / 4) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ N : ℝ, X ≤ N → ∀ a t r : ℝ, 1 ≤ a → a ≤ N → 0 < t →
      N ^ (-3 / 2 : ℝ) ≤ t * (a / N) ^ (d + 2) →
      t * (a / N) ^ (d + 2) ≤ N ^ (-1 / 2 : ℝ) →
      ∀ p q : ℤ, N ≤ a * p + r → a * q + r ≤ 2 * N →
      ‖∑ n ∈ Icc p q, eK (t * (-Real.log (a * n + r)))‖ ≤
        16 * N ^ (1 - δ / (2 : ℝ) ^ d) := by
  let K : ℝ := (d + 1).factorial / (4 : ℝ) ^ (d + 2)
  let c : ℝ := (4 : ℝ) ^ (d + 2)
  let B : ℝ := 8 * (2 * c * Real.sqrt K + 1 / Real.sqrt K)
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨X₁, hX₁, hterminal⟩ := constant_mul_rpow_le_eventually B (7 / 8) (1 - δ) (by linarith)
  have hpowpos : 0 < (2 : ℝ) ^ d := by positivity
  obtain ⟨X₂, hX₂, heps⟩ := constant_mul_rpow_le_eventually 2 (-δ / (2 : ℝ) ^ d) 0 (div_neg_of_neg_of_pos (neg_neg_of_pos hδ) hpowpos)
  have hh : ∀ᶠ N : ℝ in Filter.atTop, 2 ≤ N ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (Filter.eventually_ge_atTop 2)
  obtain ⟨X₃, hX₃⟩ := Filter.eventually_atTop.mp hh
  refine ⟨max X₁ (max X₂ X₃), hX₁.trans (le_max_left _ _), ?_⟩
  intro N hNX a t r ha haN ht hlow hhigh p q hleft hright
  have hNX₁ : X₁ ≤ N := (le_max_left _ _).trans hNX
  have hNX₂ : X₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNX)
  have hNX₃ : X₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNX)
  have hN : 1 ≤ N := hX₁.trans hNX₁
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := by linarith
  let L : ℕ := ⌊N ^ δ⌋₊
  let eps : ℝ := 2 * N ^ (-δ / (2 : ℝ) ^ d)
  have hbig : 2 ≤ N ^ δ := hX₃ N hNX₃
  have hfloor := floor_shift_inverse hN0 hbig
  have hLbound : (L : ℝ) ≤ N ^ δ := Nat.floor_le (Real.rpow_nonneg hN0.le _)
  have hLU : (L : ℝ) ≤ 2 * N := by
    have hh : N ^ δ ≤ N := by
      calc N ^ δ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
           _ = N := Real.rpow_one N
    linarith
  have heps0 : 0 ≤ eps := by dsimp [eps]; positivity
  have heps1 : eps ≤ 1 := by simpa only [Real.rpow_zero] using heps N hNX₂
  have hepsexp : eps ^ (2 ^ d) = (2 : ℝ) ^ (2 ^ d) * N ^ (-δ) := differencing_error_power hN0 d
  have htwo : 2 ≤ (2 : ℝ) ^ (2 ^ d) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.one_le_two_pow)
  have hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ d) := by
    rw [hepsexp]
    exact hfloor.2.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN0.le _))
  have hsize : ((Icc p q).card : ℝ) ≤ 2 * N := by
    by_cases hpq : p ≤ q
    · have hdiff0 : (0 : ℝ) ≤ (q : ℝ) - p := by exact_mod_cast sub_nonneg.mpr hpq
      have hdiff : (q : ℝ) - p ≤ N := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) hdiff0]
      have hz : 0 ≤ q + 1 - p := by omega
      have hzcast : ((q + 1 - p).toNat : ℝ) = ((q + 1 - p : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hz
      rw [Int.card_Icc, hzcast]
      push_cast
      linarith
    · rw [Icc_eq_empty_of_lt (by omega), card_empty, Nat.cast_zero]
      positivity
  have hright4 : a * ((q : ℝ) + 2) + r ≤ 4 * N := by nlinarith
  have htest := logarithmic_iterated_bound d p q L ha0 ht hN0 (by linarith : N ≤ 4 * N)
    hleft hright4 hfloor.1 (by positivity : 0 < 2 * N) hLU hsize heps0 heps1 hLin
    (by
      intro hs hlen hhs
      have hwindow := logDifferenceScale_window hs hN ht.le hLbound
        (by simpa only [hlen] using hδd) (by
          intro h hh
          have hh' := hhs h hh
          exact ⟨by exact_mod_cast hh'.1, by exact_mod_cast hh'.2.le⟩)
        (by simpa only [hlen] using hlow) (by simpa only [hlen] using hhigh)
      have hwindow' : K * N ^ (-3 / 2 : ℝ) ≤ logDifferenceScale a t (4 * N) hs ∧
          logDifferenceScale a t (4 * N) hs ≤ K * N ^ (-1 / 4 : ℝ) := by
        simpa only [K, hlen] using hwindow
      have hb := terminal_bound_of_window hN hK hc hwindow'.1 hwindow'.2
      have hratio : (4 * N) / N = (4 : ℝ) := by field_simp
      rw [hratio]
      calc
        _ ≤ B * N ^ (7 / 8 : ℝ) := hb
        _ ≤ N ^ (1 - δ) := hterminal N hNX₁
        _ ≤ (2 * N) * eps ^ (2 ^ d) := by
          rw [hepsexp]
          have hid : N ^ (1 - δ) = N * N ^ (-δ) := by
            calc
              _ = N ^ (1 + -δ) := by congr 1
              _ = N ^ (1 : ℝ) * N ^ (-δ) := Real.rpow_add hN0 _ _
              _ = _ := by rw [Real.rpow_one]
          rw [hid]
          exact mul_le_mul (by linarith : N ≤ 2 * N)
            (le_mul_of_one_le_left (Real.rpow_nonneg hN0.le _) (by linarith : 1 ≤ (2 : ℝ) ^ (2 ^ d)))
            (Real.rpow_nonneg hN0.le _) (by positivity))
  calc
    _ ≤ 4 * (2 * N) * eps := htest
    _ = 16 * N ^ (1 - δ / (2 : ℝ) ^ d) := by
      dsimp [eps]
      have hid : N ^ (1 - δ / (2 : ℝ) ^ d) = N * N ^ (-δ / (2 : ℝ) ^ d) := by
        nth_rw 2 [← Real.rpow_one N]
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      rw [hid]
      ring

/-- Page 21. A bounded derivative order gives one threshold and one positive power saving. -/
theorem logarithmic_bounded_order (J : ℕ) :
    ∃ σ X : ℝ, 0 < σ ∧ 1 ≤ X ∧ ∀ N : ℝ, X ≤ N →
      ∀ a t r : ℝ, 1 ≤ a → a ≤ N → 0 < t →
      ∀ d : ℕ, d ≤ J →
      N ^ (-3 / 2 : ℝ) ≤ t * (a / N) ^ (d + 2) →
      t * (a / N) ^ (d + 2) ≤ N ^ (-1 / 2 : ℝ) →
      ∀ p q : ℤ, N ≤ a * p + r → a * q + r ≤ 2 * N →
      ‖∑ n ∈ Icc p q, eK (t * (-Real.log (a * n + r)))‖ ≤ 16 * N ^ (1 - σ) := by
  classical
  let δ : ℝ := 1 / (16 * ((J : ℝ) + 1))
  have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 16 * ((J : ℝ) + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ < 1 / 8 := by
    dsimp [δ]
    apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 8)).mpr
    linarith
  have hδd : ∀ d : Fin (J + 1), δ * (d.val : ℝ) ≤ 1 / 4 := by
    intro d
    have hd : (d.val : ℝ) ≤ J := by exact_mod_cast (show d.val ≤ J by omega)
    dsimp [δ]
    rw [show 1 / (16 * ((J : ℝ) + 1)) * (d.val : ℝ) = (d.val : ℝ) / (16 * ((J : ℝ) + 1)) by ring]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  choose X hX1 hX using (fun d : Fin (J + 1) => logarithmic_fixed_order d.val hδ hδsmall (hδd d))
  let Xmax : ℝ := (univ : Finset (Fin (J + 1))).sup' univ_nonempty X
  let σ : ℝ := δ / (2 : ℝ) ^ J
  have hσ : 0 < σ := by dsimp [σ]; positivity
  refine ⟨σ, Xmax, hσ, ?_, ?_⟩
  · exact (hX1 ⟨0, by omega⟩).trans (le_sup' X (mem_univ _))
  · intro N hN a t r ha haN ht d hd hlo hhi p q hleft hright
    let i : Fin (J + 1) := ⟨d, by omega⟩
    have hXi : X i ≤ N := (le_sup' X (mem_univ i)).trans hN
    have hb := hX i N hXi a t r ha haN ht hlo hhi p q hleft hright
    have hNone : 1 ≤ N := (hX1 i).trans hXi
    have hσd : σ ≤ δ / (2 : ℝ) ^ d := by
      dsimp [σ]
      exact div_le_div_of_nonneg_left hδ.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hd)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)) (by norm_num))

#print axioms logarithmic_bounded_order
#print axioms logarithmic_fixed_order
#print axioms constant_mul_rpow_le_eventually
#print axioms floor_shift_inverse
#print axioms differencing_error_power
#print axioms terminal_bound_of_window
end LeanLab.BakerHarmanPintz1997.Parameter219

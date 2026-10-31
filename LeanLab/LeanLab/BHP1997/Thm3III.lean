/-
P0069 page 5, unit U-5033: Theorem 3 (III) from Theorem 3 (II) and Baker-Harman's lower bound
`π(x) - π(x - y) ≫ y / log x` for `x^{0.535} ≤ y ≤ x`, "as in Montgomery and Vaughan".
With `X = x + x^μ` and `y = X^{0.535}`, the primes `q ∈ (X - y, X]` number `≫ y / log X`, more
than the exceptional `h ≤ y` of (II); so some `h = ⌊X⌋ - q` is good, a prime `p` lies in
`(h - h^λ, h]`, and `p + q ∈ (X - 2 - y^λ, X] ⊆ [x, x + x^μ]` since `0.535 λ < μ = 0.0335`.
PROVED here CONDITIONAL ON Theorem 3 (II) and the Baker-Harman bound, both cited.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.BHP1997.Statements

namespace LeanLab.BHP1997
open Real Filter Classical

/-- Baker and Harman [2] as quoted on page 5: `π(x) - π(x - y) ≫ y / log x` for
`x^{0.535} ≤ y ≤ x`. CITED. -/
def BakerHarman535 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℝ, C ≤ X → ∀ y : ℝ, X ^ (0.535 : ℝ) ≤ y → y ≤ X →
    c * y / Real.log X ≤ piAP X y 1 0

/-- A good `h` has a prime in `(⌊h - h^λ⌋, h]`. -/
theorem prime_of_good {lam : ℝ} {h : ℕ} (h2 : 2 ≤ h)
    (hg : 0.05 * (h : ℝ) ^ lam / Real.log h
      < (Nat.primeCounting h : ℝ) - ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card) :
    ∃ p : ℕ, p.Prime ∧ ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊ < p ∧ p ≤ h := by
  have hh : (2 : ℝ) ≤ h := by exact_mod_cast h2
  have hpos : 0 < 0.05 * (h : ℝ) ^ lam / Real.log h :=
    div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _))
      (Real.log_pos (by linarith))
  by_contra hno
  push_neg at hno
  have hsub : (Finset.range (h + 1)).filter Nat.Prime
      ⊆ (Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic] at hp ⊢
    refine ⟨?_, hp.2⟩
    by_contra hlt
    push_neg at hlt
    exact absurd (hno p hp.2 hlt) (by omega)
  have hc := Finset.card_le_card hsub
  have hpc : Nat.primeCounting h = ((Finset.range (h + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hpc] at hg
  have : ((((Finset.range (h + 1)).filter Nat.Prime).card : ℕ) : ℝ)
      ≤ (((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hc
  linarith

/-- `⌊X⌋ - q ≤ ⌊y⌋` for `q > ⌊X - y⌋`. -/
theorem h_le_floor {X y : ℝ} {q : ℕ} (hXy : 0 ≤ X - y) (hy : 0 ≤ y) (hq : ⌊X - y⌋₊ < q) :
    ⌊X⌋₊ - q ≤ ⌊y⌋₊ := by
  have h1 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have h2 : X - y < ⌊X - y⌋₊ + 1 := Nat.lt_floor_add_one _
  have h3 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one _
  have : (⌊X⌋₊ : ℝ) < ⌊X - y⌋₊ + ⌊y⌋₊ + 2 := by linarith
  have : ⌊X⌋₊ < ⌊X - y⌋₊ + ⌊y⌋₊ + 2 := by exact_mod_cast this
  omega

/-- The pigeonhole core: more primes in `(X - y, X]` than exceptional `h` plus `H0` give a
prime `q` there with `h = ⌊X⌋ - q ≥ H0` good. -/
theorem core {X y lam : ℝ} {H0 : ℕ} (hH0 : 2 ≤ H0) (hXy : 0 ≤ X - y) (hy : 0 ≤ y)
    (hcard : ((Finset.Icc 2 ⌊y⌋₊).filter (fun h : ℕ => ¬ (0.05 * (h : ℝ) ^ lam / Real.log h
      < (Nat.primeCounting h : ℝ) - ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card))).card
      + H0 < piAP X y 1 0) :
    ∃ q p : ℕ, q.Prime ∧ ⌊X - y⌋₊ < q ∧ q ≤ ⌊X⌋₊ ∧ H0 ≤ ⌊X⌋₊ - q ∧ p.Prime ∧
      ⌊((⌊X⌋₊ - q : ℕ) : ℝ) - ((⌊X⌋₊ - q : ℕ) : ℝ) ^ lam⌋₊ < p ∧ p ≤ ⌊X⌋₊ - q := by
  set E := (Finset.Icc 2 ⌊y⌋₊).filter (fun h : ℕ => ¬ (0.05 * (h : ℝ) ^ lam / Real.log h
      < (Nat.primeCounting h : ℝ) - ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card))
    with hE
  set Q := (Finset.Ioc ⌊X - y⌋₊ ⌊X⌋₊).filter (fun p => p.Prime ∧ p % 1 = 0 % 1) with hQ
  by_contra hno
  push_neg at hno
  have hmaps : ∀ q ∈ Q, ⌊X⌋₊ - q ∈ E ∪ Finset.range H0 := by
    intro q hq
    simp only [hQ, Finset.mem_filter, Finset.mem_Ioc] at hq
    rcases lt_or_ge (⌊X⌋₊ - q) H0 with hlt | hge
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr hlt)
    · apply Finset.mem_union_left
      simp only [hE, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, h_le_floor hXy hy hq.1.1⟩, fun hg => ?_⟩
      obtain ⟨p, hp, hp1, hp2⟩ := prime_of_good (by omega) hg
      exact absurd hp2 (not_le.mpr (hno q p hq.2.1 hq.1.1 hq.1.2 hge hp hp1))
  have hinj : Set.InjOn (fun q => ⌊X⌋₊ - q) Q := by
    intro a ha b hb hab
    simp only [hQ, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    omega
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinj
  have h2 := Finset.card_union_le E (Finset.range H0)
  rw [Finset.card_range] at h2
  have hpq : piAP X y 1 0 = Q.card := rfl
  rw [hpq] at hcard
  omega

set_option maxHeartbeats 1000000 in
/-- Page 5: Theorem 3 (III) from Theorem 3 (II) and Baker-Harman. CONDITIONAL ON both. -/
theorem theorem3III_of (h2 : Theorem3II) (hBH : BakerHarman535) : Theorem3III := by
  set lam : ℝ := 1 / 16 - 1 / 10 ^ 5 with hlam
  obtain ⟨B, C2, hB⟩ := h2 lam le_rfl 2 two_pos
  obtain ⟨c, hc, C1, hC1⟩ := hBH
  set ν : ℝ := 0.535 * lam with hν
  have hν0 : 0 < ν := by rw [hν, hlam]; norm_num
  have hν1 : ν ≤ 1 := by rw [hν, hlam]; norm_num
  have hμν : 0 < (0.0335 : ℝ) - ν := by rw [hν, hlam]; norm_num
  have hlam_half : lam ≤ 1 / 2 := by rw [hlam]; norm_num
  have hlam0 : 0 ≤ lam := by rw [hlam]; norm_num
  clear_value ν lam
  -- eventual facts in X
  have t535 := tendsto_rpow_atTop (show (0 : ℝ) < 0.535 by norm_num)
  have tL := Real.tendsto_log_atTop
  have EA : ∀ᶠ X : ℝ in atTop, C1 ≤ X ∧ C2 ≤ X ^ (0.535 : ℝ) ∧ 1 ≤ X ∧
      2 * |B| / (0.286225 * c) ≤ Real.log X ∧ 2 ≤ X ^ (0.465 : ℝ) ∧ 4 ≤ X ∧
      Real.log X ≤ c / 32 * X ^ (0.535 : ℝ) := by
    have b : ∀ᶠ X : ℝ in atTop, Real.log X ≤ c / 32 * X ^ (0.535 : ℝ) := by
      filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.535 by norm_num)).bound
        (show (0 : ℝ) < c / 32 by positivity), eventually_ge_atTop 1] with X hX hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX1),
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hX
      exact hX
    filter_upwards [eventually_ge_atTop C1, t535.eventually (eventually_ge_atTop C2),
      eventually_ge_atTop 1, tL.eventually (eventually_ge_atTop (2 * |B| / (0.286225 * c))),
      (tendsto_rpow_atTop (show (0 : ℝ) < 0.465 by norm_num)).eventually (eventually_ge_atTop 2),
      eventually_ge_atTop 4, b] with X h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp EA
  have FA : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 4 ≤ x ^ ((0.0335 : ℝ) - ν) := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_rpow_atTop hμν).eventually (eventually_ge_atTop 4)] with x h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp FA
  refine ⟨max X0 x1, fun x hx => ?_⟩
  obtain ⟨hx1', hx4⟩ := hx1 x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith
  set X := x + x ^ (0.0335 : ℝ) with hXdef
  have hxμ0 : 0 ≤ x ^ (0.0335 : ℝ) := Real.rpow_nonneg hx0.le _
  have hxμx : x ^ (0.0335 : ℝ) ≤ x := by
    calc x ^ (0.0335 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
      _ = x := Real.rpow_one x
  have hXx : x ≤ X := by linarith
  obtain ⟨hC1X, hC2X, hX1, hLB, hX465, hX4, hLy⟩ := hX0 X (le_trans (le_max_left _ _) (le_trans hx hXx))
  have hXpos : 0 < X := by linarith
  clear_value X
  set y := X ^ (0.535 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hXpos _
  -- y ≤ X / 2, so X - y ≥ 2
  have hyX : y ≤ X / 2 := by
    have e : y * X ^ (0.465 : ℝ) = X := by
      rw [hy, ← Real.rpow_add hXpos]; norm_num
    nlinarith
  have hXy : 2 ≤ X - y := by linarith
  set L := Real.log X with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hlogy : Real.log y = 0.535 * L := by rw [hy, Real.log_rpow hXpos]
  clear_value L
  -- the counts
  have hBH := hC1 X hC1X y le_rfl (by linarith)
  have hex := hB y hC2X
  rw [show Real.log y ^ (2 : ℝ) = Real.log y ^ 2 by norm_cast, hlogy] at hex
  have hBle : B ≤ c * 0.286225 * L / 2 := by
    have hB' : B ≤ |B| := le_abs_self B
    have : 2 * |B| ≤ 0.286225 * c * L := by
      rw [div_le_iff₀ (by positivity)] at hLB; linarith
    linarith
  have e1 : B * y / (0.535 * L) ^ 2 ≤ c * y / (2 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hBle (by positivity : (0 : ℝ) ≤ y * (2 * L))
    nlinarith
  have e2 : 8 < c * y / (2 * L) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have e3 : c * y / (2 * L) + c * y / (2 * L) = c * y / L := by field_simp; ring
  have hcount : (((Finset.Icc 2 ⌊y⌋₊).filter (fun h : ℕ => ¬ (0.05 * (h : ℝ) ^ lam / Real.log h
      < (Nat.primeCounting h : ℝ) - ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card))).card
      + 8 : ℝ) < piAP X y 1 0 := by
    have : c * y / Real.log X = c * y / L := by rw [hL]
    linarith
  obtain ⟨q, p, hq, hq1, hq2, hh8, hp, hp1, hp2⟩ := core (X := X) (y := y) (H0 := 8) (lam := lam) (by norm_num)
    (by linarith only [hXy]) hy0.le (by exact_mod_cast hcount)
  set h := ⌊X⌋₊ - q with hh
  have hh8' : (8 : ℝ) ≤ h := by exact_mod_cast hh8
  clear_value h
  -- h^λ ≤ h / 2
  have hlam_le : (h : ℝ) ^ lam ≤ h / 2 := by
    have h1 : (h : ℝ) ^ lam ≤ (h : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hlam_half
    rw [← Real.sqrt_eq_rpow] at h1
    have hs : √(h : ℝ) * √(h : ℝ) = h := Real.mul_self_sqrt (by linarith)
    have hs4 : 2 ≤ √(h : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have h3 := mul_le_mul_of_nonneg_right hs4 (Real.sqrt_nonneg (h : ℝ))
    refine le_trans h1 ?_
    rw [le_div_iff₀ two_pos]
    calc √(h : ℝ) * 2 = 2 * √(h : ℝ) := by ring
      _ ≤ √(h : ℝ) * √(h : ℝ) := h3
      _ = h := hs
  -- p ≥ 3 and q ≥ 3
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) ≤ (h : ℝ) - (h : ℝ) ^ lam := by linarith
    have : 3 ≤ ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊ := Nat.le_floor (by exact_mod_cast this)
    omega
  have hq3 : 3 ≤ q := by
    have : 2 ≤ ⌊X - y⌋₊ := Nat.le_floor (by exact_mod_cast hXy)
    omega
  have hpodd := hp.odd_of_ne_two (by omega)
  have hqodd := hq.odd_of_ne_two (by omega)
  refine ⟨p + q, ?_, ?_, hpodd.add_odd hqodd, ⟨p, q, hp, hq, rfl⟩⟩
  · -- lower end
    have hfl : (h : ℝ) - (h : ℝ) ^ lam < ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊ + 1 := Nat.lt_floor_add_one _
    have hpR : ((⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hp1
    have hXf : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one _
    have hhq : ((h : ℕ) : ℝ) + q = ⌊X⌋₊ := by
      have : h + q = ⌊X⌋₊ := by omega
      exact_mod_cast this
    -- h^λ ≤ y^λ = X^ν ≤ 2 x^ν
    have hhy : (h : ℝ) ≤ y := by
      have := h_le_floor (by linarith) hy0.le hq1
      rw [← hh] at this
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0.le)
    have hpow1 : (h : ℝ) ^ lam ≤ y ^ lam :=
      Real.rpow_le_rpow (by positivity) hhy hlam0
    have hpow2 : y ^ lam = X ^ ν := by rw [hy, ← Real.rpow_mul hXpos.le, hν]
    have hX2x : X ≤ 2 * x := by linarith
    have hpow3 : X ^ ν ≤ (2 * x) ^ ν := Real.rpow_le_rpow hXpos.le hX2x hν0.le
    have hpow4 : (2 * x) ^ ν ≤ 2 * x ^ ν := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      have : (2 : ℝ) ^ ν ≤ 2 := by
        calc (2 : ℝ) ^ ν ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hν1
          _ = 2 := Real.rpow_one 2
      nlinarith [Real.rpow_nonneg hx0.le ν]
    have hxν1 : 1 ≤ x ^ ν := Real.one_le_rpow hx1' hν0.le
    have hxμ : x ^ (0.0335 : ℝ) = x ^ ν * x ^ ((0.0335 : ℝ) - ν) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hF : 2 + 2 * x ^ ν ≤ x ^ (0.0335 : ℝ) := by
      rw [hxμ]
      have := mul_le_mul_of_nonneg_left hx4 (by linarith : (0 : ℝ) ≤ x ^ ν)
      linarith only [this, hxν1]
    push_cast
    linarith only [hpR, hfl, hhq, hXf, hpow1, hpow2, hpow3, hpow4, hF, hXdef]
  · -- upper end
    have hpq : p + q ≤ ⌊X⌋₊ := by omega
    have : ((p + q : ℕ) : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hpq
    have := Nat.floor_le hXpos.le
    linarith

end LeanLab.BHP1997

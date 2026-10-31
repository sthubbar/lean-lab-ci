/-
I-0062, run 20261017T1203Z-5538, unit U-0300. AI-written Lean code, Claude. Checked only by
the Lean kernel.

The right asymptotic constant for almost all even m. From Siegel-Walfisz alone: for every
c < 1 and every C > 0, all but O(X (log X)^{-C}) even m ≤ X satisfy
r(m) ≥ c 𝔖(m) m / log² m, where r(m) counts ordered pairs of primes p + q = m.
So the I-0061 constant 13/240 becomes any c < 1 times 𝔖(m), and with 𝔖(m) ≥ 1.3 any
constant below 13/10.

The loss factor 12 in RightOrderSharp.lean came from two places: the window (2x, 3x],
where x ≥ m/3, and the bound log 3x ≤ 2 log m. Here the window is (2x, 2(1 + δ)x], so
x ≥ m / (2(1 + δ)), the weight log p log(m - p) is bounded by log² m directly, and the
symmetry p ↦ m - p doubles the count of pairs with p ≤ x. The cover of [1, X] uses
ratio 1/(1 + δ).

KNOWN mathematics: almost all even m have r(m) ~ 𝔖(m) m / log² m, circle method,
Chudakov, van der Corput and Estermann 1937 to 1938. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.RightOrderSharp

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Real Filter

attribute [local instance] Classical.propDecidable

/-- Pairs with `p ≤ x < m/2` are at most half of the ordered pairs counted by `r(m)`. -/
theorem two_mul_card_le_r (x : ℝ) (m : ℕ) (hm : 2 * x < (m : ℝ)) :
    2 * ((range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x)).card ≤
      LeanLab.SchnirelmannGoldbach.r m := by
  unfold LeanLab.SchnirelmannGoldbach.r
  set S := (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x)
  set R := (range m).filter (fun p => p.Prime ∧ (m - p).Prime)
  have hmemS : ∀ p ∈ S, p < m ∧ p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x := by
    intro p hp
    simp only [S, mem_filter, mem_range] at hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    refine ⟨?_, hp2, hp3, hp4⟩
    by_contra hcon
    have : m - p = 0 := by omega
    rw [this] at hp3
    exact Nat.not_prime_zero hp3
  have hS : S ⊆ R := by
    intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hmemS p hp
    simp only [R, mem_filter, mem_range]
    exact ⟨h1, h2, h3⟩
  have hT : S.image (fun p => m - p) ⊆ R := by
    intro q hq
    rw [mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨h1, h2, h3, -⟩ := hmemS p hp
    simp only [R, mem_filter, mem_range]
    refine ⟨by have := h2.pos; omega, h3, ?_⟩
    have : m - (m - p) = p := by omega
    rw [this]; exact h2
  have hdisj : Disjoint S (S.image (fun p => m - p)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_image] at hb
    obtain ⟨p, hp, hpa⟩ := hb
    obtain ⟨h1, -, -, h4⟩ := hmemS p hp
    obtain ⟨-, -, -, h4'⟩ := hmemS a ha
    have : (a : ℝ) + p = m := by
      have : a + p = m := by omega
      exact_mod_cast this
    linarith
  have hinj : (S.image (fun p => m - p)).card = S.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    have h1 := (hmemS a ha).1
    have h2 := (hmemS b hb).1
    simp only at hab
    omega
  have := card_le_card (union_subset hS hT)
  rw [card_union_of_disjoint hdisj, hinj] at this
  omega

/-- `N₂(x, m) ≤ log² m · r(m) / 2` when `2x < m`. -/
theorem N2_le_half (x : ℝ) (m : ℕ) (hm : 2 * x < (m : ℝ)) :
    N2 x m ≤ Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) / 2 := by
  unfold N2
  set S := (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x)
  have hterm : ∀ p ∈ S, Real.log p * Real.log (m - p : ℕ) ≤ Real.log m ^ 2 := by
    intro p hp
    simp only [S, mem_filter, mem_range] at hp
    obtain ⟨hp1, hp2, hp3, -⟩ := hp
    have hpm : p ≤ m := by omega
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp2.one_lt.le
    have h2 : (1 : ℝ) ≤ ((m - p : ℕ) : ℝ) := by exact_mod_cast hp3.one_lt.le
    have hl1 : 0 ≤ Real.log p := Real.log_nonneg h1
    have hl2 : 0 ≤ Real.log ((m - p : ℕ) : ℝ) := Real.log_nonneg h2
    have hpm' : (p : ℝ) ≤ m := by exact_mod_cast hpm
    have hmp' : ((m - p : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m p
    have hb1 : Real.log p ≤ Real.log m := Real.log_le_log (by linarith) hpm'
    have hb2 : Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m :=
      Real.log_le_log (by linarith) hmp'
    calc Real.log p * Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m * Real.log m :=
          mul_le_mul hb1 hb2 hl2 (hl1.trans hb1)
      _ = Real.log m ^ 2 := by ring
  have h2 : (2 * S.card : ℕ) ≤ LeanLab.SchnirelmannGoldbach.r m := two_mul_card_le_r x m hm
  have h2' : 2 * (S.card : ℝ) ≤ (LeanLab.SchnirelmannGoldbach.r m : ℝ) := by exact_mod_cast h2
  have hL : 0 ≤ Real.log m ^ 2 := sq_nonneg _
  calc ∑ p ∈ S, Real.log p * Real.log ((m - p : ℕ) : ℝ) ≤ ∑ _p ∈ S, Real.log m ^ 2 :=
        sum_le_sum hterm
    _ = (S.card : ℝ) * Real.log m ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) / 2 := by nlinarith

/-- Even `m ∈ (2x, 2(1 + δ)x]` with `r(m) < c 𝔖(m) m / log² m`. -/
def lowRepsW (c δ x : ℝ) : Finset ℕ :=
  ((range (⌊2 * (1 + δ) * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) < c * singular m * m / Real.log m ^ 2)

/-- Even `m ≤ X`, `m ≥ 4`, with `r(m) < c 𝔖(m) m / log² m`. -/
def lowUpToW (c X : ℝ) : Finset ℕ :=
  (range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) < c * singular m * m / Real.log m ^ 2)

/-- Even `m ∈ (2x, 3x]` with `N₂(x, m) < (1 - η) x 𝔖(m)`. -/
def fewRepsEta (η x : ℝ) : Finset ℕ :=
  ((range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧ N2 x m < (1 - η) * (x * singular m))

theorem fewRepsEta_card_of_theorem1 (h1 : Theorem1) {η : ℝ} (hη : 0 < η) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((fewRepsEta η x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K1, hK1⟩ := h1 C hC
  refine ⟨K1 / η, fun x hx => ?_⟩
  set T := (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))
  have hx0 : 0 < x := by linarith
  have hterm : ∀ m ∈ fewRepsEta η x, η * x ≤ |N2 x m - x * singular m| := by
    intro m hm
    obtain ⟨-, hev, hlt⟩ := mem_filter.mp hm
    have hs : (1 : ℝ) ≤ singular m := le_trans (by norm_num) (singular_ge_13 hev)
    have hxs : η * x ≤ η * (x * singular m) := by
      have := mul_le_mul_of_nonneg_left hs hx0.le
      nlinarith
    have : η * x ≤ x * singular m - N2 x m := by nlinarith
    exact this.trans ((le_abs_self _).trans (abs_sub_comm _ _).le)
  have hsub : fewRepsEta η x ⊆ T := filter_subset _ _
  have hA : ((fewRepsEta η x).card : ℝ) * (η * x) ≤ ∑ m ∈ T, |N2 x m - x * singular m| := by
    calc ((fewRepsEta η x).card : ℝ) * (η * x) = ∑ m ∈ fewRepsEta η x, η * x := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ fewRepsEta η x, |N2 x m - x * singular m| := sum_le_sum hterm
      _ ≤ ∑ m ∈ T, |N2 x m - x * singular m| :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hB := hA.trans (hK1 x hx)
  have hpos : 0 < η * x := by positivity
  rw [← le_div_iff₀ hpos] at hB
  calc ((fewRepsEta η x).card : ℝ) ≤ K1 * x ^ 2 * Real.log x ^ (-C) / (η * x) := hB
    _ = K1 / η * x * Real.log x ^ (-C) := by field_simp

/-- With `c (1 + δ) = 1 - η`, a low `m` in the short window has few weighted pairs. -/
theorem lowRepsW_subset {c δ η x : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hcη : c * (1 + δ) = 1 - η) (hx : 2 ≤ x) : lowRepsW c δ x ⊆ fewRepsEta η x := by
  intro m hm
  simp only [lowRepsW, fewRepsEta, mem_filter, mem_range] at hm ⊢
  obtain ⟨⟨hm1, hm2⟩, hev, hlt⟩ := hm
  have hmX : (m : ℝ) ≤ 2 * (1 + δ) * x := by
    have : m ≤ ⌊2 * (1 + δ) * x⌋₊ := by omega
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
  have hm3 : (m : ℝ) ≤ 3 * x := by nlinarith
  have hm3' : m ≤ ⌊3 * x⌋₊ := Nat.le_floor hm3
  refine ⟨⟨by omega, hm2⟩, hev, ?_⟩
  have hm4 : (4 : ℝ) < m := by linarith
  have hlm : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log m ^ 2 := by positivity
  have hs : (0 : ℝ) < singular m := lt_of_lt_of_le (by norm_num) (singular_ge_13 hev)
  have hmul : Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) <
      c * singular m * m := by
    rw [lt_div_iff₀ hl2] at hlt; linarith
  have hN := N2_le_half x m hm2
  have hcs : 0 ≤ c * singular m := by positivity
  calc N2 x m ≤ Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) / 2 := hN
    _ < c * singular m * m / 2 := by linarith
    _ ≤ c * singular m * (2 * (1 + δ) * x) / 2 := by gcongr
    _ = (c * (1 + δ)) * (x * singular m) := by ring
    _ = (1 - η) * (x * singular m) := by rw [hcη]

/-- The intervals `(X q^{k+1}, X q^k]`, `k < J`, cover `(X q^J, X]`. -/
lemma coverW {q X m : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hX : 0 < X) :
    ∀ J : ℕ, X * q ^ J < m → m ≤ X → ∃ k < J, X * q ^ (k + 1) < m ∧ m ≤ X * q ^ k :=
  cover' hq0 hq1 hX

set_option maxHeartbeats 1000000 in
/-- The geometric cover with ratio `1/(1 + δ)`. -/
theorem lowUpToW_card_of (c δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hK : ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      ((lowRepsW c δ x).card : ℝ) ≤ K * x * Real.log x ^ (-C)) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((lowUpToW c X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  obtain ⟨K1, hK1⟩ := hK C hC
  set K1' := max K1 0
  have hlo := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hlo
  set X0 := max (max X1 16) 3
  set q : ℝ := 1 / (1 + δ)
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hq23 : 2 / 3 ≤ q := by rw [le_div_iff₀ (by linarith)]; linarith
  have hqδ : q * (1 + δ) = 1 := by
    simp only [q]; rw [one_div, inv_mul_cancel₀ (by linarith)]
  set G : ℝ := 1 / (1 - q)
  have hG0 : 0 < G := by have : 0 < 1 - q := by linarith
                         positivity
  refine ⟨max (2 + K1' * 2 ^ C * G) (2 * Real.log X0 ^ C), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hLC : 0 < Real.log X ^ C := Real.rpow_pos_of_pos hL0 C
  have hLmC : Real.log X ^ (-C) = (Real.log X ^ C)⁻¹ := Real.rpow_neg hL0.le C
  have htriv : ((lowUpToW c X).card : ℝ) ≤ X + 1 := by
    have : (lowUpToW c X).card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (by simp)
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
    calc ((lowUpToW c X).card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ X + 1 := by push_cast; linarith
  by_cases hsmall : X ≤ X0
  · have hlX : Real.log X ≤ Real.log X0 := Real.log_le_log hX0 hsmall
    have hpow : Real.log X ^ C ≤ Real.log X0 ^ C :=
      Real.rpow_le_rpow hL0.le hlX hC.le
    have hone : 1 ≤ Real.log X0 ^ C * Real.log X ^ (-C) := by
      rw [hLmC, ← div_eq_mul_inv, le_div_iff₀ hLC]; linarith
    calc ((lowUpToW c X).card : ℝ) ≤ X + 1 := htriv
      _ ≤ 2 * X := by linarith
      _ ≤ 2 * X * (Real.log X0 ^ C * Real.log X ^ (-C)) := by nlinarith
      _ = (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by ring
      _ ≤ max (2 + K1' * 2 ^ C * G) (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by
          gcongr; exact le_max_right _ _
  push_neg at hsmall
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall.le
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall.le
  have hb := hX1 X hXX1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLC,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hb
  have hsq : X ^ (1 / 2 : ℝ) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  rw [hsq] at hb
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have ht1 : Real.log X ^ (-C) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have ht0 : 0 < Real.log X ^ (-C) := Real.rpow_pos_of_pos hL0 _
  obtain ⟨J, hJ1, hJ2⟩ := exists_pow_between' hq0 hq1 ht0 ht1
  set t := Real.log X ^ (-C)
  have hsqX : 4 ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX0.le]; linarith
  have hsqpos : 0 < Real.sqrt X := by linarith
  have hsq2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hXt : Real.sqrt X ≤ X * t / 3 := by
    have : t = (Real.log X ^ C)⁻¹ := hLmC
    rw [this, le_div_iff₀ (by norm_num), ← div_eq_mul_inv, le_div_iff₀ hLC]
    nlinarith
  set x : ℕ → ℝ := fun k => X * q ^ (k + 1) / 2
  have hxk : ∀ k < J, Real.sqrt X ≤ x k := by
    intro k hk
    have h1 : q ^ J ≤ q ^ (k + 1) := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    have h4 : q * t ≤ q ^ (k + 1) := (hJ2.trans_le h1).le
    have h5 : 2 / 3 * t ≤ q * t := by nlinarith
    simp only [x]; nlinarith
  have hx2 : ∀ k < J, 2 ≤ x k := fun k hk => by linarith [hxk k hk]
  have hlogx : ∀ k < J, Real.log X / 2 ≤ Real.log (x k) := by
    intro k hk
    have h1 := Real.log_le_log hsqpos (hxk k hk)
    rwa [Real.log_sqrt hX0.le] at h1
  have hterm : ∀ k < J, ((lowRepsW c δ (x k)).card : ℝ) ≤ K1' * 2 ^ C * (x k * t) := by
    intro k hk
    have h1 := hK1 (x k) (hx2 k hk)
    have hpos : 0 < Real.log X / 2 := by linarith
    have h2 : Real.log (x k) ^ (-C) ≤ (Real.log X / 2) ^ (-C) :=
      Real.rpow_le_rpow_of_nonpos hpos (hlogx k hk) (by linarith)
    have h3 : (Real.log X / 2) ^ (-C) = 2 ^ C * t := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
      ring
    have hxk0 : 0 ≤ x k := by linarith [hx2 k hk]
    have h4 : K1 * x k * Real.log (x k) ^ (-C) ≤ K1' * x k * Real.log (x k) ^ (-C) := by
      have : 0 ≤ x k * Real.log (x k) ^ (-C) :=
        mul_nonneg hxk0 (Real.rpow_nonneg (by linarith [hlogx k hk]) _)
      nlinarith [le_max_left K1 0]
    have h5 : K1' * x k * Real.log (x k) ^ (-C) ≤ K1' * x k * (2 ^ C * t) := by
      rw [← h3]; gcongr
    calc ((lowRepsW c δ (x k)).card : ℝ) ≤ K1 * x k * Real.log (x k) ^ (-C) := h1
      _ ≤ K1' * x k * (2 ^ C * t) := h4.trans h5
      _ = K1' * 2 ^ C * (x k * t) := by ring
  set Y := X * q ^ J
  have hsub : lowUpToW c X ⊆
      (range (⌊Y⌋₊ + 1)) ∪ (range J).biUnion (fun k => lowRepsW c δ (x k)) := by
    intro m hm
    simp only [lowUpToW, mem_filter, mem_range] at hm
    obtain ⟨hm1, hev, hm4, hlt⟩ := hm
    by_cases hmY : (m : ℝ) ≤ Y
    · apply mem_union_left; rw [mem_range]
      have := Nat.le_floor hmY; omega
    · push_neg at hmY
      have hmX : (m : ℝ) ≤ X := by
        have : m ≤ ⌊X⌋₊ := by omega
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hX0.le)
      obtain ⟨k, hk, hk1, hk2⟩ := coverW hq0 hq1 hX0 J hmY hmX
      apply mem_union_right
      rw [mem_biUnion]
      refine ⟨k, mem_range.mpr hk, ?_⟩
      simp only [lowRepsW, mem_filter, mem_range]
      have e3 : 2 * (1 + δ) * x k = X * q ^ k := by
        simp only [x]; rw [pow_succ]
        calc 2 * (1 + δ) * (X * (q ^ k * q) / 2) = X * q ^ k * (q * (1 + δ)) := by ring
          _ = X * q ^ k := by rw [hqδ, mul_one]
      have e2 : 2 * x k = X * q ^ (k + 1) := by simp only [x]; ring
      refine ⟨⟨?_, by rw [e2]; exact hk1⟩, hev, hlt⟩
      have : m ≤ ⌊2 * (1 + δ) * x k⌋₊ := Nat.le_floor (by rw [e3]; exact hk2)
      omega
  have hcard := card_le_card hsub
  have hY : ((range (⌊Y⌋₊ + 1)).card : ℝ) ≤ X * t + 1 := by
    rw [card_range]; push_cast
    have : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by positivity)
    have : Y ≤ X * t := by simp only [Y]; nlinarith
    linarith
  have hgeom : ∑ k ∈ range J, x k ≤ X * G := by
    have hg : ∑ k ∈ range J, q ^ k ≤ G := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hq0.le hq1
      rw [← range_eq_Ico, pow_zero] at this
      exact this
    have hxe : ∀ k, x k = X * q / 2 * q ^ k := fun k => by simp only [x]; rw [pow_succ]; ring
    simp only [hxe]
    rw [← mul_sum]
    have hc : 0 ≤ X * q / 2 := by positivity
    calc X * q / 2 * ∑ k ∈ range J, q ^ k ≤ X * q / 2 * G := mul_le_mul_of_nonneg_left hg hc
      _ = (q / 2) * (X * G) := by ring
      _ ≤ 1 * (X * G) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = X * G := one_mul _
  have hB : (((range J).biUnion (fun k => lowRepsW c δ (x k))).card : ℝ) ≤
      K1' * 2 ^ C * G * (X * t) := by
    have h1 := card_biUnion_le (s := range J) (t := fun k => lowRepsW c δ (x k))
    have h2 : (∑ k ∈ range J, ((lowRepsW c δ (x k)).card : ℝ)) ≤
        ∑ k ∈ range J, K1' * 2 ^ C * (x k * t) :=
      sum_le_sum fun k hk => hterm k (mem_range.mp hk)
    have h3 : ∑ k ∈ range J, K1' * 2 ^ C * (x k * t) =
        K1' * 2 ^ C * t * ∑ k ∈ range J, x k := by
      rw [mul_sum]; congr 1; ext k; ring
    have hK0 : 0 ≤ K1' * 2 ^ C * t :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)) ht0.le
    calc (((range J).biUnion (fun k => lowRepsW c δ (x k))).card : ℝ)
        ≤ ∑ k ∈ range J, ((lowRepsW c δ (x k)).card : ℝ) := by exact_mod_cast h1
      _ ≤ K1' * 2 ^ C * t * ∑ k ∈ range J, x k := h2.trans h3.le
      _ ≤ K1' * 2 ^ C * t * (X * G) := mul_le_mul_of_nonneg_left hgeom hK0
      _ = K1' * 2 ^ C * G * (X * t) := by ring
  have hone : 1 ≤ X * t := by
    have : Real.sqrt X ≤ X * t / 3 := hXt
    linarith
  have hU := card_union_le (range (⌊Y⌋₊ + 1))
    ((range J).biUnion (fun k => lowRepsW c δ (x k)))
  have hK2 : 0 ≤ K1' * 2 ^ C * G :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)) hG0.le
  calc ((lowUpToW c X).card : ℝ)
      ≤ ((range (⌊Y⌋₊ + 1)).card : ℝ) +
          (((range J).biUnion (fun k => lowRepsW c δ (x k))).card : ℝ) := by
        exact_mod_cast hcard.trans hU
    _ ≤ X * t + 1 + K1' * 2 ^ C * G * (X * t) := by linarith
    _ ≤ (2 + K1' * 2 ^ C * G) * X * t := by nlinarith
    _ ≤ max (2 + K1' * 2 ^ C * G) (2 * Real.log X0 ^ C) * X * t := by
        gcongr; exact le_max_left _ _

/-- **I-0062.** From Siegel-Walfisz alone: for every `c < 1` and every `C > 0`, all but
`O(X (log X)^{-C})` even `m ≤ X` have `r(m) ≥ c 𝔖(m) m / log² m`, `r(m)` counting ordered
pairs. Zero sorry. KNOWN mathematics. Binary Goldbach is OPEN. -/
theorem rightOrderAsymp_of_siegelWalfisz (hSW : SiegelWalfisz) {c : ℝ} (hc1 : c < 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((lowUpToW c X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  -- reduce to `c > 0` by monotonicity in `c`
  set c' : ℝ := max c (1 / 2)
  have hc'0 : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'1 : c' < 1 := max_lt hc1 (by norm_num)
  set δ : ℝ := (1 - c') / 2
  have hδ0 : 0 < δ := by simp only [δ]; linarith
  have hδ : δ ≤ 1 / 2 := by simp only [δ]; linarith [le_max_right c (1 / 2)]
  set η : ℝ := 1 - c' * (1 + δ)
  have hη : 0 < η := by
    simp only [η, δ]; nlinarith
  have hcη : c' * (1 + δ) = 1 - η := by simp only [η]; ring
  have hW : ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      ((lowRepsW c' δ x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
    intro C hC
    obtain ⟨K, hK⟩ := fewRepsEta_card_of_theorem1 (theorem1_of_siegelWalfisz hSW) hη C hC
    exact ⟨K, fun x hx =>
      (Nat.cast_le.mpr (card_le_card (lowRepsW_subset hc'0 hδ0 hδ hcη hx))).trans (hK x hx)⟩
  obtain ⟨K, hK⟩ := lowUpToW_card_of c' δ hδ0 hδ hW C hC
  refine ⟨K, fun X hX => le_trans ?_ (hK X hX)⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro m hm
  simp only [lowUpToW, mem_filter, mem_range] at hm ⊢
  obtain ⟨h1, hev, h4, hlt⟩ := hm
  refine ⟨h1, hev, h4, lt_of_lt_of_le hlt ?_⟩
  have hs : (0 : ℝ) ≤ singular m := le_trans (by norm_num) (singular_ge_13 hev)
  have hl : 0 ≤ Real.log m ^ 2 := sq_nonneg _
  have hcc : c ≤ c' := le_max_left _ _
  gcongr

/-- **I-0062, numeric form.** For every `c < 13/10`, all but `O(X (log X)^{-C})` even
`m ≤ X` have `r(m) ≥ c m / log² m`, from Siegel-Walfisz and `𝔖(m) ≥ 1.3`. -/
theorem rightOrderAsympNum_of_siegelWalfisz (hSW : SiegelWalfisz) {c : ℝ} (hc : c < 13 / 10)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((lowUpToc c X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  obtain ⟨K, hK⟩ := rightOrderAsymp_of_siegelWalfisz hSW
    (c := max c 0 * (10 / 13)) (by
      rcases le_total c 0 with h | h
      · rw [max_eq_right h]; norm_num
      · rw [max_eq_left h]; linarith) C hC
  refine ⟨K, fun X hX => le_trans ?_ (hK X hX)⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro m hm
  simp only [lowUpToc, lowUpToW, mem_filter, mem_range] at hm ⊢
  obtain ⟨h1, hev, h4, hlt⟩ := hm
  refine ⟨h1, hev, h4, lt_of_lt_of_le hlt ?_⟩
  have hs := singular_ge_13 hev
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log m ^ 2 := sq_nonneg _
  apply div_le_div_of_nonneg_right _ hl
  apply mul_le_mul_of_nonneg_right _ hm0
  have hc0 : c ≤ max c 0 := le_max_left _ _
  have hm00 : 0 ≤ max c 0 := le_max_right _ _
  nlinarith

end LeanLab.HeathBrown1985

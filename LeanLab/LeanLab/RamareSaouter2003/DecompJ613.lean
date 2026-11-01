import Mathlib
import LeanLab.RamareSaouter2003.Theorem4JSplit
import LeanLab.RamareSaouter2003.Lemma3Zeros

namespace LeanLab.RamareSaouter2003.DecompJ613

open Real LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4Parts
  LeanLab.RamareSaouter2003.Thm4Assembly LeanLab.RamareSaouter2003.Thm4JSplit
  LeanLab.RamareSaouter2003.L3Zeros

variable {ι : Type*} {γ β : ι → ℝ} {T0 : ℝ} {m : ℕ} {T x : ℝ}

/-- LEAF. p. 15. The terms `a i` and `b i` are bounded by `x * dT γ m T i`. -/
theorem lemma3_hab_le (hx1 : 1 ≤ x) (hx0 : 0 ≤ x) (hT : 1000 ≤ T) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (i : ι) :
    (if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0) ≤ x * dT γ m T i ∧
    (if T < |γ i| then x ^ (1 - β i) / |γ i| ^ (m + 1) else 0) ≤ x * dT γ m T i := by
  simp only [dT]
  split_ifs with h
  · have e1 : x ^ (β i) ≤ x := by
      calc x ^ (β i) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (hβ i).2
        _ = x := Real.rpow_one x
    have e2 : x ^ (1 - β i) ≤ x := by
      calc x ^ (1 - β i) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [(hβ i).1])
        _ = x := Real.rpow_one x
    have hg : 0 < |γ i| ^ (m + 1) := pow_pos (by linarith [hT, h]) _
    rw [mul_one_div]
    exact ⟨div_le_div_of_nonneg_right e1 hg.le, div_le_div_of_nonneg_right e2 hg.le⟩
  · have h0 : 0 ≤ x * 0 := mul_nonneg hx0 (le_refl 0)
    exact ⟨h0, h0⟩

/-- LEAF. p. 15. The sum of `x * dT` over a finite set is bounded by `L2` term. -/
theorem lemma3_hsumx (hx0 : 0 < x) (hN : Lemma1Count γ) (hm : 1 ≤ m) (hT : 1000 ≤ T) (s : Finset ι) :
    ∑ i ∈ s, x * dT γ m T i ≤ x * (L2 m T / T ^ m) := by
  have hL2T := lemma2_upper hN hm hT
  rw [← Finset.mul_sum, sum_dT]
  exact mul_le_mul_of_nonneg_left (hL2T s) hx0.le

/-- LEAF. p. 15. The terms `(a i + b i) / 2` are pointwise bounded using `T` and `T0` tails. -/
theorem lemma3_hpt (hx1 : 1 ≤ x) (hx10 : 10^5 ≤ x) (hT : 1000 ≤ T) (hTT0 : T ≤ T0) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (hRH : ∀ i, |γ i| ≤ T0 → β i = 1 / 2) (i : ι) :
    ((if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0) +
     (if T < |γ i| then x ^ (1 - β i) / |γ i| ^ (m + 1) else 0)) / 2 ≤
    √x * dT γ m T i + (1 + 1 / 10 ^ 5) * x / 2 * dT γ m T0 i := by
  set K : ℝ := 1 + 1 / 10 ^ 5
  simp only [dT]
  by_cases h : T < |γ i|
  · have hg : 0 < |γ i| ^ (m + 1) := pow_pos (by linarith) _
    simp only [if_pos h]
    by_cases h0 : T0 < |γ i|
    · rw [if_pos h0]
      have hs := rpow_add_rpow_le hx1 (hβ i).1 (hβ i).2
      have hK : 1 + x ≤ K * x := by simp only [K]; linarith
      have hsq : 0 ≤ √x := Real.sqrt_nonneg x
      have : (x ^ (β i) / |γ i| ^ (m + 1) + x ^ (1 - β i) / |γ i| ^ (m + 1)) / 2 ≤
          K * x / 2 * (1 / |γ i| ^ (m + 1)) := by
        rw [← add_div, div_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have : 0 ≤ √x * (1 / |γ i| ^ (m + 1)) := by positivity
      linarith
    · simp only [if_neg h0]
      have hb' := hRH i (le_of_not_gt h0)
      rw [hb']
      have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [e, ← Real.sqrt_eq_rpow]
      ring_nf; rfl
  · simp only [if_neg h]
    have : ¬ T0 < |γ i| := fun h' => h (lt_of_le_of_lt hTT0 h')
    rw [if_neg this]; simp

/-- LEAF. p. 15. `L2 m t <= sm m t` for `t >= 1000`. -/
theorem lemma3_Lsm {t : ℝ} (hm : 1 ≤ m) (ht : 1000 ≤ t) :
    L2 m t ≤ sm m t := by
  have hl := ℓ_pos ht
  have h0 : 0 ≤ L2 m t := by unfold L2; positivity
  have : sm m t = L2 m t * (1 + 1 / 10 ^ 5) := by unfold sm L2 ℓ; ring
  rw [this]
  nlinarith

/-- LEAF. p. 15. The finite sum of `(a + b) / 2` is bounded by `sm` terms. -/
theorem lemma3_hfin (hx1 : 1 ≤ x) (hx10: 10^5 ≤ x) (hN : Lemma1Count γ) (hm : 1 ≤ m) (hT : 1000 ≤ T) (hTT0 : T ≤ T0) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (hRH : ∀ i, |γ i| ≤ T0 → β i = 1 / 2) (s : Finset ι) :
    ∑ i ∈ s, (((if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0) +
               (if T < |γ i| then x ^ (1 - β i) / |γ i| ^ (m + 1) else 0)) / 2) ≤
    sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m) := by
  have hL2T := lemma2_upper hN hm hT
  have hT0 : 1000 ≤ T0 := by linarith
  have hL2T0 := lemma2_upper hN hm hT0
  have hpt := lemma3_hpt (m := m) (x := x) (T := T) (T0 := T0) (γ := γ) (β := β) hx1 hx10 hT hTT0 hβ hRH
  refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_dT, sum_dT]
  have h1 : √x * ∑ i ∈ s.filter (fun i => T < |γ i|), 1 / |γ i| ^ (m + 1) ≤
      sm m T * √x / T ^ m := by
    calc _ ≤ √x * (L2 m T / T ^ m) := mul_le_mul_of_nonneg_left (hL2T s) (Real.sqrt_nonneg x)
      _ ≤ √x * (sm m T / T ^ m) := by gcongr; exact lemma3_Lsm hm hT
      _ = _ := by ring
  have h2 : (1 + 1 / 10 ^ 5) * x / 2 * ∑ i ∈ s.filter (fun i => T0 < |γ i|), 1 / |γ i| ^ (m + 1) ≤
      sm m T0 * x / (2 * T0 ^ m) := by
    have hK0 : 0 ≤ (1 + 1 / 10 ^ 5) * x / 2 := by positivity
    have hsmL : sm m T0 = L2 m T0 * (1 + 1 / 10 ^ 5) := by unfold sm L2 ℓ; ring
    calc _ ≤ (1 + 1 / 10 ^ 5) * x / 2 * (L2 m T0 / T0 ^ m) := mul_le_mul_of_nonneg_left (hL2T0 s) hK0
      _ = _ := by rw [hsmL]; field_simp
  linarith

/-- **Lemma 3 of Ramaré-Saouter 2003, p. 15**, for a zero family. PROVED CONDITIONAL ON
`Lemma1Count γ`, RH to height `T0` for the family, `0 ≤ β ≤ 1` and the functional equation
symmetry `σ`. Assembled from leaves. -/
theorem lemma3_of_assembly (hN : Lemma1Count γ) (σ : ι → ι)
    (hσ : Function.Injective σ) (hσγ : ∀ i, |γ (σ i)| = |γ i|) (hσβ : ∀ i, β (σ i) = 1 - β i)
    (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1) (hRH : ∀ i, |γ i| ≤ T0 → β i = 1 / 2) :
    Lemma3Bound (ZsF γ β) T0 := by
  intro m T x hm hT hTT0 hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 1000 ≤ T0 := hT.trans hTT0
  set a : ι → ℝ := fun i => if T < |γ i| then x ^ (β i) / |γ i| ^ (m + 1) else 0 with ha
  set b : ι → ℝ := fun i => if T < |γ i| then x ^ (1 - β i) / |γ i| ^ (m + 1) else 0 with hb
  have ha0 : ∀ i, 0 ≤ a i := fun i => by simp only [ha]; split_ifs <;> positivity
  have hb0 : ∀ i, 0 ≤ b i := fun i => by simp only [hb]; split_ifs <;> positivity
  have hab_le : ∀ i, a i ≤ x * dT γ m T i ∧ b i ≤ x * dT γ m T i := lemma3_hab_le hx1 hx0.le hT hβ
  have hsumx : ∀ s : Finset ι, ∑ i ∈ s, x * dT γ m T i ≤ x * (L2 m T / T ^ m) := lemma3_hsumx hx0 hN hm hT
  have hsa : Summable a := summable_of_sum_le (fun i => ha0 i)
    fun s => (Finset.sum_le_sum fun i _ => (hab_le i).1).trans (hsumx s)
  have hsb : Summable b := summable_of_sum_le (fun i => hb0 i)
    fun s => (Finset.sum_le_sum fun i _ => (hab_le i).2).trans (hsumx s)
  have hab : a = b ∘ σ := by
    funext i
    simp only [ha, hb, Function.comp, hσγ, hσβ]
    congr 2; ring_nf
  have hhalf : ∑' i, a i ≤ ∑' i, (a i + b i) / 2 := by
    have hle : ∑' i, a i ≤ ∑' i, b i := by
      rw [hab]; exact tsum_comp_le_tsum_of_inj hsb hb0 hσ
    rw [tsum_div_const, hsa.tsum_add hsb]; linarith
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, (a i + b i) / 2 ≤ sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m) :=
    lemma3_hfin hx1 hx hN hm hT hTT0 hβ hRH
  have hRHS : 0 ≤ sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m) := by
    have hlT := lemma3_Lsm hm hT
    have hlT0 := lemma3_Lsm hm hT0
    have h1 : 0 ≤ L2 m T := by have := ℓ_pos hT; unfold L2; positivity
    have h2 : 0 ≤ L2 m T0 := by have := ℓ_pos hT0; unfold L2; positivity
    have : 0 ≤ sm m T := by linarith
    have : 0 ≤ sm m T0 := by linarith
    positivity
  refine ⟨tsum_nonneg ha0, ?_⟩
  exact hhalf.trans (tsum_le_of_sum_le' hRHS hfin)

end LeanLab.RamareSaouter2003.DecompJ613

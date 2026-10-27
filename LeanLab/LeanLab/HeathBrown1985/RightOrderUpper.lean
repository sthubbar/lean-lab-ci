/-
I-0062 upper half, run 20261017T1203Z-5538, unit U-0301. AI-written Lean code, Claude.
Checked only by the Lean kernel.

From Siegel-Walfisz alone: for every c > 1 and every C > 0, all but O(X (log X)^{-C}) even
m ≤ X satisfy r(m) ≤ c 𝔖(m) m / log² m. With RightOrderAsymp.lean this gives
r(m) ~ 𝔖(m) m / log² m for almost all even m, r counting ordered pairs.

Method: for m in the window (2x, 2(1 + δ)x] with δ = (log X)^{-3}, the ordered pairs split
into p ≤ x, m - p ≤ x and a middle range of length below δ m; pairs with p ≥ m^θ carry
weight at least θ² log² m in N₂(x, m), and pairs with p < m^θ are at most m^θ + 1. The
cover of [1, X] has ratio 1/(1 + δ), about (log X)^4 windows, absorbed by asking Theorem 1
for the exponent C + 3.

KNOWN mathematics, the circle method for almost all even m. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.RightOrderAsymp

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Real Filter

attribute [local instance] Classical.propDecidable

/-- The pairs with `p ≤ x`. -/
def pairsLe (x : ℝ) (m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x)

/-- `r(m) ≤ 2 #{p ≤ x} + (m - 2x) + 2` when `0 ≤ x` and `2x < m`. -/
theorem r_le_two_mul_add (x : ℝ) (m : ℕ) (hx : 0 ≤ x) (hm : 2 * x < (m : ℝ)) :
    (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤ 2 * ((pairsLe x m).card : ℝ) + ((m : ℝ) - 2 * x) + 2 := by
  unfold LeanLab.SchnirelmannGoldbach.r
  set S := pairsLe x m
  set R := (range m).filter (fun p => p.Prime ∧ (m - p).Prime)
  set M := Ioo ⌊x⌋₊ (m - ⌊x⌋₊)
  have hsub : R ⊆ S ∪ S.image (fun p => m - p) ∪ M := by
    intro p hp
    simp only [R, mem_filter, mem_range] at hp
    obtain ⟨hpm, hp1, hp2⟩ := hp
    by_cases h1 : (p : ℝ) ≤ x
    · apply mem_union_left; apply mem_union_left
      simp only [S, pairsLe, mem_filter, mem_range]
      exact ⟨by omega, hp1, hp2, h1⟩
    · by_cases h2 : ((m - p : ℕ) : ℝ) ≤ x
      · apply mem_union_left; apply mem_union_right
        rw [mem_image]
        refine ⟨m - p, ?_, by omega⟩
        simp only [S, pairsLe, mem_filter, mem_range]
        have : m - (m - p) = p := by omega
        rw [this]
        exact ⟨by omega, hp2, hp1, h2⟩
      · apply mem_union_right
        push_neg at h1 h2
        simp only [M, mem_Ioo]
        have a1 : ⌊x⌋₊ < p := (Nat.floor_lt hx).mpr h1
        have a2 : ⌊x⌋₊ < m - p := (Nat.floor_lt hx).mpr h2
        omega
  have hc := card_le_card hsub
  have hu1 := card_union_le (S ∪ S.image (fun p => m - p)) M
  have hu2 := card_union_le S (S.image (fun p => m - p))
  have hi : (S.image (fun p => m - p)).card ≤ S.card := card_image_le
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hfl2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h2f : 2 * ⌊x⌋₊ < m := by
    have : (2 * ⌊x⌋₊ : ℝ) < m := by linarith
    exact_mod_cast this
  have hM : M.card + 2 * ⌊x⌋₊ ≤ m := by
    simp only [M, Nat.card_Ioo]; omega
  have hM' : (M.card : ℝ) + 2 * (⌊x⌋₊ : ℝ) ≤ m := by exact_mod_cast hM
  have htot : R.card ≤ 2 * S.card + M.card := by omega
  have htot' : (R.card : ℝ) ≤ 2 * (S.card : ℝ) + (M.card : ℝ) := by exact_mod_cast htot
  linarith

/-- Pairs with `p ≥ m^θ` weigh at least `θ² log² m`, the rest number at most `m^θ + 1`. -/
theorem pairsLe_card_le (x θ : ℝ) (m : ℕ) (hθ0 : 0 < θ) (hm : 2 * x < (m : ℝ))
    (hm1 : 1 < (m : ℝ)) (h2 : 2 * (m : ℝ) ^ θ ≤ m) :
    θ ^ 2 * Real.log m ^ 2 * ((pairsLe x m).card : ℝ) ≤ N2 x m + θ ^ 2 * Real.log m ^ 2 * ((m : ℝ) ^ θ + 1) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hlm : 0 < Real.log m := Real.log_pos hm1
  set S := pairsLe x m
  set Sb := S.filter (fun p : ℕ => (m : ℝ) ^ θ ≤ (p : ℝ))
  set Ss := S.filter (fun p : ℕ => ¬ ((m : ℝ) ^ θ ≤ (p : ℝ)))
  have hsplit : S.card = Sb.card + Ss.card := by
    simp only [Sb, Ss]; exact (card_filter_add_card_filter_not _).symm
  have hmθ : 0 < (m : ℝ) ^ θ := Real.rpow_pos_of_pos hm0 θ
  have hlogθ : Real.log ((m : ℝ) ^ θ) = θ * Real.log m := Real.log_rpow hm0 θ
  have hSs : (Ss.card : ℝ) ≤ (m : ℝ) ^ θ + 1 := by
    have hsub : Ss ⊆ range (⌊(m : ℝ) ^ θ⌋₊ + 1) := by
      intro p hp
      simp only [Ss, mem_filter] at hp
      rw [mem_range]
      have := Nat.le_floor (le_of_lt (not_le.mp hp.2))
      omega
    have := card_le_card hsub
    rw [card_range] at this
    have h' : ((⌊(m : ℝ) ^ θ⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) ^ θ := Nat.floor_le hmθ.le
    calc (Ss.card : ℝ) ≤ ((⌊(m : ℝ) ^ θ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ (m : ℝ) ^ θ + 1 := by push_cast; linarith
  have hw : ∀ p ∈ Sb, θ ^ 2 * Real.log m ^ 2 ≤ Real.log p * Real.log (m - p : ℕ) := by
    intro p hp
    simp only [Sb, S, pairsLe, mem_filter, mem_range] at hp
    obtain ⟨⟨hp1, hp2, hp3, hp4⟩, hp5⟩ := hp
    have hpm : p ≤ m := by omega
    have hcast : ((m - p : ℕ) : ℝ) = (m : ℝ) - p := by
      rw [Nat.cast_sub hpm]
    have hmp : (m : ℝ) ^ θ ≤ ((m - p : ℕ) : ℝ) := by
      rw [hcast]; linarith
    have l1 : θ * Real.log m ≤ Real.log p := by
      rw [← hlogθ]; exact Real.log_le_log hmθ hp5
    have l2 : θ * Real.log m ≤ Real.log ((m - p : ℕ) : ℝ) := by
      rw [← hlogθ]; exact Real.log_le_log hmθ hmp
    have l0 : 0 ≤ θ * Real.log m := by positivity
    calc θ ^ 2 * Real.log m ^ 2 = (θ * Real.log m) * (θ * Real.log m) := by ring
      _ ≤ Real.log p * Real.log ((m - p : ℕ) : ℝ) := mul_le_mul l1 l2 l0 (l0.trans l1)
  have hnn : ∀ p ∈ S, 0 ≤ Real.log p * Real.log (m - p : ℕ) := by
    intro p hp
    simp only [S, pairsLe, mem_filter, mem_range] at hp
    obtain ⟨-, hp2, hp3, -⟩ := hp
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp2.one_lt.le))
      (Real.log_nonneg (by exact_mod_cast hp3.one_lt.le))
  have hN : (Sb.card : ℝ) * (θ ^ 2 * Real.log m ^ 2) ≤ N2 x m := by
    calc (Sb.card : ℝ) * (θ ^ 2 * Real.log m ^ 2) = ∑ _p ∈ Sb, θ ^ 2 * Real.log m ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Sb, Real.log p * Real.log (m - p : ℕ) := sum_le_sum hw
      _ ≤ ∑ p ∈ S, Real.log p * Real.log (m - p : ℕ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ => hnn p hp)
      _ = N2 x m := rfl
  have hsplit' : (S.card : ℝ) = Sb.card + Ss.card := by exact_mod_cast hsplit
  have hk : 0 ≤ θ ^ 2 * Real.log m ^ 2 := by positivity
  rw [hsplit']
  nlinarith

/-- Even `m ∈ (2x, 3x]` with `N₂(x, m) > (1 + η) x 𝔖(m)`. -/
def manyRepsEta (η x : ℝ) : Finset ℕ :=
  ((range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧ (1 + η) * (x * singular m) < N2 x m)

theorem manyRepsEta_card_of_theorem1 (h1 : Theorem1) {η : ℝ} (hη : 0 < η) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((manyRepsEta η x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K1, hK1⟩ := h1 C hC
  refine ⟨K1 / η, fun x hx => ?_⟩
  set T := (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))
  have hx0 : 0 < x := by linarith
  have hterm : ∀ m ∈ manyRepsEta η x, η * x ≤ |N2 x m - x * singular m| := by
    intro m hm
    obtain ⟨-, hev, hlt⟩ := mem_filter.mp hm
    have hs : (1 : ℝ) ≤ singular m := le_trans (by norm_num) (singular_ge_13 hev)
    have hxs : η * x ≤ η * (x * singular m) := by
      have := mul_le_mul_of_nonneg_left hs hx0.le
      nlinarith
    have : η * x ≤ N2 x m - x * singular m := by nlinarith
    exact this.trans (le_abs_self _)
  have hsub : manyRepsEta η x ⊆ T := filter_subset _ _
  have hA : ((manyRepsEta η x).card : ℝ) * (η * x) ≤ ∑ m ∈ T, |N2 x m - x * singular m| := by
    calc ((manyRepsEta η x).card : ℝ) * (η * x) = ∑ m ∈ manyRepsEta η x, η * x := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ manyRepsEta η x, |N2 x m - x * singular m| := sum_le_sum hterm
      _ ≤ ∑ m ∈ T, |N2 x m - x * singular m| :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hB := hA.trans (hK1 x hx)
  have hpos : 0 < η * x := by positivity
  rw [← le_div_iff₀ hpos] at hB
  calc ((manyRepsEta η x).card : ℝ) ≤ K1 * x ^ 2 * Real.log x ^ (-C) / (η * x) := hB
    _ = K1 / η * x * Real.log x ^ (-C) := by field_simp

set_option maxHeartbeats 1000000 in
/-- The pointwise step: a high `m` in the window `(2x, 2(1 + δ)x]`, `δ = (log X)^{-3}`, has
many weighted pairs, once `X` is large in the explicit sense of the hypotheses. -/
theorem upper_impl {θ η μ c x X : ℝ} {m : ℕ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : 0 ≤ η)
    (hc : c = (1 + η) / θ ^ 2 + μ) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (hx : 0 ≤ x)
    (hL1 : 1 ≤ Real.log X) (hLμ : 2 / μ ≤ Real.log X)
    (hcond : 12 * Real.log X ^ 2 ≤ μ * Real.sqrt X ^ (1 - θ))
    (hm1 : 2 * x < (m : ℝ)) (hm2 : (m : ℝ) ≤ 2 * (1 + (Real.log X ^ 3)⁻¹) * x)
    (hmX : (m : ℝ) ≤ X) (hmsq : Real.sqrt X ≤ m) (hev : Even m)
    (hhigh : c * singular m * m / Real.log m ^ 2 < (LeanLab.SchnirelmannGoldbach.r m : ℝ)) :
    (1 + η) * (x * singular m) < N2 x m := by
  by_contra hcon
  push_neg at hcon
  set L := Real.log X
  have hL0 : 0 < L := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  -- m^{1-θ} ≥ 6
  have hpowX : 12 / μ ≤ Real.sqrt X ^ (1 - θ) := by
    rw [div_le_iff₀ hμ0]; nlinarith
  have hpowm : Real.sqrt X ^ (1 - θ) ≤ (m : ℝ) ^ (1 - θ) :=
    Real.rpow_le_rpow hsq0 hmsq (by linarith)
  have h6 : 6 ≤ (m : ℝ) ^ (1 - θ) := by
    have : 6 ≤ 12 / μ := by rw [le_div_iff₀ hμ0]; linarith
    linarith
  have hm1' : 1 < (m : ℝ) := by
    by_contra h
    push_neg at h
    have : (m : ℝ) ^ (1 - θ) ≤ 1 := Real.rpow_le_one hm0.le h (by linarith)
    linarith
  have hsplitm : (m : ℝ) ^ θ * (m : ℝ) ^ (1 - θ) = m := by
    rw [← Real.rpow_add hm0]; simp
  have hmθ1 : 1 ≤ (m : ℝ) ^ θ := Real.one_le_rpow hm1'.le hθ0.le
  have h2θ : 2 * (m : ℝ) ^ θ ≤ m := by nlinarith
  have hlm : 0 < Real.log m := Real.log_pos hm1'
  have hlmL : Real.log m ≤ L := Real.log_le_log hm0 hmX
  have hs : (1 : ℝ) ≤ singular m := le_trans (by norm_num) (singular_ge_13 hev)
  -- the pair bounds
  have hr := r_le_two_mul_add x m hx hm1
  have hA := pairsLe_card_le x θ m hθ0 hm1 hm1' h2θ
  set A := ((pairsLe x m).card : ℝ)
  set r := (LeanLab.SchnirelmannGoldbach.r m : ℝ)
  set lm := Real.log m
  have hθl : 0 < θ ^ 2 * lm ^ 2 := by positivity
  -- A ≤ N2 / (θ² lm²) + m^θ + 1
  have hA' : A ≤ N2 x m / (θ ^ 2 * lm ^ 2) + ((m : ℝ) ^ θ + 1) := by
    rw [div_add' _ _ _ hθl.ne', le_div_iff₀ hθl]; linarith
  have hN2 : N2 x m / (θ ^ 2 * lm ^ 2) ≤ (1 + η) * (x * singular m) / (θ ^ 2 * lm ^ 2) :=
    div_le_div_of_nonneg_right hcon hθl.le
  have hxm : 2 * ((1 + η) * (x * singular m)) ≤ (1 + η) * singular m * m := by
    have : 0 ≤ (1 + η) * singular m := by positivity
    nlinarith
  -- middle range
  have hδ : (m : ℝ) - 2 * x ≤ m / L ^ 3 := by
    have hL3 : 0 < L ^ 3 := by positivity
    have : (m : ℝ) - 2 * x ≤ 2 * x * (L ^ 3)⁻¹ := by nlinarith
    have h2 : 2 * x * (L ^ 3)⁻¹ ≤ m * (L ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_right hm1.le (inv_nonneg.mpr hL3.le)
    rw [div_eq_mul_inv]; linarith
  -- the total
  have hmain : r ≤ (1 + η) * singular m * m / (θ ^ 2 * lm ^ 2) + 2 * (m : ℝ) ^ θ + m / L ^ 3 + 4 := by
    have e : 2 * ((1 + η) * (x * singular m) / (θ ^ 2 * lm ^ 2)) ≤
        (1 + η) * singular m * m / (θ ^ 2 * lm ^ 2) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hxm hθl.le
    linarith
  -- error terms
  set D := (m : ℝ) / L ^ 2
  have hD0 : 0 < D := by positivity
  have hE1 : (m : ℝ) / L ^ 3 ≤ μ / 2 * D := by
    have : (m : ℝ) / L ^ 3 = D * L⁻¹ := by simp only [D]; field_simp
    rw [this]
    have hLi : L⁻¹ ≤ μ / 2 := by
      rw [inv_le_comm₀ hL0 (by positivity)]
      calc (μ / 2)⁻¹ = 2 / μ := by field_simp
        _ ≤ L := hLμ
    nlinarith
  have hE2 : 6 * (m : ℝ) ^ θ ≤ μ / 2 * D := by
    have h12 : 12 * L ^ 2 ≤ μ * (m : ℝ) ^ (1 - θ) :=
      hcond.trans (mul_le_mul_of_nonneg_left hpowm hμ0.le)
    have e : (m : ℝ) ^ θ * (μ * (m : ℝ) ^ (1 - θ)) = μ * m := by
      calc (m : ℝ) ^ θ * (μ * (m : ℝ) ^ (1 - θ)) = μ * ((m : ℝ) ^ θ * (m : ℝ) ^ (1 - θ)) := by ring
        _ = μ * m := by rw [hsplitm]
    have h3 := mul_le_mul_of_nonneg_left h12 (by linarith : (0 : ℝ) ≤ (m : ℝ) ^ θ)
    rw [e] at h3
    have hD : μ / 2 * D = (μ / 2 * m) / L ^ 2 := by simp only [D]; ring
    rw [hD, le_div_iff₀ (by positivity)]
    linarith
  have hDsing : μ * D ≤ μ * singular m * m / lm ^ 2 := by
    have hlm2 : lm ^ 2 ≤ L ^ 2 := by
      have := hlm.le; nlinarith
    have h1 : (m : ℝ) / L ^ 2 ≤ m / lm ^ 2 :=
      div_le_div_of_nonneg_left hm0.le (by positivity) hlm2
    have h2 : (m : ℝ) / lm ^ 2 ≤ singular m * m / lm ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    calc μ * D ≤ μ * ((m : ℝ) / lm ^ 2) := mul_le_mul_of_nonneg_left h1 hμ0.le
      _ ≤ μ * (singular m * m / lm ^ 2) := mul_le_mul_of_nonneg_left h2 hμ0.le
      _ = μ * singular m * m / lm ^ 2 := by ring
  have hsplitc : c * singular m * m / lm ^ 2 =
      (1 + η) * singular m * m / (θ ^ 2 * lm ^ 2) + μ * singular m * m / lm ^ 2 := by
    rw [hc]; field_simp
  have : r ≤ c * singular m * m / lm ^ 2 := by
    rw [hsplitc]; linarith
  linarith

/-- Even `m ≤ X`, `m ≥ 4`, with `r(m) > c 𝔖(m) m / log² m`. -/
def highUpToW (c X : ℝ) : Finset ℕ :=
  (range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
      c * singular m * m / Real.log m ^ 2 < (LeanLab.SchnirelmannGoldbach.r m : ℝ))

set_option maxHeartbeats 2000000 in
/-- The cover with windows `(2x, 2(1 + δ)x]`, `δ = (log X)^{-3}`. -/
theorem highUpToW_card_of {θ η μ c : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : 0 < η)
    (hc : c = (1 + η) / θ ^ 2 + μ) (hμ0 : 0 < μ) (hμ2 : μ ≤ 2)
    (hN : ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      ((manyRepsEta η x).card : ℝ) ≤ K * x * Real.log x ^ (-C)) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((highUpToW c X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  obtain ⟨K1, hK1⟩ := hN (C + 3) (by linarith)
  set K1' := max K1 0
  have e1 := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 3)
  have e2 := (isLittleO_log_rpow_rpow_atTop 2 (by linarith : (0 : ℝ) < (1 - θ) / 2)).bound
    (by positivity : (0 : ℝ) < μ / 12)
  have e3 := Real.tendsto_log_atTop.eventually_ge_atTop (max (2 / μ) 2)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp (e1.and (e2.and e3))
  set X0 := max (max X1 16) 3
  set C3 : ℝ := C + 3
  refine ⟨max (2 + K1' * 2 ^ C3) (2 * Real.log X0 ^ C), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hLC : 0 < Real.log X ^ C := Real.rpow_pos_of_pos hL0 C
  have hLmC : Real.log X ^ (-C) = (Real.log X ^ C)⁻¹ := Real.rpow_neg hL0.le C
  have htriv : ((highUpToW c X).card : ℝ) ≤ X + 1 := by
    have : (highUpToW c X).card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (by simp)
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
    calc ((highUpToW c X).card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ X + 1 := by push_cast; linarith
  by_cases hsmall : X ≤ X0
  · have hlX : Real.log X ≤ Real.log X0 := Real.log_le_log hX0 hsmall
    have hpow : Real.log X ^ C ≤ Real.log X0 ^ C :=
      Real.rpow_le_rpow hL0.le hlX hC.le
    have hone : 1 ≤ Real.log X0 ^ C * Real.log X ^ (-C) := by
      rw [hLmC, ← div_eq_mul_inv, le_div_iff₀ hLC]; linarith
    calc ((highUpToW c X).card : ℝ) ≤ X + 1 := htriv
      _ ≤ 2 * X := by linarith
      _ ≤ 2 * X * (Real.log X0 ^ C * Real.log X ^ (-C)) := by nlinarith
      _ = (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by ring
      _ ≤ max (2 + K1' * 2 ^ C3) (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by
          gcongr; exact le_max_right _ _
  push_neg at hsmall
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall.le
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall.le
  obtain ⟨hb, hb2, hb3⟩ := hX1 X hXX1
  set L := Real.log X
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLC,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hb
  have hsq : X ^ (1 / 2 : ℝ) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  rw [hsq] at hb
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hb3
  have hLμ : 2 / μ ≤ L := le_trans (le_max_left _ _) hb3
  have hL1 : 1 ≤ L := by linarith
  -- the condition 12 L² ≤ μ √X^{1-θ}
  have hcond : 12 * L ^ 2 ≤ μ * Real.sqrt X ^ (1 - θ) := by
    have hL2' : 0 < L ^ (2 : ℝ) := Real.rpow_pos_of_pos hL0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL2',
      abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hb2
    have r1 : L ^ (2 : ℝ) = L ^ 2 := by exact_mod_cast Real.rpow_natCast L 2
    have r2 : X ^ ((1 - θ) / 2) = Real.sqrt X ^ (1 - θ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]; congr 1; ring
    rw [r1, r2] at hb2
    linarith
  have ht1 : L ^ (-C) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have ht0 : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL0 _
  set δ : ℝ := (L ^ 3)⁻¹
  have hL3 : 8 ≤ L ^ 3 := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 2 := by
    simp only [δ]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set q : ℝ := 1 / (1 + δ)
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hq23 : 2 / 3 ≤ q := by rw [le_div_iff₀ (by linarith)]; linarith
  have hqδ : q * (1 + δ) = 1 := by
    simp only [q]; rw [one_div, inv_mul_cancel₀ (by linarith)]
  obtain ⟨J, hJ1, hJ2⟩ := exists_pow_between' hq0 hq1 ht0 ht1
  set t := L ^ (-C)
  have hsqX : 4 ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX0.le]; linarith
  have hsqpos : 0 < Real.sqrt X := by linarith
  have hsq2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hXt : Real.sqrt X ≤ X * t / 3 := by
    have : t = (L ^ C)⁻¹ := hLmC
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
  have hlogx : ∀ k < J, L / 2 ≤ Real.log (x k) := by
    intro k hk
    have h1 := Real.log_le_log hsqpos (hxk k hk)
    rwa [Real.log_sqrt hX0.le] at h1
  set t3 := L ^ (-C3)
  have ht3 : t3 * L ^ 3 = t := by
    simp only [t3, t, C3]
    rw [show -(C + 3) = -C + -3 by ring, Real.rpow_add hL0, Real.rpow_neg hL0.le (3 : ℝ)]
    have : L ^ (3 : ℝ) = L ^ 3 := by exact_mod_cast Real.rpow_natCast L 3
    rw [this]; field_simp
  have hterm : ∀ k < J, ((manyRepsEta η (x k)).card : ℝ) ≤ K1' * 2 ^ C3 * (x k * t3) := by
    intro k hk
    have h1 := hK1 (x k) (hx2 k hk)
    have hpos : 0 < L / 2 := by linarith
    have h2 : Real.log (x k) ^ (-C3) ≤ (L / 2) ^ (-C3) :=
      Real.rpow_le_rpow_of_nonpos hpos (hlogx k hk) (by simp only [C3]; linarith)
    have h3 : (L / 2) ^ (-C3) = 2 ^ C3 * t3 := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
      ring
    have hxk0 : 0 ≤ x k := by linarith [hx2 k hk]
    have h4 : K1 * x k * Real.log (x k) ^ (-C3) ≤ K1' * x k * Real.log (x k) ^ (-C3) := by
      have : 0 ≤ x k * Real.log (x k) ^ (-C3) :=
        mul_nonneg hxk0 (Real.rpow_nonneg (by linarith [hlogx k hk]) _)
      nlinarith [le_max_left K1 0]
    have h5 : K1' * x k * Real.log (x k) ^ (-C3) ≤ K1' * x k * (2 ^ C3 * t3) := by
      rw [← h3]; gcongr
    calc ((manyRepsEta η (x k)).card : ℝ) ≤ K1 * x k * Real.log (x k) ^ (-C3) := h1
      _ ≤ K1' * x k * (2 ^ C3 * t3) := h4.trans h5
      _ = K1' * 2 ^ C3 * (x k * t3) := by ring
  set Y := X * q ^ J
  have hsub : highUpToW c X ⊆
      (range (⌊Y⌋₊ + 1)) ∪ (range J).biUnion (fun k => manyRepsEta η (x k)) := by
    intro m hm
    simp only [highUpToW, mem_filter, mem_range] at hm
    obtain ⟨hm1, hev, hm4, hhigh⟩ := hm
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
      have e3 : 2 * (1 + δ) * x k = X * q ^ k := by
        simp only [x]; rw [pow_succ]
        calc 2 * (1 + δ) * (X * (q ^ k * q) / 2) = X * q ^ k * (q * (1 + δ)) := by ring
          _ = X * q ^ k := by rw [hqδ, mul_one]
      have e2 : 2 * x k = X * q ^ (k + 1) := by simp only [x]; ring
      have hxk0 : 0 ≤ x k := by linarith [hx2 k hk]
      have hw1 : 2 * x k < (m : ℝ) := by rw [e2]; exact hk1
      have hw2 : (m : ℝ) ≤ 2 * (1 + δ) * x k := by rw [e3]; exact hk2
      have hmsq : Real.sqrt X ≤ m := by linarith [hxk k hk]
      have himp := upper_impl hθ0 hθ1 hη.le hc hμ0 hμ2 hxk0 hL1 hLμ hcond hw1 hw2 hmX hmsq hev
        hhigh
      simp only [manyRepsEta, mem_filter, mem_range]
      have hm3 : (m : ℝ) ≤ 3 * x k := by nlinarith
      have : m ≤ ⌊3 * x k⌋₊ := Nat.le_floor hm3
      exact ⟨⟨by omega, hw1⟩, hev, himp⟩
  have hcard := card_le_card hsub
  have hY : ((range (⌊Y⌋₊ + 1)).card : ℝ) ≤ X * t + 1 := by
    rw [card_range]; push_cast
    have : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by positivity)
    have : Y ≤ X * t := by simp only [Y]; nlinarith
    linarith
  have h1q : 1 - q = q * δ := by linarith [hqδ]
  have hgeom : ∑ k ∈ range J, x k ≤ X * L ^ 3 / 2 := by
    have hg : ∑ k ∈ range J, q ^ k ≤ 1 / (1 - q) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hq0.le hq1
      rw [← range_eq_Ico, pow_zero] at this
      exact this
    have hxe : ∀ k, x k = X * q / 2 * q ^ k := fun k => by simp only [x]; rw [pow_succ]; ring
    simp only [hxe]
    rw [← mul_sum]
    have hc0 : 0 ≤ X * q / 2 := by positivity
    calc X * q / 2 * ∑ k ∈ range J, q ^ k ≤ X * q / 2 * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left hg hc0
      _ = X * L ^ 3 / 2 := by
          rw [h1q]; simp only [δ]; field_simp
  have hB : (((range J).biUnion (fun k => manyRepsEta η (x k))).card : ℝ) ≤
      K1' * 2 ^ C3 / 2 * (X * t) := by
    have h1 := card_biUnion_le (s := range J) (t := fun k => manyRepsEta η (x k))
    have h2 : (∑ k ∈ range J, ((manyRepsEta η (x k)).card : ℝ)) ≤
        ∑ k ∈ range J, K1' * 2 ^ C3 * (x k * t3) :=
      sum_le_sum fun k hk => hterm k (mem_range.mp hk)
    have h3 : ∑ k ∈ range J, K1' * 2 ^ C3 * (x k * t3) =
        K1' * 2 ^ C3 * t3 * ∑ k ∈ range J, x k := by
      rw [mul_sum]; congr 1; ext k; ring
    have ht30 : 0 < t3 := Real.rpow_pos_of_pos hL0 _
    have hK0 : 0 ≤ K1' * 2 ^ C3 * t3 :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)) ht30.le
    calc (((range J).biUnion (fun k => manyRepsEta η (x k))).card : ℝ)
        ≤ ∑ k ∈ range J, ((manyRepsEta η (x k)).card : ℝ) := by exact_mod_cast h1
      _ ≤ K1' * 2 ^ C3 * t3 * ∑ k ∈ range J, x k := h2.trans h3.le
      _ ≤ K1' * 2 ^ C3 * t3 * (X * L ^ 3 / 2) := mul_le_mul_of_nonneg_left hgeom hK0
      _ = K1' * 2 ^ C3 / 2 * (X * (t3 * L ^ 3)) := by ring
      _ = K1' * 2 ^ C3 / 2 * (X * t) := by rw [ht3]
  have hone : 1 ≤ X * t := by
    have : Real.sqrt X ≤ X * t / 3 := hXt
    linarith
  have hU := card_union_le (range (⌊Y⌋₊ + 1))
    ((range J).biUnion (fun k => manyRepsEta η (x k)))
  have hK2 : 0 ≤ K1' * 2 ^ C3 :=
    mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)
  calc ((highUpToW c X).card : ℝ)
      ≤ ((range (⌊Y⌋₊ + 1)).card : ℝ) +
          (((range J).biUnion (fun k => manyRepsEta η (x k))).card : ℝ) := by
        exact_mod_cast hcard.trans hU
    _ ≤ X * t + 1 + K1' * 2 ^ C3 / 2 * (X * t) := by linarith
    _ ≤ (2 + K1' * 2 ^ C3) * X * t := by nlinarith
    _ ≤ max (2 + K1' * 2 ^ C3) (2 * Real.log X0 ^ C) * X * t := by
        gcongr; exact le_max_left _ _

/-- **I-0062, upper half.** From Siegel-Walfisz alone: for every `c > 1` and every `C > 0`,
all but `O(X (log X)^{-C})` even `m ≤ X` have `r(m) ≤ c 𝔖(m) m / log² m`, `r(m)` counting
ordered pairs. KNOWN mathematics. Binary Goldbach is OPEN. -/
theorem rightOrderUpper_of_siegelWalfisz (hSW : SiegelWalfisz) {c : ℝ} (hc1 : 1 < c)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((highUpToW c X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  set c' : ℝ := min c 2
  have hc'1 : 1 < c' := lt_min hc1 (by norm_num)
  have hc'2 : c' ≤ 2 := min_le_right _ _
  have hc'0 : 0 < c' := by linarith
  set s : ℝ := (c' - 1) / (4 * c')
  have hs0 : 0 < s := by positivity
  have hcs : c' * s = (c' - 1) / 4 := by simp only [s]; field_simp
  have hs1 : s < 1 / 4 := by
    simp only [s]; rw [div_lt_iff₀ (by positivity)]; linarith
  set θ : ℝ := 1 - s
  set η : ℝ := (c' - 1) / 4
  set μ : ℝ := c' - (1 + η) / θ ^ 2
  have hθ0 : 0 < θ := by simp only [θ]; linarith
  have hθ1 : θ < 1 := by simp only [θ]; linarith
  have hη : 0 < η := by simp only [η]; linarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hkey : 1 + η < c' * θ ^ 2 := by
    have : c' * θ ^ 2 = c' - 2 * (c' * s) + (c' * s) * s := by simp only [θ]; ring
    rw [this, hcs]
    simp only [η]
    have : 0 ≤ (c' - 1) / 4 * s := by positivity
    linarith
  have hμ0 : 0 < μ := by
    simp only [μ]
    have : (1 + η) / θ ^ 2 < c' := by rw [div_lt_iff₀ hθ2]; linarith
    linarith
  have hμ2 : μ ≤ 2 := by
    simp only [μ]
    have : 0 ≤ (1 + η) / θ ^ 2 := by positivity
    linarith
  have hcμ : c' = (1 + η) / θ ^ 2 + μ := by simp only [μ]; ring
  obtain ⟨K, hK⟩ := highUpToW_card_of hθ0 hθ1 hη hcμ hμ0 hμ2
    (fun C hC => manyRepsEta_card_of_theorem1 (theorem1_of_siegelWalfisz hSW) hη C hC) C hC
  refine ⟨K, fun X hX => le_trans ?_ (hK X hX)⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro m hm
  simp only [highUpToW, mem_filter, mem_range] at hm ⊢
  obtain ⟨h1, hev, h4, hlt⟩ := hm
  refine ⟨h1, hev, h4, lt_of_le_of_lt ?_ hlt⟩
  have hs : (0 : ℝ) ≤ singular m := le_trans (by norm_num) (singular_ge_13 hev)
  have hl : 0 ≤ Real.log m ^ 2 := sq_nonneg _
  have hcc : c' ≤ c := min_le_left _ _
  gcongr

/-- **I-0062, both halves.** From Siegel-Walfisz alone: for every `ε > 0` and `C > 0`, all
but `O(X (log X)^{-C})` even `4 ≤ m ≤ X` satisfy
`(1 - ε) 𝔖(m) m / log² m ≤ r(m) ≤ (1 + ε) 𝔖(m) m / log² m`. KNOWN mathematics.
Binary Goldbach is OPEN. -/
theorem rightOrderAsymptotic_of_siegelWalfisz (hSW : SiegelWalfisz) {ε : ℝ} (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X →
      (((range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
        ¬ ((1 - ε) * singular m * m / Real.log m ^ 2 ≤ (LeanLab.SchnirelmannGoldbach.r m : ℝ) ∧
           (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤ (1 + ε) * singular m * m / Real.log m ^ 2))).card : ℝ)
        ≤ K * X * Real.log X ^ (-C) := by
  obtain ⟨K1, hK1⟩ := rightOrderAsymp_of_siegelWalfisz hSW (c := 1 - ε) (by linarith) C hC
  obtain ⟨K2, hK2⟩ := rightOrderUpper_of_siegelWalfisz hSW (c := 1 + ε) (by linarith) C hC
  refine ⟨K1 + K2, fun X hX => ?_⟩
  have hsub : ((range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
        ¬ ((1 - ε) * singular m * m / Real.log m ^ 2 ≤ (LeanLab.SchnirelmannGoldbach.r m : ℝ) ∧
           (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤ (1 + ε) * singular m * m / Real.log m ^ 2)))
      ⊆ lowUpToW (1 - ε) X ∪ highUpToW (1 + ε) X := by
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨h1, hev, h4, hn⟩ := hm
    rw [not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · apply mem_union_left
      simp only [lowUpToW, mem_filter, mem_range]; exact ⟨h1, hev, h4, h⟩
    · apply mem_union_right
      simp only [highUpToW, mem_filter, mem_range]; exact ⟨h1, hev, h4, h⟩
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at h'
  refine le_trans h' ?_
  have := add_le_add (hK1 X hX) (hK2 X hX)
  linarith

end LeanLab.HeathBrown1985

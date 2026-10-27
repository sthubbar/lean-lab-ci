/-
P0087 Akeno 2026 Lemma 2.3 pages 4 to 5.
The block argument for M at least q/4.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.DiophantineSmall

namespace LeanLab.Akeno2026.DiophantineCount
open Finset

def blockIndex (q : ℕ) (m : ℤ) : ℤ := (m - 1) / (q : ℤ)
noncomputable def blockRange (M : ℝ) (q : ℕ) : Finset ℤ :=
  Finset.Icc ⌈M / (q : ℝ) - 1⌉ ⌊2 * M / (q : ℝ)⌋
noncomputable def blockPairs (α M δ : ℝ) (q : ℕ) (s : ℤ) : Finset (Σ _m : ℤ, ℤ) :=
  (rationalPairs α M δ).filter (fun p => blockIndex q p.1 = s)
noncomputable def blockCenter (α : ℝ) (a : ℤ) (q : ℕ) (s : ℤ) : ℝ :=
  (q : ℝ) ^ 2 * ((a : ℝ) / q - α) * s

/-- This is the paper's decomposition m = q s + r with 1 at most r at most q. -/
theorem block_remainder_bounds {q : ℕ} (hq : 1 ≤ q) (m : ℤ) :
    1 ≤ m - (q : ℤ) * blockIndex q m ∧ m - (q : ℤ) * blockIndex q m ≤ q := by
  have hqI : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have h0 := Int.emod_nonneg (m - 1) (ne_of_gt hqI)
  have h1 := Int.emod_lt_of_pos (m - 1) hqI
  have he := Int.mul_ediv_add_emod (m - 1) (q : ℤ)
  dsimp [blockIndex]
  constructor <;> nlinarith

theorem block_mem_range {M : ℝ} {q : ℕ} {m : ℤ}
    (hq : 1 ≤ q) (hm : m ∈ denominatorRange M) : blockIndex q m ∈ blockRange M q := by
  obtain ⟨hm0, hm1⟩ := mem_denominatorRange.mp hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr := block_remainder_bounds hq m
  have hrR : (1 : ℝ) ≤ (m : ℝ) - (q : ℝ) * (blockIndex q m : ℝ) ∧
      (m : ℝ) - (q : ℝ) * (blockIndex q m : ℝ) ≤ q := by exact_mod_cast hr
  have hlo : M / (q : ℝ) - 1 ≤ (blockIndex q m : ℝ) := by
    have h := (div_le_iff₀ hqR).mpr
      (show M ≤ ((blockIndex q m : ℝ) + 1) * q by nlinarith [hrR.2])
    linarith
  have hhi : (blockIndex q m : ℝ) ≤ 2 * M / (q : ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    nlinarith [hrR.1]
  simp only [blockRange, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  exact ⟨hlo, hhi⟩

theorem blockRange_card_le {M : ℝ} {q : ℕ} (hM : 0 < M) (hq : 1 ≤ q)
    (hMq : (q : ℝ) / 4 ≤ M) :
    ((blockRange M q).card : ℝ) ≤ 9 * M / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hx : 0 ≤ M / (q : ℝ) := by positivity
  have he : 2 * M / (q : ℝ) = 2 * (M / (q : ℝ)) := by ring
  have hab : M / (q : ℝ) - 1 ≤ 2 * M / (q : ℝ) := by rw [he]; linarith
  have h := card_integer_interval_le hab
  have hquarter : (1 / 4 : ℝ) ≤ M / (q : ℝ) :=
    (le_div_iff₀ hqR).mpr (by nlinarith)
  calc
    ((blockRange M q).card : ℝ) ≤ 2 * M / (q : ℝ) - (M / (q : ℝ) - 1) + 1 := h
    _ = M / (q : ℝ) + 2 := by ring
    _ ≤ 9 * (M / (q : ℝ)) := by linarith
    _ = 9 * M / (q : ℝ) := by ring

/-- Inside a block, the determinant lies in a translated interval of bounded length. -/
theorem determinant_block_bound {α M δ : ℝ} {a : ℤ} {q : ℕ}
    (hM : 0 < M) (hδ : 0 < δ) (hq : 1 ≤ q)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    {p : Σ _m : ℤ, ℤ} (hp : p ∈ rationalPairs α M δ) :
    |((a * p.1 - (q : ℤ) * p.2 : ℤ) : ℝ) - blockCenter α a q (blockIndex q p.1)| ≤
      2 * (q : ℝ) * δ * M + 1 := by
  obtain ⟨hm0, hm1, hn⟩ := mem_rationalPairs hM |>.mp hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : 0 < (p.1 : ℝ) := hM.trans hm0
  let e : ℝ := (a : ℝ) / q - α
  let r : ℝ := (p.1 : ℝ) - (q : ℝ) * (blockIndex q p.1 : ℝ)
  have hrI := block_remainder_bounds hq p.1
  have hr : (1 : ℝ) ≤ r ∧ r ≤ q := by dsimp [r]; exact_mod_cast hrI
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have heB : |e| ≤ 1 / (q : ℝ) ^ 2 := by
    dsimp [e]
    rwa [abs_sub_comm]
  have hnb := numerator_bounds hmR hn
  have hnB : |α * (p.1 : ℝ) - (p.2 : ℝ)| ≤ δ * p.1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hnb.1, hnb.2]
  have hprod : (q : ℝ) * |e| * r ≤ 1 := by
    calc
      (q : ℝ) * |e| * r ≤ (q : ℝ) * (1 / (q : ℝ) ^ 2) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heB hqR.le) hr0
      _ ≤ (q : ℝ) * (1 / (q : ℝ) ^ 2) * q :=
        mul_le_mul_of_nonneg_left hr.2 (by positivity)
      _ = 1 := by field_simp [ne_of_gt hqR]
  have heq : ((a * p.1 - (q : ℤ) * p.2 : ℤ) : ℝ) - blockCenter α a q (blockIndex q p.1) =
      (q : ℝ) * e * r + (q : ℝ) * (α * p.1 - p.2) := by
    dsimp [blockCenter, e, r]
    push_cast
    field_simp [ne_of_gt hqR]
    ring
  have hnq := mul_le_mul_of_nonneg_left hnB hqR.le
  have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ (q : ℝ) * δ by positivity)
  rw [heq]
  calc
    |(q : ℝ) * e * r + (q : ℝ) * (α * p.1 - p.2)| ≤
        |(q : ℝ) * e * r| + |(q : ℝ) * (α * p.1 - p.2)| := abs_add_le _ _
    _ = (q : ℝ) * |e| * r + (q : ℝ) * |α * p.1 - p.2| := by
      simp only [abs_mul, abs_of_pos hqR, abs_of_nonneg hr0]
    _ ≤ 2 * (q : ℝ) * δ * M + 1 := by nlinarith

/-- There are at most 4 q delta M plus 3 pairs in one denominator block. -/
theorem blockPairs_card_le {α M δ : ℝ} {a : ℤ} {q : ℕ}
    (hM : 0 < M) (hδ : 0 < δ) (hq : 1 ≤ q) (hc : Int.gcd a q = 1)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (s : ℤ) :
    ((blockPairs α M δ q s).card : ℝ) ≤ 4 * (q : ℝ) * δ * M + 3 := by
  have hqI : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  let S := blockPairs α M δ q s
  let c := blockCenter α a q s
  let B : ℝ := 2 * (q : ℝ) * δ * M + 1
  let T : Finset ℤ := Finset.Icc ⌈c - B⌉ ⌊c + B⌋
  let f : (Σ _m : ℤ, ℤ) → ℤ := fun p => a * p.1 - (q : ℤ) * p.2
  have hmem : ∀ p ∈ S, f p ∈ T := by
    intro p hp
    obtain ⟨hpair, hblock⟩ := Finset.mem_filter.mp hp
    have h := determinant_block_bound hM hδ hq ha hpair
    rw [hblock] at h
    have h' := abs_le.mp h
    simp only [T, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
    dsimp [c, B, f]
    constructor <;> linarith [h'.1, h'.2]
  have hinj : Set.InjOn f (↑S : Set (Σ _m : ℤ, ℤ)) := by
    intro p hp p' hp' heq
    have hs := (Finset.mem_filter.mp hp).2
    have hs' := (Finset.mem_filter.mp hp').2
    have hr := block_remainder_bounds hq p.1
    have hr' := block_remainder_bounds hq p'.1
    rw [hs] at hr
    rw [hs'] at hr'
    have hw : |p.1 - p'.1| < (q : ℤ) := by
      apply abs_lt.mpr
      constructor <;> nlinarith [hr.1, hr.2, hr'.1, hr'.2]
    have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hc
    obtain ⟨hm, hn⟩ := determinant_injective hqI hcop hw heq
    cases p
    cases p'
    simp only at hm hn
    subst_vars
    rfl
  have hcard := Finset.card_le_card_of_injOn f hmem hinj
  have hcardR : (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT := card_integer_interval_le (show c - B ≤ c + B by linarith)
  calc
    ((blockPairs α M δ q s).card : ℝ) ≤ (T.card : ℝ) := hcardR
    _ ≤ (c + B) - (c - B) + 1 := hT
    _ = 4 * (q : ℝ) * δ * M + 3 := by dsimp [B]; ring

/-- The complete M at least q/4 regime of the page 5 block argument. -/
theorem pairCount_large_M {α M δ : ℝ} {a : ℤ} {q : ℕ}
    (hM : 0 < M) (hδ : 0 < δ) (hq : 1 ≤ q) (hc : Int.gcd a q = 1)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (hMq : (q : ℝ) / 4 ≤ M) :
    (pairCount α M δ : ℝ) ≤ 36 * δ * M ^ 2 + 27 * M / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let S := rationalPairs α M δ
  let R := blockRange M q
  have hcover : Set.MapsTo (fun p : Σ _m : ℤ, ℤ => blockIndex q p.1) (↑S : Set _) (↑R : Set ℤ) := by
    intro p hp
    have hm := (Finset.mem_sigma.mp hp).1
    exact block_mem_range hq hm
  have hcard := Finset.card_eq_sum_card_fiberwise hcover
  have heq : pairCount α M δ = ∑ s ∈ R, (blockPairs α M δ q s).card := by
    rw [← rationalPairs_card]
    exact hcard
  have hsum : (pairCount α M δ : ℝ) ≤ (R.card : ℝ) * (4 * (q : ℝ) * δ * M + 3) := by
    rw [heq]
    push_cast
    calc
      ∑ s ∈ R, ((blockPairs α M δ q s).card : ℝ) ≤
          ∑ _s ∈ R, (4 * (q : ℝ) * δ * M + 3) :=
        Finset.sum_le_sum (fun s _ => blockPairs_card_le hM hδ hq hc ha s)
      _ = (R.card : ℝ) * (4 * (q : ℝ) * δ * M + 3) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hR := blockRange_card_le hM hq hMq
  have hmul := mul_le_mul_of_nonneg_right hR
    (show 0 ≤ 4 * (q : ℝ) * δ * M + 3 by positivity)
  calc
    (pairCount α M δ : ℝ) ≤ (R.card : ℝ) * (4 * (q : ℝ) * δ * M + 3) := hsum
    _ ≤ (9 * M / (q : ℝ)) * (4 * (q : ℝ) * δ * M + 3) := hmul
    _ = 36 * δ * M ^ 2 + 27 * M / (q : ℝ) := by
      field_simp [ne_of_gt hqR]
      ring

/-- Lemma 2.3 with a uniform absolute constant 64. -/
theorem lemma23_bound : Lemma23Bound := by
  refine ⟨64, by norm_num, ?_⟩
  intro α a q hq hc ha M δ hM hδ
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h1 : 0 ≤ M / (q : ℝ) := by positivity
  have h2 : 0 ≤ (q : ℝ) * δ * M := by positivity
  have h3 : 0 ≤ δ * M ^ 2 := by positivity
  have he : (64 : ℝ) * M * (1 / (q : ℝ) + q * δ + δ * M) =
      64 * (M / (q : ℝ) + (q : ℝ) * δ * M + δ * M ^ 2) := by ring
  rw [he]
  by_cases hMq : M ≤ (q : ℝ) / 4
  · have h := pairCount_small_M hM hδ hq hc ha hMq
    linarith
  · have h := pairCount_large_M hM hδ hq hc ha (by linarith)
    rw [mul_div_assoc] at h
    linarith

end LeanLab.Akeno2026.DiophantineCount

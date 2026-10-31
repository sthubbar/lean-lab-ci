/-
P0087 Akeno 2026 Lemma 2.3 pages 4 to 5.
The small denominator range M at most q/4.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.DiophantineCount

namespace LeanLab.Akeno2026.DiophantineCount
open Finset

noncomputable def rationalPairs (α M δ : ℝ) : Finset (Σ _m : ℤ, ℤ) :=
  (denominatorRange M).sigma (numeratorRange α δ)

theorem rationalPairs_card (α M δ : ℝ) : (rationalPairs α M δ).card = pairCount α M δ := by
  simp [rationalPairs, pairCount]

theorem mem_rationalPairs {α M δ : ℝ} (hM : 0 < M) {p : Σ _m : ℤ, ℤ} :
    p ∈ rationalPairs α M δ ↔
      M < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * M ∧ |α - (p.2 : ℝ) / p.1| ≤ δ := by
  simp only [rationalPairs, Finset.mem_sigma]
  constructor
  · intro hp
    obtain ⟨h0, h1⟩ := mem_denominatorRange.mp hp.1
    exact ⟨h0, h1, (mem_numeratorRange (hM.trans h0)).mp hp.2⟩
  · rintro ⟨h0, h1, hn⟩
    exact ⟨mem_denominatorRange.mpr ⟨h0, h1⟩, (mem_numeratorRange (hM.trans h0)).mpr hn⟩

/-- Equal determinants and a denominator difference below q force equal pairs. -/
theorem determinant_injective {a q m₁ m₂ n₁ n₂ : ℤ} (hq : 0 < q)
    (hc : IsCoprime a q) (hw : |m₁ - m₂| < q)
    (he : a * m₁ - q * n₁ = a * m₂ - q * n₂) : m₁ = m₂ ∧ n₁ = n₂ := by
  have hd : q ∣ a * (m₁ - m₂) := by
    refine ⟨n₁ - n₂, ?_⟩
    nlinarith
  have hm : q ∣ m₁ - m₂ := hc.symm.dvd_of_dvd_mul_left hd
  have habs : (m₁ - m₂).natAbs < q.natAbs := by
    have hh : ((m₁ - m₂).natAbs : ℤ) < (q.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hq]
      exact hw
    exact_mod_cast hh
  have hzero : m₁ - m₂ = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hm habs
  have hmeq : m₁ = m₂ := sub_eq_zero.mp hzero
  refine ⟨hmeq, ?_⟩
  subst m₁
  have hn : q * n₁ = q * n₂ := by nlinarith
  exact mul_left_cancel₀ (ne_of_gt hq) hn

/-- The determinant bound from the two approximation inequalities. -/
theorem determinant_bound {α δ : ℝ} {a m n : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hm : 0 < (m : ℝ))
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (hn : |α - (n : ℝ) / m| ≤ δ) :
    |((a * m - (q : ℤ) * n : ℤ) : ℝ)| ≤ (q : ℝ) * δ * m + (m : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hd : |(a : ℝ) / q - (n : ℝ) / m| ≤ 1 / (q : ℝ) ^ 2 + δ := by
    calc
      |(a : ℝ) / q - (n : ℝ) / m| ≤ |(a : ℝ) / q - α| + |α - (n : ℝ) / m| := abs_sub_le _ _ _
      _ ≤ 1 / (q : ℝ) ^ 2 + δ := add_le_add (by simpa only [abs_sub_comm] using ha) hn
  have he : (a : ℝ) * m - (q : ℝ) * n =
      (q : ℝ) * m * ((a : ℝ) / q - (n : ℝ) / m) := by
    field_simp [ne_of_gt hq0, ne_of_gt hm]
  push_cast
  rw [he, abs_mul, abs_of_pos (mul_pos hq0 hm)]
  calc
    (q : ℝ) * m * |(a : ℝ) / q - (n : ℝ) / m| ≤
        (q : ℝ) * m * (1 / (q : ℝ) ^ 2 + δ) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (q : ℝ) * δ * m + (m : ℝ) / q := by
      field_simp [ne_of_gt hq0]
      ring

/-- In the small denominator range, every counted pair forces q delta M at least 1/4. -/
theorem quarter_le_of_pair {α M δ : ℝ} {a : ℤ} {q : ℕ}
    (hM : 0 < M) (hδ : 0 < δ) (hq : 1 ≤ q) (hc : Int.gcd a q = 1)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (hMq : M ≤ (q : ℝ) / 4)
    {p : Σ _m : ℤ, ℤ} (hp : p ∈ rationalPairs α M δ) : 1 / 4 ≤ (q : ℝ) * δ * M := by
  obtain ⟨hm0, hm1, hn⟩ := mem_rationalPairs hM |>.mp hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqI : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : 0 < (p.1 : ℝ) := hM.trans hm0
  have hmI : (0 : ℤ) < p.1 := by exact_mod_cast hmR
  have hmLt : (p.1 : ℝ) < q := by linarith
  have hmLtI : p.1 < (q : ℤ) := by exact_mod_cast hmLt
  have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have hne : a * p.1 - (q : ℤ) * p.2 ≠ 0 := by
    intro he
    have h := determinant_injective hqI hcop
      (show |p.1 - 0| < (q : ℤ) by simpa [abs_of_pos hmI] using hmLtI)
      (show a * p.1 - (q : ℤ) * p.2 = a * 0 - (q : ℤ) * 0 by simpa using he)
    omega
  have hgapI : (1 : ℤ) ≤ |a * p.1 - (q : ℤ) * p.2| := by
    have h := abs_pos.mpr hne
    omega
  have hgap : (1 : ℝ) ≤ |((a * p.1 - (q : ℤ) * p.2 : ℤ) : ℝ)| := by exact_mod_cast hgapI
  have hb := determinant_bound hq hmR ha hn
  have hd : (p.1 : ℝ) / q ≤ 1 / 2 := (div_le_iff₀ hqR).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ (q : ℝ) * δ by positivity)
  nlinarith

/-- The complete M at most q/4 regime of Lemma 2.3, with an explicit bound. -/
theorem pairCount_small_M {α M δ : ℝ} {a : ℤ} {q : ℕ}
    (hM : 0 < M) (hδ : 0 < δ) (hq : 1 ≤ q) (hc : Int.gcd a q = 1)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (hMq : M ≤ (q : ℝ) / 4) :
    (pairCount α M δ : ℝ) ≤ 12 * (q : ℝ) * δ * M := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqI : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  let S := rationalPairs α M δ
  let B : ℝ := 2 * (q : ℝ) * δ * M + 1 / 2
  let T : Finset ℤ := Finset.Icc ⌈-B⌉ ⌊B⌋
  let f : (Σ _m : ℤ, ℤ) → ℤ := fun p => a * p.1 - (q : ℤ) * p.2
  by_cases he : S = ∅
  · have hz : pairCount α M δ = 0 := by rw [← rationalPairs_card]; exact congrArg Finset.card he
    rw [hz, Nat.cast_zero]
    positivity
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hquarter := quarter_le_of_pair hM hδ hq hc ha hMq hp₀
    have hmem : ∀ p ∈ S, f p ∈ T := by
      intro p hp
      obtain ⟨hm0, hm1, hn⟩ := mem_rationalPairs hM |>.mp hp
      have hmR := hM.trans hm0
      have hb := determinant_bound hq hmR ha hn
      have hd : (p.1 : ℝ) / q ≤ 1 / 2 := (div_le_iff₀ hqR).mpr (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ (q : ℝ) * δ by positivity)
      have hab : |((f p : ℤ) : ℝ)| ≤ B := by dsimp [f, B]; nlinarith
      rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      exact abs_le.mp hab
    have hinj : Set.InjOn f (↑S : Set (Σ _m : ℤ, ℤ)) := by
      intro p hp p' hp' heq
      obtain ⟨hm0, hm1, _⟩ := mem_rationalPairs hM |>.mp hp
      obtain ⟨hm0', hm1', _⟩ := mem_rationalPairs hM |>.mp hp'
      have hwR : |(p.1 : ℝ) - (p'.1 : ℝ)| < (q : ℝ) := by
        apply abs_lt.mpr
        constructor <;> linarith
      have hwI : |p.1 - p'.1| < (q : ℤ) := by exact_mod_cast hwR
      have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hc
      obtain ⟨hm, hn⟩ := determinant_injective hqI hcop hwI heq
      cases p
      cases p'
      simp only at hm hn
      subst_vars
      rfl
    have hcard := Finset.card_le_card_of_injOn f hmem hinj
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hT := card_integer_interval_le (show -B ≤ B by linarith)
    have hS : ((S.card : ℕ) : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
    rw [rationalPairs_card] at hS
    change ((pairCount α M δ : ℕ) : ℝ) ≤ (T.card : ℝ) at hS
    dsimp [T, B] at hT
    nlinarith

end LeanLab.Akeno2026.DiophantineCount

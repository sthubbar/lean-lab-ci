/-
P0076 J. Teräväinen, arXiv 1611.08585, Remark 3.6, page 12 to 13: the ternary versions of
Lemmas 3.4 and 3.5, which the paper describes in words only, and the local step for Theorem 1.2:
every odd `m` is `m ≡ B₁ + B₂ + B₃ (mod W)` with all three `W n + Bᵢ` amenable, with no further
local condition, matching "all large enough odd n" in Theorem 1.2.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6756.
Checked only by the Lean kernel. Binary Goldbach is OPEN; ternary Goldbach is a theorem,
Helfgott 2013. Theorem 1.2 itself stays cited.
-/
import Mathlib
import LeanLab.Teravainen2016.Amenable

open Finset

namespace LeanLab.Teravainen2016

/-- Ternary Lemma 3.4, Remark 3.6: for `J ≥ 5` every integer `n` is `a + b + c` with
`a ≡ 2^i (mod 2^(i+2))`, `b ≡ 2^j (mod 2^(j+2))`, `c ≡ 2^k (mod 2^(k+2))`, `i, j, k ≤ J - 3`. -/
theorem lemma_3_4_ternary (J : ℕ) (hJ : 5 ≤ J) (n : ℤ) : ∃ a b c : ℤ, n = a + b + c ∧
    ∃ i j k : ℕ, i ≤ J - 3 ∧ j ≤ J - 3 ∧ k ≤ J - 3 ∧ a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)] ∧
      b ≡ 2 ^ j [ZMOD 2 ^ (j + 2)] ∧ c ≡ 2 ^ k [ZMOD 2 ^ (k + 2)] := by
  have hpow : (2 : ℤ) ^ (J - 1) = 4 * 2 ^ (J - 3) := by
    rw [show J - 1 = (J - 3) + 2 by omega, pow_add]; ring
  by_cases h1 : (2 : ℤ) ^ (J - 1) ∣ n - 1
  · -- then `2^(J-1) ∤ n - 2`, take `c = 2`
    have h2 : ¬ (2 : ℤ) ^ (J - 1) ∣ n - 2 := by
      intro h2
      have := dvd_sub h1 h2
      rw [show n - 1 - (n - 2) = 1 by ring, hpow] at this
      have := (dvd_mul_right (4 : ℤ) _).trans this
      omega
    obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := lemma_3_4_proved J hJ (n - 2) h2
    exact ⟨a, b, 2, by linear_combination hab, i, j, 1, hi, hj, by omega, ha, hb,
      by simp only [Int.ModEq]; norm_num⟩
  · obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := lemma_3_4_proved J hJ (n - 1) h1
    exact ⟨a, b, 1, by linear_combination hab, i, j, 0, hi, hj, by omega, ha, hb,
      by simp only [Int.ModEq]; norm_num⟩

/-! ### Remark 3.6: the ternary versions of Lemmas 3.4 and 3.5 and the ternary local step -/

/-- Ternary Lemma 3.5, Remark 3.6: every `m'` is `≡ x₁² + ⋯ + x₆² (mod 27)` with each of the three
pair sums `≢ 1 (mod 3)` and `≢ 0 (mod 27)`; no restriction on `m'`. PROVED by a witness for each
residue mod 27. -/
theorem lemma_3_5_ternary (m : ℤ) : ∃ x₁ x₂ x₃ x₄ x₅ x₆ : ℤ,
    m ≡ (x₁ ^ 2 + x₂ ^ 2) + (x₃ ^ 2 + x₄ ^ 2) + (x₅ ^ 2 + x₆ ^ 2) [ZMOD 27] ∧
    ¬ x₁ ^ 2 + x₂ ^ 2 ≡ 1 [ZMOD 3] ∧ ¬ x₃ ^ 2 + x₄ ^ 2 ≡ 1 [ZMOD 3] ∧
    ¬ x₅ ^ 2 + x₆ ^ 2 ≡ 1 [ZMOD 3] ∧
    ¬ x₁ ^ 2 + x₂ ^ 2 ≡ 0 [ZMOD 27] ∧ ¬ x₃ ^ 2 + x₄ ^ 2 ≡ 0 [ZMOD 27] ∧
    ¬ x₅ ^ 2 + x₆ ^ 2 ≡ 0 [ZMOD 27] := by
  have h : m % 27 = 0 ∨ m % 27 = 1 ∨ m % 27 = 2 ∨ m % 27 = 3 ∨ m % 27 = 4 ∨ m % 27 = 5 ∨ m % 27 = 6 ∨ m % 27 = 7 ∨ m % 27 = 8 ∨ m % 27 = 9 ∨ m % 27 = 10 ∨ m % 27 = 11 ∨ m % 27 = 12 ∨ m % 27 = 13 ∨ m % 27 = 14 ∨ m % 27 = 15 ∨ m % 27 = 16 ∨ m % 27 = 17 ∨ m % 27 = 18 ∨ m % 27 = 19 ∨ m % 27 = 20 ∨ m % 27 = 21 ∨ m % 27 = 22 ∨ m % 27 = 23 ∨ m % 27 = 24 ∨ m % 27 = 25 ∨ m % 27 = 26 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨1, 1, 1, 1, 1, 7, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 13, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 0, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 5, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 0, 3, 1, 10, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 2, 0, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 1, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 0, 3, 1, 7, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 13, 0, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 2, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 0, 3, 1, 5, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 3, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 13, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 2, 3, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 8, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 2, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 13, 3, 3, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 11, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 13, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 0, 3, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 4, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 2, 0, 3, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, 1, 10, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 2, 3, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 13, 0, 3, 0, 3, by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩

/-- Chinese remainder theorem for the three coprime parts of `W`. -/
theorem crt_W (J : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q) (x y z : ℤ) :
    ∃ B : ℤ, B ≡ x [ZMOD 2 ^ J] ∧ B ≡ y [ZMOD 27] ∧ B ≡ z [ZMOD ∏ p ∈ S, (p : ℤ)] := by
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  have hc : IsCoprime ((2 : ℤ) ^ J) 27 := IsCoprime.pow_left ⟨-13, 1, by norm_num⟩
  obtain ⟨B₀, hB0a, hB0b⟩ := crt2 hc x y
  have hc' : IsCoprime ((2 : ℤ) ^ J * 27) (∏ p ∈ S, (p : ℤ)) := by
    apply isCoprime_of_primes
    intro p hp h1 h2'
    have hpS := prime_dvd_prod hSp hp h2'
    have : (p : ℤ) ∣ Wmod J ∅ := by unfold Wmod; simpa using h1
    rcases prime_dvd_Wmod (by simp) hp this with rfl | rfl | h
    · have := (hS 2 hpS).2; omega
    · have := (hS 3 hpS).2; omega
    · simp at h
  obtain ⟨B, hBa, hBb⟩ := crt2 hc' B₀ z
  exact ⟨B, (hBa.of_dvd (dvd_mul_right _ _)).trans hB0a,
    (hBa.of_dvd (dvd_mul_left _ _)).trans hB0b, hBb⟩

/-- Amenability of `W n + (B mod W)` from the congruences used in the proof of Theorem 1.1:
`B ≡ 2a + 1 (mod 2^J)` with `a ≡ 2^i (mod 2^(i+2))`, `i ≤ J - 3`; `B ≡ 2c + 1 (mod 27)` with
`c = x² + y²`, `c ≢ 1 (mod 3)`, `c ≢ 0 (mod 27)`; `p ∤ B (B - 1)` for `p ∈ S`. -/
theorem amenable_emod {J : ℕ} (hJ : 5 ≤ J) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q)
    {B a c : ℤ} {i : ℕ} (hi : i ≤ J - 3) (ha : a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)])
    (hBJ : B ≡ 2 * a + 1 [ZMOD 2 ^ J]) (hB27 : B ≡ 2 * c + 1 [ZMOD 27])
    (hc1 : ¬ c ≡ 1 [ZMOD 3]) (hc0 : ¬ c ≡ 0 [ZMOD 27]) (h9 : (3 : ℤ) ∣ c → (9 : ℤ) ∣ c)
    (hp : ∀ p ∈ S, ¬ (p : ℤ) ∣ B ∧ ¬ (p : ℤ) ∣ B - 1) : Amenable (Wmod J S) (B % Wmod J S) := by
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  have hW1 : ∀ d : ℤ, d ∣ Wmod J S → B % Wmod J S ≡ B [ZMOD d] := fun d hd =>
    (Int.mod_modEq B _).of_dvd hd
  have e1 : B % Wmod J S ≡ 2 * a + 1 [ZMOD 2 ^ (i + 1 + 2)] :=
    (hW1 _ (two_pow_dvd_Wmod S (by omega))).trans (hBJ.of_dvd (pow_dvd_pow 2 (by omega)))
  have e2 : B % Wmod J S - 1 ≡ 2 ^ (i + 1) [ZMOD 2 ^ (i + 1 + 2)] := by
    have := e1.sub_right 1
    rw [show 2 * a + 1 - 1 = 2 * a by ring] at this
    exact this.trans (double_modEq ha)
  have e3 : B % Wmod J S ≡ 2 * c + 1 [ZMOD 27] := (hW1 _ (dvd27_Wmod J S)).trans hB27
  obtain ⟨f1, f2, f3⟩ := three_facts e3 hc1 hc0 h9
  refine amenable_of_local (by omega) hSp (j := i + 1) (by omega) (by omega) e2 f1 f2 f3 ?_
  intro p hp'
  have ep : B % Wmod J S ≡ B [ZMOD p] := hW1 _ (dvd_Wmod_of_mem hp')
  exact ⟨fun h => (hp p hp').1 (dvd_of_modEq ep h),
    fun h => (hp p hp').2 (dvd_of_modEq (ep.sub_right 1) h)⟩

/-- **Local step for Theorem 1.2, Remark 3.6, PROVED.** Let `J ≥ 5` and `S` a finite set of primes
`≥ 5`, `W = 2^J · 3^3 · ∏_{p ∈ S} p`. Every odd `m` is `m ≡ B₁ + B₂ + B₃ (mod W)` with
`0 ≤ Bᵢ < W` and all three `W n + Bᵢ` amenable. No condition mod 9 or mod `2^J` is needed. -/
theorem local_split_ternary (J : ℕ) (hJ : 5 ≤ J) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q)
    (m : ℤ) (ho : ¬ (2 : ℤ) ∣ m) :
    ∃ B₁ B₂ B₃ : ℤ, 0 ≤ B₁ ∧ B₁ < Wmod J S ∧ 0 ≤ B₂ ∧ B₂ < Wmod J S ∧ 0 ≤ B₃ ∧ B₃ < Wmod J S ∧
      m ≡ B₁ + B₂ + B₃ [ZMOD Wmod J S] ∧ Amenable (Wmod J S) B₁ ∧ Amenable (Wmod J S) B₂ ∧
      Amenable (Wmod J S) B₃ := by
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => (hS q hq).1
  obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' + 3 := ⟨(m - 3) / 2, by omega⟩
  obtain ⟨a₁, a₂, a₃, ha, i, j, k, hi, hj, hk, hai, haj, hak⟩ := lemma_3_4_ternary J hJ m'
  obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆, hm27, hc1, hc2, hc3, hz1, hz2, hz3⟩ := lemma_3_5_ternary m'
  have h91 := nine_dvd_of_three_dvd_sum_sq x₁ x₂
  have h92 := nine_dvd_of_three_dvd_sum_sq x₃ x₄
  have h93 := nine_dvd_of_three_dvd_sum_sq x₅ x₆
  generalize x₁ ^ 2 + x₂ ^ 2 = c₁ at *
  generalize x₃ ^ 2 + x₄ ^ 2 = c₂ at *
  generalize x₅ ^ 2 + x₆ ^ 2 = c₃ at *
  obtain ⟨b₁, hb₁⟩ := exists_avoid S hS 0
  obtain ⟨b₂, hb₂⟩ := exists_avoid S hS (2 * m' + 3 - b₁)
  obtain ⟨B, hBJ, hB27, hBP⟩ := crt_W J hS (2 * a₁ + 1) (2 * c₁ + 1) b₁
  obtain ⟨B', hB'J, hB'27, hB'P⟩ := crt_W J hS (2 * a₂ + 1) (2 * c₂ + 1) b₂
  set W := Wmod J S with hW
  have hWpos : 0 < W := Wmod_pos hSp
  set B'' := 2 * m' + 3 - B - B'
  have hB''J : B'' ≡ 2 * a₃ + 1 [ZMOD 2 ^ J] := by
    have := ((Int.ModEq.refl (2 * m' + 3)).sub hBJ).sub hB'J
    rwa [show 2 * m' + 3 - (2 * a₁ + 1) - (2 * a₂ + 1) = 2 * a₃ + 1 by rw [ha]; ring] at this
  have hB''27 : B'' ≡ 2 * c₃ + 1 [ZMOD 27] := by
    simp only [B'']
    unfold Int.ModEq at hB27 hB'27 hm27 ⊢
    omega
  refine ⟨B % W, B' % W, B'' % W, Int.emod_nonneg _ hWpos.ne', Int.emod_lt_of_pos _ hWpos,
    Int.emod_nonneg _ hWpos.ne', Int.emod_lt_of_pos _ hWpos,
    Int.emod_nonneg _ hWpos.ne', Int.emod_lt_of_pos _ hWpos, ?_, ?_, ?_, ?_⟩
  · have := ((Int.mod_modEq B W).add (Int.mod_modEq B' W)).add (Int.mod_modEq B'' W)
    rw [show B + B' + B'' = 2 * m' + 3 by simp only [B'']; ring] at this
    exact this.symm
  · refine amenable_emod hJ hS hi hai hBJ hB27 hc1 hz1 h91 fun p hp => ?_
    have ep : B ≡ b₁ [ZMOD p] := hBP.of_dvd (dvd_prod_of_mem _ hp)
    exact ⟨fun h => (hb₁ p hp).1 (dvd_of_modEq ep h),
      fun h => (hb₁ p hp).2.1 (dvd_of_modEq (ep.sub_right 1) h)⟩
  · refine amenable_emod hJ hS hj haj hB'J hB'27 hc2 hz2 h92 fun p hp => ?_
    have ep : B' ≡ b₂ [ZMOD p] := hB'P.of_dvd (dvd_prod_of_mem _ hp)
    exact ⟨fun h => (hb₂ p hp).1 (dvd_of_modEq ep h),
      fun h => (hb₂ p hp).2.1 (dvd_of_modEq (ep.sub_right 1) h)⟩
  · refine amenable_emod hJ hS hk hak hB''J hB''27 hc3 hz3 h93 fun p hp => ?_
    have ep : B'' ≡ 2 * m' + 3 - b₁ - b₂ [ZMOD p] :=
      ((Int.ModEq.refl _).sub (hBP.of_dvd (dvd_prod_of_mem _ hp))).sub
        (hB'P.of_dvd (dvd_prod_of_mem _ hp))
    exact ⟨fun h => (hb₂ p hp).2.2.1 (dvd_of_modEq ep h),
      fun h => (hb₂ p hp).2.2.2 (dvd_of_modEq (ep.sub_right 1) h)⟩

end LeanLab.Teravainen2016

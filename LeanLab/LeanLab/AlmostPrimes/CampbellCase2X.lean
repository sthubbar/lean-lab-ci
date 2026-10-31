/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2113Z-cloud51, unit U-6748.
P0020 P. J. Campbell 2026, arXiv 2608.09488 v1, Case 2 of Theorem 1.2, continued from
CampbellCase2.lean.

PROVED, no cited input:
* `X_ge`: `N - 1 ≤ 3 X`, where `X = Xcount N` counts `1 ≤ n ≤ N - 1` with `3 ∤ aₙ`; this is
  the paper's `X ≥ (N - 1)/3`, MATCH, equality for `N ≡ 1 mod 3`.
* `case2Sieve_of`: `Case2Sieve` from `Case2SieveX`, the same display with `X` in place of
  `(N - 1)/3`, so the cited sieve input is Theorem 2.1 with Lemma 4.1(1) and bound (4.4) only.
* `S2_pos_of`: a certificate criterion for `S(u, v; 14.8, 0.2) > 0` with `p^{0.2} ≥ 1`,
  `v^{2.96} ≤ v^3`, `u^{16.5} ≥ u^{16}` and `F > 0.042`.
* `table_upto83`: the `Case2Table` statement for every `N > N₀` with `z = N^{1/16.5} ≤ 83`,
  by 11 interval certificates `(38, 41], (41, 43], …, (79, 83]`, all at `δ = 0.2`.
  FINITE CHECK GATE: these are rows of the paper's own Case 2 partition, which the paper does not
  print; they close the cited `Case2Table` on `N₀ < N ≤ 83^{16.5}` only. 11 certificates, not
  11 theorems.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellCase2

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellCase2X
open LeanLab.AlmostPrimes Campbell2026 CampbellCase3 CampbellCase2

/-! ### `X ≥ (N - 1)/3` -/

/-- `X = |𝒜|`: the `1 ≤ n ≤ N - 1` with `3 ∤ aₙ`. -/
def Xcount (N : ℕ) : ℕ := ((Icc 1 (N - 1)).filter (fun n => ¬ 3 ∣ aSeq N n)).card

lemma three_dvd_aSeq {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N - 1) (h : 3 ∣ aSeq N n) :
    3 ∣ n ∨ 3 ∣ (N - n) := by
  have hm : 3 ∣ n * (N - n) := by
    unfold aSeq at h
    split_ifs at h with he
    · exact h
    · have hev : 2 ∣ n * (N - n) := by
        rcases Nat.even_or_odd n with h' | h'
        · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h') _
        · apply Dvd.dvd.mul_left
          apply even_iff_two_dvd.mp
          have hNo : Odd N := Nat.not_even_iff_odd.mp he
          obtain ⟨k, hk⟩ := h'; obtain ⟨j, hj⟩ := hNo
          exact ⟨j - k, by omega⟩
      exact dvd_trans h (Nat.div_dvd_of_dvd hev)
  exact (Nat.Prime.dvd_mul Nat.prime_three).mp hm

lemma le_Xcount (N r c : ℕ)
    (h : ∀ j, j < c → 1 ≤ 3 * j + r ∧ 3 * j + r ≤ N - 1 ∧ ¬ 3 ∣ (3 * j + r) ∧
      ¬ 3 ∣ (N - (3 * j + r))) : c ≤ Xcount N := by
  have hsub : (range c).image (fun j => 3 * j + r) ⊆
      (Icc 1 (N - 1)).filter (fun n => ¬ 3 ∣ aSeq N n) := by
    intro n hn
    simp only [mem_image, mem_range] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    obtain ⟨h1, h2, h3, h4⟩ := h j hj
    rw [mem_filter, mem_Icc]
    refine ⟨⟨h1, h2⟩, fun hd => ?_⟩
    rcases three_dvd_aSeq h1 h2 hd with h5 | h5
    · exact h3 h5
    · exact h4 h5
  have hcard : ((range c).image (fun j => 3 * j + r)).card = c := by
    rw [card_image_of_injective _ (fun a b hab => by have h3 : 3 * a + r = 3 * b + r := hab; omega), card_range]
  have := card_le_card hsub
  unfold Xcount; omega

/-- **`X ≥ (N - 1)/3`, PROVED**, as `N - 1 ≤ 3 X`. -/
theorem X_ge (N : ℕ) : N - 1 ≤ 3 * Xcount N := by
  rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h | h | h
  · have := le_Xcount N 1 (N / 3) (fun j hj => by omega)
    omega
  · have := le_Xcount N 2 (N / 3) (fun j hj => by omega)
    omega
  · have := le_Xcount N 1 (N / 3 + 1) (fun j hj => by omega)
    omega

theorem X_ge_real {N : ℕ} (hN : 1 ≤ N) : ((N : ℝ) - 1) / 3 ≤ Xcount N := by
  have h := X_ge N
  have : ((N - 1 : ℕ) : ℝ) ≤ ((3 * Xcount N : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hN] at this
  linarith

lemma V_nonneg (N : ℕ) (z : ℝ) : 0 ≤ V N z := by
  unfold V
  apply prod_nonneg
  intro p hp
  rw [mem_primesBelow] at hp
  exact (factor_bounds N hp.1 hp.2.1).1

/-- Cited: Theorem 2.1 at `s = 14.8`, `K = 1.146` by Lemma 4.1(1), with the bound (4.4)
`2 R₄(𝒜, z^s) ≤ (19/3) v^{sδ} ∏_{p < v, p ∈ 𝒫} (1 + 8/p^δ)` for `z ≤ v`, `0 < δ < 1`. -/
def Case2SieveX : Prop :=
  ∀ N : ℕ, N0 < N → N < N1 → ∀ v δ : ℝ, zOf N ≤ v → 0 < δ → δ < 1 →
    (Xcount N : ℝ) * V N (zOf N) * F 14.8 (2 + log 1.146)
      - 19 / 3 * v ^ (14.8 * δ) * ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ)
      ≤ (siftCount N (zOf N) : ℝ)

/-- **`Case2Sieve` from `Case2SieveX` and `X_ge`.** -/
theorem case2Sieve_of (h : Case2SieveX) : Case2Sieve := by
  intro N h0 h1 v δ hzv hδ0 hδ1
  refine le_trans ?_ (h N h0 h1 v δ hzv hδ0 hδ1)
  have hN : 1 ≤ N := by unfold N0 at h0; omega
  have hX := X_ge_real hN
  have hV := V_nonneg N (zOf N)
  have hF : 0 ≤ F 14.8 (2 + log 1.146) := by linarith [case2_F]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hV) hF
  linarith

/-! ### Certificates for the first intervals of the Case 2 partition -/

lemma primesBelow_nat (n : ℕ) :
    primesBelow (n : ℝ) = (range n).filter (fun p => p.Prime ∧ p ≠ 3) := by
  ext p
  rw [mem_primesBelow, mem_filter, mem_range]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨by exact_mod_cast c, a, b⟩
  · rintro ⟨c, a, b⟩; exact ⟨a, b, by exact_mod_cast c⟩

lemma primes5Below_nat (n : ℕ) :
    primes5Below (n : ℝ) = (range n).filter (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 2) := by
  unfold primes5Below
  rw [primesBelow_nat, filter_filter]
  simp only [and_assoc]

/-- **Certificate criterion** for `S(u, v; 14.8, 0.2) > 0`. -/
theorem S2_pos_of (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (h : 19 / 3 * (v : ℝ) ^ 3 * 9 ^ ((range v).filter (fun p => p.Prime ∧ p ≠ 3)).card <
      ((u : ℝ) ^ 16 - 1) / 6 *
        (∏ p ∈ (range v).filter (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 2), (1 - 2 / (p : ℝ))) * 0.042) :
    0 < S2 u v 14.8 0.2 := by
  unfold S2
  rw [primesBelow_nat, primes5Below_nat]
  set P := ∏ p ∈ (range v).filter (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 2), (1 - 2 / (p : ℝ)) with hPdef
  set A := (range v).filter (fun p => p.Prime ∧ p ≠ 3) with hAdef
  have hP0 : 0 ≤ P := by
    apply prod_nonneg; intro p hp
    rw [mem_filter] at hp
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast two_le_of_ne3 hp.2.1 hp.2.2.2 hp.2.2.1
    have : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hQ : ∏ p ∈ A, (1 + 8 / (p : ℝ) ^ (0.2 : ℝ)) ≤ 9 ^ A.card := by
    rw [← prod_const]
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      rw [hAdef, mem_filter] at hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
      have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (0.2 : ℝ) := one_le_rpow hp1 (by norm_num)
      have : 8 / (p : ℝ) ^ (0.2 : ℝ) ≤ 8 := div_le_self (by norm_num) h1
      linarith
  have hQ0 : 0 ≤ ∏ p ∈ A, (1 + 8 / (p : ℝ) ^ (0.2 : ℝ)) := prod_nonneg (fun p _ => by positivity)
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hv3 : (v : ℝ) ^ ((14.8 : ℝ) * 0.2) ≤ (v : ℝ) ^ 3 := by
    have := rpow_le_rpow_of_exponent_le hv1 (show (14.8 : ℝ) * 0.2 ≤ ((3 : ℕ) : ℝ) by norm_num)
    rwa [rpow_natCast] at this
  have hu16 : (u : ℝ) ^ 16 ≤ (u : ℝ) ^ (16.5 : ℝ) := by
    have := rpow_le_rpow_of_exponent_le hu1 (show ((16 : ℕ) : ℝ) ≤ 16.5 by norm_num)
    rwa [rpow_natCast] at this
  have hu16' : 1 ≤ (u : ℝ) ^ 16 := one_le_pow₀ hu1
  have hF := case2_F
  have hE : 19 / 3 * (v : ℝ) ^ ((14.8 : ℝ) * 0.2) * ∏ p ∈ A, (1 + 8 / (p : ℝ) ^ (0.2 : ℝ)) ≤
      19 / 3 * (v : ℝ) ^ 3 * 9 ^ A.card := by
    apply mul_le_mul _ hQ hQ0 (by positivity)
    exact mul_le_mul_of_nonneg_left hv3 (by norm_num)
  have hM1 : ((u : ℝ) ^ 16 - 1) / 6 * P ≤ ((u : ℝ) ^ (16.5 : ℝ) - 1) / 6 * P :=
    mul_le_mul_of_nonneg_right (by linarith) hP0
  have hM0 : 0 ≤ ((u : ℝ) ^ 16 - 1) / 6 * P := mul_nonneg (by linarith) hP0
  have hM2 : ((u : ℝ) ^ 16 - 1) / 6 * P * 0.042 ≤
      ((u : ℝ) ^ (16.5 : ℝ) - 1) / 6 * P * F 14.8 (2 + log 1.146) :=
    mul_le_mul hM1 hF.le (by norm_num) (le_trans hM0 hM1)
  have e : (14.8 : ℝ) * 0.2 = 14.8 * 0.2 := rfl
  linarith

/-- `38^{16.5} < N₀`, so `z > 38` throughout Case 2. -/
lemma z_gt_38 {N : ℕ} (hN : N0 < N) : (38 : ℝ) < zOf N := by
  have h33 : ((38 : ℝ) ^ (16.5 : ℝ)) ^ 2 = (38 : ℝ) ^ 33 := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
  have hlt : ((38 : ℝ) ^ (16.5 : ℝ)) ^ 2 < (N0 : ℝ) ^ 2 := by
    rw [h33]; unfold N0; norm_num
  have h1 : (38 : ℝ) ^ (16.5 : ℝ) < N0 :=
    lt_of_pow_lt_pow_left₀ 2 (by unfold N0; positivity) hlt
  have h2 : (N0 : ℝ) < N := by exact_mod_cast hN
  by_contra hc
  rw [not_lt] at hc
  have hz0 : 0 ≤ zOf N := rpow_nonneg (Nat.cast_nonneg N) _
  have := rpow_le_rpow hz0 hc (by norm_num : (0 : ℝ) ≤ 16.5)
  rw [zOf_pow] at this
  linarith

macro "cert" : tactic => `(tactic| (
  apply S2_pos_of _ _ (by norm_num) (by norm_num)
  simp only [prod_filter, card_filter, prod_range_succ, sum_range_succ, prod_range_zero,
    sum_range_zero]
  norm_num))

theorem cert_38_41 : 0 < S2 (38 : ℕ) (41 : ℕ) 14.8 0.2 := by cert
theorem cert_41_43 : 0 < S2 (41 : ℕ) (43 : ℕ) 14.8 0.2 := by cert
theorem cert_43_47 : 0 < S2 (43 : ℕ) (47 : ℕ) 14.8 0.2 := by cert
theorem cert_47_53 : 0 < S2 (47 : ℕ) (53 : ℕ) 14.8 0.2 := by cert
theorem cert_53_59 : 0 < S2 (53 : ℕ) (59 : ℕ) 14.8 0.2 := by cert
theorem cert_59_61 : 0 < S2 (59 : ℕ) (61 : ℕ) 14.8 0.2 := by cert
theorem cert_61_67 : 0 < S2 (61 : ℕ) (67 : ℕ) 14.8 0.2 := by cert
theorem cert_67_71 : 0 < S2 (67 : ℕ) (71 : ℕ) 14.8 0.2 := by cert
theorem cert_71_73 : 0 < S2 (71 : ℕ) (73 : ℕ) 14.8 0.2 := by cert
theorem cert_73_79 : 0 < S2 (73 : ℕ) (79 : ℕ) 14.8 0.2 := by cert
theorem cert_79_83 : 0 < S2 (79 : ℕ) (83 : ℕ) 14.8 0.2 := by cert

/-- **`Case2Table` for `N₀ < N` with `z ≤ 83`, PROVED by the 11 certificates.** -/
theorem table_upto83 (N : ℕ) (hN : N0 < N) (hz : zOf N ≤ 83) :
    ∃ u v δ : ℝ, 1 ≤ u ∧ u < zOf N ∧ zOf N ≤ v ∧ 0 < δ ∧ δ < 1 ∧ 0 < S2 u v 14.8 δ := by
  have key : ∀ u v : ℕ, 1 ≤ u → (u : ℝ) < zOf N → zOf N ≤ v → 0 < S2 u v 14.8 0.2 →
      ∃ u v δ : ℝ, 1 ≤ u ∧ u < zOf N ∧ zOf N ≤ v ∧ 0 < δ ∧ δ < 1 ∧ 0 < S2 u v 14.8 δ :=
    fun u v hu h1 h2 h3 => ⟨u, v, 0.2, by exact_mod_cast hu, h1, h2, by norm_num, by norm_num, h3⟩
  have h38 := z_gt_38 hN
  rcases le_or_gt (zOf N) 41 with h | h41
  · exact key 38 41 (by norm_num) (by exact_mod_cast h38) (by exact_mod_cast h) cert_38_41
  rcases le_or_gt (zOf N) 43 with h | h43
  · exact key 41 43 (by norm_num) (by exact_mod_cast h41) (by exact_mod_cast h) cert_41_43
  rcases le_or_gt (zOf N) 47 with h | h47
  · exact key 43 47 (by norm_num) (by exact_mod_cast h43) (by exact_mod_cast h) cert_43_47
  rcases le_or_gt (zOf N) 53 with h | h53
  · exact key 47 53 (by norm_num) (by exact_mod_cast h47) (by exact_mod_cast h) cert_47_53
  rcases le_or_gt (zOf N) 59 with h | h59
  · exact key 53 59 (by norm_num) (by exact_mod_cast h53) (by exact_mod_cast h) cert_53_59
  rcases le_or_gt (zOf N) 61 with h | h61
  · exact key 59 61 (by norm_num) (by exact_mod_cast h59) (by exact_mod_cast h) cert_59_61
  rcases le_or_gt (zOf N) 67 with h | h67
  · exact key 61 67 (by norm_num) (by exact_mod_cast h61) (by exact_mod_cast h) cert_61_67
  rcases le_or_gt (zOf N) 71 with h | h71
  · exact key 67 71 (by norm_num) (by exact_mod_cast h67) (by exact_mod_cast h) cert_67_71
  rcases le_or_gt (zOf N) 73 with h | h73
  · exact key 71 73 (by norm_num) (by exact_mod_cast h71) (by exact_mod_cast h) cert_71_73
  rcases le_or_gt (zOf N) 79 with h | h79
  · exact key 73 79 (by norm_num) (by exact_mod_cast h73) (by exact_mod_cast h) cert_73_79
  · exact key 79 83 (by norm_num) (by exact_mod_cast h79) (by exact_mod_cast hz) cert_79_83

#print axioms X_ge
#print axioms X_ge_real
#print axioms case2Sieve_of
#print axioms S2_pos_of
#print axioms z_gt_38
#print axioms cert_38_41
#print axioms cert_79_83
#print axioms table_upto83

end LeanLab.AlmostPrimes.CampbellCase2X

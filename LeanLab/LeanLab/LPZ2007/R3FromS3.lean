/-
P0045 Languasco, Pintz, Zaccagnini 2007, p.7, display (15) to (16): the weight `n` of
`R^(3)_k(N) = Σ_ν n_ν 𝔖(n_ν)` is `N (1 + o(1))`, so `R3Asymp` follows from the unweighted
asymptotic `S3Asymp` for `S3_k(N) = Σ_ν 𝔖(n_ν)`, the sum the paper writes as `R^(4)_k(N)/N`
after expanding `𝔖`.

Unit U-6832, CLOUD 20261021T0217Z-cloud56, track T2. AI-written Lean code, Claude. Checked only by
the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

* `S3`, `S3Asymp`: the unweighted sum and its asymptotic `2c0 C(k, N) L^k + o(L^k)`.
* `r3Asymp_of_s3Asymp : S3Asymp → R3Asymp`, PROVED: `0 ≤ N − n_ν ≤ k X 2^{−√L}`.
* `mainJ_twoC0_of_cor42_s3`, `main_19_24_of_cor42_s3`: the repaired Theorem and the I-0091
  shape CONDITIONAL ON `Cor42W` and `S3Asymp`.
-/
import Mathlib
import LeanLab.LPZ2007.Eq14FromCor42

namespace LeanLab.LPZ2007.R3FromS3

open Finset Real LeanLab.LPZ2007 LeanLab.LPZ2007.Eq14FromCor42

noncomputable section

/-- `S3_k(N) = Σ_{ν ∈ [1, L']^k} 𝔖(N − 2^{ν_1} − … − 2^{ν_k})`. -/
def S3 (k : ℕ) (X : ℝ) (N : ℕ) : ℝ := ∑ ν ∈ tuples k ⌊Lp X⌋₊, sing (N - pow2sum ν)

/-- (16) to (24) unweighted, with the factor `2c0` of F-0038:
`S3_k(N) = 2c0 C(k, N) L^k + o(L^k)` uniformly in even `N ∈ J(X)`. A named input. -/
def S3Asymp : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
    |S3 k X N - twoC0 * Ckn k N * Lg X ^ k| ≤ η * Lg X ^ k

theorem S3_nonneg (k : ℕ) (X : ℝ) (N : ℕ) : 0 ≤ S3 k X N :=
  sum_nonneg fun _ _ => sing_nonneg _

/-- `2^{ν_1} + … + 2^{ν_k} ≤ δ X` once `√L ≥ k/δ`. -/
theorem pow2sum_le_delta {k : ℕ} {X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) (hL1 : 1 ≤ Lg X)
    (hL : k / δ ≤ √(Lg X)) {ν : Fin k → ℕ} (hν : ν ∈ tuples k ⌊Lp X⌋₊) :
    (pow2sum ν : ℝ) ≤ δ * X := by
  have h2 : (k : ℝ) / δ < (2 : ℝ) ^ √(Lg X) := lt_of_le_of_lt hL (lt_two_rpow (Real.sqrt_nonneg _))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ √(Lg X) := by positivity
  have hk : (k : ℝ) ≤ δ * (2 : ℝ) ^ √(Lg X) := by
    rw [div_lt_iff₀ hδ] at h2; linarith
  calc (pow2sum ν : ℝ) ≤ k * (2 : ℝ) ^ ⌊Lp X⌋₊ := by exact_mod_cast pow2sum_le hν
    _ ≤ k * (X / (2 : ℝ) ^ √(Lg X)) :=
        mul_le_mul_of_nonneg_left (two_pow_floorLp_le hX hL1) (Nat.cast_nonneg _)
    _ = (k : ℝ) * X / (2 : ℝ) ^ √(Lg X) := by ring
    _ ≤ δ * X := by
        rw [div_le_iff₀ hpos]; nlinarith

/-- **(15) to (16), the weight**: `S3Asymp → R3Asymp`. -/
theorem r3Asymp_of_s3Asymp (h : S3Asymp) : R3Asymp := by
  intro k hk η hη
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set Cm := ∑' d, romanovTerm d with hCmdef
  have hc0 : 0 ≤ twoC0 := twoC0_pos.le
  have hCm : 0 ≤ Cm := le_trans (by norm_num) ((Corollary.Ckn_bounds j 0).1.trans
    (Corollary.Ckn_bounds j 0).2)
  set A := twoC0 * Cm + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set δ := min (η / (3 * A)) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδA : δ * A ≤ η / 3 := by
    have : δ ≤ η / (3 * A) := min_le_left _ _
    calc δ * A ≤ η / (3 * A) * A := mul_le_mul_of_nonneg_right this (by linarith)
      _ = η / 3 := by field_simp
  set η' := min (η / 2) 1 with hη'
  obtain ⟨X1, H⟩ := h (j + 1) hk η' (lt_min (by linarith) one_pos)
  have hk0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  set L0 : ℝ := (((j + 1 : ℕ) : ℝ) / (2 * δ / 3)) ^ 2 + 1 with hL0
  refine ⟨max X1 (max 2 ((2 : ℝ) ^ L0)), fun X hX N hNe hNJ => ?_⟩
  have hX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXL : (2 : ℝ) ^ L0 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hL : L0 ≤ Lg X := Eq14FromCor42.Lg_ge hXL
  have hsq0 : 0 ≤ (((j + 1 : ℕ) : ℝ) / (2 * δ / 3)) ^ 2 := sq_nonneg _
  have hL1 : 1 ≤ Lg X := by linarith
  have hsq : ((j + 1 : ℕ) : ℝ) / (2 * δ / 3) ≤ √(Lg X) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; linarith
  have hN0 : 2 * X / 3 ≤ N := hNJ.1
  have hp : ∀ ν ∈ tuples (j + 1) ⌊Lp X⌋₊, (pow2sum ν : ℝ) ≤ δ * N := by
    intro ν hν
    have := pow2sum_le_delta hX0 (by positivity) hL1 hsq hν
    have hXN : 2 * δ / 3 * X ≤ δ * N := by nlinarith
    linarith
  have hpN : ∀ ν ∈ tuples (j + 1) ⌊Lp X⌋₊, pow2sum ν ≤ N := by
    intro ν hν
    have h1 := hp ν hν
    have h2 : δ * (N : ℝ) ≤ N := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast h1.trans h2
  -- `R3 = N S3 − E`
  set E := ∑ ν ∈ tuples (j + 1) ⌊Lp X⌋₊, (pow2sum ν : ℝ) * sing (N - pow2sum ν) with hE
  have hR3 : R3 (j + 1) X N = N * S3 (j + 1) X N - E := by
    unfold R3 S3; rw [hE, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun ν hν => ?_
    rw [Nat.cast_sub (hpN ν hν)]; ring
  have hE0 : 0 ≤ E := sum_nonneg fun ν _ => mul_nonneg (Nat.cast_nonneg _) (sing_nonneg _)
  have hEle : E ≤ δ * N * S3 (j + 1) X N := by
    unfold S3; rw [hE, mul_sum]
    exact sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right (hp ν hν) (sing_nonneg _)
  -- the input
  have hS := H X hX1 N hNe hNJ
  set Q := Lg X ^ (j + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set s0 := twoC0 * Ckn (j + 1) N * Q with hs0
  have hs0le : s0 ≤ twoC0 * Cm * Q := by
    rw [hs0]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Corollary.Ckn_bounds j N).2 hc0) hQ0
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'2 : η' ≤ η / 2 := min_le_left _ _
  have hSup : S3 (j + 1) X N ≤ A * Q := by
    have := (abs_le.1 hS).2
    have : η' * Q ≤ 1 * Q := mul_le_mul_of_nonneg_right hη'1 hQ0
    rw [hA]; linarith
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hEbound : E ≤ η / 3 * (N * Q) := by
    calc E ≤ δ * N * S3 (j + 1) X N := hEle
      _ ≤ δ * N * (A * Q) := mul_le_mul_of_nonneg_left hSup (by positivity)
      _ = (δ * A) * (N * Q) := by ring
      _ ≤ η / 3 * (N * Q) := mul_le_mul_of_nonneg_right hδA (by positivity)
  have hmain : (N : ℝ) * |S3 (j + 1) X N - s0| ≤ η / 2 * (N * Q) := by
    have : |S3 (j + 1) X N - s0| ≤ η / 2 * Q :=
      hS.trans (mul_le_mul_of_nonneg_right hη'2 hQ0)
    nlinarith
  have hrw : R3 (j + 1) X N - twoC0 * Ckn (j + 1) N * N * Lg X ^ (j + 1) =
      N * (S3 (j + 1) X N - s0) - E := by rw [hR3, hs0, hQ]; ring
  rw [hrw]
  calc |(N : ℝ) * (S3 (j + 1) X N - s0) - E| ≤ |(N : ℝ) * (S3 (j + 1) X N - s0)| + |E| :=
        abs_sub _ _
    _ = (N : ℝ) * |S3 (j + 1) X N - s0| + E := by rw [abs_mul, abs_of_nonneg hNn, abs_of_nonneg hE0]
    _ ≤ η / 2 * (N * Q) + η / 3 * (N * Q) := add_le_add hmain hEbound
    _ ≤ η * N * Lg X ^ (j + 1) := by
        rw [← hQ]; nlinarith [mul_nonneg hNn hQ0]

/-- **The repaired Theorem on `J(X)`, CONDITIONAL ON `Cor42W` and `S3Asymp` only.** -/
theorem mainJ_twoC0_of_cor42_s3 (hC : Cor42W) (h3 : S3Asymp) : MainJ_twoC0 :=
  mainJ_twoC0_of_cor42_r3 hC (r3Asymp_of_s3Asymp h3)

/-- **I-0091 at `σ = 19/24`, CONDITIONAL ON `MinorBoundσ (19/24)`, `Cor42W` and `S3Asymp`.** -/
theorem main_19_24_of_cor42_s3 (hm : MinorBessel.MinorBoundσ (19 / 24)) (hC : Cor42W)
    (h3 : S3Asymp) :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((ExcJC (fun k N => twoC0 * Ckn k N) k X η).card : ℝ) ≤
        B * X ^ (7 / 12 : ℝ) * Real.log X ^ 10 :=
  main_19_24_of_cor42_r3 hm hC (r3Asymp_of_s3Asymp h3)

/-! ### (16) to (17): the divisor expansion of `𝔖`, so `S3 = 2c0 · R^(4)/N` -/

open Classical in
/-- `𝔖(n) = 2c0 Σ_{d ∣ n, d odd squarefree} f(d)` for even `n ≠ 0`, p.9 with (2). -/
theorem sing_expand {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    sing n = twoC0 * ∑ d ∈ n.divisors.filter OddSqf, fd d := by
  classical
  rw [eq2_proof n hn h0]
  congr 1
  set F := n.primeFactors.filter (2 < ·) with hF
  have h1 : ∏ p ∈ F, ((p : ℝ) - 1) / ((p : ℝ) - 2) = ∏ p ∈ F, (1 + 1 / ((p : ℝ) - 2)) := by
    refine prod_congr rfl fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp; ring
  rw [h1, prod_one_add]
  symm
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    simp only [mem_powerset]
    intro p hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [hF, mem_filter]
    refine ⟨Nat.primeFactors_mono hd.1.1 h0 hp, ?_⟩
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hd.2.1) (even_iff_two_dvd.2 hpd)
    have := hpp.two_le; omega
  · intro T hT
    simp only [mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime ∧ 2 < p := fun p hp => by
      have := hT hp; rw [hF, mem_filter] at this
      exact ⟨Nat.prime_of_mem_primeFactors this.1, this.2⟩
    obtain ⟨hsq, -, -⟩ := LeanLab.LPZ2007B.set_facts hTp
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨(prod_dvd_prod_of_subset _ _ _ (hT.trans (filter_subset _ _))).trans
      (Nat.prod_primeFactors_dvd n), h0⟩, hsq.2.1, hsq.2.2⟩
  · intro d hd
    simp only [mem_filter] at hd
    exact Nat.prod_primeFactors_of_squarefree hd.2.2
  · intro T hT
    simp only [mem_powerset] at hT
    exact Nat.primeFactors_prod fun p hp => by
      have := hT hp; rw [hF, mem_filter] at this; exact Nat.prime_of_mem_primeFactors this.1
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    unfold fd
    congr 1
    refine filter_true_of_mem fun p hp => ?_
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hd.2.1) (even_iff_two_dvd.2 hpd)
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega

open Classical in
/-- `R^(4)_k(N)/N = Σ'_{d ≤ N} f(d) #{ν ∈ [1, L']^k : d ∣ N − 2^{ν_1} − … − 2^{ν_k}}`, (17) p.7. -/
def D4 (k : ℕ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 N).filter OddSqf, fd d * #{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν}

/-- `S3 = 2c0 · D4` when every `n_ν ≥ 1` and `N` is even. -/
theorem S3_eq_D4 (k : ℕ) (X : ℝ) {N : ℕ} (hN : Even N)
    (hlt : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν < N) : S3 k X N = twoC0 * D4 k X N := by
  classical
  unfold S3 D4
  rw [sum_congr rfl fun ν hν => sing_expand ((Nat.even_sub (hlt ν hν).le).2
    ⟨fun _ => Eq14FromCor42.even_pow2sum hν, fun _ => hN⟩) (by have := hlt ν hν; omega), ← mul_sum]
  congr 1
  have hdiv : ∀ ν ∈ tuples k ⌊Lp X⌋₊, (N - pow2sum ν).divisors.filter OddSqf =
      ((Icc 1 N).filter OddSqf).filter (· ∣ N - pow2sum ν) := by
    intro ν hν
    have := hlt ν hν
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨⟨hd, hne⟩, ho⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
      exact ⟨⟨⟨by omega, by omega⟩, ho⟩, hd⟩
    · rintro ⟨⟨_, ho⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, ho⟩
  rw [sum_congr rfl fun ν hν => by rw [hdiv ν hν, sum_filter], sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- (17) to (24) with the constant `C(k, N)`: `R^(4)_k(N)/N = C(k, N) L^k + o(L^k)` uniformly in
even `N ∈ J(X)`. A named input, the paper's arithmetic; the `2c0` of F-0038 sits outside. -/
def D4Asymp : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
    |D4 k X N - Ckn k N * Lg X ^ k| ≤ η * Lg X ^ k

/-- **(16) to (17)**: `D4Asymp → S3Asymp`. -/
theorem s3Asymp_of_d4Asymp (h : D4Asymp) : S3Asymp := by
  intro k hk η hη
  have hc0 : 0 < twoC0 := twoC0_pos
  obtain ⟨X1, H⟩ := h k hk (η / (twoC0 + 1)) (by positivity)
  refine ⟨max X1 (max 2 ((2 : ℝ) ^ (36 * (k : ℝ) ^ 2))), fun X hX N hNe hNJ => ?_⟩
  have hX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXL : (2 : ℝ) ^ (36 * (k : ℝ) ^ 2) ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hL := Eq14FromCor42.Lg_ge hXL
  have hlt : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν < N := by
    intro ν hν
    have h1 := Eq14FromCor42.pow2sum_small hk hX0 hL hν
    have h2 : 2 * X / 3 ≤ N := hNJ.1
    exact_mod_cast (show (pow2sum ν : ℝ) < N by linarith)
  rw [S3_eq_D4 k X hNe hlt]
  have hQ0 : 0 ≤ Lg X ^ k := pow_nonneg (by nlinarith) k
  have e : twoC0 * D4 k X N - twoC0 * Ckn k N * Lg X ^ k =
      twoC0 * (D4 k X N - Ckn k N * Lg X ^ k) := by ring
  rw [e, abs_mul, abs_of_pos hc0]
  have h1 := H X hX1 N hNe hNJ
  calc twoC0 * |D4 k X N - Ckn k N * Lg X ^ k| ≤ twoC0 * (η / (twoC0 + 1) * Lg X ^ k) :=
        mul_le_mul_of_nonneg_left h1 hc0.le
    _ = (twoC0 / (twoC0 + 1)) * η * Lg X ^ k := by ring
    _ ≤ 1 * η * Lg X ^ k := by
        gcongr; rw [div_le_one (by positivity)]; linarith
    _ = η * Lg X ^ k := by ring

/-- **The repaired Theorem on `J(X)`, CONDITIONAL ON `Cor42W` and `D4Asymp` only.** -/
theorem mainJ_twoC0_of_cor42_d4 (hC : Cor42W) (h4 : D4Asymp) : MainJ_twoC0 :=
  mainJ_twoC0_of_cor42_s3 hC (s3Asymp_of_d4Asymp h4)

/-- **I-0091 at `σ = 19/24`, CONDITIONAL ON `MinorBoundσ (19/24)`, `Cor42W` and `D4Asymp`.** -/
theorem main_19_24_of_cor42_d4 (hm : MinorBessel.MinorBoundσ (19 / 24)) (hC : Cor42W)
    (h4 : D4Asymp) :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((ExcJC (fun k N => twoC0 * Ckn k N) k X η).card : ℝ) ≤
        B * X ^ (7 / 12 : ℝ) * Real.log X ^ 10 :=
  main_19_24_of_cor42_s3 hm hC (s3Asymp_of_d4Asymp h4)

end

end LeanLab.LPZ2007.R3FromS3

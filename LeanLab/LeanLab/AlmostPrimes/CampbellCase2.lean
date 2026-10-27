/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2113Z-cloud51, unit U-6748.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1, read on arxiv.org/html/2608.09488 this session, Section 5, proof of
Theorem 1.2, Case 2, `N₀ < N < N₁ = 10^132`, `z = N^{1/16.5}`, `z₀ < z < z₁ = 10^8`:
`s = 14.8`, `k = 2 + log 1.146`, `δ ∈ {0.20, 0.60, 0.75, 0.85, 0.93}`, and for `z ∈ (u, v]`
`S(𝒜, z) > S(u, v; s, δ) =
  (u^{16.5} - 1)/6 · ∏_{5 ≤ p < v} (1 - 2/p) · F(s, k) - (19/3) v^{sδ} ∏_{p < v, p ≠ 3} (1 + 8/p^δ)`,
from `X > (u^{16.5} - 1)/3`, `V(z) ≥ V(v) ≥ ½ ∏_{5 ≤ p < v} (1 - 2/p)` and
`2 R₄ ≤ (19/3) v^{sδ} ∏ (1 + 8/p^δ)`; then `max_δ S(qᵢ, qᵢ₊₁; s, δ) > 0` on a partition
`z₀ = q₀ < … < q_j = z₁` checked by the script verify_case2_presieved.py.

PROVED here, no cited input:
* `case2_F`: `F(14.8, 2 + log 1.146) > 0.042`; the paper prints no value, only `F > 0`;
  Python value 0.0430101. `case2_s_cond`: `s ≥ 2k + 3`, MATCH.
* `V_anti`: `V(z) ≥ V(v)` for `z ≤ v`; `V_ge_half`: `V(v) ≥ ½ ∏_{5 ≤ p < v} (1 - 2/p)`, for the
  pre-sieved `g`: `g(2) = 1/2`, `g(p) = 2/p` or `1/p` for `p ≥ 5`, prime 3 removed. MATCH.
* `S_ge_S2`: the paper's step from the sieve display to `S(u, v; s, δ)`, any `N`, `u < z ≤ v`.
CONDITIONAL, counted apart:
* `case2Check_of`, `Campbell2026`'s Case 2 input, ON `Case2Sieve`, Theorem 2.1 with Lemma 4.1(1),
  `X ≥ (N - 1)/3` and the `R₄` bound (4.4), and `Case2Table`, the script's partition.
* `theorem1_2_of_inputs`, Theorem 1.2, ON `GapTable`, `Case2Sieve`, `Case2Table`, `Case3Sieve`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellCase3

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellCase2
open LeanLab.AlmostPrimes Campbell2026 CampbellCase3

/-! ### The sieve factor -/

/-- `F(s, k) = 1 - (s + 3)/(2e^k) · (2ek/(s - 3))^{(s-3)/2}`, Theorem 2.1. -/
def F (s k : ℝ) : ℝ := 1 - (s + 3) / (2 * exp k) * (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2)

lemma log1146_le : log 1.146 ≤ (0.1363 : ℝ) := by
  have h := abs_log_sub_add_sum_range_le (x := (-0.146 : ℝ)) (by norm_num) 6
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h
  linarith [h.1]

/-- `s ≥ 2k + 3` in Case 2. MATCHES; also in `Campbell2026.s_conditions`. -/
theorem case2_s_cond : 2 * (2 + log 1.146) + 3 ≤ (14.8 : ℝ) := s_conditions.2

/-- **Case 2's sieve factor** `F(14.8, 2 + log 1.146) > 0.042`, value 0.04301. -/
theorem case2_F : (0.042 : ℝ) < F 14.8 (2 + log 1.146) := by
  unfold F
  set s : ℝ := 14.8
  set k : ℝ := 2 + log 1.146 with hkdef
  have hl0 : 0 < log (1.146 : ℝ) := log_pos (by norm_num)
  have hl := log1146_le
  have he1 := exp_one_lt_d9
  have he2 := exp_one_gt_d9
  have hk : exp k = exp 1 ^ 2 * 1.146 := by
    rw [hkdef, exp_add, exp_log (by norm_num), exp_one_pow]; norm_num
  have hx0 : 0 < 2 * exp 1 * k / (s - 3) := by
    have := exp_pos 1; have : 0 < k := by rw [hkdef]; linarith
    have : (0 : ℝ) < s - 3 := by norm_num [s]
    positivity
  have hx : 2 * exp 1 * k / (s - 3) ≤ 0.98425 := by
    rw [div_le_iff₀ (by norm_num [s])]
    have : 2 * exp 1 * k ≤ 2 * 2.7182818286 * (2 + 0.1363) := by
      rw [hkdef]; apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    norm_num [s] at this ⊢; linarith
  have hlx : log (2 * exp 1 * k / (s - 3)) ≤ -0.01575 := by
    have := log_le_sub_one_of_pos hx0; linarith
  have hpow : (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) ≤ (exp 0.0929)⁻¹ := by
    rw [rpow_def_of_pos hx0, ← exp_neg]
    apply exp_le_exp.mpr
    norm_num [s] at hlx ⊢; nlinarith
  have hE : (1.0972 : ℝ) ≤ exp 0.0929 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.0929 : ℝ)) (by norm_num) 3
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hinv : (exp 0.0929)⁻¹ ≤ (1.0972 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hE
  have he2' : (2.7182818283 : ℝ) ^ 2 ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he2.le 2
  have hc : (s + 3) / (2 * exp k) ≤ 17.8 / (2 * (2.7182818283 ^ 2 * 1.146)) := by
    rw [hk, show s + 3 = (17.8 : ℝ) by norm_num [s]]
    gcongr
  have hc0 : 0 ≤ (s + 3) / (2 * exp k) := by
    have := exp_pos k; have : (0 : ℝ) ≤ s + 3 := by norm_num [s]
    positivity
  have hp0 : 0 ≤ (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) := rpow_nonneg hx0.le _
  have := mul_le_mul hc (hpow.trans hinv) hp0 (by norm_num)
  have fin : 17.8 / (2 * ((2.7182818283 : ℝ) ^ 2 * 1.146)) * (1.0972 : ℝ)⁻¹ < 0.958 := by
    norm_num
  linarith

/-! ### `V(z)` for the pre-sieved sequence -/

/-- `𝒫` below `z`: the primes `p < z` other than 3. -/
def primesBelow (z : ℝ) : Finset ℕ :=
  (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 3 ∧ (p : ℝ) < z)

/-- The primes `5 ≤ p < z`. -/
def primes5Below (z : ℝ) : Finset ℕ := (primesBelow z).filter (fun p => p ≠ 2)

/-- `g(p)`: `1/2` at `p = 2`, `1/p` for `p ∣ N`, `2/p` otherwise. -/
def g (N p : ℕ) : ℝ := if p = 2 then 1 / 2 else if p ∣ N then 1 / p else 2 / p

/-- `V(z) = ∏_{p < z, p ∈ 𝒫} (1 - g(p))`. -/
def V (N : ℕ) (z : ℝ) : ℝ := ∏ p ∈ primesBelow z, (1 - g N p)

lemma mem_primesBelow {z : ℝ} {p : ℕ} :
    p ∈ primesBelow z ↔ p.Prime ∧ p ≠ 3 ∧ (p : ℝ) < z := by
  unfold primesBelow
  simp only [mem_filter, mem_range, and_iff_right_iff_imp]
  intro ⟨_, _, hpz⟩
  have : (p : ℝ) ≤ ⌊z⌋₊ ∨ True := Or.inr trivial
  have h0 : (0 : ℝ) ≤ z := le_trans (Nat.cast_nonneg p) hpz.le
  have := Nat.lt_floor_add_one z
  have : (p : ℝ) < (⌊z⌋₊ + 1 : ℕ) := by push_cast; linarith [Nat.floor_le h0]
  exact_mod_cast this

lemma two_le_of_ne3 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have := hp.two_le
  by_contra h
  interval_cases p
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hp (by norm_num)

lemma factor_bounds (N : ℕ) {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    0 ≤ 1 - g N p ∧ 1 - g N p ≤ 1 := by
  unfold g
  split_ifs with h2 hd
  · constructor <;> norm_num
  · have h5 : (5 : ℝ) ≤ p := by exact_mod_cast two_le_of_ne3 hp h2 h3
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    constructor
    · linarith
    · have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
  · have h5 : (5 : ℝ) ≤ p := by exact_mod_cast two_le_of_ne3 hp h2 h3
    have : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    constructor
    · linarith
    · have : 0 ≤ 2 / (p : ℝ) := by positivity
      linarith

lemma primesBelow_mono {z v : ℝ} (h : z ≤ v) : primesBelow z ⊆ primesBelow v := by
  intro p hp
  rw [mem_primesBelow] at hp ⊢
  exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 h⟩

/-- **`V(z) ≥ V(v)` for `z ≤ v`.** -/
theorem V_anti (N : ℕ) {z v : ℝ} (h : z ≤ v) : V N v ≤ V N z := by
  unfold V
  rw [← prod_sdiff (primesBelow_mono h)]
  have hA : ∀ p ∈ primesBelow v, 0 ≤ 1 - g N p ∧ 1 - g N p ≤ 1 := by
    intro p hp; rw [mem_primesBelow] at hp; exact factor_bounds N hp.1 hp.2.1
  have h1 : ∏ p ∈ primesBelow v \ primesBelow z, (1 - g N p) ≤ 1 :=
    prod_le_one₀ (fun p hp => (hA p (mem_sdiff.mp hp).1).1)
      (fun p hp => (hA p (mem_sdiff.mp hp).1).2)
  have h0 : 0 ≤ ∏ p ∈ primesBelow z, (1 - g N p) :=
    prod_nonneg (fun p hp => (hA p (primesBelow_mono h hp)).1)
  nlinarith

/-- **`V(v) ≥ ½ ∏_{5 ≤ p < v} (1 - 2/p)`.** -/
theorem V_ge_half (N : ℕ) (v : ℝ) :
    (1 / 2) * ∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ)) ≤ V N v := by
  have hP : ∀ p ∈ primes5Below v, 0 ≤ 1 - 2 / (p : ℝ) ∧ 1 - 2 / (p : ℝ) ≤ 1 - g N p := by
    intro p hp
    unfold primes5Below at hp
    rw [mem_filter, mem_primesBelow] at hp
    obtain ⟨⟨hpr, h3, _⟩, h2⟩ := hp
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast two_le_of_ne3 hpr h2 h3
    have : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    refine ⟨by linarith, ?_⟩
    unfold g; simp only [h2, if_false]
    split_ifs
    · have : 1 / (p : ℝ) ≤ 2 / p := by gcongr; norm_num
      linarith
    · exact le_refl _
  have hQ : ∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ)) ≤ ∏ p ∈ primes5Below v, (1 - g N p) :=
    prod_le_prod₀ (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2)
  have hQ0 : 0 ≤ ∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ)) := prod_nonneg (fun p hp => (hP p hp).1)
  have hfilt : primes5Below v = (primesBelow v).erase 2 := by
    unfold primes5Below; ext p; simp [mem_filter, mem_erase, and_comm]
  unfold V
  by_cases h2 : 2 ∈ primesBelow v
  · rw [← mul_prod_erase _ _ h2, ← hfilt]
    have : 1 - g N 2 = 1 / 2 := by unfold g; norm_num
    rw [this]; nlinarith
  · have he : (primesBelow v).erase 2 = primesBelow v := erase_eq_of_notMem h2
    rw [hfilt, he] at hQ hQ0 ⊢
    nlinarith

/-! ### From the sieve display to `S(u, v; s, δ)` -/

/-- `S(u, v; s, δ)` as printed, with `F = F(14.8, 2 + log 1.146)`. -/
def S2 (u v s δ : ℝ) : ℝ :=
  (u ^ (16.5 : ℝ) - 1) / 6 * (∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ))) * F 14.8 (2 + log 1.146)
    - 19 / 3 * v ^ (s * δ) * ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ)

/-- `z = N^{1/16.5}`. -/
def zOf (N : ℕ) : ℝ := (N : ℝ) ^ (1 / (16.5 : ℝ))

lemma zOf_pow (N : ℕ) : zOf N ^ (16.5 : ℝ) = N := by
  unfold zOf; rw [← rpow_mul (Nat.cast_nonneg N)]; norm_num

/-- Cited: Theorem 2.1 at `s = 14.8`, `K = 1.146` by Lemma 4.1(1), with `X ≥ (N - 1)/3` and
the bound (4.4) `2 R₄(𝒜, z^s) ≤ (19/3) v^{sδ} ∏_{p < v, p ∈ 𝒫} (1 + 8/p^δ)` for `z ≤ v`,
`0 < δ < 1`, in the range of Case 2. -/
def Case2Sieve : Prop :=
  ∀ N : ℕ, N0 < N → N < N1 → ∀ v δ : ℝ, zOf N ≤ v → 0 < δ → δ < 1 →
    ((N : ℝ) - 1) / 3 * V N (zOf N) * F 14.8 (2 + log 1.146)
      - 19 / 3 * v ^ (14.8 * δ) * ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ)
      ≤ (siftCount N (zOf N) : ℝ)

/-- **The paper's step `S(𝒜, z) > S(u, v; s, δ)`, PROVED from the sieve display.** -/
theorem S_ge_S2 {N : ℕ} {u v δ : ℝ} (hu : 1 ≤ u) (huz : u < zOf N) (hzv : zOf N ≤ v)
    (hsieve : ((N : ℝ) - 1) / 3 * V N (zOf N) * F 14.8 (2 + log 1.146)
      - 19 / 3 * v ^ (14.8 * δ) * ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ)
      ≤ (siftCount N (zOf N) : ℝ)) :
    S2 u v 14.8 δ ≤ (siftCount N (zOf N) : ℝ) := by
  refine le_trans ?_ hsieve
  unfold S2
  have hF := case2_F
  have hP0 : 0 ≤ ∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ)) := by
    apply prod_nonneg; intro p hp
    unfold primes5Below at hp
    rw [mem_filter, mem_primesBelow] at hp
    have h5 : (5 : ℝ) ≤ p := by exact_mod_cast two_le_of_ne3 hp.1.1 hp.2 hp.1.2.1
    have : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hV := (V_ge_half N v).trans (V_anti N hzv)
  have hu1 : 0 ≤ u ^ (16.5 : ℝ) - 1 := by
    have : (1 : ℝ) ≤ u ^ (16.5 : ℝ) := one_le_rpow hu (by norm_num)
    linarith
  have huN : u ^ (16.5 : ℝ) ≤ N := by
    rw [← zOf_pow N]; exact rpow_le_rpow (by linarith) huz.le (by norm_num)
  have hmain : (u ^ (16.5 : ℝ) - 1) / 6 * (∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ))) ≤
      ((N : ℝ) - 1) / 3 * V N (zOf N) := by
    calc (u ^ (16.5 : ℝ) - 1) / 6 * (∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ)))
        = (u ^ (16.5 : ℝ) - 1) / 3 * ((1 / 2) * ∏ p ∈ primes5Below v, (1 - 2 / (p : ℝ))) := by
          ring
      _ ≤ ((N : ℝ) - 1) / 3 * V N (zOf N) := by
          apply mul_le_mul (by linarith) hV (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_right hmain (by linarith : (0 : ℝ) ≤ F 14.8 (2 + log 1.146))
  linarith

/-- Cited: the script verify_case2_presieved.py, read as: for each `N` of Case 2 some interval
`(u, v]` of the partition, `u ≥ z₀ > 1`, holds `z` and some `δ ∈ (0, 1)` has
`S(u, v; 14.8, δ) > 0`. -/
def Case2Table : Prop :=
  ∀ N : ℕ, N0 < N → N < N1 → ∃ u v δ : ℝ, 1 ≤ u ∧ u < zOf N ∧ zOf N ≤ v ∧ 0 < δ ∧ δ < 1 ∧
    0 < S2 u v 14.8 δ

/-- **Case 2, CONDITIONAL ON `Case2Sieve` and `Case2Table`.** -/
theorem case2Check_of (hs : Case2Sieve) (ht : Case2Table) : Case2Check := by
  intro N h0 h1
  obtain ⟨u, v, δ, hu, huz, hzv, hδ0, hδ1, hpos⟩ := ht N h0 h1
  have := S_ge_S2 hu huz hzv (hs N h0 h1 v δ hzv hδ0 hδ1)
  have hc : 0 < siftCount N (zOf N) := by exact_mod_cast lt_of_lt_of_le hpos this
  exact siftedExists_of_count_pos hc

/-- **Theorem 1.2, CONDITIONAL ON `GapTable`, `Case2Sieve`, `Case2Table`, `Case3Sieve`.** -/
theorem theorem1_2_of_inputs (hG : GapTable) (hs : Case2Sieve) (ht : Case2Table)
    (h3 : Case3Sieve) : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N :=
  theorem1_2_of_cases hG (case2Check_of hs ht) h3

#print axioms case2_s_cond
#print axioms case2_F
#print axioms V_anti
#print axioms V_ge_half
#print axioms S_ge_S2
#print axioms case2Check_of
#print axioms theorem1_2_of_inputs

end LeanLab.AlmostPrimes.CampbellCase2

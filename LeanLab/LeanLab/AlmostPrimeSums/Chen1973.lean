/-
AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1274, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, "On the representation of a larger even integer
as the sum of a prime and the product of at most two primes". Original NOT read.
Secondary sources used:
* Li, arXiv 2405.05727v4, eq. (1) to (3): Chen 1973 proved D_{1,2}(N) ≥ 0.67 C(N) N / log² N,
  D_{1,2}(N) = #{p ≤ N : N - p = P₂}, P₂ with at most two prime factors with multiplicity,
  C(N) = ∏_{p∣N, p>2} (p-1)/(p-2) · ∏_{p>2} (1 - 1/(p-1)²). Later constants 0.689 (HR), ...
* Bordignon-Johnston-Starichkova, arXiv 2207.09452v6 (lab copy copies/P0009.txt), Lemma 37
  (= Nathanson, Thm 10.2), Theorems 44, 50, 51, Lemma 52 and Section 9, for the switching
  form of Chen's weighted sieve and the limit constant 𝓕 = 2 log 3 - log 6 - c̄.
The combinatorial Chen inequality itself is `ChenExplicit.chen_inequality` (Bridge.lean),
already PROVED for arbitrary cut-offs; here it is instantiated at Chen's classical z = N^{1/10}.
Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Bridge
import LeanLab.ChenExplicit.BJSCbar
import LeanLab.ChenDoubleSieve.Statements

open Finset Real

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973

open LeanLab.ChenExplicit

/-! ### 1. The quantitative statement of Chen 1973, as a `Prop`, and its links -/

/-- Chen 1973, quantitative form, as quoted in arXiv 2405.05727 eq. (2):
for all large even `N`, `D_{1,2}(N) ≥ 0.67 C(N) N / log² N`. `ChenLower b` is from
`ChenDoubleSieve`: `b Θ(N) ≤ D12 N` eventually, `Θ(N) = C_N N / log² N`. -/
def Chen1973Quant : Prop := LeanLab.ChenDoubleSieve.ChenLower 0.67

/-- Halberstam-Richert's 0.689, or any later constant, implies Chen's 0.67. -/
theorem chen1973Quant_of_lower {b : ℝ} (hb : 0.67 ≤ b) (h : LeanLab.ChenDoubleSieve.ChenLower b) :
    Chen1973Quant :=
  LeanLab.ChenDoubleSieve.chenLower_mono hb h

/-- Chen's quantitative 1973 theorem implies the qualitative statement `chen1973`. -/
theorem chenAbove_of_chen1973Quant (h : Chen1973Quant) : ∃ T : ℝ, ChenAbove T :=
  LeanLab.ChenDoubleSieve.chenAbove_of_chenLower (by norm_num) h

/-! ### 2. Chen's switching, an exact bijection -/

/-- **Switching identity.** For any property `Q`, the primes `p < N` with `Q (N - p)` are in
bijection with the `m ∈ [1, N]` with `Q m` and `N - m` prime, by `p ↦ N - p`. This is the
bookkeeping behind replacing `#{p : N - p = p₁p₂p₃}` by a count over the set `B`. -/
theorem switching_card (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    #((range N).filter fun p => p.Prime ∧ Q (N - p)) =
      #((Icc 1 N).filter fun m => Q m ∧ (N - m).Prime) := by
  refine Finset.card_bij (fun p _ => N - p) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_range, mem_Icc] at hp ⊢
    obtain ⟨hpN, hp, hQ⟩ := hp
    refine ⟨⟨by omega, by omega⟩, hQ, ?_⟩
    rwa [Nat.sub_sub_self hpN.le]
  · intro a ha b hb hab
    simp only [mem_filter, mem_range] at ha hb
    omega
  · intro m hm
    simp only [mem_filter, mem_range, mem_Icc] at hm ⊢
    obtain ⟨⟨h1, h2⟩, hQ, hpr⟩ := hm
    refine ⟨N - m, ⟨by omega, hpr, ?_⟩, by omega⟩
    rwa [Nat.sub_sub_self h2]

/-- Vacuity check: at `N = 10` with `Q m := m = 7`, `10 - 7 = 3` is prime, so the left side
of `switching_card` is `1`, not `0`. -/
example : #((range 10).filter fun p => p.Prime ∧ (10 - p) = 7) = 1 := by decide

/-! ### 3. The Chen inequality at Chen's classical cut-off `z = N^{1/10}` -/

lemma rpow_1024_tenth : (1024 : ℝ) ^ ((1 : ℝ) / 10) = 2 := by
  rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **Chen's weighted inequality with `z = N^{1/10}`, `y = N^{1/3}`**, for `N ≥ 1024`:
`π₂(N) > S(A,P(z)) − ½ Σ_{z≤q<y, q∤N} S(A_q,P(z)) − ½ S(B,P(y)) − 2N^{9/10} − N^{1/3}`,
unconditional, from `ChenExplicit.chen_inequality`. -/
theorem chen_inequality_tenth (N : ℕ) (hN : 1024 ≤ N) :
    (SA N ((N : ℝ) ^ ((1 : ℝ) / 10)) : ℝ)
      - (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 10)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      - (SB N ((N : ℝ) ^ ((1 : ℝ) / 10)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      - 2 * (N : ℝ) ^ ((9 : ℝ) / 10) - (N : ℝ) ^ ((1 : ℝ) / 3) < chenCount N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [← rpow_1024_tenth]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
  have hy : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN0 _
  have hy3 : (N : ℝ) ≤ ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have h910 : 2 * (N : ℝ) ^ ((9 : ℝ) / 10) = 2 * N / (N : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [show (9 : ℝ) / 10 = 1 - 1 / 10 by norm_num, Real.rpow_sub hN0, Real.rpow_one,
      mul_div_assoc]
  rw [h910]
  exact chen_inequality N _ _ hz hy hy3

/-! ### 4. The limit constant of the switching method, `𝓕 = 2 log 3 − log 6 − c̄` -/

/-- `2 log 3 − log 6 = log (3/2)`. -/
lemma two_log3_sub_log6 : 2 * log 3 - log 6 = log 3 - log 2 := by
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h6]; ring

/-- **The limit margin is positive**: `0.0423 < 2 log 3 − log 6 − c̄ < 0.0425`, from
`c̄ < 0.363084` (BJS Lemma 52, PROVED in `BJSCbar`) and `c̄ > 0.3630`. True value ≈ 0.042381. -/
theorem limitMargin_bounds :
    0.0423 < 2 * log 3 - log 6 - BJS.cbar ∧ 2 * log 3 - log 6 - BJS.cbar < 0.0425 := by
  have hc1 := BJS.cbar_lt
  have hc2 := BJS.cbar_gt
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  rw [two_log3_sub_log6]
  constructor <;> norm_num at * <;> linarith

/-- **Conditional assembly**, in any unit `M`: if the three sieve inputs hold with slack `η`,
i.e. `S₁ ≥ (2 log 3 − η) M`, `½ S₂ ≤ (log 6 + η) M`, `½ S₃ ≤ (c̄ + η) M`, and the error
`E ≤ η M`, and Chen's inequality `π₂ > S₁ − ½S₂ − ½S₃ − E` holds, then
`π₂ > (0.0423 − 4η) M`. Pure algebra on top of `limitMargin_bounds`. -/
theorem assembly (M η S₁ S₂ S₃ E π₂ : ℝ)
    (hchen : S₁ - S₂ / 2 - S₃ / 2 - E < π₂)
    (h1 : (2 * log 3 - η) * M ≤ S₁) (h2 : S₂ / 2 ≤ (log 6 + η) * M)
    (h3 : S₃ / 2 ≤ (BJS.cbar + η) * M) (hE : E ≤ η * M) (hM : 0 ≤ M) :
    (0.0423 - 4 * η) * M < π₂ := by
  have := (limitMargin_bounds).1
  nlinarith

/-- The three named sieve inputs at `z = N^{1/8}`, `y = N^{1/3}`, with slack `η` and unit
`M N`, for all large even `N`: BJS Theorem 44 (lower bound for S(A,P(z))), Theorem 50
(upper bound for Σ S(A_q,P(z))) and Theorem 51 with Lemma 52 (upper bound for S(B,P(y))),
in their limit form, plus the error terms of Lemma 37. CITED INPUTS, not proved here. -/
def SieveLimits (M : ℕ → ℝ) (η : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    let z := (N : ℝ) ^ ((1 : ℝ) / 8)
    let y := (N : ℝ) ^ ((1 : ℝ) / 3)
    0 < M N ∧
    (2 * log 3 - η) * M N ≤ SA N z ∧
    (sumSAq N z y : ℝ) / 2 ≤ (log 6 + η) * M N ∧
    (SB N z y : ℝ) / 2 ≤ (BJS.cbar + η) * M N ∧
    2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3) ≤ η * M N

/-- **CONDITIONAL ON `SieveLimits M η`**: every large even `N` has
`chenCount N > (0.0423 − 4η) M N`, positive when `η < 0.0105`. Uses BJS Lemma 37 PROVED
in Bridge.lean and the PROVED margin. -/
theorem chenCount_lower_of_sieveLimits (M : ℕ → ℝ) (η : ℝ) (h : SieveLimits M η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → (0.0423 - 4 * η) * M N < chenCount N := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨max N₀ 256, fun N he hle => ?_⟩
  obtain ⟨hM, h1, h2, h3, hE⟩ := hN N he (le_of_max_le_left hle)
  have h37 := lemma37 N (le_of_max_le_right hle)
  exact assembly (M N) η _ _ _ (2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3)) _
    (by linarith) h1 h2 h3 hE hM.le

/-- **CONDITIONAL ON `SieveLimits M η`**, `η ≤ 0.01`: Chen's theorem, `∃ T, ChenAbove T`. -/
theorem chen_of_sieveLimits (M : ℕ → ℝ) (η : ℝ) (hη : η ≤ 0.01) (h : SieveLimits M η) :
    ∃ T : ℝ, ChenAbove T := by
  obtain ⟨N₁, hN₁⟩ := chenCount_lower_of_sieveLimits M η h
  obtain ⟨N₀, hN⟩ := h
  refine ⟨max N₀ N₁, fun N he hT => ?_⟩
  have hle0 : N₀ ≤ N := by exact_mod_cast (le_max_left _ _).trans hT.le
  have hle1 : N₁ ≤ N := by
    have : ((max N₀ N₁ : ℕ) : ℝ) < N := by exact_mod_cast hT
    exact_mod_cast (le_max_right N₀ N₁).trans (by exact_mod_cast this.le)
  have hM := (hN N he hle0).1
  have hc := hN₁ N he hle1
  have hpos : 0 < (chenCount N : ℝ) := by
    have : 0 ≤ (0.0423 - 4 * η) * M N := mul_nonneg (by linarith) hM.le
    linarith
  have hpos' : 0 < chenCount N := by exact_mod_cast hpos
  unfold chenCount at hpos'
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos'
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, N - p, hp.2.1, by omega, hp.2.2⟩

/-- Vacuity of `assembly`: the hypotheses are satisfiable, e.g. `M = 1`, `η = 0`,
`S₁ = 2 log 3`, `S₂ = 2 log 6`, `S₃ = 2 c̄`, `E = 0`, `π₂ = 1`. -/
example : (0.0423 - 4 * (0 : ℝ)) * 1 < 1 :=
  assembly 1 0 (2 * log 3) (2 * log 6) (2 * BJS.cbar) 0 1
    (by have := (limitMargin_bounds).2; linarith) (by simp) (by simp) (by simp) (by simp)
    (by norm_num)

end LeanLab.AlmostPrimeSums.Chen1973

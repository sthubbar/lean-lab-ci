/-
Li and Pan's density theorem through explicit profiles and their local corollary.
Sources: https://arxiv.org/abs/math/0701240v3 pages 7 to 12 and
https://arxiv.org/abs/1206.6139v2 page 1 Theorem 1.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408c
import LeanLab.DensityGoldbach.LiPanCor21

open Finset
open Filter Real
open scoped Classical

namespace LeanLab.DensityGoldbach.Decomp408e

noncomputable section

/-! ### Analytic inputs, in the shapes the profile uses -/

/-- `θ` as a sum over `range (N + 1)`. -/
private lemma chebyshev_theta_eq_sum (N : ℕ) :
    Chebyshev.theta (N : ℝ) = ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, sum_filter, sum_filter]
  exact LeanLab.HardyLittlewood1923.sum_Ioc_zero_eq_range _ (by simp) N

/-- `ψ(N; 1, 1)` is Chebyshev's `ψ`. -/
private lemma psi_one_one_eq (N : ℕ) :
    HeathBrown1985.psi (N : ℝ) 1 1 = Chebyshev.psi (N : ℝ) := by
  rw [LeanLab.HardyLittlewood1923.psi_eq_sum_gfun, Chebyshev.psi, Nat.floor_natCast,
    LeanLab.HardyLittlewood1923.sum_Ioc_zero_eq_range _ (by simp) N]
  refine sum_congr rfl fun m _ => ?_
  unfold LeanLab.HardyLittlewood1923.gfun
  rw [if_pos (by simp [Nat.mod_one])]

/-- `exp (-c √log x) → 0`. -/
private lemma tendsto_exp_neg_sqrt_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have h2 := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  exact h2.congr fun x => by simp [neg_mul]

/-- `log x · exp (-c √log x) → 0`. -/
private lemma log_mul_exp_decay {c : ℝ} (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ ε := by
  have h1 : Tendsto (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-c * u)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc
  have h2 : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_log_atTop
  have h3 : ∀ᶠ x : ℝ in atTop, (Real.sqrt (Real.log x)) ^ (2 : ℝ) *
      Real.exp (-c * Real.sqrt (Real.log x)) < ε := (h1.comp h2).eventually (gt_mem_nhds hε)
  refine (h3.and (eventually_ge_atTop (1 : ℝ))).mono ?_
  intro x hx
  obtain ⟨h4, h5⟩ := hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg h5
  rw [Real.rpow_two, Real.sq_sqrt hlog] at h4
  linarith [h4.le]

/-- `θ(N) ≥ (1 - η) N` eventually: the prime number theorem at `q = 1`, from Siegel-Walfisz. -/
private lemma theta_lower (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (1 - η) * (N : ℝ) ≤ ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.PsiChi.siegelWalfisz 1 one_pos
  have hlim := tendsto_exp_neg_sqrt_log hc
  have hE : ∀ᶠ N : ℕ in atTop,
      K * Real.exp (-c * Real.sqrt (Real.log N)) ≤ η / 2 := by
    have hpos : 0 < η / 2 / (|K| + 1) := by positivity
    have h3 := hlim.eventually (gt_mem_nhds hpos)
    refine (tendsto_natCast_atTop_atTop.eventually h3).mono fun N hN => ?_
    have h4 : K ≤ |K| + 1 := by linarith [le_abs_self K]
    have h5 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log N)) := (Real.exp_pos _).le
    have h6 : (|K| + 1) * Real.exp (-c * Real.sqrt (Real.log N)) ≤ η / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < |K| + 1)] at hN
      linarith
    nlinarith
  have hlog : ∀ᶠ N : ℕ in atTop, Real.log N ≤ η / 8 * (N : ℝ) ^ ((1 : ℝ) / 2) :=
    LeanLab.HardyLittlewood1923.eventually_log_le (η / 8) (1 / 2) (by positivity) (by norm_num)
  have hge : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N := by
    have h1 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
      tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
    exact tendsto_natCast_atTop_atTop.eventually h1
  refine (hE.and (hlog.and (hge.and hlog1))).mono ?_
  intro N hN
  obtain ⟨hE', hlog', hge', hlog1'⟩ := hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hge'
  have hSW := hK (N : ℝ) hN2 1 1 le_rfl (Nat.coprime_one_left 1) (by simpa using hlog1')
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hSW
  rw [psi_one_one_eq] at hSW
  rw [abs_le] at hSW
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have h1 : Real.log (N : ℝ) ≤ η / 8 * Real.sqrt (N : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using hlog'
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
  have hpt : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ η / 4 * (N : ℝ) := by
    nlinarith [hsqrt0, hN0]
  have hsub : Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) ≤
      2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
    Chebyshev.psi_sub_theta_le (by linarith)
  rw [← chebyshev_theta_eq_sum]
  nlinarith

/-- Chebyshev `ψ` as a range sum. -/
private lemma psi_range (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ∑ n ∈ range (N + 1), ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  exact LeanLab.HardyLittlewood1923.sum_Ioc_zero_eq_range _ (by simp) N

/-! ### The per-class cap `f ≤ 1` -/

/-- Sum of `log p` over the primes of a fixed residue class with `3p < 2N` is at most `ψ`. -/
private lemma primeClassSum_le_psi (W a N : ℕ) (hW : 0 < W) :
    ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * N),
        Real.log p ≤
      HeathBrown1985.psi ((2 * N / 3 : ℕ) : ℝ) W a := by
  rw [LeanLab.HardyLittlewood1923.psi_eq_sum_gfun]
  set S := (range (N + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * N) with hS
  have hstep : ∑ p ∈ S, Real.log p =
      ∑ p ∈ S, LeanLab.HardyLittlewood1923.gfun W a p := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter, mem_range] at hp
    unfold LeanLab.HardyLittlewood1923.gfun
    rw [if_pos hp.2.2.1, ArithmeticFunction.vonMangoldt_apply_prime hp.2.1]
  rw [hstep]
  refine sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨-, hpp, -, hlt⟩ := hp
    rw [mem_range]
    have hple : p ≤ 2 * N / 3 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
    omega
  · intro p _ _
    unfold LeanLab.HardyLittlewood1923.gfun
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- Siegel-Walfisz: `ψ(N; W, a) ≤ N/φ(W) + K N exp(-c √log N)` eventually. -/
private lemma psi_ap_upper (W a : ℕ) (hW : 1 ≤ W) (ha : Nat.Coprime a W) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      HeathBrown1985.psi (N : ℝ) W a ≤
        (N : ℝ) / (Nat.totient W : ℝ) +
          K * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.PsiChi.siegelWalfisz 1 one_pos
  refine ⟨c, hc, max K 0, le_max_right _ _, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, (W : ℝ) ≤ Real.log N := by
    have h1 : ∀ᶠ x : ℝ in atTop, (W : ℝ) ≤ Real.log x :=
      tendsto_log_atTop.eventually_ge_atTop (W : ℝ)
    exact tendsto_natCast_atTop_atTop.eventually h1
  have hge : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  refine (hlog.and hge).mono ?_
  intro N hN
  obtain ⟨hlog', hge'⟩ := hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hge'
  have hSW := hK (N : ℝ) hN2 W a hW ha (by rwa [Real.rpow_one])
  rw [abs_le] at hSW
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hKle : K ≤ max K 0 := le_max_left _ _
  have hE0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log N)) := (Real.exp_pos _).le
  have hmono : K * Real.exp (-c * Real.sqrt (Real.log N)) ≤
      max K 0 * Real.exp (-c * Real.sqrt (Real.log N)) :=
    mul_le_mul_of_nonneg_right hKle hE0
  nlinarith


/-- `Σ log p` over the primes of one reduced class with `3p < 2N` is at most
`2N/(3φ(W))` plus a Siegel-Walfisz error, the error still evaluated at `X = ⌊2N/3⌋`. -/
private lemma class_sum_le (W a : ℕ) (hW : 1 ≤ W) (ha : Nat.Coprime a W) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * N),
          Real.log p ≤
        (2 * (N : ℝ) / 3) / (Nat.totient W : ℝ) +
          K * (2 * (N : ℝ) / 3) *
            Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) := by
  obtain ⟨c, hc, K, hK0, hK⟩ := psi_ap_upper W a hW ha
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hK
  refine ⟨c, hc, K, hK0, ?_⟩
  have hXle : ∀ N : ℕ, ((2 * N / 3 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / 3 := by
    intro N
    have h := Nat.div_mul_le_self (2 * N) 3
    have h3 : ((2 * N / 3 : ℕ) : ℝ) * 3 ≤ 2 * (N : ℝ) := by exact_mod_cast h
    linarith
  refine (eventually_ge_atTop (max (3 * N₀ + 1) 3)).mono ?_
  intro N hN
  have h1 : HeathBrown1985.psi ((2 * N / 3 : ℕ) : ℝ) W a ≤
      ((2 * N / 3 : ℕ) : ℝ) / (Nat.totient W : ℝ) +
        K * ((2 * N / 3 : ℕ) : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) := by
    refine hN₀ (2 * N / 3) ?_
    omega
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * N),
        Real.log p
      ≤ HeathBrown1985.psi ((2 * N / 3 : ℕ) : ℝ) W a := primeClassSum_le_psi W a N (by omega)
    _ ≤ ((2 * N / 3 : ℕ) : ℝ) / (Nat.totient W : ℝ) +
          K * ((2 * N / 3 : ℕ) : ℝ) *
            Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) := h1
    _ ≤ (2 * (N : ℝ) / 3) / (Nat.totient W : ℝ) +
          K * (2 * (N : ℝ) / 3) *
            Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) := by
        have hΦ0 : (0 : ℝ) < (Nat.totient W : ℝ) := by
          have h := Nat.totient_pos.2 (by omega : 0 < W)
          exact_mod_cast h
        have hA : ((2 * N / 3 : ℕ) : ℝ) / (Nat.totient W : ℝ) ≤
            (2 * (N : ℝ) / 3) / (Nat.totient W : ℝ) := by gcongr; exact hXle N
        have hB : K * ((2 * N / 3 : ℕ) : ℝ) *
            Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) ≤
            K * (2 * (N : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) := by
          have hE : 0 ≤ Real.exp (-c * Real.sqrt (Real.log ((2 * N / 3 : ℕ) : ℝ))) :=
            (Real.exp_pos _).le
          have h3 : K * ((2 * N / 3 : ℕ) : ℝ) ≤ K * (2 * (N : ℝ) / 3) := by
            have h4 : (0:ℝ) ≤ K := hK0
            nlinarith [hXle N]
          exact mul_le_mul_of_nonneg_right h3 hE
        linarith

/-! ### Bounds on the relative density -/

/-- The relative density is nonnegative. -/
private lemma relRatio_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ relRatio A N := by
  classical
  unfold relRatio; positivity

/-- The relative density is never above `1`. -/
private lemma relRatio_le_one (A : Set ℕ) (N : ℕ) : relRatio A N ≤ 1 := by
  classical
  unfold relRatio
  rcases Nat.eq_zero_or_pos #{n ∈ Icc 1 N | n.Prime} with h | h
  · rw [h]; norm_num
  · have h1 : #{n ∈ Icc 1 N | n ∈ A ∧ n.Prime} ≤ #{n ∈ Icc 1 N | n.Prime} := by
      refine card_le_card ?_
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.2⟩
    have h3 : (0 : ℝ) < (#{n ∈ Icc 1 N | n.Prime} : ℝ) := by exact_mod_cast h
    rw [div_le_one h3]
    exact_mod_cast h1

/-- The lower density is at most `1`. -/
private lemma lowerDensity_le_one (A : Set ℕ) : lowerDensity A ≤ 1 := by
  have hb : IsBoundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop (relRatio A) :=
    isBoundedUnder_of ⟨0, fun N => relRatio_nonneg A N⟩
  have hc : IsCoboundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop (relRatio A) := by
    refine ⟨1, fun a ha => ?_⟩
    have h2 : ∀ᶠ x : ℝ in Filter.map (relRatio A) atTop, x ≤ 1 := by
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun N => relRatio_le_one A N
    obtain ⟨x, h1, h3⟩ := (ha.and h2).exists
    linarith
  refine (Filter.liminf_le_iff (f := atTop) (u := relRatio A) (x := 1) hc hb).2 ?_
  intro y hy
  exact (Filter.Eventually.of_forall fun N => lt_of_le_of_lt (relRatio_le_one A N) hy).frequently

private lemma count_Icc_range (A : Set ℕ) (N : ℕ) :
    #{n ∈ Icc 1 N | n ∈ A ∧ n.Prime} =
      ((range (N + 1)).filter (fun p => p.Prime ∧ p ∈ A)).card := by
  classical
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3.2, h3.1⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h3.1.pos, by omega⟩, h3.2, h3.1⟩

private lemma prime_Icc_range (N : ℕ) :
    #{n ∈ Icc 1 N | n.Prime} = ((range (N + 1)).filter Nat.Prime).card := by
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h3.pos, by omega⟩, h3⟩

/-- The lower density gives an asymptotic lower bound on the count of primes of `A`. -/
private lemma count_eventually (A : Set ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (lowerDensity A - η) * (((range (N + 1)).filter Nat.Prime).card : ℝ) ≤
        (((range (N + 1)).filter (fun p => p.Prime ∧ p ∈ A)).card : ℝ) := by
  classical
  have hb : IsBoundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop (relRatio A) :=
    isBoundedUnder_of ⟨0, fun N => relRatio_nonneg A N⟩
  have hc : IsCoboundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop (relRatio A) := by
    refine ⟨1, fun a ha => ?_⟩
    have h2 : ∀ᶠ x : ℝ in Filter.map (relRatio A) atTop, x ≤ 1 := by
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun N => relRatio_le_one A N
    obtain ⟨x, h1, h3⟩ := (ha.and h2).exists
    linarith
  have h := (Filter.le_liminf_iff (f := atTop) (u := relRatio A) (x := lowerDensity A) hc hb).1
    le_rfl (lowerDensity A - η) (by linarith)
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < (#{n ∈ Icc 1 N | n.Prime} : ℝ) := by
    refine (eventually_ge_atTop 2).mono fun N hN => ?_
    have h2 : 2 ∈ ({n ∈ Icc 1 N | n.Prime} : Finset ℕ) := by
      simp only [mem_filter, mem_Icc, Nat.prime_two, and_true]; omega
    exact_mod_cast Finset.card_pos.2 ⟨2, h2⟩
  refine (h.and hpos).mono ?_
  intro N hN
  obtain ⟨h1, h2⟩ := hN
  have h4 : relRatio A N * (#{n ∈ Icc 1 N | n.Prime} : ℝ) =
      (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime} : ℝ) := by
    unfold relRatio; field_simp
  have h3 : (lowerDensity A - η) * (#{n ∈ Icc 1 N | n.Prime} : ℝ) <
      (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime} : ℝ) := by
    have := mul_lt_mul_of_pos_right h1 h2
    rw [h4] at this
    exact this
  rw [count_Icc_range, prime_Icc_range] at h3
  exact h3.le

/-- `X ^ (1 - α) log X` and `log X` are `o(X)`, in the explicit form needed below. -/
private lemma log_mul_rpow_small {α ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) * ((X : ℝ) ^ (1 - α) + 1) ≤ ε / 4 * (X : ℝ) := by
  have hlog_le : ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) ≤ (X : ℝ) ^ (α / 2) := by
    have h := LeanLab.HardyLittlewood1923.eventually_log_le 1 (α / 2) one_pos (by linarith)
    simpa using h
  have hrpow : ∀ᶠ X : ℕ in atTop, (8 : ℝ) / ε ≤ (X : ℝ) ^ (α / 2) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (α / 2)) atTop atTop :=
      tendsto_rpow_atTop (by linarith : (0 : ℝ) < α / 2)
    exact tendsto_natCast_atTop_atTop.eventually (h1.eventually_ge_atTop (8 / ε))
  refine (hlog_le.and (hrpow.and (eventually_ge_atTop 2))).mono ?_
  intro X hX
  obtain ⟨h1, h2, h3⟩ := hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hApos : 0 < (X : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hX0 _
  have hBpos : 0 ≤ (X : ℝ) ^ (1 - α) := Real.rpow_nonneg hX0.le _
  -- `X ^ (1 - α / 2) ≤ ε / 8 * X`
  have hA : (X : ℝ) ^ (1 - α / 2) ≤ ε / 8 * (X : ℝ) := by
    have h4 : (X : ℝ) ^ (1 - α / 2) = (X : ℝ) * (X : ℝ) ^ (-(α / 2)) := by
      have h := Real.rpow_add hX0 (1 : ℝ) (-(α / 2))
      rw [Real.rpow_one] at h
      rw [← h]
      ring_nf
    have h5 : (X : ℝ) ^ (-(α / 2)) ≤ ε / 8 := by
      rw [Real.rpow_neg hX0.le, ← one_div]
      rw [div_le_iff₀ hApos]
      have h8 : ε * (8 / ε) = 8 := by field_simp
      nlinarith [h2, hε, hApos]
    rw [h4]
    calc (X : ℝ) * (X : ℝ) ^ (-(α / 2)) ≤ (X : ℝ) * (ε / 8) :=
          mul_le_mul_of_nonneg_left h5 hX0.le
      _ = ε / 8 * (X : ℝ) := by ring
  -- `X ^ (α / 2) ≤ ε / 8 * X`
  have hB : (X : ℝ) ^ (α / 2) ≤ ε / 8 * (X : ℝ) := by
    refine le_trans ?_ hA
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : α / 2 ≤ 1 - α / 2)
  -- combine
  have hD : (X : ℝ) ^ (α / 2) * (X : ℝ) ^ (1 - α) = (X : ℝ) ^ (1 - α / 2) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  have h1' : Real.log (X : ℝ) * (X : ℝ) ^ (1 - α) ≤ (X : ℝ) ^ (α / 2) * (X : ℝ) ^ (1 - α) :=
    mul_le_mul_of_nonneg_right h1 hBpos
  have hexp : Real.log (X : ℝ) * ((X : ℝ) ^ (1 - α) + 1) =
      Real.log (X : ℝ) * (X : ℝ) ^ (1 - α) + Real.log (X : ℝ) := by ring
  rw [hexp]
  linarith [h1', hD, hA, hB]

set_option maxHeartbeats 1000000 in
/-- The log-mass of the primes of `A` up to `X` is at least `(d - ε) X`, `d` the relative
lower density: split at `Y = ⌊X^(1-α)⌋`, at most `Y + 1` primes lie below the split, and every
prime above it has log at least `(1 - α) log X`. -/
private lemma set_mass_lower (A : Set ℕ) (hA : A ⊆ P) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (lowerDensity A - ε) * (X : ℝ) ≤
        ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A), Real.log p := by
  classical
  by_cases hbig : 1 ≤ ε
  · refine Filter.Eventually.of_forall fun X => ?_
    have hd1 : lowerDensity A ≤ 1 := lowerDensity_le_one A
    have hnn : 0 ≤ ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A), Real.log p :=
      sum_nonneg fun p _ => Real.log_natCast_nonneg p
    have h2 : (lowerDensity A - ε) * (X : ℝ) ≤ 0 := by
      have h3 : lowerDensity A - ε ≤ 0 := by linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) X]
    linarith
  push Not at hbig
  by_cases hsmall : lowerDensity A ≤ ε
  · refine Filter.Eventually.of_forall fun X => ?_
    have hnn : 0 ≤ ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A), Real.log p :=
      sum_nonneg fun p _ => Real.log_natCast_nonneg p
    have h2 : (lowerDensity A - ε) * (X : ℝ) ≤ 0 := by
      have h3 : lowerDensity A - ε ≤ 0 := by linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) X]
    linarith
  push Not at hsmall
  set d := lowerDensity A with hddef
  set α : ℝ := ε / 16 with hαdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hcount := count_eventually A (ε / 8) (by linarith)
  have htheta := theta_lower (ε / 8) (by linarith)
  have hsmall' := log_mul_rpow_small (α := α) (ε := ε) hα0 hα1 hε
  refine (hcount.and (htheta.and (hsmall'.and (eventually_ge_atTop 4)))).mono ?_
  intro X hX
  obtain ⟨hcX, hθX, hsm, hX4⟩ := hX
  set Y : ℕ := ⌊(X : ℝ) ^ (1 - α)⌋₊ with hYdef
  set SA : Finset ℕ := (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A) with hSAdef
  set PL : Finset ℕ := (range (X + 1)).filter Nat.Prime with hPLdef
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hpowpos : (0 : ℝ) < (X : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    apply Real.log_pos
    have h5 : 1 < X := by omega
    exact_mod_cast h5
  have hθle : ∑ p ∈ PL, Real.log p ≤ (PL.card : ℝ) * Real.log (X : ℝ) := by
    calc ∑ p ∈ PL, Real.log p ≤ ∑ _p ∈ PL, Real.log (X : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [hPLdef, mem_filter, mem_range] at hp
          exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast (by omega : p ≤ X))
      _ = (PL.card : ℝ) * Real.log (X : ℝ) := by rw [sum_const, nsmul_eq_mul]
  have hm : (1 - ε / 8) * (X : ℝ) ≤ (PL.card : ℝ) * Real.log (X : ℝ) := by
    refine le_trans ?_ hθle
    rw [hPLdef]; exact hθX
  have hj : (d - ε / 8) * (PL.card : ℝ) ≤ (SA.card : ℝ) := by
    rw [hPLdef, hSAdef]; exact hcX
  have hj0 : 0 ≤ (SA.card : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (PL.card : ℝ) := Nat.cast_nonneg _
  -- split the primes of `A` at `Y`
  have hsplit : ((SA.card : ℝ)) = (((SA.filter (fun p => Y < p)).card : ℝ)) +
      ((({a ∈ SA | ¬ Y < a}).card : ℝ)) := by
    have h1 := Finset.card_filter_add_card_filter_not (s := SA) (fun p => Y < p)
    rw [← h1]; push_cast; ring
  have hlow_le : (({a ∈ SA | ¬ Y < a}).card : ℝ) ≤ (Y : ℝ) + 1 := by
    have h1 : ({a ∈ SA | ¬ Y < a}) ⊆ range (Y + 1) := by
      intro p hp
      rw [mem_filter, hSAdef, mem_filter, mem_range] at hp
      obtain ⟨⟨hp1, -⟩, hp2⟩ := hp
      rw [mem_range]; omega
    have h2 : ({a ∈ SA | ¬ Y < a}).card ≤ Y + 1 := by
      calc _ ≤ (range (Y + 1)).card := card_le_card h1
        _ = Y + 1 := card_range _
    exact_mod_cast h2
  have hhigh : (SA.card : ℝ) - ((Y : ℝ) + 1) ≤ ((SA.filter (fun p => Y < p)).card : ℝ) := by
    linarith
  -- logs of the primes above the split
  have hlogY : ((1 - α) * Real.log (X : ℝ)) ≤ Real.log ((Y : ℝ) + 1) := by
    have h1 : Real.log ((X : ℝ) ^ (1 - α)) = (1 - α) * Real.log (X : ℝ) := Real.log_rpow hX0 _
    rw [← h1]
    refine Real.log_le_log hpowpos ?_
    have h2 : (X : ℝ) ^ (1 - α) < (Y : ℝ) + 1 := by
      have h3 := Nat.lt_floor_add_one ((X : ℝ) ^ (1 - α))
      rw [← hYdef] at h3
      exact h3
    linarith
  have hsum_high : ((1 - α) * Real.log (X : ℝ)) * ((SA.card : ℝ) - ((Y : ℝ) + 1)) ≤
      ∑ p ∈ SA, Real.log p := by
    have hlogY1 : 0 ≤ Real.log ((Y : ℝ) + 1) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact Real.log_natCast_nonneg (Y + 1)
    have h1 : ((1 - α) * Real.log (X : ℝ)) * ((SA.card : ℝ) - ((Y : ℝ) + 1)) ≤
        Real.log ((Y : ℝ) + 1) * ((SA.filter (fun p => Y < p)).card : ℝ) := by
      have hA1 : 0 ≤ (1 - α) * Real.log (X : ℝ) := by positivity
      rcases le_total 0 ((SA.card : ℝ) - ((Y : ℝ) + 1)) with hnn | hneg
      · exact mul_le_mul hlogY hhigh hnn hlogY1
      · have h4 : ((1 - α) * Real.log (X : ℝ)) * ((SA.card : ℝ) - ((Y : ℝ) + 1)) ≤ 0 := by
          nlinarith
        have h5 : 0 ≤ Real.log ((Y : ℝ) + 1) * ((SA.filter (fun p => Y < p)).card : ℝ) := by
          positivity
        linarith
    have h2 : Real.log ((Y : ℝ) + 1) * ((SA.filter (fun p => Y < p)).card : ℝ) ≤
        ∑ p ∈ SA.filter (fun p => Y < p), Real.log p := by
      calc Real.log ((Y : ℝ) + 1) * ((SA.filter (fun p => Y < p)).card : ℝ)
          = ∑ _p ∈ SA.filter (fun p => Y < p), Real.log ((Y : ℝ) + 1) := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ p ∈ SA.filter (fun p => Y < p), Real.log p := by
            refine sum_le_sum fun p hp => ?_
            rw [mem_filter] at hp
            have h3 : Y < p := hp.2
            have h5 : Y + 1 ≤ p := by omega
            have h4 : ((Y : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast h5
            have h6 : (0 : ℝ) < (Y : ℝ) + 1 := by positivity
            exact Real.log_le_log h6 h4
    have h3 : ∑ p ∈ SA.filter (fun p => Y < p), Real.log p ≤ ∑ p ∈ SA, Real.log p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => Real.log_natCast_nonneg p
    linarith
  -- the loss at the split
  have hloss : Real.log (X : ℝ) * ((Y : ℝ) + 1) ≤ ε / 4 * (X : ℝ) := by
    have h1 : (Y : ℝ) + 1 ≤ (X : ℝ) ^ (1 - α) + 1 := by
      have h2 : (Y : ℝ) ≤ (X : ℝ) ^ (1 - α) := by
        rw [hYdef]; exact Nat.floor_le hpowpos.le
      linarith
    have h2 : Real.log (X : ℝ) * ((Y : ℝ) + 1) ≤
        Real.log (X : ℝ) * ((X : ℝ) ^ (1 - α) + 1) :=
      mul_le_mul_of_nonneg_left h1 hlogXpos.le
    linarith
  -- the gain is more than `(1 - α) log X` times the reduced-class mass
  have hstep : ((1 - α) * Real.log (X : ℝ)) * ((SA.card : ℝ) - ((Y : ℝ) + 1)) ≥
      (1 - α) * ((d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ))) -
        Real.log (X : ℝ) * ((Y : ℝ) + 1) := by
    have hA1 : 0 ≤ (1 - α) * Real.log (X : ℝ) := by positivity
    have h1 : (SA.card : ℝ) - ((Y : ℝ) + 1) ≥ (d - ε / 8) * (PL.card : ℝ) - ((Y : ℝ) + 1) := by
      linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hA1
    have h4 : (1 - α) * Real.log (X : ℝ) *
          ((d - ε / 8) * (PL.card : ℝ) - ((Y : ℝ) + 1)) =
        (1 - α) * ((d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ))) -
          (1 - α) * Real.log (X : ℝ) * ((Y : ℝ) + 1) := by ring
    have h5 : (1 - α) * Real.log (X : ℝ) * ((Y : ℝ) + 1) ≤
        Real.log (X : ℝ) * ((Y : ℝ) + 1) := by
      have h6 : 0 ≤ Real.log (X : ℝ) * ((Y : ℝ) + 1) := by positivity
      nlinarith
    linarith
  -- the coefficient bound `(1 - α)(d - ε/8)(1 - ε/8) ≥ d - 3ε/4`
  have hcoef : d - 3 * ε / 4 ≤ (1 - α) * ((d - ε / 8) * (1 - ε / 8)) := by
    have hd1 : d ≤ 1 := lowerDensity_le_one A
    have hA2 : 0 ≤ d - ε / 8 := by linarith
    have hB2 : 0 ≤ 1 - ε / 8 := by linarith
    have hx1 : d - ε / 4 ≤ (d - ε / 8) * (1 - ε / 8) := by nlinarith
    have hx2 : d - ε / 4 - α ≤ (1 - α) * (d - ε / 4) := by nlinarith
    have hx3 : (1 - α) * (d - ε / 4) ≤ (1 - α) * ((d - ε / 8) * (1 - ε / 8)) :=
      mul_le_mul_of_nonneg_left hx1 (by linarith : (0 : ℝ) ≤ 1 - α)
    have hx4 : d - 3 * ε / 4 ≤ d - ε / 4 - α := by
      rw [hαdef]; linarith
    linarith
  have hkey : (d - 3 * ε / 4) * (X : ℝ) ≤
      (1 - α) * ((d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ))) := by
    have hd1 : d ≤ 1 := lowerDensity_le_one A
    have hA2 : 0 ≤ d - ε / 8 := by linarith
    have h1e : (1 - ε / 8) * (X : ℝ) ≤ (PL.card : ℝ) * Real.log (X : ℝ) := hm
    have h2e : (d - ε / 8) * ((1 - ε / 8) * (X : ℝ)) ≤
        (d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left h1e hA2
    have h3e : (1 - α) * ((d - ε / 8) * ((1 - ε / 8) * (X : ℝ))) ≤
        (1 - α) * ((d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_left h2e (by linarith : (0 : ℝ) ≤ 1 - α)
    calc (d - 3 * ε / 4) * (X : ℝ)
        ≤ ((1 - α) * ((d - ε / 8) * (1 - ε / 8))) * (X : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef hX0.le
      _ = (1 - α) * ((d - ε / 8) * ((1 - ε / 8) * (X : ℝ))) := by ring
      _ ≤ (1 - α) * ((d - ε / 8) * ((PL.card : ℝ) * Real.log (X : ℝ))) := h3e
  have hfin : (d - ε) * (X : ℝ) ≤ ∑ p ∈ SA, Real.log p := by
    linarith [hsum_high, hstep, hloss, hkey]
  exact hfin


/-! ### The per-class cap `f ≤ 1` -/

/-- The profile sum over one reduced class is at most `2n` after multiplying by `3φ(W)`. -/
private lemma class_cap_coprime (W : ℕ) (hW : 1 ≤ W) (a : ℕ) (ha : Nat.Coprime a W)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      3 * (Nat.totient W : ℝ) *
        (∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * n),
          (Real.log p - δ / 8)) ≤ 2 * n := by
  classical
  obtain ⟨c, hc, K, hK0, hK⟩ := class_sum_le W a hW ha
  set Φ : ℝ := (Nat.totient W : ℝ) with hΦdef
  have hΦ0 : 0 < Φ := by
    rw [hΦdef]; exact_mod_cast Nat.totient_pos.2 (by omega)
  have hXtend : Tendsto (fun n : ℕ => ((2 * n / 3 : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨3 * ⌈b⌉₊ + 2, fun n hn => ?_⟩
    have h2 : ⌈b⌉₊ ≤ 2 * n / 3 := by omega
    have h3 : b ≤ ((⌈b⌉₊ : ℕ) : ℝ) := Nat.le_ceil b
    have h4 : ((⌈b⌉₊ : ℕ) : ℝ) ≤ ((2 * n / 3 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hdec : ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) *
        Real.log ((2 * n / 3 : ℕ) : ℝ) ≤ δ / (8 * Φ * (K + 1)) := by
    have h := log_mul_exp_decay (c := c) hc (δ / (8 * Φ * (K + 1))) (by positivity)
    simpa [mul_comm] using hXtend.eventually h
  refine (hK.and (hdec.and (eventually_ge_atTop 3))).mono ?_
  intro n hn
  obtain ⟨h1, h2, h3⟩ := hn
  set X : ℕ := 2 * n / 3 with hXdef
  set S : Finset ℕ := (range (n + 1)).filter
    (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * n) with hSdef
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hX1 : 1 < X := by omega
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    apply Real.log_pos; exact_mod_cast hX1
  have hlogXn : Real.log (X : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by positivity)
    have h5 : X ≤ n := by omega
    exact_mod_cast h5
  set P : ℝ := ∑ p ∈ S, Real.log p with hPdef
  set k : ℝ := (S.card : ℝ) with hkdef
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hsplit : ∑ p ∈ S, (Real.log p - δ / 8) = P - k * (δ / 8) := by
    rw [hPdef, hkdef, sum_sub_distrib, sum_const, nsmul_eq_mul]
  rw [hsplit]
  have hEpos : 0 ≤ Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) :=
    (Real.exp_pos _).le
  have htrivP : P ≤ k * Real.log (X : ℝ) := by
    rw [hPdef]
    calc ∑ p ∈ S, Real.log p ≤ ∑ _p ∈ S, Real.log (X : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [hSdef, mem_filter, mem_range] at hp
          obtain ⟨-, hpp, -, hlt⟩ := hp
          have hpX : p ≤ X := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
          exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpX)
      _ = k * Real.log (X : ℝ) := by rw [sum_const, nsmul_eq_mul]
  have hpsiP : P ≤ (2 * (n : ℝ) / 3) / Φ +
      K * (2 * (n : ℝ) / 3) * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by
    rw [hPdef, hSdef]; exact h1
  rcases le_total (k * Real.log (X : ℝ)) (2 * (n : ℝ) / 3 / Φ) with hcase | hcase
  · -- few primes in the class
    have hPle : P ≤ 2 * (n : ℝ) / 3 / Φ := le_trans htrivP hcase
    have h5 : 3 * Φ * P ≤ 2 * n := by
      have h6 : 3 * Φ * P ≤ 3 * Φ * (2 * (n : ℝ) / 3 / Φ) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
      have h7 : 3 * Φ * (2 * (n : ℝ) / 3 / Φ) = 2 * n := by field_simp
      linarith
    have h8 : 0 ≤ k * (δ / 8) := by positivity
    nlinarith [hΦ0]
  · -- many primes in the class: the sharp bound plus the count gain
    have hk_lower : (2 * (n : ℝ) / 3 / Φ) / Real.log (X : ℝ) ≤ k := by
      rw [div_le_iff₀ hlogXpos]
      exact hcase
    have hgain : δ * (n : ℝ) / (4 * Real.log (X : ℝ)) ≤ (3 * Φ * δ / 8) * k := by
      have h5 : (0 : ℝ) ≤ 3 * Φ * δ / 8 := by positivity
      have h6 := mul_le_mul_of_nonneg_left hk_lower h5
      have h7 : 3 * Φ * δ / 8 * ((2 * (n : ℝ) / 3 / Φ) / Real.log (X : ℝ)) =
          δ * (n : ℝ) / (4 * Real.log (X : ℝ)) := by
        field_simp
        ring
      linarith
    have hElog : Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) * Real.log (X : ℝ) ≤
        δ / (8 * Φ * (K + 1)) := by
      have h7 : X = 2 * n / 3 := hXdef
      rw [h7]
      exact h2
    have hE : 2 * Φ * K * (n : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) ≤
        δ * (n : ℝ) / (4 * Real.log (X : ℝ)) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (X : ℝ))]
      have h3' : 2 * Φ * K * (Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) *
          Real.log (X : ℝ)) ≤ 2 * Φ * K * (δ / (8 * Φ * (K + 1))) :=
        mul_le_mul_of_nonneg_left hElog (by positivity)
      have h4' : 2 * Φ * K * (δ / (8 * Φ * (K + 1))) ≤ δ / 4 := by
        have h6 : K / (K + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h7 : 2 * Φ * K * (δ / (8 * Φ * (K + 1))) = δ * (K / (K + 1)) / 4 := by
          field_simp
          ring
        rw [h7]
        nlinarith
      nlinarith [h3', h4', hn0]
    have h9 : 3 * Φ * P ≤ 2 * n +
        2 * Φ * K * (n : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by
      have h10 : 3 * Φ * ((2 * (n : ℝ) / 3) / Φ) = 2 * n := by field_simp
      nlinarith [hpsiP, hΦ0]
    have h13 : (3 * Φ * δ / 8) * k = 3 * Φ * (k * (δ / 8)) := by ring
    have h12 : 3 * Φ * (P - k * (δ / 8)) = 3 * Φ * P - 3 * Φ * (k * (δ / 8)) := by ring
    linarith [h9, hE, hgain, h12, h13]


/-! ### The non-reduced classes -/

/-- A prime congruent to a non-reduced residue mod `W` divides `W`. -/
private lemma prime_dvd_of_modEq_not_coprime {p W a : ℕ} (hp : p.Prime)
    (hmod : p % W = a % W) (hc : ¬ Nat.Coprime a W) (hW : 0 < W) : p ∣ W := by
  set g := Nat.gcd a W with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a W
  have hgW : g ∣ W := Nat.gcd_dvd_right a W
  have hg1 : g ≠ 1 := fun h1 => hc (Nat.coprime_iff_gcd_eq_one.mpr h1)
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgW hW
  have hg2 : 2 ≤ g := by omega
  have hmod' : p ≡ a [MOD W] := by rw [Nat.ModEq]; exact hmod
  have hmodg : p ≡ a [MOD g] := hmod'.of_dvd hgW
  have haz : a ≡ 0 [MOD g] := Nat.modEq_zero_iff_dvd.mpr hga
  have hpz : p ≡ 0 [MOD g] := hmodg.trans haz
  have hgp : g ∣ p := Nat.modEq_zero_iff_dvd.mp hpz
  rcases (Nat.dvd_prime hp).mp hgp with h1 | h1
  · exact absurd h1 hg1
  · rw [← h1]; exact hgW

/-- The profile sum over a non-reduced class is at most `2n` after multiplying by `3φ(W)`. -/
private lemma class_cap_noncoprime (W : ℕ) (hW : 0 < W) (z : ℕ) (hWz : W = primorial z)
    (a : ℕ) (ha : ¬ Nat.Coprime a W) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      3 * (Nat.totient W : ℝ) *
        (∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * n),
          (Real.log p - δ / 8)) ≤ 2 * n := by
  classical
  have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_natCast_nonneg z
  have hkey : ∀ᶠ n : ℕ in atTop,
      3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) ≤ 2 * n := by
    refine (Filter.eventually_ge_atTop (⌈3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) / 2⌉₊ + 1)).mono ?_
    intro n hn
    have h1 : 3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) / 2 ≤
        (⌈3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) / 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) / 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : ⌈3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) / 2⌉₊ ≤ n)
    linarith
  refine hkey.mono ?_
  intro n hn
  set S : Finset ℕ := (range (n + 1)).filter
    (fun p => p.Prime ∧ p % W = a % W ∧ 3 * p < 2 * n) with hSdef
  -- all elements of `S` are equal
  have hsingle : ∀ p ∈ S, ∀ q ∈ S, p = q := by
    intro p hp q hq
    rw [hSdef, mem_filter, mem_range] at hp hq
    obtain ⟨-, hpp, hpmod, -⟩ := hp
    obtain ⟨-, hqp, hqmod, -⟩ := hq
    have hpd := prime_dvd_of_modEq_not_coprime hpp hpmod ha hW
    have hqd := prime_dvd_of_modEq_not_coprime hqp hqmod ha hW
    have hple : p ≤ W := Nat.le_of_dvd hW hpd
    have hqle : q ≤ W := Nat.le_of_dvd hW hqd
    rcases lt_or_eq_of_le hple with hplt | hpe
    · have hpval : p % W = p := Nat.mod_eq_of_lt hplt
      rw [hpval] at hpmod
      rcases lt_or_eq_of_le hqle with hqlt | hqe
      · rw [Nat.mod_eq_of_lt hqlt] at hqmod
        rw [← hpmod] at hqmod
        exact hqmod.symm
      · rw [hqe, Nat.mod_self] at hqmod
        rw [← hqmod] at hpmod
        rw [hpmod] at hpp
        exact absurd hpp Nat.not_prime_zero
    · rw [hpe, Nat.mod_self] at hpmod
      have ha0 : a % W = 0 := hpmod.symm
      rcases lt_or_eq_of_le hqle with hqlt | hqe
      · rw [Nat.mod_eq_of_lt hqlt, ha0] at hqmod
        rw [hqmod] at hqp
        exact absurd hqp Nat.not_prime_zero
      · rw [hqe, hpe]
  have hcard : S.card ≤ 1 := Finset.card_le_one.2 hsingle
  -- the sum is at most `log z`
  have hsum : ∑ p ∈ S, (Real.log p - δ / 8) ≤ Real.log (z : ℝ) := by
    have h1 : ∑ p ∈ S, (Real.log p - δ / 8) ≤ ∑ p ∈ S, Real.log (z : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      rw [hSdef, mem_filter, mem_range] at hp
      obtain ⟨-, hpp, hpmod, -⟩ := hp
      have hpd := prime_dvd_of_modEq_not_coprime hpp hpmod ha hW
      have hple : p ≤ z := by
        rw [hWz] at hpd
        exact (Nat.Prime.dvd_primorial_iff hpp).1 hpd
      have h2 : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hple)
      have h3 : 0 ≤ δ / 8 := by positivity
      linarith
    have h2 : ∑ _p ∈ S, Real.log (z : ℝ) = (S.card : ℝ) * Real.log (z : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    have h4 : ((S.card : ℝ)) * Real.log (z : ℝ) ≤ 1 * Real.log (z : ℝ) := by
      have h5 : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith
    rw [h2] at h1
    linarith
  have h6 : 3 * (Nat.totient W : ℝ) * ∑ p ∈ S, (Real.log p - δ / 8) ≤
      3 * (Nat.totient W : ℝ) * Real.log (z : ℝ) := by
    have h7 : (0 : ℝ) ≤ 3 * (Nat.totient W : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hsum h7
  linarith

/-! ### The reduced residues collect the primes of `A` -/

private lemma exists_unit_rep {m : ℕ} [NeZero m] (hm : Odd m) {z p : ℕ}
    (hW : primorial z = 2 * m) (hp : p.Prime) (hc : Nat.Coprime p (primorial z)) :
    ∃ b ∈ unitsMod m,
      Profiles408.oddRepresentative m b % primorial z = p % primorial z := by
  classical
  have hmdvd : m ∣ primorial z := by rw [hW]; exact ⟨2, by ring⟩
  have hcopm : Nat.Coprime p m := Nat.Coprime.of_dvd_right hmdvd hc
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hc
    have h2dvd : (2 : ℕ) ∣ primorial z := by rw [hW]; exact ⟨m, rfl⟩
    have hg : Nat.gcd 2 (primorial z) = 1 := hc.gcd_eq_one
    have hd : (2 : ℕ) ∣ Nat.gcd 2 (primorial z) := Nat.dvd_gcd (dvd_refl 2) h2dvd
    rw [hg] at hd; omega
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact Nat.odd_iff.2 h
  have hbunit : IsUnit ((p % m : ℕ) : ZMod m) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one]
    have h1 : Nat.gcd (p % m) m = Nat.gcd p m := by
      rw [← Nat.gcd_rec m p, Nat.gcd_comm]
    rw [h1]
    exact hcopm.gcd_eq_one
  refine ⟨((p % m : ℕ) : ZMod m), ?_, ?_⟩
  · simp only [unitsMod, mem_filter, mem_univ, true_and]
    exact hbunit
  · obtain ⟨-, hrodd, hrmod⟩ :=
      Profiles408.oddRepresentative_properties m hm ((p % m : ℕ) : ZMod m)
    have hbval : ((p % m : ℕ) : ZMod m).val = p % m := by
      rw [ZMod.val_natCast, Nat.mod_mod]
    have h1 : Profiles408.oddRepresentative m ((p % m : ℕ) : ZMod m) ≡ p [MOD m] := by
      rw [Nat.ModEq, hrmod, hbval]
    have h2 : Profiles408.oddRepresentative m ((p % m : ℕ) : ZMod m) ≡ p [MOD 2] := by
      rw [Nat.ModEq, Nat.odd_iff.mp hrodd, Nat.odd_iff.mp hpodd]
    have h3 : Profiles408.oddRepresentative m ((p % m : ℕ) : ZMod m) ≡ p [MOD 2 * m] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hm)).mp ⟨h2, h1⟩
    rw [hW]
    exact h3

/-- Summing the class log-masses over the reduced residues collects every prime of `A` coprime to
the primorial at least once. -/
private lemma sum_units_lower {m : ℕ} [NeZero m] (hm : Odd m) {z : ℕ}
    (hW : primorial z = 2 * m) (A : Set ℕ) (hA : A ⊆ P) (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter
        (fun p => p.Prime ∧ p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)),
        Real.log p ≤
      ∑ b ∈ unitsMod m,
        ∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p := by
  classical
  set S0 : Finset ℕ := (range (n + 1)).filter (fun p => p ∈ A ∧ 3 * p < 2 * n) with hS0
  have hTeq : ∀ b : ZMod m,
      ∑ p ∈ (range (n + 1)).filter
          (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
            ∧ 3 * p < 2 * n), Real.log p =
        ∑ p ∈ S0,
          (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then Real.log p
            else 0) := by
    intro b
    have hfil : (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
          ∧ 3 * p < 2 * n) =
        S0.filter (fun p => p % primorial z = Profiles408.oddRepresentative m b % primorial z) := by
      rw [hS0, Finset.filter_filter]
      congr 1
      funext p
      simp only [and_assoc, and_left_comm, and_comm]
    rw [hfil, Finset.sum_filter]
  have hstep3 : ∑ p ∈ S0, (if Nat.Coprime p (primorial z) then (1 : ℝ) else 0) * Real.log p ≤
      ∑ p ∈ S0,
        (∑ b ∈ unitsMod m,
          (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then (1 : ℝ)
            else 0)) * Real.log p := by
    refine sum_le_sum fun p hp => ?_
    rw [hS0, mem_filter, mem_range] at hp
    obtain ⟨-, hpA, hlt⟩ := hp
    have hpprime : p.Prime := hA hpA
    have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hc : Nat.Coprime p (primorial z)
    · rw [if_pos hc]
      obtain ⟨b, hb, hres⟩ := exists_unit_rep hm hW hpprime hc
      have hsingle : (if p % primorial z = Profiles408.oddRepresentative m b % primorial z
          then (1 : ℝ) else 0) ≤
          ∑ b' ∈ unitsMod m,
            (if p % primorial z = Profiles408.oddRepresentative m b' % primorial z
              then (1 : ℝ) else 0) :=
        single_le_sum (f := fun b' => if p % primorial z =
          Profiles408.oddRepresentative m b' % primorial z then (1 : ℝ) else 0)
          (fun b' _ => by split_ifs <;> norm_num) hb
      have hone : (if p % primorial z = Profiles408.oddRepresentative m b % primorial z
          then (1 : ℝ) else 0) = 1 := by rw [if_pos hres.symm]
      rw [hone] at hsingle
      calc (1 : ℝ) * Real.log p = Real.log p := one_mul _
        _ ≤ (∑ b' ∈ unitsMod m,
            (if p % primorial z = Profiles408.oddRepresentative m b' % primorial z
              then (1 : ℝ) else 0)) * Real.log p :=
            le_mul_of_one_le_left hlogp hsingle
    · rw [if_neg hc]
      have hsum0 : (0 : ℝ) ≤ ∑ b' ∈ unitsMod m,
          (if p % primorial z = Profiles408.oddRepresentative m b' % primorial z
            then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
      nlinarith [hlogp, hsum0]
  have hstep4 : ∑ p ∈ S0, (if Nat.Coprime p (primorial z) then (1 : ℝ) else 0) * Real.log p =
      ∑ p ∈ (range (n + 1)).filter
        (fun p => p.Prime ∧ p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)),
        Real.log p := by
    have hfil : (range (n + 1)).filter
        (fun p => p.Prime ∧ p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)) =
        S0.filter (fun p => Nat.Coprime p (primorial z)) := by
      rw [hS0]
      ext p
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨h0, h1, h2, h3, h4⟩
        exact ⟨⟨h0, h2, h3⟩, h4⟩
      · rintro ⟨⟨h0, h2, h3⟩, h4⟩
        exact ⟨h0, hA h2, h2, h3, h4⟩
    conv_rhs => rw [hfil, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  have hstep2 : ∑ p ∈ S0,
        (∑ b ∈ unitsMod m,
          (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then (1 : ℝ)
            else 0)) * Real.log p =
      ∑ p ∈ S0, ∑ b ∈ unitsMod m,
        (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then Real.log p
          else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  calc ∑ p ∈ (range (n + 1)).filter
        (fun p => p.Prime ∧ p ∈ A ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)), Real.log p
      = ∑ p ∈ S0, (if Nat.Coprime p (primorial z) then (1 : ℝ) else 0) * Real.log p :=
        hstep4.symm
    _ ≤ ∑ p ∈ S0,
          (∑ b ∈ unitsMod m,
            (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then (1 : ℝ)
              else 0)) * Real.log p := hstep3
    _ = ∑ p ∈ S0, ∑ b ∈ unitsMod m,
          (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then Real.log p
            else 0) := hstep2
    _ = ∑ b ∈ unitsMod m, ∑ p ∈ S0,
          (if p % primorial z = Profiles408.oddRepresentative m b % primorial z then Real.log p
            else 0) := Finset.sum_comm
    _ = ∑ b ∈ unitsMod m,
          ∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ∧ p % primorial z = Profiles408.oddRepresentative m b % primorial z
              ∧ 3 * p < 2 * n), Real.log p := by
        refine Finset.sum_congr rfl fun b _ => (hTeq b).symm

/-- Primes of `A` up to `X` that are not coprime to the primorial contribute at most
`(z + 1) log z`. -/
private lemma noncoprime_mass_le (A : Set ℕ) {z : ℕ} (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z)),
        Real.log p ≤ ((z : ℝ) + 1) * Real.log (z : ℝ) := by
  classical
  have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_natCast_nonneg z
  have h1 : ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z)),
        Real.log p ≤
      ∑ _p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z)),
        Real.log (z : ℝ) := by
    refine sum_le_sum fun p hp => ?_
    rw [mem_filter, mem_range] at hp
    obtain ⟨-, hpp, -, hpc⟩ := hp
    have hdvd : p ∣ primorial z := by
      by_contra h
      exact hpc (hpp.coprime_iff_not_dvd.2 h)
    have hple : p ≤ z := (Nat.Prime.dvd_primorial_iff hpp).1 hdvd
    exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hple)
  have h2 : ∑ _p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z)),
      Real.log (z : ℝ) =
      (((range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ) *
        Real.log (z : ℝ) := by
    rw [sum_const, nsmul_eq_mul]
  have h3 : (((range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ)
      ≤ (z : ℝ) + 1 := by
    have hsub : (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z))
        ⊆ range (z + 1) := by
      intro p hp
      rw [mem_filter, mem_range] at hp
      obtain ⟨-, hpp, -, hpc⟩ := hp
      have hdvd : p ∣ primorial z := by
        by_contra h
        exact hpc (hpp.coprime_iff_not_dvd.2 h)
      have hple : p ≤ z := (Nat.Prime.dvd_primorial_iff hpp).1 hdvd
      rw [mem_range]; omega
    have h4 : (((range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ)
        ≤ ((range (z + 1)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have h5 : ((range (z + 1)).card : ℝ) = (z : ℝ) + 1 := by
      rw [card_range]; push_cast; ring
    linarith
  rw [h2] at h1
  calc ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z)),
        Real.log p
      ≤ (((range (n + 1)).filter (fun p => p.Prime ∧ p ∈ A ∧ ¬ Nat.Coprime p (primorial z))).card : ℝ) *
          Real.log (z : ℝ) := h1
    _ ≤ ((z : ℝ) + 1) * Real.log (z : ℝ) := by
        refine mul_le_mul_of_nonneg_right h3 hlogz0

/-- A non-reduced class contains at most one prime with `3p < 2n`, and its log is at most
`log z`. -/
private lemma class_noncoprime_log_le {z a n : ℕ} (hcop : ¬ Nat.Coprime a (primorial z)) :
    (∑ p ∈ (range (n + 1)).filter
        (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
      ≤ Real.log (z : ℝ) := by
  classical
  have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_natCast_nonneg z
  have hWpos : 0 < primorial z := primorial_pos z
  set S : Finset ℕ := (range (n + 1)).filter
    (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n) with hSdef
  have hsingle : ∀ p ∈ S, ∀ q ∈ S, p = q := by
    intro p hp q hq
    rw [hSdef, mem_filter, mem_range] at hp hq
    obtain ⟨-, hpp, hpmod, -⟩ := hp
    obtain ⟨-, hqp, hqmod, -⟩ := hq
    have hpd := prime_dvd_of_modEq_not_coprime hpp hpmod hcop hWpos
    have hqd := prime_dvd_of_modEq_not_coprime hqp hqmod hcop hWpos
    have hple : p ≤ primorial z := Nat.le_of_dvd hWpos hpd
    have hqle : q ≤ primorial z := Nat.le_of_dvd hWpos hqd
    rcases lt_or_eq_of_le hple with hplt | hpe
    · have hpval : p % primorial z = p := Nat.mod_eq_of_lt hplt
      rw [hpval] at hpmod
      rcases lt_or_eq_of_le hqle with hqlt | hqe
      · rw [Nat.mod_eq_of_lt hqlt] at hqmod
        rw [← hpmod] at hqmod
        exact hqmod.symm
      · rw [hqe, Nat.mod_self] at hqmod
        rw [← hqmod] at hpmod
        rw [hpmod] at hpp
        exact absurd hpp Nat.not_prime_zero
    · rw [hpe, Nat.mod_self] at hpmod
      have ha0 : a % primorial z = 0 := hpmod.symm
      rcases lt_or_eq_of_le hqle with hqlt | hqe
      · rw [Nat.mod_eq_of_lt hqlt, ha0] at hqmod
        rw [hqmod] at hqp
        exact absurd hqp Nat.not_prime_zero
      · rw [hqe, hpe]
  have hcard : S.card ≤ 1 := Finset.card_le_one.2 hsingle
  have h1 : (∑ p ∈ S, Real.log p) ≤ ∑ _p ∈ S, Real.log (z : ℝ) := by
    refine sum_le_sum fun p hp => ?_
    rw [hSdef, mem_filter, mem_range] at hp
    obtain ⟨-, hpp, hpmod, -⟩ := hp
    have hpd := prime_dvd_of_modEq_not_coprime hpp hpmod hcop hWpos
    have hple : p ≤ z := (Nat.Prime.dvd_primorial_iff hpp).1 hpd
    exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hple)
  have h2 : ∑ _p ∈ S, Real.log (z : ℝ) = (S.card : ℝ) * Real.log (z : ℝ) := by
    rw [sum_const, nsmul_eq_mul]
  rw [h2] at h1
  have h3 : (S.card : ℝ) * Real.log (z : ℝ) ≤ 1 * Real.log (z : ℝ) := by
    have h4 : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    nlinarith
  linarith

/-- The number of reduced residues modulo `m` is `φ(m)`. -/
private lemma unitsMod_card (m : ℕ) [NeZero m] : (unitsMod m).card = m.totient := by
  classical
  have himg : (unitsMod m) = (Finset.univ.image (fun u : (ZMod m)ˣ => (u : ZMod m))) := by
    ext x
    rw [unitsMod, mem_filter]
    simp only [mem_univ, true_and, mem_image]
    constructor
    · intro hx
      exact ⟨hx.unit, by simp⟩
    · rintro ⟨u, rfl⟩
      exact u.isUnit
  rw [himg, Finset.card_image_of_injective _ (fun u v h => Units.ext h), Finset.card_univ,
    ZMod.card_units_eq_totient]

set_option maxHeartbeats 2000000



set_option maxHeartbeats 2000000

/-- LEAF. Li and Pan pages 7 to 8, Section 3, choosing the W-tricked
residues from the positive global density margin. The logarithmic cutoff
and normalization here are Shao page 15's profile. The local inequality is
Corollary 2.1's hypothesis and does not assert an integer representation. -/
theorem mixed_global_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Fin 3 → Set ℕ) (hA : ∀ i, A i ⊆ P)
    (hdensity : 2 + δ ≤ lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := fun i => Profiles408.halfProfile (A i) z n δ m
      (∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) ∧
      2 * (m.totient : ℝ) < ∑ b ∈ unitsMod m, (f 0 b + f 1 b + f 2 b) := by
  classical
  obtain ⟨hmpos, hmodd, -⟩ := half_primorial_props hz
  haveI : NeZero (primorial z / 2) := ⟨hmpos.ne'⟩
  have hWpos : 0 < primorial z := primorial_pos z
  have hW2 : primorial z = 2 * (primorial z / 2) := by
    have h2 : 2 ∣ primorial z := prime_dvd_primorial Nat.prime_two (by omega)
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel h2).symm
  have hΦeq : ((primorial z).totient : ℝ) = ((primorial z / 2).totient : ℝ) := by
    rw [hW2, Nat.totient_mul (Nat.coprime_two_left.mpr hmodd)]
    norm_num
  have hΦ0 : (0 : ℝ) < ((primorial z).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hWpos
  set Φ : ℝ := ((primorial z).totient : ℝ) with hΦdef
  set ε : ℝ := δ / 16 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  -- (I) the weighted class sum is at most `1 + δ/8`, uniformly in the class
  have hclass : ∀ a : ℕ, ∀ᶠ n : ℕ in atTop,
      (3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
        ≤ 1 + δ / 8 := by
    intro a
    by_cases hcop : Nat.Coprime a (primorial z)
    · obtain ⟨c, hc, K, hK0, hK⟩ := class_sum_le (primorial z) a (by omega) hcop
      -- the Siegel-Walfisz error is below `δ/8`
      have hdec : ∀ᶠ x : ℝ in atTop,
          Φ * (K * Real.exp (-c * Real.sqrt (Real.log x))) ≤ δ / 8 := by
        have h1 : 0 < δ / 8 / (Φ * K + 1) := by positivity
        have h2 := tendsto_exp_neg_sqrt_log hc |>.eventually (gt_mem_nhds h1)
        refine h2.mono fun x hx => ?_
        have h3 : (0:ℝ) < Φ * K + 1 := by positivity
        have h4 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ δ / 8 / (Φ * K + 1) := le_of_lt hx
        have h5 : Φ * K ≤ Φ * K + 1 := by linarith
        have h6 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log x)) := (Real.exp_pos _).le
        have h7 : Φ * K * Real.exp (-c * Real.sqrt (Real.log x)) ≤
            (Φ * K + 1) * Real.exp (-c * Real.sqrt (Real.log x)) :=
          mul_le_mul_of_nonneg_right h5 h6
        have h8 : (Φ * K + 1) * Real.exp (-c * Real.sqrt (Real.log x)) ≤
            (Φ * K + 1) * (δ / 8 / (Φ * K + 1)) := mul_le_mul_of_nonneg_left h4 h3.le
        have h9 : (Φ * K + 1) * (δ / 8 / (Φ * K + 1)) = δ / 8 := by field_simp
        linarith [h7, h8, h9]
      have hXtend : Tendsto (fun n : ℕ => ((2 * n / 3 : ℕ) : ℝ)) atTop atTop := by
        refine tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨3 * ⌈b⌉₊ + 2, fun n hn => ?_⟩
        have h8 : ⌈b⌉₊ ≤ 2 * n / 3 := by omega
        have h9 : b ≤ ((⌈b⌉₊ : ℕ) : ℝ) := Nat.le_ceil b
        have h10 : ((⌈b⌉₊ : ℕ) : ℝ) ≤ ((2 * n / 3 : ℕ) : ℝ) := by exact_mod_cast h8
        linarith
      have hdec' : ∀ᶠ n : ℕ in atTop,
          Φ * (K * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) ≤ δ / 8 :=
        hXtend.eventually hdec
      refine (hK.and (hdec'.and (eventually_ge_atTop 3))).mono ?_
      intro n hn
      obtain ⟨h1, h2, h3⟩ := hn
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have h4 : (0:ℕ) < n := by omega
        exact_mod_cast h4
      have h2n : (0:ℝ) < 2 * n := by positivity
      have hX0 : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
        have h := Nat.div_mul_le_self (2 * n) 3
        have h4 : ((2 * n / 3 : ℕ) : ℝ) * 3 ≤ 2 * (n : ℝ) := by exact_mod_cast h
        linarith
      have hX1 : (0:ℝ) ≤ ((2 * n / 3 : ℕ) : ℝ) := Nat.cast_nonneg _
      set S := ∑ p ∈ (range (n + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p with hS
      -- `class_sum_le` gives the bound directly for this class sum
      have hS5 : S ≤ (2 * (n : ℝ) / 3) / Φ +
          K * (2 * (n : ℝ) / 3) *
            Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by
        rw [hS]
        refine le_trans h1 ?_
        have hS3 : ((2 * n / 3 : ℕ) : ℝ) / Φ ≤ (2 * (n : ℝ) / 3) / Φ := by gcongr
        have hS4 : K * ((2 * n / 3 : ℕ) : ℝ) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) ≤
            K * (2 * (n : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by
          have h5 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) :=
            (Real.exp_pos _).le
          have h6 : K * ((2 * n / 3 : ℕ) : ℝ) ≤ K * (2 * (n : ℝ) / 3) := by nlinarith
          exact mul_le_mul_of_nonneg_right h6 h5
        linarith [hS3, hS4]
      -- multiply by `3Φ`
      have h4 : 3 * Φ * S ≤ 2 * n + 2 * Φ * K * (n : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by
        have h5 : 3 * Φ * S ≤ 3 * Φ * ((2 * (n : ℝ) / 3) / Φ +
            K * (2 * (n : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hS5 (by positivity)
        have h6 : 3 * Φ * ((2 * (n : ℝ) / 3) / Φ) = 2 * n := by field_simp
        have h7 : 3 * Φ * (K * (2 * (n : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) =
            2 * Φ * K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) := by ring
        have h8 : 3 * Φ * ((2 * (n : ℝ) / 3) / Φ +
            K * (2 * (n : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) =
            3 * Φ * ((2 * (n : ℝ) / 3) / Φ) + 3 * Φ * (K * (2 * (n : ℝ) / 3) *
              Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) := by ring
        linarith [h5, h6, h7, h8, mul_pos hΦ0 hn0]
      have h5 : 2 * Φ * K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))
          ≤ (δ / 8) * (2 * n) := by
        have h6 : Φ * (K * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))) ≤ δ / 8 := h2
        have h7 : 2 * Φ * K * (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))) =
            (2 * (n : ℝ)) * (Φ * (K * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ))))) := by ring
        rw [h7]
        calc (2 * (n : ℝ)) * (Φ * (K * Real.exp (-c * Real.sqrt (Real.log ((2 * n / 3 : ℕ) : ℝ)))))
            ≤ (2 * (n : ℝ)) * (δ / 8) := mul_le_mul_of_nonneg_left h6 (by positivity)
          _ = (δ / 8) * (2 * n) := by ring
      rw [div_mul_eq_mul_div, div_le_iff₀ h2n]
      linarith [h4, h5]
    · -- a non-reduced class: at most one prime, at most `log z`
      have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_natCast_nonneg z
      refine (Filter.eventually_ge_atTop
        (max 3 (⌈(3 * Φ * Real.log (z : ℝ)) / (2 * (δ / 8))⌉₊ + 1))).mono ?_
      intro n hn
      have hsum : (∑ p ∈ (range (n + 1)).filter
          (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
          ≤ Real.log (z : ℝ) := class_noncoprime_log_le hcop
      have hn3 : 3 ≤ n := by omega
      have h1 : 3 * Φ * Real.log (z : ℝ) / (2 * (δ / 8)) ≤
          (⌈(3 * Φ * Real.log (z : ℝ)) / (2 * (δ / 8))⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(3 * Φ * Real.log (z : ℝ)) / (2 * (δ / 8))⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : ⌈(3 * Φ * Real.log (z : ℝ)) / (2 * (δ / 8))⌉₊ ≤ n)
      have h3 : (0:ℝ) < δ / 8 := by positivity
      have hn0 : (0:ℝ) < (n : ℝ) := by
        have h4 : (0:ℕ) < n := by omega
        exact_mod_cast h4
      have hnpos : (0:ℝ) < 2 * n := by positivity
      have h4 : Φ * Real.log (z : ℝ) ≤ (δ / 8) * (2 * (n : ℝ)) / 3 := by
        have h9 : 3 * Φ * Real.log (z : ℝ) / (2 * (δ / 8)) * (2 * (δ / 8)) = 3 * Φ * Real.log (z : ℝ) := by
          field_simp
        have h10 : (0:ℝ) < 2 * (δ / 8) := by positivity
        have h11 : 3 * Φ * Real.log (z : ℝ) ≤ (n : ℝ) * (2 * (δ / 8)) := by
          calc 3 * Φ * Real.log (z : ℝ) = 3 * Φ * Real.log (z : ℝ) / (2 * (δ / 8)) * (2 * (δ / 8)) := h9.symm
            _ ≤ (n : ℝ) * (2 * (δ / 8)) := by
                refine mul_le_mul_of_nonneg_right ?_ h10.le
                linarith [h1, h2]
        nlinarith [h11, h3]
      rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
      have h5 : 3 * Φ * (∑ p ∈ (range (n + 1)).filter
            (fun p => p.Prime ∧ p % primorial z = a % primorial z ∧ 3 * p < 2 * n), Real.log p)
          ≤ 3 * Φ * Real.log (z : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h6 : 3 * Φ * Real.log (z : ℝ) ≤ 3 * ((δ / 8) * (2 * (n : ℝ)) / 3) := by
        have h7 : (0:ℝ) ≤ 3 * Φ := by positivity
        nlinarith [h4]
      have h8 : 3 * ((δ / 8) * (2 * (n : ℝ)) / 3) = (δ / 8) * (2 * n) := by ring
      nlinarith [h5, h6, h8, h3, hn0]
  -- (I finished) the cap, uniformly over the finitely many classes
  have hcap_ev : ∀ᶠ n : ℕ in atTop, ∀ ib : Fin 3 × ZMod (primorial z / 2),
      Profiles408.halfProfile (A ib.1) z n δ (primorial z / 2) ib.2 ≤ 1 := by
    choose NN hNN using fun ib : Fin 3 × ZMod (primorial z / 2) =>
      Filter.eventually_atTop.1 (hclass (Profiles408.oddRepresentative (primorial z / 2) ib.2))
    refine Filter.eventually_atTop.2 ⟨Finset.univ.sup NN, fun n hn ib => ?_⟩
    have h1 : NN ib ≤ Finset.univ.sup NN := Finset.le_sup (Finset.mem_univ ib)
    have h2 := hNN ib n (le_trans h1 hn)
    have hprof : Profiles408.halfProfile (A ib.1) z n δ (primorial z / 2) ib.2 =
        max ((3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ib.1 ∧ p % primorial z
              = Profiles408.oddRepresentative (primorial z / 2) ib.2 % primorial z ∧ 3 * p < 2 * n),
            Real.log p) - δ / 8) 0 := by
      simp only [Profiles408.halfProfile, Profiles408.primeProfile, hΦdef]
    rw [hprof]
    refine max_le ?_ (by norm_num)
    have hsub : (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ib.1 ∧ p % primorial z
              = Profiles408.oddRepresentative (primorial z / 2) ib.2 % primorial z ∧ 3 * p < 2 * n),
            Real.log p) ≤
        ∑ p ∈ (range (n + 1)).filter
            (fun p => p.Prime ∧ p % primorial z
              = Profiles408.oddRepresentative (primorial z / 2) ib.2 % primorial z ∧ 3 * p < 2 * n),
            Real.log p := by
      refine sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨hp.1, hA ib.1 hp.2.1, hp.2.2⟩
      · intro p _ _; exact Real.log_natCast_nonneg p
    have h3 : (0:ℝ) ≤ 3 * Φ / (2 * n) := by
      by_cases hnz : n = 0
      · simp [hnz]
      · have h4 : (0:ℝ) < 2 * n := by
          have h5 : (0:ℕ) < 2 * n := by omega
          exact_mod_cast h5
        positivity
    have h4 : (3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A ib.1 ∧ p % primorial z
              = Profiles408.oddRepresentative (primorial z / 2) ib.2 % primorial z ∧ 3 * p < 2 * n),
            Real.log p) ≤ 1 + δ / 8 := by
      refine le_trans ?_ h2
      exact mul_le_mul_of_nonneg_left hsub h3
    linarith [h4]
  -- (II) the mass
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 (set_mass_lower (A 0) (hA 0) ε hε0)
  obtain ⟨M1, hM1⟩ := Filter.eventually_atTop.1 (set_mass_lower (A 1) (hA 1) ε hε0)
  obtain ⟨M2, hM2⟩ := Filter.eventually_atTop.1 (set_mass_lower (A 2) (hA 2) ε hε0)
  have hmass_ev : ∀ᶠ n : ℕ in atTop,
      2 * ((primorial z / 2).totient : ℝ) <
        ∑ b ∈ unitsMod (primorial z / 2),
          (Profiles408.halfProfile (A 0) z n δ (primorial z / 2) b +
           Profiles408.halfProfile (A 1) z n δ (primorial z / 2) b +
           Profiles408.halfProfile (A 2) z n δ (primorial z / 2) b) := by
    have e0 : ∀ᶠ n : ℕ in atTop, 3 * M0 + 2 ≤ n := eventually_ge_atTop _
    have e1 : ∀ᶠ n : ℕ in atTop, 3 * M1 + 2 ≤ n := eventually_ge_atTop _
    have e2 : ∀ᶠ n : ℕ in atTop, 3 * M2 + 2 ≤ n := eventually_ge_atTop _
    have e3 : ∀ᶠ n : ℕ in atTop, 3 ≤ n := eventually_ge_atTop 3
    have e4 : ∀ᶠ n : ℕ in atTop, 144 / δ ≤ (n : ℝ) := by
      have h4 : (0:ℝ) < 144 / δ := by positivity
      exact tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (144 / δ))
    have e5 : ∀ᶠ n : ℕ in atTop, 72 * ((z : ℝ) + 1) * Real.log (z : ℝ) / δ ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (72 * ((z : ℝ) + 1) * Real.log (z : ℝ) / δ))
    refine ((((e0.and e1).and e2).and e3).and e4).and e5 |>.mono ?_
    intro n hn
    obtain ⟨⟨⟨⟨⟨hM0', hM1'⟩, hM2'⟩, hn3⟩, hn4⟩, hn5⟩ := hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have h1 : (0:ℕ) < n := by omega
      exact_mod_cast h1
    have h2n : (0 : ℝ) < 2 * n := by
      have h1 : (0:ℕ) < 2 * n := by omega
      exact_mod_cast h1
    set X : ℕ := (2 * n - 1) / 3 with hXdef
    have hX0 : M0 ≤ X := by omega
    have hX1 : M1 ≤ X := by omega
    have hX2 : M2 ≤ X := by omega
    -- the class sums collect the mass of each `A i`
    have hmass_i : ∀ i : Fin 3,
        (lowerDensity (A i) - ε) * (X : ℝ) - ((z : ℝ) + 1) * Real.log (z : ℝ) ≤
          ∑ b ∈ unitsMod (primorial z / 2),
            ∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p := by
      intro i
      have hXi : (lowerDensity (A i) - ε) * (X : ℝ) ≤
          ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A i), Real.log p := by
        fin_cases i
        · exact hM0 X hX0
        · exact hM1 X hX1
        · exact hM2 X hX2
      have hsplit : (∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A i), Real.log p) ≤
          (∑ p ∈ (range (X + 1)).filter
            (fun p => p.Prime ∧ p ∈ A i ∧ Nat.Coprime p (primorial z)), Real.log p) +
            ((z : ℝ) + 1) * Real.log (z : ℝ) := by
        have hadd := Finset.sum_filter_add_sum_filter_not
          (s := (range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A i))
          (p := fun p => Nat.Coprime p (primorial z)) (f := fun p => Real.log p)
        have h2 : (∑ p ∈ ((range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A i)).filter
              (fun p => Nat.Coprime p (primorial z)), Real.log p) =
            ∑ p ∈ (range (X + 1)).filter
              (fun p => p.Prime ∧ p ∈ A i ∧ Nat.Coprime p (primorial z)), Real.log p := by
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext p
          simp only [mem_filter, and_assoc]
        have h3 : (∑ p ∈ ((range (X + 1)).filter (fun p => p.Prime ∧ p ∈ A i)).filter
              (fun p => ¬ Nat.Coprime p (primorial z)), Real.log p) =
            ∑ p ∈ (range (X + 1)).filter
              (fun p => p.Prime ∧ p ∈ A i ∧ ¬ Nat.Coprime p (primorial z)), Real.log p := by
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext p
          simp only [mem_filter, and_assoc]
        have h4 := noncoprime_mass_le (z := z) (A i) X
        linarith [hadd, h2, h3, h4]
      have hinto : (∑ p ∈ (range (X + 1)).filter
            (fun p => p.Prime ∧ p ∈ A i ∧ Nat.Coprime p (primorial z)), Real.log p) ≤
          ∑ p ∈ (range (n + 1)).filter
            (fun p => p.Prime ∧ p ∈ A i ∧ 3 * p < 2 * n ∧ Nat.Coprime p (primorial z)),
            Real.log p := by
        refine sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          rw [mem_filter, mem_range] at hp ⊢
          obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
          have hpX : p ≤ X := by omega
          have h3X : 3 * X ≤ 2 * n - 1 := by omega
          exact ⟨by omega, hp2, hp3, by omega, hp4⟩
        · intro p _ _; exact Real.log_natCast_nonneg p
      have hsu := sum_units_lower hmodd (hW := hW2) (A i) (hA i) n
      linarith
    -- the number of reduced residues
    have hcardm : (unitsMod (primorial z / 2)).card = (primorial z / 2).totient := by
      have h := unitsMod_card (primorial z / 2)
      exact h
    -- each profile is at least `c_n · (class sum) - δ/8`
    have hprof_i : ∀ i : Fin 3, ∀ b : ZMod (primorial z / 2),
        (3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
              ∧ 3 * p < 2 * n), Real.log p) - δ / 8 ≤
          Profiles408.halfProfile (A i) z n δ (primorial z / 2) b := by
      intro i b
      have hprof : Profiles408.halfProfile (A i) z n δ (primorial z / 2) b =
          max ((3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0 := by
        simp only [Profiles408.halfProfile, Profiles408.primeProfile, hΦdef]
      rw [hprof]
      exact le_max_left _ _
    -- per set: the reduced residues' profile mass
    have hper_i : ∀ i : Fin 3,
        (3 * Φ / (2 * n)) * ((lowerDensity (A i) - ε) * (X : ℝ) - ((z : ℝ) + 1) * Real.log (z : ℝ))
            - Φ * (δ / 8) ≤
          ∑ b ∈ unitsMod (primorial z / 2), Profiles408.halfProfile (A i) z n δ (primorial z / 2) b := by
      intro i
      have h1 : (∑ b ∈ unitsMod (primorial z / 2), ((3 * Φ / (2 * n)) *
            (∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p) - δ / 8)) ≤
          ∑ b ∈ unitsMod (primorial z / 2), Profiles408.halfProfile (A i) z n δ (primorial z / 2) b :=
        Finset.sum_le_sum fun b _ => hprof_i i b
      have h2 : (∑ b ∈ unitsMod (primorial z / 2), ((3 * Φ / (2 * n)) *
            (∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p) - δ / 8)) =
          (3 * Φ / (2 * n)) * (∑ b ∈ unitsMod (primorial z / 2),
            (∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p)) -
            ((primorial z / 2).totient : ℝ) * (δ / 8) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul, hcardm]
      have h3 : (3 * Φ / (2 * n)) * ((lowerDensity (A i) - ε) * (X : ℝ) - ((z : ℝ) + 1) * Real.log (z : ℝ)) ≤
          (3 * Φ / (2 * n)) * (∑ b ∈ unitsMod (primorial z / 2),
            (∑ p ∈ (range (n + 1)).filter
              (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
                ∧ 3 * p < 2 * n), Real.log p)) :=
        mul_le_mul_of_nonneg_left (hmass_i i) (by positivity)
      have h4 : ((primorial z / 2).totient : ℝ) * (δ / 8) = Φ * (δ / 8) := by rw [← hΦeq]
      linarith [h1, h2, h3, h4]
    -- sum over the three sets
    have hswap : (∑ b ∈ unitsMod (primorial z / 2),
          (Profiles408.halfProfile (A 0) z n δ (primorial z / 2) b +
           Profiles408.halfProfile (A 1) z n δ (primorial z / 2) b +
           Profiles408.halfProfile (A 2) z n δ (primorial z / 2) b)) =
        ∑ i : Fin 3, ∑ b ∈ unitsMod (primorial z / 2),
          Profiles408.halfProfile (A i) z n δ (primorial z / 2) b := by
      rw [Fin.sum_univ_three, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hswap]
    have hsum3 : (3 * Φ / (2 * n)) *
          (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ) -
            3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) - 3 * (Φ * (δ / 8)) ≤
        ∑ i : Fin 3, ∑ b ∈ unitsMod (primorial z / 2),
          Profiles408.halfProfile (A i) z n δ (primorial z / 2) b := by
      have h1 : (∑ i : Fin 3, ((3 * Φ / (2 * n)) *
            ((lowerDensity (A i) - ε) * (X : ℝ) - ((z : ℝ) + 1) * Real.log (z : ℝ)) - Φ * (δ / 8))) ≤
          ∑ i : Fin 3, ∑ b ∈ unitsMod (primorial z / 2),
            Profiles408.halfProfile (A i) z n δ (primorial z / 2) b :=
        Finset.sum_le_sum fun i _ => hper_i i
      have h2 : (∑ i : Fin 3, ((3 * Φ / (2 * n)) *
            ((lowerDensity (A i) - ε) * (X : ℝ) - ((z : ℝ) + 1) * Real.log (z : ℝ)) - Φ * (δ / 8))) =
          (3 * Φ / (2 * n)) *
            (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ) -
              3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) - 3 * (Φ * (δ / 8)) := by
        rw [Fin.sum_univ_three]
        ring
      linarith [h1, h2]
    -- the arithmetic
    have hX2 : (2 * (n : ℝ) / 3 - 2 : ℝ) ≤ (X : ℝ) := by
      have h1 : 2 * n - 4 ≤ 3 * X := by omega
      have h2 : ((2 * n - 4 : ℕ) : ℝ) ≤ 3 * (X : ℝ) := by
        have h3 : ((2 * n - 4 : ℕ) : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h3 ⊢
        linarith
      have h3 : ((2 * n - 4 : ℕ) : ℝ) = 2 * (n : ℝ) - 4 := by
        rw [Nat.cast_sub (by omega : 4 ≤ 2 * n)]
        push_cast
        ring
      linarith [h2, h3]
    have hfinal : 2 * Φ < (3 * Φ / (2 * n)) *
          (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ) -
            3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) - 3 * (Φ * (δ / 8)) := by
      set A0 : ℝ := 2 + δ - 3 * ε with hA0def
      have hA0pos : 0 < A0 := by rw [hA0def, hεdef]; linarith
      have hA0le : A0 ≤ 3 := by rw [hA0def, hεdef]; linarith
      have hDA : A0 ≤ (lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε := by
        rw [hA0def]; linarith
      -- the main term
      have hmain : Φ * A0 - Φ * (δ / 16) ≤ (3 * Φ / (2 * n)) *
          (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ)) := by
        have h1 : Φ * A0 - 3 * Φ * A0 / (n : ℝ) ≤ (3 * Φ / (2 * n)) * (A0 * (X : ℝ)) := by
          have h2 : (3 * Φ / (2 * n)) * (A0 * (2 * (n : ℝ) / 3 - 2)) = Φ * A0 - 3 * Φ * A0 / (n : ℝ) := by
            field_simp
            try ring
          have h3 : (3 * Φ / (2 * n)) * (A0 * (2 * (n : ℝ) / 3 - 2)) ≤
              (3 * Φ / (2 * n)) * (A0 * (X : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hX2 (le_of_lt hA0pos)
          linarith [h2, h3]
        have h4 : (3 * Φ / (2 * n)) * (A0 * (X : ℝ)) ≤ (3 * Φ / (2 * n)) *
            (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hDA (Nat.cast_nonneg X)
        have h5 : 3 * Φ * A0 / (n : ℝ) ≤ Φ * (δ / 16) := by
          rw [div_le_iff₀ hn0]
          have h6 : 3 * A0 ≤ 9 := by linarith
          have h7 : 3 * Φ * A0 ≤ 9 * Φ := by
            have h8 : (0:ℝ) ≤ Φ := le_of_lt hΦ0
            nlinarith
          have h9 : (9 : ℝ) ≤ δ / 16 * (n : ℝ) := by
            have h10 : 144 / δ ≤ (n : ℝ) := hn4
            rw [div_le_iff₀ hδ] at h10
            nlinarith
          nlinarith
        linarith
      -- the loss from the non-coprime primes
      have hloss : (3 * Φ / (2 * n)) * (3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) ≤ Φ * (δ / 16) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)]
        have h10 : 72 * ((z : ℝ) + 1) * Real.log (z : ℝ) / δ ≤ (n : ℝ) := hn5
        rw [div_le_iff₀ hδ] at h10
        nlinarith
      have hexp : (3 * Φ / (2 * n)) *
            (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ) -
              3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) =
          (3 * Φ / (2 * n)) * (((lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) - 3 * ε) * (X : ℝ)) -
            (3 * Φ / (2 * n)) * (3 * ((z : ℝ) + 1) * Real.log (z : ℝ)) := by ring
      rw [hexp]
      have hkey : Φ * (2 + 5 * δ / 16) =
          Φ * A0 - Φ * (δ / 16) - Φ * (δ / 16) - 3 * (Φ * (δ / 8)) := by
        rw [hA0def, hεdef]
        ring
      have hpos2 : 2 * Φ < Φ * (2 + 5 * δ / 16) := by
        have h11 : (0:ℝ) < Φ * (5 * δ / 16) := by positivity
        nlinarith
      linarith [hmain, hloss, hkey, hpos2]
    linarith [hsum3, hfinal]
  -- assemble the two halves
  obtain ⟨Nc, hNc⟩ := Filter.eventually_atTop.1 hcap_ev
  obtain ⟨Nm, hNm⟩ := Filter.eventually_atTop.1 hmass_ev
  refine ⟨max Nc Nm, ?_⟩
  intro n hn m inst hm
  cases hm
  dsimp only
  constructor
  · intro i b
    refine ⟨?_, hNc n (le_trans (le_max_left _ _) hn) (i, b)⟩
    have hprof : Profiles408.halfProfile (A i) z n δ (primorial z / 2) b =
        max ((3 * Φ / (2 * n)) * (∑ p ∈ (range (n + 1)).filter
            (fun p => p ∈ A i ∧ p % primorial z = Profiles408.oddRepresentative (primorial z / 2) b % primorial z
              ∧ 3 * p < 2 * n), Real.log p) - δ / 8) 0 := by
      simp only [Profiles408.halfProfile, Profiles408.primeProfile, hΦdef]
    rw [hprof]
    exact le_max_right _ _
  · exact hNm n (le_trans (le_max_right _ _) hn)


/-- Exact original LiPan stub. The local result is already proved in the lab.
CONDITIONAL ON the mixed profile and shared analytic supply leaves. -/
theorem liPan_decomposed : LiPan := by
  intro A₁ A₂ A₃ hA₁ hA₂ hA₃ hden
  let A : Fin 3 → Set ℕ := ![A₁, A₂, A₃]
  have hA : ∀ i, A i ⊆ P := by
    intro i
    fin_cases i
    · exact hA₁
    · exact hA₂
    · exact hA₃
  let δ : ℝ := min ((lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃ - 2) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 2 + δ ≤ lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2) := by
    have := min_le_left ((lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃ - 2) / 2) (1 / 8)
    change 2 + δ ≤ lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting_mixed Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := mixed_global_profile δ hδ hδsmall z hz A hA hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := fun i => Profiles408.halfProfile (A i) z n δ m
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hsum, hprod⟩ :=
    liPanCor21_odd m hmodd hmsq (f 0) (f 1) (f 2) (hbound 0) (hbound 1) (hbound 2)
      hmass (n : ZMod m)
  have hp : 0 < f 0 b₁ * f 1 b₂ * f 2 b₃ := lt_of_le_of_ne
    (mul_nonneg (mul_nonneg (hbound 0 b₁).1 (hbound 1 b₂).1) (hbound 2 b₃).1) (Ne.symm hprod)
  obtain ⟨h1, h2, h3⟩ := Decomp408c.positive_factors (f 0 b₁) (f 1 b₂) (f 2 b₃)
    (hbound 0 b₁).1 (hbound 1 b₂).1 (hbound 2 b₃).1 hp
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃
    he.symm h1 h2 h3 (by linarith)

end

end LeanLab.DensityGoldbach.Decomp408e

#print axioms LeanLab.DensityGoldbach.Decomp408e.liPan_decomposed

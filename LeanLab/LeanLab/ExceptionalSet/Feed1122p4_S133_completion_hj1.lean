import LeanLab.ExceptionalSet.Feed1122p2_S133_hj1
import LeanLab.PNTPort.LargeSieve.Basic

/-!
Burst burst-20261122, session S133, wave 13. Split of `leaf_theorem2_subblock_S133hj1` of
`Feed1122p2_S133_hj1.lean`, the sub-interval form of Theorem 2 of P0082 page 354.

The sub-interval sum is completed: for `(u, v]` inside `(N/2, N]`, the indicator of `(u, v]` is
expanded in the additive characters modulo `N`, so the sub-interval sum is at most `2 + log N`
times the largest twisted block sum `Σ_{N/2 < n ≤ N} e(α F(n) + β n)`. This is proved here,
`complete`, from orthogonality and the bound `1/(2‖θ‖)` for a geometric sum, which is
`PNTPort.LargeSieve.norm_geom_le`. The factor `2 + log N` is absorbed into
`exp((κ'/2) (log N)^(3 - 2γ))`, `log_absorb`, proved.

The leaf left, `leaf_theorem2_twisted_S133hj1`, is Theorem 2 for the full block with a linear twist
`β n`. In the paper's proof, section 8 page 377, Theorem 2 comes from Karacuba's Lemma 10 applied
to `f(x) = α F(x)`; a linear term changes only the first derivative of `f`, and the derivative
conditions of Lemma 10 concern the derivatives of order `s` in a range far above `1`, so the same
proof applies to `α F(x) + β x`. This answers the S133 review QUESTION on the sub-interval form:
the strengthening is now isolated in the twist, with the completion proved.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553d

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: P0082 Theorem 2 on page 354 with a linear twist, from Karacuba's Lemma 10 on page 370
applied to `α F(x) + β x` as in section 8 page 377. Class HARD, cited. For `1 < γ < 3/2`,
`0 < c < 1` and `0 < C' < γ - 1` there are `κ' > 0` and `A ≥ 0` such that for every `N ≥ 1`,
every `α` with `F(N)^(-c) ≤ |α| ≤ F(N)^C'` and every real `β`, the sum
`Σ_{N/2 < n ≤ N} e(α F(n) + β n)` is at most `A N exp(-κ' (log N)^(3 - 2γ))`. -/
theorem leaf_theorem2_twisted_S133hj1 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' → ∀ β : ℝ,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n + β * n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := by
  sorry

namespace CompletionS133S133hj1

open LeanLab.PNTPort.LargeSieve (e e_add e_zero norm_e e_int e_nat_mul dist0 dist0_nonneg
  four_dist0_le norm_geom_le dist0_neg)

theorem eC_eq_e (x : ℝ) : eC x = e x := by
  simp only [eC, e]; congr 1; push_cast; ring

/-- Orthogonality of the additive characters modulo `N` on `[1, N]`. -/
theorem ortho (N : ℕ) (hN : 1 ≤ N) (n m : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    ∑ r ∈ range N, e (r * (((n : ℝ) - m) / N)) = if n = m then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [e_zero]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set θ : ℝ := ((n : ℝ) - m) / N with hθ
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hθ1 : |θ| < 1 := by
      rw [hθ, abs_div, abs_of_pos hNpos, div_lt_one hNpos, abs_lt]
      constructor <;> linarith
    have hθ0 : θ ≠ 0 := by
      intro h0
      rw [hθ, div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · apply h; exact_mod_cast (sub_eq_zero.mp h0)
      · linarith
    have hd : 0 < dist0 θ := by
      rcases (dist0_nonneg θ).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have h0 : θ - round θ = 0 := abs_eq_zero.mp heq.symm
        have hz : |((round θ : ℤ) : ℝ)| < 1 := by rw [← sub_eq_zero.mp h0]; exact hθ1
        have hz' : |round θ| < 1 := by exact_mod_cast hz
        have hz0 : round θ = 0 := by rw [abs_lt] at hz'; omega
        apply hθ0
        have := sub_eq_zero.mp h0
        rw [this, hz0]; simp
    have hne : e θ ≠ 1 := by
      intro h1
      have := four_dist0_le θ
      rw [h1, sub_self, norm_zero] at this
      linarith
    simp_rw [e_nat_mul]
    rw [geom_sum_eq hne]
    have hpow : e θ ^ N = 1 := by
      rw [← e_nat_mul]
      have : (N : ℝ) * θ = (((n : ℤ) - m : ℤ) : ℝ) := by
        rw [hθ]; push_cast; field_simp
      rw [this, e_int]
    rw [hpow, sub_self, zero_div]

/-- `min(x, 1 - x) ≤ ‖x‖` for `0 ≤ x ≤ 1`. -/
theorem min_le_dist0 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : min x (1 - x) ≤ dist0 x := by
  unfold dist0
  rcases le_or_gt (round x) 0 with hz | hz
  · have : ((round x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hz
    calc min x (1 - x) ≤ x := min_le_left _ _
      _ ≤ x - round x := by linarith
      _ ≤ |x - round x| := le_abs_self _
  · have : (1 : ℝ) ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast hz
    calc min x (1 - x) ≤ 1 - x := min_le_right _ _
      _ ≤ round x - x := by linarith
      _ ≤ |x - round x| := by rw [abs_sub_comm]; exact le_abs_self _

/-- The coefficient bound for `r` in `[1, N - 1]`. -/
theorem coef_bound (N : ℕ) (u v r : ℕ) (hr0 : 1 ≤ r) (hrN : r < N) :
    ‖∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))‖ ≤ N / (2 * r) + N / (2 * (N - r)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrN' : (r : ℝ) + 1 ≤ N := by exact_mod_cast hrN
  set x : ℝ := (r : ℝ) / N with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hNpos]; linarith
  have hd : min x (1 - x) ≤ dist0 (-x) := by rw [dist0_neg]; exact min_le_dist0 x hx0.le hx1.le
  have hmin : 0 < min x (1 - x) := lt_min hx0 (by linarith)
  have hsum : ∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N)) =
      e (-((r : ℝ) * (u + 1) / N)) * ∑ k ∈ range (v - u), e (k * (-x)) := by
    have hI : Finset.Ioc u v = Finset.Ico (u + 1) (v + 1) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    have : v + 1 - (u + 1) = v - u := by omega
    rw [this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← e_add]; congr 1; rw [hx]; push_cast; field_simp; ring
  rw [hsum, norm_mul, norm_e, one_mul]
  refine (norm_geom_le _ (lt_of_lt_of_le hmin hd)).trans ?_
  have h1 : 1 / (2 * dist0 (-x)) ≤ 1 / (2 * min x (1 - x)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine h1.trans ?_
  have h2 : 1 / (2 * min x (1 - x)) ≤ 1 / (2 * x) + 1 / (2 * (1 - x)) := by
    rcases min_choice x (1 - x) with h | h <;> rw [h]
    · have : 0 ≤ 1 / (2 * (1 - x)) := by
        have : 0 < 1 - x := by linarith
        positivity
      linarith
    · have : 0 ≤ 1 / (2 * x) := by positivity
      linarith
  refine h2.trans (le_of_eq ?_)
  rw [hx]
  have hNr : (0 : ℝ) < N - r := by linarith
  field_simp


/-- The `L¹` norm of the coefficients. -/
theorem coef_sum (N : ℕ) (hN : 1 ≤ N) (u v : ℕ) (hv : v ≤ N) :
    ∑ r ∈ range N, ‖∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))‖ ≤ N * (2 + Real.log N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hc0 : ‖∑ m ∈ Finset.Ioc u v, e (-(((0 : ℕ) : ℝ) * m / ((M + 1 : ℕ) : ℝ)))‖ ≤ (M + 1 : ℕ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_e, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
    exact_mod_cast (by omega : v - u ≤ M + 1)
  have hcr : ∀ r ∈ range M, ‖∑ m ∈ Finset.Ioc u v, e (-(((r + 1 : ℕ) : ℝ) * m / ((M + 1 : ℕ) : ℝ)))‖ ≤
      ((M + 1 : ℕ) : ℝ) / 2 * (1 / ((r : ℝ) + 1) + 1 / ((M : ℝ) - r)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    refine (coef_bound (M + 1) u v (r + 1) (by omega) (by omega)).trans (le_of_eq ?_)
    have hr' : (r : ℝ) + 1 ≤ M := by exact_mod_cast hr
    have h1 : (0 : ℝ) < (M : ℝ) - r := by linarith
    push_cast
    rw [show (M : ℝ) + 1 - ((r : ℝ) + 1) = (M : ℝ) - r by ring]
    field_simp
  have hrefl : ∑ r ∈ range M, 1 / ((M : ℝ) - r) = ∑ r ∈ range M, 1 / ((r : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) M]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.mem_range] at hr
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hharm : ∑ r ∈ range M, 1 / ((r : ℝ) + 1) ≤ 1 + Real.log ((M + 1 : ℕ) : ℝ) := by
    have h := harmonic_le_one_add_log M
    have hcast : ((harmonic M : ℚ) : ℝ) = ∑ r ∈ range M, 1 / ((r : ℝ) + 1) := by
      simp [harmonic, Rat.cast_sum, one_div]
    have hlog : Real.log (M : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0; simp
      · exact Real.log_le_log (by exact_mod_cast h0) (by push_cast; linarith)
    rw [← hcast]; linarith
  have hsum := Finset.sum_le_sum hcr
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hrefl] at hsum
  have hN0 : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc _ ≤ ((M + 1 : ℕ) : ℝ) / 2 *
        (∑ r ∈ range M, 1 / ((r : ℝ) + 1) + ∑ r ∈ range M, 1 / ((r : ℝ) + 1)) +
        ((M + 1 : ℕ) : ℝ) := add_le_add hsum hc0
    _ ≤ ((M + 1 : ℕ) : ℝ) / 2 * (2 * (1 + Real.log ((M + 1 : ℕ) : ℝ))) +
        ((M + 1 : ℕ) : ℝ) := by
        gcongr
        linarith
    _ = _ := by ring

/-- Completion: a sum over a sub-interval `(u, v]` of `(N/2, N]` is at most `2 + log N` times
the largest twisted sum `Σ_{N/2 < n ≤ N} e(f(n) + β n)`. Proved. -/
theorem complete (N : ℕ) (hN : 1 ≤ N) (f : ℕ → ℝ) (u v : ℕ) (hu : N / 2 ≤ u) (hv : v ≤ N)
    (B : ℝ) (hB : ∀ β : ℝ, ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (f n + β * n)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc u v, eC (f n)‖ ≤ (2 + Real.log N) * B := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : Finset.Ioc u v ⊆ Finset.Ioc (N / 2) N := by
    intro m; simp only [Finset.mem_Ioc]; omega
  have hexp : (N : ℂ) * ∑ n ∈ Finset.Ioc u v, e (f n) =
      ∑ r ∈ range N, (∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))) *
        (∑ n ∈ Finset.Ioc (N / 2) N, e (f n) * e ((r : ℝ) * n / N)) := by
    have step1 : ∀ r : ℕ, (∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))) *
        (∑ n ∈ Finset.Ioc (N / 2) N, e (f n) * e ((r : ℝ) * n / N)) =
        ∑ n ∈ Finset.Ioc (N / 2) N, ∑ m ∈ Finset.Ioc u v,
          e (f n) * e (r * (((n : ℝ) - m) / N)) := by
      intro r
      rw [Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
      rw [mul_comm (e _) (e (f n) * _), mul_assoc, ← e_add]
      congr 2; field_simp; ring
    rw [Finset.sum_congr rfl (fun r _ => step1 r), Finset.sum_comm]
    have step2 : ∀ n ∈ Finset.Ioc (N / 2) N, ∑ r ∈ range N, ∑ m ∈ Finset.Ioc u v,
        e (f n) * e (r * (((n : ℝ) - m) / N)) =
        if n ∈ Finset.Ioc u v then (N : ℂ) * e (f n) else 0 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.sum_comm]
      have h3 : ∀ m ∈ Finset.Ioc u v, ∑ r ∈ range N, e (f n) * e (r * (((n : ℝ) - m) / N)) =
          if n = m then (N : ℂ) * e (f n) else 0 := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [← Finset.mul_sum, ortho N hN n m (by omega) hn.2 (by omega) (by omega)]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl step2, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
      Finset.mul_sum]
  have hT : ∀ r : ℕ, ‖∑ n ∈ Finset.Ioc (N / 2) N, e (f n) * e ((r : ℝ) * n / N)‖ ≤ B := by
    intro r
    have := hB ((r : ℝ) / N)
    refine le_of_eq_of_le ?_ this
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [eC_eq_e, ← e_add]; congr 1; ring
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hS : ∑ n ∈ Finset.Ioc u v, eC (f n) = ∑ n ∈ Finset.Ioc u v, e (f n) :=
    Finset.sum_congr rfl (fun n _ => eC_eq_e _)
  rw [hS]
  have key : (N : ℝ) * ‖∑ n ∈ Finset.Ioc u v, e (f n)‖ ≤ N * (2 + Real.log N) * B := by
    have h1 : (N : ℝ) * ‖∑ n ∈ Finset.Ioc u v, e (f n)‖ =
        ‖(N : ℂ) * ∑ n ∈ Finset.Ioc u v, e (f n)‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [h1, hexp]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ r ∈ range N, ‖∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))‖ * B := by
          refine Finset.sum_le_sum (fun r _ => ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hT r) (norm_nonneg _)
      _ = (∑ r ∈ range N, ‖∑ m ∈ Finset.Ioc u v, e (-((r : ℝ) * m / N))‖) * B := by
          rw [Finset.sum_mul]
      _ ≤ (N * (2 + Real.log N)) * B := mul_le_mul_of_nonneg_right (coef_sum N hN u v hv) hB0
  have : (N : ℝ) * ‖∑ n ∈ Finset.Ioc u v, e (f n)‖ ≤ N * ((2 + Real.log N) * B) := by
    linarith
  exact le_of_mul_le_mul_left this hNpos

/-- `2 + log N ≤ K exp(μ (log N)^p)` for all `N ≥ 1`, when `p, μ > 0`. Proved. -/
theorem log_absorb (p μ : ℝ) (hp : 0 < p) (hμ : 0 < μ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      2 + Real.log N ≤ K * Real.exp (μ * Real.log N ^ p) := by
  have ho := (isLittleO_log_rpow_atTop hp).bound (show 0 < μ / 2 by linarith)
  have tL : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tP : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ p) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp tL
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (tL.eventually ho)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (tL.eventually_ge_atTop 2)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (tP.eventually_ge_atTop (2 * Real.log 2 / μ))
  set N₀ := max (max N₁ N₂) (max N₃ 1)
  refine ⟨2 + Real.log N₀, ?_, fun N hN => ?_⟩
  · have : (1 : ℝ) ≤ N₀ := by exact_mod_cast (le_trans (le_max_right _ _) (le_max_right _ _))
    have := Real.log_nonneg this; linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hE1 : 1 ≤ Real.exp (μ * Real.log N ^ p) :=
    Real.one_le_exp (mul_nonneg hμ.le (Real.rpow_nonneg hlogN _))
  rcases lt_or_ge N N₀ with hlt | hge
  · have : Real.log N ≤ Real.log N₀ :=
      Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hlt.le)
    have h0 : 0 ≤ 2 + Real.log N₀ := by
      have : (1 : ℝ) ≤ N₀ := by exact_mod_cast (le_trans (le_max_right _ _) (le_max_right _ _))
      have := Real.log_nonneg this; linarith
    nlinarith
  · have g1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hge
    have g2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hge
    have g3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hge
    set t := Real.log (N : ℝ) with ht
    have ht2 : 2 ≤ t := hN₂ N g2
    have hb := hN₁ N g1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
    have hlogt : Real.log t ≤ μ / 2 * t ^ p := le_trans (le_abs_self _) hb
    have h3 := hN₃ N g3
    rw [div_le_iff₀ hμ] at h3
    have hl2t : Real.log (2 + t) ≤ Real.log 2 + Real.log t := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hK1 : 1 ≤ 2 + Real.log N₀ := by
      have : (1 : ℝ) ≤ N₀ := by exact_mod_cast (le_trans (le_max_right _ _) (le_max_right _ _))
      have := Real.log_nonneg this; linarith
    calc 2 + t = Real.exp (Real.log (2 + t)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (μ * t ^ p) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ (2 + Real.log N₀) * Real.exp (μ * t ^ p) := by
          have := Real.exp_pos (μ * t ^ p); nlinarith

end CompletionS133S133hj1

/-- `leaf_theorem2_subblock_S133hj1`, statement verbatim, from the twisted block leaf
`leaf_theorem2_twisted_S133hj1` by the proved completion `CompletionS133S133hj1.complete`. -/
theorem leaf_theorem2_subblock_S133hj1_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ c C' : ℝ, 0 < c → c < 1 → 0 < C' → C' < γ - 1 →
      ∃ κ' A : ℝ, 0 < κ' ∧ 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N → ∀ u v : ℕ, N / 2 ≤ u → v ≤ N →
        ∀ α : ℝ, F γ N ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C' →
          ‖∑ n ∈ Finset.Ioc u v, eC (α * F γ n)‖ ≤
            A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := by
  intro c C' hc hc1 hC' hC'γ
  obtain ⟨κ', A, hκ', hA, hTw⟩ := leaf_theorem2_twisted_S133hj1 γ h1 h2 c C' hc hc1 hC' hC'γ
  obtain ⟨K, hK1, hK⟩ := CompletionS133S133hj1.log_absorb (3 - 2 * γ) (κ' / 2) (by linarith)
    (by linarith)
  refine ⟨κ' / 2, K * A, by linarith, by positivity, fun N hN u v hu hv α hlo hhi => ?_⟩
  have hc := CompletionS133S133hj1.complete N hN (fun n => α * F γ n) u v hu hv
    (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))) (fun β => hTw N hN α hlo hhi β)
  refine hc.trans ?_
  have hk := hK N hN
  have hAN : 0 ≤ A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := by positivity
  have hexp : Real.exp ((κ' / 2) * Real.log N ^ (3 - 2 * γ)) *
      Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) =
      Real.exp (-(κ' / 2) * Real.log N ^ (3 - 2 * γ)) := by
    rw [← Real.exp_add]; ring_nf
  calc (2 + Real.log N) * (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
      ≤ (K * Real.exp ((κ' / 2) * Real.log N ^ (3 - 2 * γ))) *
          (A * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))) :=
        mul_le_mul_of_nonneg_right hk hAN
    _ = K * A * N * (Real.exp ((κ' / 2) * Real.log N ^ (3 - 2 * γ)) *
          Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))) := by ring
    _ = K * A * N * Real.exp (-(κ' / 2) * Real.log N ^ (3 - 2 * γ)) := by rw [hexp]

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_theorem2_subblock_S133hj1_split =
    type_of% @leaf_theorem2_subblock_S133hj1 := rfl

#print axioms CompletionS133S133hj1.complete
#print axioms CompletionS133S133hj1.log_absorb

end LeanLab.ExceptionalSet.Decomp553d

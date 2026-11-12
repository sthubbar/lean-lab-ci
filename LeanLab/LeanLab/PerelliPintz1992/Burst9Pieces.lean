/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, pp. 361 to 364.

ROUTE BURST session 9, 2026-11-12. Proved pieces of the split of
`Burst8P2.rpart_block_bound`:

* `arc_to_eta`: the arc integral of `|R(α - a/q)|²` over `|α - a/q| < 1/(qQ)`, p. 364, is at
  most the integral of `|R(η)|²` over `|η| < 1/(qQ)`.
* `minkowski_fin`: Minkowski's inequality in `L²` for a finite sum, the Cauchy and Schwarz
  step from display 13 to the character sum of display 27, p. 364.
* `Ex_sum_le`: the terms with `(n, q) > 1` of display 13, p. 361, are `≤ q (log₂ 2N + 1) log 2N`.
* `card_aWin_le_two`: at most two numerators `a'` of display 25, p. 364, per modulus.
* `gallagher_Psx`: Gallagher's lemma for `Ψ'` of display 13 at the radius `1/(qQ)`, with the
  window `qQ/2` of `Decomp1624.gallagherWindow`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Leaves

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

/-! ### Continuity -/

theorem e_eq_character (x : ℝ) : e x = Burst9G.character293 x := by
  unfold e Burst9G.character293
  congr 1
  push_cast
  ring

theorem continuous_Rx (I : Finset ℕ) (q a : ℕ) : Continuous (Rx I q a) := by
  unfold Rx Sx Tx e
  fun_prop

theorem continuous_Psx (I : Finset ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    Continuous (Psx I χ) := by
  unfold Psx e
  fun_prop

theorem continuous_Ex (I : Finset ℕ) (q a : ℕ) : Continuous (Ex I q a) := by
  unfold Ex e
  fun_prop

/-- `Ψ'` is Gallagher's exponential sum with the coefficients `cf χ`. PROVED. -/
theorem Psx_eq_cexpSum (I : Finset ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (η : ℝ) :
    Psx I χ η = Burst9G.cexpSum I (cf χ) η := by
  unfold Psx Burst9G.cexpSum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [e_eq_character]

/-! ### The arc integral, p. 364 -/

/-- The arc integral of `|R(α - a/q)|²` over `arcM`, a part of `|α - a/q| < 1/(qQ)`, is at most
the integral of `|R(η)|²` over `|η| < 1/(qQ)`, p. 364. PROVED. -/
theorem arc_to_eta (N : ℕ) (A : ℝ) (q a : ℕ) (hq : 0 < (q : ℝ) * Q N) :
    (∫ α in arcM N A q a, ‖Decomp1519.R N q a (α - (a : ℝ) / q)‖ ^ 2) ≤
      ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)),
        ‖Decomp1519.R N q a η‖ ^ 2 := by
  set δ := 1 / ((q : ℝ) * Q N) with hδ
  set c := (a : ℝ) / q with hc
  have hδ0 : 0 < δ := by positivity
  have hcont : Continuous fun η => ‖Decomp1519.R N q a η‖ ^ 2 := by
    rw [show (fun η => ‖Decomp1519.R N q a η‖ ^ 2) =
      fun η => ‖Rx (Finset.Icc N (2 * N)) q a η‖ ^ 2 from rfl]
    exact (continuous_Rx _ q a).norm.pow 2
  have hcont' : Continuous fun α => ‖Decomp1519.R N q a (α - c)‖ ^ 2 :=
    hcont.comp (continuous_id.sub continuous_const)
  have hsub : arcM N A q a ⊆ Ioo (c - δ) (c + δ) := inter_subset_left
  calc (∫ α in arcM N A q a, ‖Decomp1519.R N q a (α - c)‖ ^ 2)
      ≤ ∫ α in Ioo (c - δ) (c + δ), ‖Decomp1519.R N q a (α - c)‖ ^ 2 :=
        setIntegral_mono_set (hcont'.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hsub)
    _ = ∫ α in (c - δ)..(c + δ), ‖Decomp1519.R N q a (α - c)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    _ = ∫ η in (-δ)..δ, ‖Decomp1519.R N q a η‖ ^ 2 := by
        rw [intervalIntegral.integral_comp_sub_right (fun η => ‖Decomp1519.R N q a η‖ ^ 2) c]
        congr 1 <;> ring

/-! ### Minkowski's inequality for a finite sum, the Cauchy and Schwarz step of p. 364 -/

/-- Pointwise weighted Cauchy and Schwarz: for `τ_k > 0`,
`(Σ |w_k| |f_k|)² ≤ (Σ |w_k| τ_k)(Σ |w_k| |f_k|²/τ_k)`. PROVED. -/
theorem weighted_cs {κ : Type*} (X : Finset κ) (w f τ : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hτ : ∀ k, 0 < τ k) :
    (∑ k ∈ X, w k * f k) ^ 2 ≤ (∑ k ∈ X, w k * τ k) * ∑ k ∈ X, w k / τ k * f k ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq X (fun k => √(w k * τ k)) (fun k => √(w k / τ k) * f k)
  have e1 : ∀ k, √(w k * τ k) * (√(w k / τ k) * f k) = w k * f k := by
    intro k
    rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hw k) (hτ k).le)]
    have : w k * τ k * (w k / τ k) = w k ^ 2 := by
      field_simp [(hτ k).ne']
    rw [this, Real.sqrt_sq (hw k)]
  have e2 : ∀ k, √(w k * τ k) ^ 2 = w k * τ k := fun k =>
    Real.sq_sqrt (mul_nonneg (hw k) (hτ k).le)
  have e3 : ∀ k, (√(w k / τ k) * f k) ^ 2 = w k / τ k * f k ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hw k) (hτ k).le)]
  simp only [e1, e2, e3] at h
  exact h

/-- **Minkowski in `L²` for a finite sum**: `Σ_p ∫ |Σ_k w_k f_{k,p}|² ≤
(Σ_k |w_k| (Σ_p ∫ |f_{k,p}|²)^{1/2})²`. PROVED. -/
theorem minkowski_fin {ι κ : Type*} (P : Finset ι) (X : Finset κ) (w : κ → ℂ)
    (f : κ → ι → ℝ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hf : ∀ k p, Continuous (f k p)) :
    (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤
      (∑ k ∈ X, ‖w k‖ * √(∑ p ∈ P, ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2)) ^ 2 := by
  set I : κ → ℝ := fun k => ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 with hI
  have hI0 : ∀ k, 0 ≤ I k := fun k => Finset.sum_nonneg fun p _ =>
    intervalIntegral.integral_nonneg (by linarith) fun η _ => sq_nonneg _
  set S := ∑ k ∈ X, ‖w k‖ * √(I k) with hS
  set W := ∑ k ∈ X, ‖w k‖ with hW
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => norm_nonneg _
  have key : ∀ t : ℝ, 0 < t →
      (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤ S ^ 2 + t * W * S := by
    intro t ht
    set τ : κ → ℝ := fun k => √(I k) + t with hτ
    have hτ0 : ∀ k, 0 < τ k := fun k => by
      simp only [hτ]; linarith [Real.sqrt_nonneg (I k)]
    have hpt : ∀ p η, ‖∑ k ∈ X, w k * f k p η‖ ^ 2 ≤
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := by
      intro p η
      have h1 : ‖∑ k ∈ X, w k * f k p η‖ ≤ ∑ k ∈ X, ‖w k‖ * ‖f k p η‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      have h2 := weighted_cs X (fun k => ‖w k‖) (fun k => ‖f k p η‖) τ
        (fun k => norm_nonneg _) hτ0
      have h0 : 0 ≤ ‖∑ k ∈ X, w k * f k p η‖ := norm_nonneg _
      calc ‖∑ k ∈ X, w k * f k p η‖ ^ 2 ≤ (∑ k ∈ X, ‖w k‖ * ‖f k p η‖) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ ≤ _ := h2
    have hint : ∀ k p, IntervalIntegrable (fun η => ‖f k p η‖ ^ 2) volume (-δ) δ :=
      fun k p => ((hf k p).norm.pow 2).intervalIntegrable _ _
    have hsum_int : ∀ p, (∫ η in (-δ)..δ, (∑ k ∈ X, ‖w k‖ * τ k) *
        ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2) =
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 := by
      intro p
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum
        (fun k _ => (hint k p).const_mul _)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul]
    have hcont : ∀ p, Continuous fun η => ‖∑ k ∈ X, w k * f k p η‖ ^ 2 := fun p =>
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hf k p)).norm.pow 2
    have hcont2 : ∀ p, Continuous fun η => (∑ k ∈ X, ‖w k‖ * τ k) *
        ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := fun p =>
      continuous_const.mul (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((hf k p).norm.pow 2))
    have step : (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := by
      calc (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2)
          ≤ ∑ p ∈ P, ∫ η in (-δ)..δ, (∑ k ∈ X, ‖w k‖ * τ k) *
              ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := by
            refine Finset.sum_le_sum fun p _ => ?_
            exact intervalIntegral.integral_mono_on (by linarith)
              ((hcont p).intervalIntegrable _ _) ((hcont2 p).intervalIntegrable _ _)
              fun η _ => hpt p η
        _ = ∑ p ∈ P, (∑ k ∈ X, ‖w k‖ * τ k) *
              ∑ k ∈ X, ‖w k‖ / τ k * ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 :=
            Finset.sum_congr rfl fun p _ => hsum_int p
        _ = (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.mul_sum]
    have hb : ∀ k, ‖w k‖ / τ k * I k ≤ ‖w k‖ * √(I k) := by
      intro k
      have h1 : I k ≤ τ k * √(I k) := by
        show I k ≤ (√(I k) + t) * √(I k)
        nlinarith [Real.mul_self_sqrt (hI0 k), Real.sqrt_nonneg (I k)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (hτ0 k)]
      have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (w k))
      nlinarith
    have hb2 : (∑ k ∈ X, ‖w k‖ / τ k * I k) ≤ S := Finset.sum_le_sum fun k _ => hb k
    have hA : (∑ k ∈ X, ‖w k‖ * τ k) = S + t * W := by
      simp only [hτ, hS, hW, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hA0 : 0 ≤ ∑ k ∈ X, ‖w k‖ * τ k := by rw [hA]; positivity
    calc _ ≤ (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := step
      _ ≤ (∑ k ∈ X, ‖w k‖ * τ k) * S := mul_le_mul_of_nonneg_left hb2 hA0
      _ = S ^ 2 + t * W * S := by rw [hA]; ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < ε / (W * S + 1) := by positivity
  refine (key _ ht).trans ?_
  have : ε / (W * S + 1) * W * S ≤ ε := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hW0 hS0]
  linarith

/-! ### The terms with `(n, q) > 1`, display 13 -/

/-- The integers `N ≤ n ≤ 2N` with `Λ(n) ≠ 0` and `(n, q) > 1` are prime powers `p^k` with
`p ∣ q` and `k ≤ log₂ 2N`, so there are at most `q (log₂ 2N + 1)` of them, and
`Σ Λ(n) ≤ q (log₂ 2N + 1) log 2N`. PROVED. -/
theorem Ex_sum_le (N : ℕ) (q : ℕ+) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ≤
      (q : ℕ) * ((Nat.log 2 (2 * N) : ℝ) + 1) * Real.log (2 * N) := by
  classical
  set S := (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q) with hS
  set P := S.filter (fun n => IsPrimePow n) with hP
  have h1 : (∑ n ∈ S, Λ n) = ∑ n ∈ P, Λ n := by
    refine (Finset.sum_filter_of_ne fun n _ hn => ?_).symm
    by_contra h
    exact hn (by rw [vonMangoldt_apply, if_neg h])
  have h2 : (∑ n ∈ P, Λ n) ≤ P.card * Real.log (2 * N) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnS := (Finset.mem_filter.mp hn).1
    have hn2 : n ≤ 2 * N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1).2
    refine vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ 2 * N ∨ N = 0 := by
          rcases Nat.eq_zero_or_pos N with hN | hN
          · right; exact hN
          · left; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
            linarith
        rcases this with h | h
        · exact h
        · exfalso
          have hpp := (Finset.mem_filter.mp hn).2
          exact (not_isPrimePow_zero) hpp)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn2)
  have h3 : P ⊆ (q.val.primeFactors ×ˢ Finset.range (Nat.log 2 (2 * N) + 1)).image
      (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hpp := (Finset.mem_filter.mp hn).2
    have hcop := (Finset.mem_filter.mp hnS).2
    have hn2 : n ≤ 2 * N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1).2
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p ∣ (q : ℕ) := by
      by_contra hnd
      exact hcop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    refine Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.mem_primeFactors.mpr ⟨hp, hpq, q.ne_zero⟩
    · refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      exact (Nat.pow_le_pow_left hp.two_le k).trans hn2
  have h4 : (P.card : ℝ) ≤ (q : ℕ) * ((Nat.log 2 (2 * N) : ℝ) + 1) := by
    have := (Finset.card_le_card h3).trans Finset.card_image_le
    rw [Finset.card_product, Finset.card_range] at this
    have hpf : q.val.primeFactors.card ≤ (q : ℕ) := by
      refine (Finset.card_le_card (s := q.val.primeFactors) (t := Finset.Icc 1 (q : ℕ)) ?_).trans
        (by simp)
      intro p hp
      have := Nat.mem_primeFactors.mp hp
      exact Finset.mem_Icc.mpr ⟨this.1.one_lt.le, Nat.le_of_dvd q.pos this.2.1⟩
    have h5 : P.card ≤ (q : ℕ) * (Nat.log 2 (2 * N) + 1) :=
      this.trans (Nat.mul_le_mul_right _ hpf)
    exact_mod_cast h5
  have hlog : 0 ≤ Real.log (2 * N) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · exact Real.log_nonneg (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                                linarith)
  rw [h1]
  exact h2.trans (mul_le_mul_of_nonneg_right h4 hlog)

/-- `|E(η)| ≤ Σ_{N ≤ n ≤ 2N, (n,q) > 1} Λ(n)` for `I ⊆ [N, 2N]`. PROVED. -/
theorem norm_Ex_le (N : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Icc N (2 * N)) (q : ℕ+) (a : ℕ)
    (η : ℝ) :
    ‖Ex I q a η‖ ≤ ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
  unfold Ex
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n, ‖(Λ n : ℂ) * e (n * ((a : ℝ) / q + η))‖ = Λ n := by
    intro n
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  simp only [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hI)
    (fun n _ _ => vonMangoldt_nonneg)

/-! ### At most two numerators per modulus, display 25 -/

/-- A finite set of naturals within distance `< 1` of a real `t` has at most two elements.
PROVED. -/
theorem card_le_two_of_near (S : Finset ℕ) (t : ℝ) (hS : ∀ r ∈ S, |(r : ℝ) - t| < 1) :
    S.card ≤ 2 := by
  set m : ℤ := ⌊t⌋
  have hsub : S.image (fun r : ℕ => (r : ℤ)) ⊆ {m, m + 1} := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have h := abs_lt.mp (hS r hr)
    have hm1 : (m : ℝ) ≤ t := Int.floor_le t
    have hm2 : t < (m : ℝ) + 1 := Int.lt_floor_add_one t
    have hlo : m ≤ (r : ℤ) := by
      have : (m : ℝ) - 1 < (r : ℝ) := by linarith
      have : m - 1 < (r : ℤ) := by exact_mod_cast this
      omega
    have hhi : (r : ℤ) ≤ m + 1 := by
      have : (r : ℝ) < (m : ℝ) + 2 := by linarith
      have : (r : ℤ) < m + 2 := by exact_mod_cast this
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)] at h1
  exact h1.trans (Finset.card_le_two)

/-- **At most two numerators `a'` per modulus**, display 25, p. 364: the arc
`|α - a'/q| < 1/(qQ)` meets the window `|α - ξ| < 1/H` only if `|a' - qξ| < 1/Q + q/H < 1`.
PROVED. -/
theorem card_aWin_le_two {N : ℕ} (hN : 64 ≤ N) {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) {q : ℕ}
    (hq1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q N) : (aWin N ε ξ q).card ≤ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hQ4 : 4 ≤ Q N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have : (8 : ℝ) ≤ √(N : ℝ) := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hNr
    linarith
  have hQH : Q N / H N ε ≤ 1 / 2 := by
    unfold Q H
    rw [Real.rpow_add hNpos]
    have h1 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
    have h2 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hH0 : 0 < H N ε := Real.rpow_pos_of_pos hNpos _
  refine card_le_two_of_near _ (q * ξ) fun r hr => ?_
  obtain ⟨-, α, h1, h2⟩ := of_mem_filter hr
  have hq0 : (0 : ℝ) < q := by linarith
  have e1 : (r : ℝ) - q * ξ = q * ((r : ℝ) / q - α) + q * (α - ξ) := by
    field_simp; ring
  rw [e1]
  have h1' : |(r : ℝ) / q - α| < 1 / (q * Q N) := by rw [abs_sub_comm]; exact h1
  calc |(q : ℝ) * ((r : ℝ) / q - α) + q * (α - ξ)|
      ≤ |(q : ℝ) * ((r : ℝ) / q - α)| + |(q : ℝ) * (α - ξ)| := abs_add_le _ _
    _ = q * |(r : ℝ) / q - α| + q * |α - ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos hq0]
    _ < q * (1 / (q * Q N)) + q * (1 / H N ε) := by
        have := mul_lt_mul_of_pos_left h1' hq0
        have := mul_lt_mul_of_pos_left h2 hq0
        linarith
    _ = 1 / Q N + q / H N ε := by field_simp
    _ ≤ 1 / 4 + 1 / 2 := by
        have a1 : 1 / Q N ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hQ4
        have a2 : (q : ℝ) / H N ε ≤ Q N / H N ε := div_le_div_of_nonneg_right hqQ hH0.le
        linarith
    _ < 1 := by norm_num

/-! ### Gallagher's lemma at the radius `1/(qQ)`, p. 364 -/

/-- Gallagher's lemma for `Ψ'` of display 13 at the radius `1/(qQ)`: the window is
`qQ/2 = gallagherWindow N q`. PROVED from `Burst9G.gallagher_complex`. -/
theorem gallagher_Psx (N : ℕ) (I : Finset ℕ) (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ))
    (hQ : 0 < Q N) :
    (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Psx I χ η‖ ^ 2) ≤
      2 * π ^ 2 * (1 / ((q : ℝ) * Q N)) ^ 2 *
        ∫ x : ℝ, ‖Burst9G.cwinSum I (cf χ) (gallagherWindow N q) x‖ ^ 2 := by
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hY : 0 < 1 / ((q : ℝ) * Q N) := by positivity
  have hw : 1 / (2 * (1 / ((q : ℝ) * Q N))) = gallagherWindow N q := by
    unfold gallagherWindow; field_simp
  have h := Burst9G.gallagher_complex I (cf χ) _ hY
  rw [hw] at h
  simp_rw [Psx_eq_cexpSum]
  exact h

#print axioms e_eq_character
#print axioms arc_to_eta
#print axioms weighted_cs
#print axioms minkowski_fin
#print axioms Ex_sum_le
#print axioms norm_Ex_le
#print axioms card_le_two_of_near
#print axioms card_aWin_le_two
#print axioms gallagher_Psx

end
end LeanLab.PerelliPintz1992.Burst9

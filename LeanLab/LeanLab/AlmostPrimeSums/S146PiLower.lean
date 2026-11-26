import Mathlib

/-!
AI wrote this Lean code, CLOUD S146 burst-20261122 w1. Binary Goldbach is open.
Split of `Decomp243aFeed1122Lower.leaf_pi_lower`, Rosser and Schoenfeld 1962 Corollary 1
used at BJS https://arxiv.org/abs/2207.09452 p. 43 equation 142, into the strong prime
number theorem for `ψ`, the one leaf, from which `θ(x) ≥ x - x/(8 log x)` is proved, and the
elementary bound `θ(N) + θ(N/e)/log N ≤ π(N) log N`, also proved.
-/

namespace LeanLab.AlmostPrimeSums.S146PiLower

open Finset Real Filter Topology

/-- LEAF: the prime number theorem with the de la Vallee Poussin error term for Chebyshev's
`ψ`, `|ψ(x) - x| ≤ K x exp(-c √(log x))` for `x ≥ 2`, the input behind Rosser and Schoenfeld
1962 Corollary 1; its statement is exactly that of the PROVED
`LeanLab.PNTPort.psi_explicit_strong`, not imported here only because that port is not
built in this worktree. Class EASY, wiring only. -/
theorem leaf_psi_strong : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  sorry

/-- CONDITIONAL S146 on `leaf_psi_strong` only: `θ(x) ≥ x - x/(8 log x)` for all large `x`,
using Mathlib `Chebyshev.psi_sub_theta_le` for `ψ - θ ≤ 2 √x log x`. -/
theorem leaf_theta_lower_pnt : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    x - x / (8 * log x) ≤ Chebyshev.theta x := by
  obtain ⟨c, hc, K, hK⟩ := leaf_psi_strong
  set K' := |K| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  -- (a)
  have hu : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have ha := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hu
  have ha' : ∀ᶠ x : ℝ in atTop, (c * Real.sqrt (Real.log x)) ^ 2 *
      exp (-(c * Real.sqrt (Real.log x))) < c ^ 2 / (16 * K') :=
    ha.eventually (eventually_lt_nhds (by positivity))
  -- (b)
  have hb := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (show (0 : ℝ) < 1 / 32 by norm_num)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ha'.and (hb.and (eventually_ge_atTop (3 : ℝ))))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨h1, h2, hx3⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  have hL : 1 < log x := by
    rw [← log_exp 1]; exact log_lt_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set L := log x with hLdef
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hE : 0 < exp (-c * Real.sqrt L) := exp_pos _
  -- from (a): K x e ≤ x / (16 L)
  have hA : K * x * exp (-c * Real.sqrt L) ≤ x / (16 * L) := by
    have h1' : c ^ 2 * L * exp (-c * Real.sqrt L) ≤ c ^ 2 / (16 * K') := by
      have : (c * Real.sqrt L) ^ 2 = c ^ 2 * L := by rw [mul_pow, hsq]
      rw [this, show -(c * Real.sqrt L) = -c * Real.sqrt L by ring] at h1
      exact h1.le
    have h2' : L * exp (-c * Real.sqrt L) ≤ 1 / (16 * K') := by
      have hc2 : 0 < c ^ 2 := by positivity
      have : c ^ 2 * (L * exp (-c * Real.sqrt L)) ≤ c ^ 2 * (1 / (16 * K')) := by
        calc c ^ 2 * (L * exp (-c * Real.sqrt L)) = c ^ 2 * L * exp (-c * Real.sqrt L) := by ring
          _ ≤ c ^ 2 / (16 * K') := h1'
          _ = c ^ 2 * (1 / (16 * K')) := by ring
      exact le_of_mul_le_mul_left this hc2
    have h3 : K * (L * exp (-c * Real.sqrt L)) ≤ 1 / 16 := by
      calc K * (L * exp (-c * Real.sqrt L)) ≤ K' * (L * exp (-c * Real.sqrt L)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hK']; linarith [le_abs_self K]
        _ ≤ K' * (1 / (16 * K')) := mul_le_mul_of_nonneg_left h2' hK'pos.le
        _ = 1 / 16 := by field_simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hx0.le]
  -- from (b): 2 √x L ≤ x / (16 L)
  have hB : 2 * Real.sqrt x * L ≤ x / (16 * L) := by
    have hrp : log x ^ (2 : ℝ) = L ^ 2 := by rw [← hLdef]; exact_mod_cast rpow_natCast L 2
    have hsx : x ^ ((1 : ℝ) / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    rw [hrp, hsx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] at h2
    have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    rw [le_div_iff₀ (by positivity)]
    have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 hs0]
  have hpsi := hK x (by linarith)
  have hpt := Chebyshev.psi_sub_theta_le (show 1 ≤ x by linarith)
  have hlow : x - K * x * exp (-c * Real.sqrt L) ≤ Chebyshev.psi x := by
    have := (abs_le.mp hpsi).1; linarith
  have hsplit : x / (8 * L) = x / (16 * L) + x / (16 * L) := by field_simp; ring
  linarith

/-- PROVED S146: the elementary comparison `θ(N) + θ(N/e)/log N ≤ π(N) log N`, since
`log p ≤ log N - 1` for primes `p ≤ N/e`, the device of Rosser and Schoenfeld 1962 Section 4. -/
theorem primeCounting_mul_log_ge (N : ℕ) (hN : 3 ≤ N) :
    Chebyshev.theta N + Chebyshev.theta ((N : ℝ) / exp 1) / log N ≤
      (Nat.primeCounting N : ℝ) * log N := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  set P := Nat.primesLE N
  set Q := Nat.primesLE ⌊(N : ℝ) / exp 1⌋₊
  have hQP : Q ⊆ P := by
    intro p hp
    obtain ⟨h1, h2⟩ := Nat.mem_primesLE.mp hp
    refine Nat.mem_primesLE.mpr ⟨le_trans h1 ?_, h2⟩
    apply Nat.floor_le_of_le
    have : (N : ℝ) / exp 1 ≤ N := div_le_self hN0.le (by linarith [add_one_le_exp (1:ℝ)])
    exact this
  have hθN : Chebyshev.theta N = ∑ p ∈ P, log (p : ℝ) := Chebyshev.theta_eq_sum_primesLE_log N
  have hθQ : Chebyshev.theta ((N : ℝ) / exp 1) = ∑ p ∈ Q, log (p : ℝ) :=
    Chebyshev.theta_eq_sum_primesLE _
  have hπ : (Nat.primeCounting N : ℝ) = (P.card : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
  have hQle : ∀ p ∈ Q, log (p : ℝ) ≤ log N - 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Nat.mem_primesLE.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast h2.pos
    have : (p : ℝ) ≤ N / exp 1 := le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
    calc log (p : ℝ) ≤ log (N / exp 1) := log_le_log hp0 this
      _ = log N - 1 := by rw [log_div hN0.ne' (exp_pos 1).ne', log_exp]
  have hPle : ∀ p ∈ P, log (p : ℝ) ≤ log N := by
    intro p hp
    obtain ⟨h1, h2⟩ := Nat.mem_primesLE.mp hp
    exact log_le_log (by exact_mod_cast h2.pos) (by exact_mod_cast h1)
  have hsplit := sum_sdiff hQP (f := fun p : ℕ => log (p : ℝ))
  have hA : ∑ p ∈ P \ Q, log (p : ℝ) ≤ ((P \ Q).card : ℝ) * log N := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun p hp => hPle p (sdiff_subset hp)
  have hB : ∑ p ∈ Q, log (p : ℝ) ≤ (Q.card : ℝ) * (log N - 1) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hQle
  have hC : (∑ p ∈ Q, log (p : ℝ)) / log N ≤ Q.card := by
    rw [div_le_iff₀ hL]
    calc ∑ p ∈ Q, log (p : ℝ) ≤ ∑ p ∈ Q, log (N : ℝ) :=
          sum_le_sum fun p hp => hPle p (hQP hp)
      _ = Q.card * log N := by rw [sum_const, nsmul_eq_mul]
  have hcard : ((P \ Q).card : ℝ) + Q.card = P.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hQP
  rw [hθN, hθQ, hπ, ← hsplit, ← hcard]
  nlinarith

/-- PROVED S146 from `leaf_theta_lower_pnt`: exactly the statement of
`LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower.leaf_pi_lower`, Rosser and Schoenfeld 1962
Corollary 1 in eventual form, `N / log N ≤ π(N)`, CONDITIONAL only on the leaf
`leaf_psi_strong`. -/
theorem leaf_pi_lower_s146 : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (N : ℝ) / log N ≤ Nat.primeCounting N := by
  obtain ⟨X, hX⟩ := leaf_theta_lower_pnt
  refine ⟨⌈max (exp 1 * X) (exp 2)⌉₊ + 3, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := by omega
  have hNr : max (exp 1 * X) (exp 2) ≤ (N : ℝ) := by
    have := Nat.le_ceil (max (exp 1 * X) (exp 2))
    have h2 : ((⌈max (exp 1 * X) (exp 2)⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hN0 : (0 : ℝ) < N := by positivity
  have he : 0 < exp (1 : ℝ) := exp_pos 1
  have hXe : X ≤ (N : ℝ) / exp 1 := by
    rw [le_div_iff₀ he]; linarith [le_max_left (exp 1 * X) (exp 2)]
  have hXN : X ≤ (N : ℝ) := by
    have : (N : ℝ) / exp 1 ≤ N := div_le_self hN0.le (by linarith [add_one_le_exp (1:ℝ)])
    linarith
  have hL1 : 1 ≤ log ((N : ℝ) / exp 1) := by
    rw [log_div hN0.ne' he.ne', log_exp]
    have : 2 ≤ log (N : ℝ) := by
      rw [← log_exp 2]; exact log_le_log (exp_pos 2) (le_trans (le_max_right _ _) hNr)
    linarith
  have hL : 0 < log (N : ℝ) := by
    have : log ((N : ℝ) / exp 1) = log N - 1 := by rw [log_div hN0.ne' he.ne', log_exp]
    linarith
  have h1 := hX N hXN
  have h2 := hX _ hXe
  have h3 := primeCounting_mul_log_ge N hN3
  set M := (N : ℝ) / exp 1 with hM
  have hM0 : 0 < M := by positivity
  have h2' : 7 / 8 * M ≤ Chebyshev.theta M := by
    have : M / (8 * log M) ≤ M / 8 := by
      apply div_le_div_of_nonneg_left hM0.le (by norm_num) (by linarith)
    linarith
  have hMe : (N : ℝ) = M * exp 1 := by rw [hM]; field_simp
  have he3 : exp (1 : ℝ) < 3 := by
    have := Real.exp_one_lt_d9; linarith
  -- (N / L) ≤ π  ⇔  N ≤ π L
  rw [div_le_iff₀ hL]
  set L := log (N : ℝ)
  have hθN : (N : ℝ) - N / (8 * L) ≤ Chebyshev.theta N := h1
  have hq : (N : ℝ) / (8 * L) ≤ 7 / 8 * M / L := by
    rw [div_le_div_iff₀ (by positivity) hL, hMe]
    nlinarith [mul_pos (mul_pos hM0 hL) (by linarith : (0 : ℝ) < 7 - exp 1)]
  have hq2 : 7 / 8 * M / L ≤ Chebyshev.theta M / L := by
    apply div_le_div_of_nonneg_right h2' hL.le
  linarith

end LeanLab.AlmostPrimeSums.S146PiLower

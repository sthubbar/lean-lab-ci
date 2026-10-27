/-
Tao 2012, Every odd number greater than 1 is the sum of at most five primes, arXiv 1201.6656v4,
Math. Comp. 83 (2014). Unit U-1555, run 20261026T1219Z-15327, track T1, DECOMPOSE.

Decomposition of Proposition 4.10, the mesoscopic L² estimate, Section 4 of the paper, into
leaves. Source read 2026-10-26 with WebFetch from arxiv.org/html/1201.6656 and
arxiv.org/pdf/1201.6656v4, Section 4 and the proof of Proposition 4.10 in full. Printed page
numbers were not visible in the fetched text, so leaves name the section, the proposition and the
equation numbers (4.3), (4.15), (4.16), (4.17).

Proposition 4.10. Suppose q = √x^♯. Let H ≥ 10² and D_H(α) = ∑_{h=1}^H e(hα). Then
  ∫_{ℝ/ℤ} |S_{η,q}(x,α)|² |D_H(α)|² dα ≤ (1 + ε) · 8 H² x ‖η‖²_∞,
  ε = 0.13 log x / H + (e^γ log log 2H + 2.507 / log log 2H) log 9H / (2H).      (4.15)

This file: the definitions, the Plancherel expansion, the diagonal and the off-diagonal leaves,
and the two cited inputs used there. Binary Goldbach is OPEN; nothing here bears on it directly.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Tao2012.Decomp1555

open Real Finset MeasureTheory
open scoped ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

/-! ## Definitions -/

/-- `e(t) = exp(2π i t)`, the paper's Section 2 notation. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

/-- The weight `Λ(n) 1_{(n,q)=1} η(n/x)` of the sum (4.1). -/
noncomputable def coef (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x)

/-- `S_{η,q}(x,α) = ∑_n Λ(n) e(αn) 1_{(n,q)=1} η(n/x)`, (4.1). The cutoff `η` is supported
in `[0,1]` throughout Section 4, so the sum runs over `n ≤ x`. -/
noncomputable def S (η : ℝ → ℝ) (q : ℕ) (x α : ℝ) : ℂ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), (coef η q x n : ℂ) * ee (α * n)

/-- The Dirichlet kernel `D_H(α) = ∑_{h=1}^H e(hα)`. -/
noncomputable def D (H : ℕ) (α : ℝ) : ℂ := ∑ h ∈ Icc 1 H, ee (h * α)

/-- The left side of Proposition 4.10, the integral over one period. -/
noncomputable def meso (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (H : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖S η q x α‖ ^ 2 * ‖D H α‖ ^ 2

/-- `q = √x^♯`, the product of the primes up to `√x`. -/
noncomputable def qx (x : ℝ) : ℕ := primorial ⌊Real.sqrt x⌋₊

/-- The correlation `∑_{n + h = m + h'} Λ(n)1 η(n/x) Λ(m)1 η(m/x)`, the summand of the
expanded integral in the proof of Proposition 4.10, with `m = n + h - h'`. -/
noncomputable def corr (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (h h' : ℕ) : ℝ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1),
    if n + h = m + h' then coef η q x n * coef η q x m else 0

/-- `#{p ≤ x : p + k prime, p + k ≤ x}` for an integer shift `k`. -/
noncomputable def twinCount (x : ℝ) (k : ℤ) : ℕ :=
  ((range (⌊x⌋₊ + 1)).filter fun p : ℕ =>
    Nat.Prime p ∧ 0 < (p : ℤ) + k ∧ ((p : ℤ) + k).natAbs.Prime ∧ ((p : ℤ) + k : ℝ) ≤ x).card

/-- The twin prime constant `𝔖₂ = 2 ∏_{p>2} (1 - 1/(p-1)²)`, as defined in Tao's Section 4. -/
noncomputable def twinConst : ℝ :=
  2 * ∏' p : Nat.Primes, (if 2 < (p : ℕ) then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)

/-- `∏_{p | k, p > 2} (p - 1)/(p - 2)`, the singular factor in Siebert's bound. -/
noncomputable def prodFac (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors, (if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1)

/-- `f(n) = 1_{(n,2)=1} μ²(n) ∏_{p | n, p > 2} 1/(p - 2)`, proof of Proposition 4.10. -/
noncomputable def f (n : ℕ) : ℝ :=
  if Odd n ∧ Squarefree n then ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) else 0

/-- `e^γ L + 2.507 / L`, the Rosser-Schoenfeld shape, evaluated at `L = log log 2H` in (4.15). -/
noncomputable def gRS (L : ℝ) : ℝ := exp eulerMascheroniConstant * L + 2.507 / L

/-- `ε` of (4.15), for real `x` and `H`. -/
noncomputable def eps (x H : ℝ) : ℝ :=
  0.13 * log x / H + gRS (log (log (2 * H))) * log (9 * H) / (2 * H)

/-! ## Cited inputs -/

/-- Cited, not proved in the lab: Rosser and Schoenfeld 1962, Theorem 12, `ψ(x) < 1.03883 x`
for `x > 0`, used by Tao through (4.3) as `ψ(x) ≤ 1.04 x`. -/
theorem rosser_schoenfeld_psi {x : ℝ} (hx : 0 < x) : Chebyshev.psi x ≤ 1.04 * x := by
  sorry

/-- Cited, not proved in the lab: Siebert 1976, Montgomery's weighted sieve for dimension two,
main theorem, in the form Tao uses in the proof of Proposition 4.10: for `x > 1` and an even
`k > 0`, `#{p ≤ x : p + k prime, p + k ≤ x} ≤ 8 𝔖₂ x / log² x ∏_{p | k, p > 2} (p-1)/(p-2)`. -/
theorem siebert {x : ℝ} (hx : 1 < x) {k : ℕ} (hk : 0 < k) (hke : Even k) :
    (twinCount x k : ℝ) ≤ 8 * twinConst * x / log x ^ 2 * prodFac k := by
  sorry

/-! ## Leaves -/

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, Section 4, first display:
expanding `|D_H|²` and using orthogonality of `e(kα)` on `ℝ/ℤ`,
`∫_0^1 |S_{η,q}(x,α)|² |D_H(α)|² dα = ∑_{h=1}^H ∑_{h'=1}^H ∑_{n + h = m + h'} c_n c_m`
with `c_n = Λ(n) 1_{(n,q)=1} η(n/x)`. -/
theorem plancherel_corr (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (H : ℕ) :
    meso η q x H = ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η q x h h' := by
  classical
  have orthog (k : ℤ) : (∫ α in (0 : ℝ)..1, ee (α * k)) = if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · simp [hk, ee]
    · rw [ite_eq_right hk]
      have hc : (2 * π * Complex.I * (k : ℂ)) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
      have he (α : ℝ) : ee (α * k) = Complex.exp ((2 * π * Complex.I * (k : ℂ)) * α) := by
        unfold ee
        congr 1
        push_cast
        ring
      simp_rw [he]
      rw [integral_exp_mul_complex hc]
      have hp : Complex.exp (2 * π * Complex.I * (k : ℂ)) = 1 := by
        convert Complex.exp_int_mul_two_pi_mul_I k using 2
        ring
      simp [hp]
  have norm_expansion {ι : Type} (s : Finset ι) (c : ι → ℝ) (k : ι → ℕ) (α : ℝ) :
      (‖∑ i ∈ s, (c i : ℂ) * ee (α * k i)‖ ^ 2 : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s, (c i * c j : ℂ) * ee (α * ((k i : ℝ) - k j)) := by
    have he (u v : ℝ) : ee u * conj (ee v) = ee (u - v) := by
      unfold ee
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      push_cast
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Complex.conj_ofReal, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [show (c i : ℂ) * ee (α * k i) * ((c j : ℂ) * conj (ee (α * k j))) =
      (c i * c j : ℂ) * (ee (α * k i) * conj (ee (α * k j))) by ring, he]
    congr 2
    ring
  have parseval {ι : Type} (s : Finset ι) (c : ι → ℝ) (k : ι → ℕ) :
      ∫ α in (0 : ℝ)..1, ‖∑ i ∈ s, (c i : ℂ) * ee (α * k i)‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, if k i = k j then c i * c j else 0 := by
    classical
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_pow]
    simp_rw [norm_expansion]
    have hi (i j : ι) : IntervalIntegrable
        (fun α : ℝ => (c i * c j : ℂ) * ee (α * ((k i : ℝ) - k j))) volume 0 1 := by
      unfold ee
      apply Continuous.intervalIntegrable
      fun_prop
    have hout (i : ι) : IntervalIntegrable
        (fun α : ℝ => ∑ j ∈ s, (c i * c j : ℂ) * ee (α * ((k i : ℝ) - k j))) volume 0 1 := by
      unfold ee
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_finsetSum (fun i _ => hout i)]
    push_cast
    apply sum_congr rfl
    intro i hi'
    rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
    apply sum_congr rfl
    intro j hj'
    rw [intervalIntegral.integral_const_mul]
    have he : (∫ α in (0 : ℝ)..1, ee (α * ((k i : ℝ) - k j))) =
        if k i = k j then 1 else 0 := by
      have h := orthog ((k i : ℤ) - k j)
      push_cast at h
      simpa only [sub_eq_zero, Nat.cast_inj] using h
    rw [he]
    split_ifs <;> simp_all
  have heeadd (u v : ℝ) : ee u * ee v = ee (u + v) := by
    unfold ee
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp (α : ℝ) : S η q x α * D H α =
      ∑ i ∈ (range (⌊x⌋₊ + 1)) ×ˢ (Icc 1 H),
        (coef η q x i.1 : ℂ) * ee (α * (i.1 + i.2 : ℕ)) := by
    unfold S D
    rw [sum_product, sum_mul]
    apply sum_congr rfl
    intro n hn
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    rw [mul_assoc, heeadd]
    congr 2
    push_cast
    ring
  have hparse := parseval ((range (⌊x⌋₊ + 1)) ×ˢ (Icc 1 H))
    (fun i => coef η q x i.1) (fun i => i.1 + i.2)
  simp_rw [← hp, norm_mul, mul_pow] at hparse
  unfold meso
  rw [hparse]
  simp only [sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro h hh
  calc
    _ = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ h' ∈ Icc 1 H, ∑ m ∈ range (⌊x⌋₊ + 1),
        if n + h = m + h' then coef η q x n * coef η q x m else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [sum_comm]
    _ = _ := by rw [sum_comm]; rfl

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the diagonal `h = h'`, using
`Λ(n)² ≤ Λ(n) log x` for `n ≤ x` and `0 ≤ η ≤ M`:
`∑_n c_n² ≤ M log x ∑_n c_n`. -/
theorem corr_diag_le (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (h : ℕ) :
    corr η q x h h ≤ M * log x * ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n := by
  dsimp [corr]
  have H : ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h then coef η q x n * coef η q x m else 0) = ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ^ 2 := by
    apply sum_congr rfl
    intro n hn
    have : ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h then coef η q x n * coef η q x m else 0) = ∑ m ∈ range (⌊x⌋₊ + 1), (if m = n then coef η q x n * coef η q x m else 0) := by
      apply sum_congr rfl
      intro m _hm
      have : n + h = m + h ↔ m = n := by omega
      simp only [this]
    rw [this, sum_ite_eq']
    have : n ∈ range (⌊x⌋₊ + 1) := hn
    rw [ite_eq_left_iff.mpr (fun h_not => False.elim (h_not this)), sq]
  rw [H]
  have H2 : M * log x * ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n = ∑ n ∈ range (⌊x⌋₊ + 1), M * log x * coef η q x n := by
    rw [mul_sum]
  rw [H2]
  apply sum_le_sum
  intro n hn
  dsimp [coef]
  have h1 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (if Nat.Coprime n q then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have h3 : (if Nat.Coprime n q then (1 : ℝ) else 0) ^ 2 = (if Nat.Coprime n q then 1 else 0) := by
    split_ifs <;> norm_num
  have h4 : 0 ≤ η (n / x) := hη0 _
  have h5 : η (n / x) ≤ M := hηM _
  by_cases hΛ : Λ n = 0
  · simp only [hΛ, zero_mul, mul_zero, sq, le_refl]
  have hn_pos : 0 < n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by linarith
    subst this
    have : Λ 0 = 0 := rfl
    contradiction
  have hn_le : (n : ℝ) ≤ x := by
    have : n ≤ ⌊x⌋₊ := by
      rw [mem_range] at hn
      omega
    calc (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ x := Nat.floor_le (by linarith)
  have hlog_pos : 0 ≤ log x := by
    apply Real.log_nonneg hx
  have hΛ_le : Λ n ≤ log x := by
    calc Λ n ≤ log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ log x := log_le_log (by exact_mod_cast hn_pos) hn_le
  have H3 : 0 ≤ log x * Λ n * (if Nat.Coprime n q then 1 else 0) := by
    have : 0 ≤ log x * Λ n := mul_nonneg hlog_pos h1
    exact mul_nonneg this h2
  calc (Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x)) ^ 2
    _ = (Λ n) ^ 2 * (if Nat.Coprime n q then 1 else 0) ^ 2 * η (n / x) ^ 2 := by ring
    _ = (Λ n) ^ 2 * (if Nat.Coprime n q then 1 else 0) * η (n / x) ^ 2 := by rw [h3]
    _ = Λ n * Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x) ^ 2 := by ring
    _ ≤ log x * Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x) ^ 2 := by gcongr
    _ = log x * Λ n * (if Nat.Coprime n q then 1 else 0) * (η (n / x) * η (n / x)) := by ring
    _ ≤ log x * Λ n * (if Nat.Coprime n q then 1 else 0) * (M * η (n / x)) := by gcongr
    _ = M * log x * (Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x)) := by ring

/-- LEAF. Unit U-1555. Tao 2012, (4.3), first inequality: for `0 ≤ η ≤ M`,
`∑_{n ≤ x} Λ(n) 1_{(n,q)=1} η(n/x) ≤ M ψ(x)`. -/
theorem sum_coef_le_psi (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    (q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ≤ M * Chebyshev.psi x := by
  have H : ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ≤ ∑ n ∈ range (⌊x⌋₊ + 1), M * Λ n := by
    apply sum_le_sum
    intro n _hn
    dsimp [coef]
    have h1 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : 0 ≤ (if Nat.Coprime n q then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have h3 : (if Nat.Coprime n q then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have h4 : 0 ≤ η (n / x) := hη0 _
    have h5 : η (n / x) ≤ M := hηM _
    calc Λ n * (if Nat.Coprime n q then 1 else 0) * η (n / x)
      _ ≤ Λ n * 1 * η (n / x) := by gcongr
      _ = Λ n * η (n / x) := by ring
      _ ≤ Λ n * M := by gcongr
      _ = M * Λ n := by ring
  calc ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n
    _ ≤ ∑ n ∈ range (⌊x⌋₊ + 1), M * Λ n := H
    _ = M * ∑ n ∈ range (⌊x⌋₊ + 1), Λ n := by rw [mul_sum]
    _ = M * Chebyshev.psi x := by
      rw [Chebyshev.psi_eq_sum_Icc x]
      have : range (⌊x⌋₊ + 1) = Icc 0 ⌊x⌋₊ := by
        ext k
        simp only [mem_range, mem_Icc, zero_le, true_and]
        omega
      rw [this]

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, Section 4: with `q = √x^♯` and
`x ≥ 4`, `Λ(n) 1_{(n,q)=1}` for `n ≤ x` is supported on odd primes. -/
theorem coef_support_odd_prime {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : (n : ℝ) ≤ x)
    (hΛ : Λ n ≠ 0) (hq : Nat.Coprime n (qx x)) : n.Prime ∧ Odd n := by
  have H_prime_pow : IsPrimePow n := by
    by_contra h
    have : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h
    contradiction
  have h_ex : ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ p ^ k = n := by
    rcases H_prime_pow with ⟨p, k, hp, hk, h_eq⟩
    use p, k
    exact ⟨hp.nat_prime, hk, h_eq⟩
  rcases h_ex with ⟨p, k, hp_prime, hk, rfl⟩
  have h_k_eq_1 : k = 1 := by
    by_contra h_k_ne_1
    have h_k_ge_2 : k ≥ 2 := by omega
    have h_p_le_sqrt_x : p ≤ ⌊Real.sqrt x⌋₊ := by
      apply Nat.le_floor
      have h1 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := by
        have h_p_ge_1 : (1 : ℝ) ≤ p := by exact_mod_cast hp_prime.one_lt.le
        apply pow_le_pow_right₀ h_p_ge_1 h_k_ge_2
      have h2 : (p : ℝ) ^ k = (p ^ k : ℕ) := by norm_cast
      have h3 : (p ^ k : ℕ) ≤ x := hn
      calc (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((p : ℝ) ^ k) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt (p ^ k : ℕ) := by rw [h2]
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h3
    have h_p_dvd_qx : p ∣ qx x := by
      dsimp [qx]
      apply dvd_trans hp_prime.dvd_primorial
      apply primorial_dvd_primorial h_p_le_sqrt_x
    have h_p_dvd_n : p ∣ p ^ k := dvd_pow_self p hk.ne'
    have : ¬Nat.Coprime (p ^ k) (qx x) := by
      apply Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt h_p_dvd_n h_p_dvd_qx
    contradiction
  subst h_k_eq_1
  rw [pow_one]
  have h_odd : Odd p := by
    by_contra h_even
    have h_even' : ¬ p % 2 = 1 := by
      intro h_mod
      have : Odd p := by rw [Nat.odd_iff] ; exact h_mod
      contradiction
    have h_p_2 : p = 2 := hp_prime.eq_two_or_odd.resolve_right h_even'
    subst h_p_2
    have h_2_dvd_qx : 2 ∣ qx x := by
      dsimp [qx]
      apply dvd_trans Nat.prime_two.dvd_primorial
      apply primorial_dvd_primorial
      have h_sqrt : 2 ≤ ⌊Real.sqrt x⌋₊ := by
        apply Nat.le_floor
        calc (2 : ℝ) = Real.sqrt 4 := by norm_num
          _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
      exact h_sqrt
    have : ¬Nat.Coprime 2 (qx x) := by
      apply Nat.not_coprime_of_dvd_of_dvd Nat.prime_two.one_lt (dvd_refl 2) h_2_dvd_qx
    contradiction
  exact ⟨hp_prime, h_odd⟩

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, the off-diagonal bound before
(4.16): for `h ≠ h'`, `x ≥ 4`, `q = √x^♯`, `0 ≤ η ≤ M`, the correlation vanishes unless
`h - h'` is even, and then it is at most `M² log² x #{p ≤ x : p + h - h' prime, p + h - h' ≤ x}`. -/
theorem corr_offdiag_le (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx : 4 ≤ x) {h h' : ℕ} (hne : h ≠ h') :
    corr η (qx x) x h h' ≤
      M ^ 2 * log x ^ 2 *
        (if Even ((h : ℤ) - h') then (twinCount x ((h : ℤ) - h') : ℝ) else 0) := by
  classical
  let r := range (⌊x⌋₊ + 1)
  have hx0 : 0 ≤ x := by linarith
  have hM : 0 ≤ M := (hη0 0).trans (hηM 0)
  have hlog : 0 ≤ log x := log_nonneg (by linarith)
  have hnx {n : ℕ} (hn : n ∈ r) : (n : ℝ) ≤ x :=
    (Nat.le_floor_iff hx0).mp (by simpa [r, Nat.lt_succ_iff] using hn)
  have hc0 (n : ℕ) : 0 ≤ coef η (qx x) x n := by
    unfold coef
    have := hη0 (n / x)
    have : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    split_ifs <;> positivity
  have hcb {n : ℕ} (hn : n ∈ r) : coef η (qx x) x n ≤ M * log x := by
    by_cases hn0 : n = 0
    · subst n
      simpa [coef] using mul_nonneg hM hlog
    have hl : Λ n ≤ log x := (ArithmeticFunction.vonMangoldt_le_log).trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (hnx hn))
    unfold coef
    split_ifs
    · simp only [mul_one]
      calc Λ n * η (n / x) ≤ log x * M :=
        mul_le_mul hl (hηM _) (hη0 _) hlog
        _ = M * log x := mul_comm _ _
    · simp only [mul_zero, zero_mul]
      exact mul_nonneg hM hlog
  have hsupport {n : ℕ} (hn : n ∈ r) (hc : coef η (qx x) x n ≠ 0) : n.Prime ∧ Odd n := by
    have hΛ : Λ n ≠ 0 := by intro he; exact hc (by simp [coef, he])
    have hq : n.Coprime (qx x) := by
      by_contra hq
      exact hc (by simp [coef, hq])
    exact coef_support_odd_prime hx (hnx hn) hΛ hq
  have hbound {n m : ℕ} (hn : n ∈ r) (hm : m ∈ r) :
      coef η (qx x) x n * coef η (qx x) x m ≤ M ^ 2 * log x ^ 2 := by
    have ht := mul_le_mul (hcb hn) (hcb hm) (hc0 m) (by positivity : 0 ≤ M * log x)
    nlinarith
  have hcond {n m : ℕ} (hn : n ∈ r) (hm : m ∈ r) (he : n + h = m + h')
      (hc : coef η (qx x) x n * coef η (qx x) x m ≠ 0) :
      Even ((h : ℤ) - h') ∧
        (n.Prime ∧ 0 < (n : ℤ) + ((h : ℤ) - h') ∧
          ((n : ℤ) + ((h : ℤ) - h')).natAbs.Prime ∧
          ((n : ℤ) + ((h : ℤ) - h') : ℝ) ≤ x) := by
    have hn' := hsupport hn (left_ne_zero_of_mul hc)
    have hm' := hsupport hm (right_ne_zero_of_mul hc)
    have hshift : (n : ℤ) + ((h : ℤ) - h') = m := by omega
    have heven : Even ((h : ℤ) - h') := by
      obtain ⟨a, ha⟩ := hn'.2
      obtain ⟨b, hb⟩ := hm'.2
      exact ⟨(b : ℤ) - a, by omega⟩
    refine ⟨heven, hn'.1, ?_, ?_, ?_⟩
    · rw [hshift]; exact_mod_cast hm'.1.pos
    · simpa [hshift] using hm'.1
    · have hz := congrArg (fun z : ℤ => (z : ℝ)) hshift
      push_cast at hz
      push_cast
      linarith [hnx hm]
  let T : ℕ → Prop := fun n => n.Prime ∧ 0 < (n : ℤ) + ((h : ℤ) - h') ∧
    ((n : ℤ) + ((h : ℤ) - h')).natAbs.Prime ∧
    ((n : ℤ) + ((h : ℤ) - h') : ℝ) ≤ x
  have hTc : twinCount x ((h : ℤ) - h') = (r.filter T).card := by
    unfold twinCount
    congr 1
    apply filter_congr
    intro n hn
    dsimp only [T]
    push_cast
    rfl
  have hK : 0 ≤ M ^ 2 * log x ^ 2 := by positivity
  by_cases heven : Even ((h : ℤ) - h')
  · rw [ite_eq_left heven]
    have hrow {n : ℕ} (hn : n ∈ r) :
        ∑ m ∈ r, (if n + h = m + h' then coef η (qx x) x n * coef η (qx x) x m else 0) ≤
          if T n then M ^ 2 * log x ^ 2 else 0 := by
      by_cases ht : T n
      · rw [ite_eq_left ht]
        have hind : (∑ m ∈ r, if n + h = m + h' then (1 : ℝ) else 0) ≤ 1 := by
          rw [← sum_filter]
          simp only [sum_const, nsmul_eq_mul, mul_one]
          have hc : (r.filter (fun m => n + h = m + h')).card ≤ 1 := by
            apply card_le_one.mpr
            intro a ha b hb
            have ha' := (mem_filter.mp ha).2
            have hb' := (mem_filter.mp hb).2
            omega
          exact_mod_cast hc
        have hterms : (∑ m ∈ r, if n + h = m + h' then coef η (qx x) x n * coef η (qx x) x m else 0) ≤
            M ^ 2 * log x ^ 2 * (∑ m ∈ r, if n + h = m + h' then (1 : ℝ) else 0) := by
          rw [mul_sum]
          apply sum_le_sum
          intro m hm
          split_ifs
          · simpa only [mul_one] using hbound hn hm
          · simp
        exact hterms.trans (by simpa using mul_le_mul_of_nonneg_left hind hK)
      · rw [ite_eq_right ht]
        apply le_of_eq
        apply sum_eq_zero
        intro m hm
        split_ifs with he
        · by_contra hprod
          exact ht (hcond hn hm he hprod).2
        · rfl
    have hb := sum_le_sum (fun n hn => hrow hn)
    have heq : (∑ n ∈ r, if T n then M ^ 2 * log x ^ 2 else 0) =
        M ^ 2 * log x ^ 2 * (twinCount x ((h : ℤ) - h') : ℝ) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      rw [hTc]
      ring
    rw [heq] at hb
    exact hb
  · rw [ite_eq_right heven, mul_zero]
    apply le_of_eq
    unfold corr
    apply sum_eq_zero
    intro n hn
    apply sum_eq_zero
    intro m hm
    split_ifs with he
    · by_contra hprod
      exact heven (hcond hn hm he hprod).1
    · rfl

/-- LEAF. Unit U-1555. Tao 2012, proof of Proposition 4.10, Siebert's bound for a negative
shift: the substitution `p ↦ p + k` gives `#{p ≤ x : p - k prime, p - k ≤ x}` equal to
`#{p ≤ x : p + k prime, p + k ≤ x}` for `k > 0`. -/
theorem twinCount_neg (x : ℝ) (k : ℕ) : twinCount x (-(k : ℤ)) = twinCount x k := by
  classical
  by_cases hx : 0 ≤ x
  · unfold twinCount
    apply card_nbij' (fun p => p - k) (fun p => p + k)
    · intro p hp
      simp only [mem_coe, mem_filter, mem_range] at hp ⊢
      have hkp : k < p := by omega
      have he : (p : ℤ) + -(k : ℤ) = ((p - k : ℕ) : ℤ) := by omega
      have he' : ((p - k : ℕ) : ℤ) + k = p := by omega
      have hpr : (p : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (by omega)
      refine ⟨by omega, ?_, by omega, ?_, ?_⟩
      · simpa only [he, Int.natAbs_natCast] using hp.2.2.2.1
      · simpa only [he', Int.natAbs_natCast] using hp.2.1
      · push_cast
        rw [← Nat.cast_add, Nat.sub_add_cancel hkp.le]
        exact hpr
    · intro p hp
      simp only [mem_coe, mem_filter, mem_range] at hp ⊢
      have he : ((p + k : ℕ) : ℤ) + -(k : ℤ) = p := by omega
      have hpx : ((p + k : ℕ) : ℝ) ≤ x := by
        simpa only [Int.cast_add, Int.cast_natCast, Nat.cast_add] using hp.2.2.2.2
      have hpp := hp.2.1.pos
      refine ⟨by have := (Nat.le_floor_iff hx).mpr hpx; omega, ?_, by omega, ?_, ?_⟩
      · simpa only [← Int.natCast_add, Int.natAbs_natCast] using hp.2.2.2.1
      · simpa only [he, Int.natAbs_natCast] using hp.2.1
      · have hpr : (p : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (by omega)
        push_cast
        linarith
    · intro p hp
      simp only [mem_coe, mem_filter] at hp
      dsimp only
      omega
    · intro p hp
      dsimp only
      omega
  · have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hz (j : ℤ) : ((range (⌊x⌋₊ + 1)).filter fun p : ℕ =>
        Nat.Prime p ∧ 0 < (p : ℤ) + j ∧ ((p : ℤ) + j).natAbs.Prime ∧
          ((p : ℤ) + j : ℝ) ≤ x) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp
      have hp0 : p = 0 := by simpa [hfloor] using hp
      subst p
      rintro ⟨hprime, -⟩
      exact Nat.not_prime_zero hprime
    unfold twinCount
    rw [hz, hz]

/-! ## Assembly: Siebert's bound for every even nonzero shift -/

/-- Siebert's bound for any even integer shift `k ≠ 0`, as the proof of Proposition 4.10
uses it with `k = h - h'`. CONDITIONAL ON the leaf `twinCount_neg` and the cited `siebert`. -/
theorem siebert_int {x : ℝ} (hx : 1 < x) {k : ℤ} (hk : k ≠ 0) (hke : Even k) :
    (twinCount x k : ℝ) ≤ 8 * twinConst * x / log x ^ 2 * prodFac k.natAbs := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · have hn : 0 < n := by omega
    have he : Even n := (Int.even_coe_nat n).mp hke
    simpa using siebert hx hn he
  · have hn : 0 < n := by omega
    have he : Even n := (Int.even_coe_nat n).mp (even_neg.mp hke)
    rw [twinCount_neg]
    simpa using siebert hx hn he

/-- The diagonal: `∑_n c_n² ≤ 1.04 M² x log x`, the bound `H x log x` of the proof up to the
factor `1.04` of (4.3). CONDITIONAL ON the leaves `corr_diag_le`, `sum_coef_le_psi` and the
cited `rosser_schoenfeld_psi`. -/
theorem diag_le (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (h : ℕ) :
    corr η q x h h ≤ 1.04 * M ^ 2 * x * log x := by
  have hM : 0 ≤ M := (hη0 0).trans (hηM 0)
  have hlog : 0 ≤ log x := Real.log_nonneg hx
  have h1 := corr_diag_le η hη0 hηM q hx h
  have h2 := sum_coef_le_psi η hη0 hηM q hx
  have h3 := rosser_schoenfeld_psi (by linarith : (0 : ℝ) < x)
  have hML : 0 ≤ M * log x := mul_nonneg hM hlog
  calc corr η q x h h ≤ M * log x * ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n := h1
    _ ≤ M * log x * (M * Chebyshev.psi x) := mul_le_mul_of_nonneg_left h2 hML
    _ ≤ M * log x * (M * (1.04 * x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hM) hML
    _ = 1.04 * M ^ 2 * x * log x := by ring

/-- Off-diagonal pointwise: for `h ≠ h'`, the correlation is at most
`8 𝔖₂ M² x ∏_{p | h-h', p>2} (p-1)/(p-2)` when `h - h'` is even and `0` otherwise.
CONDITIONAL ON the leaves `corr_offdiag_le`, `twinCount_neg` and the cited `siebert`. -/
theorem offdiag_le (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx : 4 ≤ x) {h h' : ℕ} (hne : h ≠ h') :
    corr η (qx x) x h h' ≤
      (if Even ((h : ℤ) - h') then 8 * twinConst * M ^ 2 * x * prodFac ((h : ℤ) - h').natAbs
        else 0) := by
  have h1 := corr_offdiag_le η hη0 hηM hx hne
  split_ifs at h1 ⊢ with he
  · have hk : ((h : ℤ) - h') ≠ 0 := by
      intro h0; apply hne; omega
    have h2 := siebert_int (by linarith : (1 : ℝ) < x) hk he
    have hlog : 0 < log x := Real.log_pos (by linarith)
    have hM2 : 0 ≤ M ^ 2 * log x ^ 2 := by positivity
    calc corr η (qx x) x h h' ≤ M ^ 2 * log x ^ 2 * (twinCount x ((h : ℤ) - h') : ℝ) := h1
      _ ≤ M ^ 2 * log x ^ 2 *
          (8 * twinConst * x / log x ^ 2 * prodFac ((h : ℤ) - h').natAbs) :=
          mul_le_mul_of_nonneg_left h2 hM2
      _ = 8 * twinConst * M ^ 2 * x * prodFac ((h : ℤ) - h').natAbs := by
          field_simp
  · simpa using h1

end LeanLab.Tao2012.Decomp1555

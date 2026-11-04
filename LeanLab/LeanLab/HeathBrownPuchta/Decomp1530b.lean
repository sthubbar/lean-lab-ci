/-
Heath-Brown and Puchta 2002, Integers represented as a sum of primes and powers of two,
arXiv math/0201299. Unit U-1530, run 20261026T0004Z-24325, type DECOMPOSE, file b of three.

Lemma 8, Section 5: `J = ∫₀¹ |S(α) T(α)|² dα ≤ {C₀ C₁ C₂ / log² 2 + 1/log 2 + o(1)} N`, with
`S(α) = Σ_{ϖN < p ≤ N} e(αp)`, `T(α) = Σ_{1 ≤ ν ≤ L} e(α 2^ν)`, `L = [log(N/2K)/log 2]`.
In Assembly.lean it enters through `lemma9_out_of_lemma8` as the hypothesis `h8`, still open.
The proof in Section 5, split here into leaves:

* `J = Σ_{μ, ν ≤ L} r(2^μ - 2^ν)`, `r(n) = #{ϖN < p₁, p₂ ≤ N : p₁ - p₂ = n}`;
* diagonal `μ = ν`: `L` terms each `π(N) - π(ϖN) ≤ (1 + o(1)) N / log N`, total `≤ N/log 2`;
* off diagonal: Chen's bound `r(n) ≤ C₀ C₁ h(n) N / log² N` stays an open input, not split
  here; `h(2^μ - 2^ν) = h(2^{μ-ν} - 1)`; grouping by `l = |μ - ν|` gives
  `2 Σ_{l ≤ L} (L - l) h(2^l - 1)`;
* `Σ_{j ≤ J} h(2^j - 1) = Σ_e κ(e) [J/e] ≤ C₂ J`, then partial summation gives
  `Σ_{l ≤ L} (L - l) h(2^l - 1) ≤ C₂ L²/2`, so the off diagonal is `≤ C₀ C₁ C₂ N / log² 2`.

Only the upper bound `Σ_{j ≤ J} h(2^j - 1) ≤ C₂ J` is needed for Lemma 8; the paper states the
asymptotic `C₂ J + O(J^{1/2})`. Page numbers are not visible in the arXiv text read for this
unit; Section and display numbers are given. The paper copy was NOT FOUND in either lab location;
the text used is arXiv math/0201299 through WebFetch, 2026-10-26.

ASSEMBLY, real proofs, CONDITIONAL ON the leaves below and using the lab's proved
`sum_kappaTrue_divisors`: `hsum_bound`, `offdiag_total`, `offdiag_main_term`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.HeathBrownPuchta.Decomp1530a
import LeanLab.HeathBrownPuchta.C2Inputs
import LeanLab.PNTPort.StrongPNT.StrongPNT

namespace LeanLab.HeathBrownPuchta.Decomp1530b

open Finset Real Filter LeanLab.HeathBrownPuchta.Decomp1530a
open LeanLab.HeathBrownPuchta.Lemma8Const LeanLab.HeathBrownPuchta.C2Inputs
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- The primes `p` with `ϖN < p ≤ N`, Section 2. -/
noncomputable def primesIn (N : ℕ) (w : ℝ) : Finset ℕ :=
  (Icc 1 N).filter fun p => p.Prime ∧ w * N < p

/-- `S(α) = Σ_{ϖN < p ≤ N} e(αp)`, Section 2. -/
noncomputable def Sp (N : ℕ) (w : ℝ) (α : ℝ) : ℂ := ∑ p ∈ primesIn N w, ee (α * p)

/-- `T(α) = Σ_{1 ≤ ν ≤ L} e(α 2^ν)`, Section 2. -/
noncomputable def Tp (L : ℕ) (α : ℝ) : ℂ := ∑ ν ∈ Icc 1 L, ee (α * 2 ^ ν)

/-- `J = ∫₀¹ |S(α) T(α)|² dα`, Section 5. -/
noncomputable def Jint (N : ℕ) (w : ℝ) (L : ℕ) : ℝ := ∫ α in (0 : ℝ)..1, ‖Sp N w α * Tp L α‖ ^ 2

/-- `r(n) = #{ϖN < p₁, p₂ ≤ N : p₁ - p₂ = n}`, Section 5. -/
noncomputable def rcount (N : ℕ) (w : ℝ) (n : ℤ) : ℕ :=
  ((primesIn N w ×ˢ primesIn N w).filter fun x => (x.1 : ℤ) - x.2 = n).card

/-- `L = [log(N/2K)/log 2]`, Section 2. -/
noncomputable def Lpar (N K : ℕ) : ℕ := ⌊Real.log (N / (2 * K)) / Real.log 2⌋₊

/-! ### Leaves: the expansion of `J` -/

/-- LEAF. Unit U-1530. Orthogonality: `∫₀¹ e(αm) dα` is `1` for `m = 0` and `0` for every other
integer `m`; Section 5, the expansion of `J`. -/
theorem orth (m : ℤ) : ∫ α in (0 : ℝ)..1, ee (α * m) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [ee]
  · rw [if_neg hm]
    unfold ee
    have hc : 2 * (π : ℂ) * Complex.I * m ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero) (by exact_mod_cast hm)
    have hh := integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) hc
    have hp : Complex.exp (2 * (π : ℂ) * Complex.I * m) = 1 := by
      simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I m
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hp, sub_self, zero_div] at hh
    convert hh using 1
    apply intervalIntegral.integral_congr
    intro α hα
    congr 1
    push_cast
    ring

/-- Finite character Parseval identity, paper page 20, the first expansion of Lemma 8. -/
theorem finite_parseval {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∫ α in (0 : ℝ)..1, ‖∑ i ∈ s, ee (α * f i)‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (if f i = f j then (1 : ℝ) else 0) := by
  classical
  have hn (z : ℂ) : Complex.ofReal (‖z‖ ^ 2) = z * (starRingEnd ℂ) z := by
    simpa only [Complex.normSq_eq_norm_sq] using (Complex.mul_conj z).symm
  have hc (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hp (α : ℝ) : Complex.ofReal (‖∑ i ∈ s, ee (α * f i)‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, ee (α * ((f i - f j : ℤ) : ℝ)) := by
    rw [hn]
    simp only [map_sum, hc, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [← hadd]
    congr 1
    push_cast
    ring
  have hex (i j : ι) : Continuous fun α : ℝ => ee (α * ((f i - f j : ℤ) : ℝ)) := by
    unfold ee
    fun_prop
  have hinner (i : ι) :
      (∫ α in (0 : ℝ)..1, ∑ j ∈ s, ee (α * ((f i - f j : ℤ) : ℝ))) =
        ∑ j ∈ s, ∫ α in (0 : ℝ)..1, ee (α * ((f i - f j : ℤ) : ℝ)) :=
    intervalIntegral.integral_finsetSum (fun j hj => (hex i j).intervalIntegrable 0 1)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun i hi => by
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop)]
  simp_rw [hinner, orth, sub_eq_zero]
  push_cast
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

/-- LEAF. Unit U-1530. `J = Σ_{1 ≤ μ, ν ≤ L} r(2^μ - 2^ν)`; Section 5, first display of the
proof of Lemma 8. -/
theorem J_expand (N : ℕ) (w : ℝ) (L : ℕ) :
    Jint N w L = ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (rcount N w ((2 : ℤ) ^ μ - 2 ^ ν) : ℝ) := by
  classical
  let s := Icc 1 L ×ˢ primesIn N w
  let f : ℕ × ℕ → ℤ := fun x => x.2 - (2 : ℤ) ^ x.1
  have hc (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have heq (α : ℝ) : Sp N w α * (starRingEnd ℂ) (Tp L α) = ∑ x ∈ s, ee (α * f x) := by
    unfold Sp Tp
    simp only [map_sum, hc, mul_sum, sum_mul]
    dsimp [s, f]
    rw [sum_product]
    apply sum_congr rfl
    intro μ hμ
    apply sum_congr rfl
    intro p hp
    rw [← hadd]
    congr 1
    push_cast
    ring
  calc
    Jint N w L = ∫ α in (0 : ℝ)..1, ‖∑ x ∈ s, ee (α * f x)‖ ^ 2 := by
      unfold Jint
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [← heq]
      simp [norm_mul]
    _ = ∑ x ∈ s, ∑ y ∈ s, (if f x = f y then (1 : ℝ) else 0) := finite_parseval s f
    _ = _ := by
      dsimp [s, f]
      simp_rw [sum_product]
      apply sum_congr rfl
      intro μ hμ
      rw [sum_comm]
      apply sum_congr rfl
      intro ν hν
      unfold rcount
      simp only [Finset.card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      have hi : ((p : ℤ) - (2 : ℤ) ^ μ = q - (2 : ℤ) ^ ν) ↔
          (p : ℤ) - q = (2 : ℤ) ^ μ - (2 : ℤ) ^ ν := by omega
      simp only [hi]

/-! ### Leaves: the diagonal -/

/-- The prime number theorem in the form used below: for every `δ > 0`, `ψ x ≤ (1 + δ) x`
eventually. Only the vanishing of the error term is used, not its rate. -/
private theorem eventually_psi_le_one_add_mul (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + δ) * x := by
  obtain ⟨c, hc, hO⟩ := StrongPNT
  -- `c * (log x)^(1/2) → ∞`, so the error factor `exp (-c * (log x)^(1/2))` tends to `0`
  have hu : Tendsto (fun x : ℝ => c * (Real.log x) ^ ((1 : ℝ) / 2)) atTop atTop :=
    Tendsto.const_mul_atTop hc
      (tendsto_rpow_atTop (by norm_num) |>.comp Real.tendsto_log_atTop)
  have hzero : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))
      atTop (nhds 0) := by
    have h := (Real.tendsto_exp_atTop.comp hu).inv_tendsto_atTop
    convert h using 1
    funext x
    simp [Real.exp_neg, neg_mul]
  -- hence the error term is `o x`
  have hg : (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))
      =o[atTop] fun x : ℝ => x := by
    rw [Asymptotics.isLittleO_iff]
    intro d hd
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) ≤ d :=
      hzero.eventually (Iic_mem_nhds hd)
    filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hpos : (0 : ℝ) ≤ Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0, abs_of_nonneg hpos]
    nlinarith
  have hfo : (ChebyshevPsi - id) =o[atTop] fun x : ℝ => x :=
    hO.trans_isLittleO hg
  have hb := (Asymptotics.isLittleO_iff.mp hfo) hδ
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hle : Chebyshev.psi x - x ≤ |Chebyshev.psi x - x| := le_abs_self _
  have hx' : |Chebyshev.psi x - x| ≤ δ * x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx0, Pi.sub_apply, ChebyshevPsi, id_eq] using hx
  linarith

/-- `#(primesIn N w) ≤ π N`: the primes of the window are primes `≤ N`. -/
private theorem card_primesIn_le_primeCounting' (N : ℕ) (w : ℝ) :
    (primesIn N w).card ≤ Nat.primeCounting N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  simp only [primesIn, Finset.mem_filter, Finset.mem_Icc] at hp
  exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2.1⟩

/-- LEAF. Unit U-1530. The prime number theorem upper half on `(ϖN, N]`: for `ϖ ≥ 0` and every
`ε > 0`, eventually `#{ϖN < p ≤ N} ≤ (1 + ε) N / log N`; Section 5, the diagonal terms of the
proof of Lemma 8. -/
theorem pi_upper {w : ℝ} (hw : 0 ≤ w) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ((primesIn N w).card : ℝ) ≤ (1 + ε) * N / Real.log N := by
  intro ε hε
  obtain ⟨C, hCpos, hCW⟩ := Chebyshev.integral_theta_div_log_sq_isBigO.exists_pos
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨ε / 2, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- the integrand is `o(x / log x)`, so it is below `δ x / log x` far out
  have hlog : ∀ᶠ x : ℝ in atTop, C / Real.log x ≤ δ := by
    have h1 : ∀ᶠ x : ℝ in atTop, C / δ ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (C / δ))
    filter_upwards [h1, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    rw [div_le_iff₀ hl]
    have hCe : δ * (C / δ) = C := by field_simp
    nlinarith [hx, hδ, hCpos]
  have key : ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1 + ε) * x / Real.log x := by
    filter_upwards [eventually_psi_le_one_add_mul δ hδ, hCW.bound, hlog,
      eventually_ge_atTop (2 : ℝ)] with x hψ hI hlogx hx2
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2]
    -- main term: `θ x ≤ ψ x ≤ (1 + δ) x`
    have hmain : Chebyshev.theta x / Real.log x ≤ (1 + δ) * x / Real.log x := by
      apply div_le_div_of_nonneg_right _ hl.le
      exact (Chebyshev.theta_le_psi x).trans hψ
    -- integral term: at most `C x / log² x`
    have hint : ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)
        ≤ C * (x / Real.log x ^ 2) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / Real.log x ^ 2)] at hI
      exact (le_abs_self _).trans hI
    have htail : C * (x / Real.log x ^ 2) ≤ δ * (x / Real.log x) := by
      have he : C * (x / Real.log x ^ 2) = (C / Real.log x) * (x / Real.log x) := by
        field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_right hlogx (by positivity)
    have harith : (1 + δ) * x / Real.log x + δ * (x / Real.log x)
        = (1 + ε) * x / Real.log x := by
      have h2δ : δ + δ = ε := by rw [hδdef]; ring
      field_simp
      nlinarith
    linarith [hmain, hint, htail, harith.ge]
  have hnat : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting ⌊(N : ℝ)⌋₊ : ℝ) ≤ (1 + ε) * (N : ℝ) / Real.log (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually key
  filter_upwards [hnat] with N hN
  rw [Nat.floor_natCast] at hN
  calc ((primesIn N w).card : ℝ) ≤ (Nat.primeCounting N : ℝ) := by
        exact_mod_cast card_primesIn_le_primeCounting' N w
    _ ≤ (1 + ε) * N / Real.log N := hN

/-- LEAF. Unit U-1530. For `N ≥ 1` and `K ≥ 1`, `L = [log(N/2K)/log 2] ≤ log N/log 2`; Section 2,
the definition of `L`. -/
theorem Lpar_le_log {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    (Lpar N K : ℝ) ≤ Real.log N / Real.log 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold Lpar
  by_cases hz : 0 ≤ Real.log ((N : ℝ) / (2 * K)) / Real.log 2
  · apply (Nat.floor_le hz).trans
    apply div_le_div_of_nonneg_right _ h2.le
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
    nlinarith
  · rw [Nat.floor_of_nonpos (le_of_not_ge hz)]
    simpa using div_nonneg hlog h2.le

/-- LEAF. Unit U-1530. For `N ≥ 1` and `K ≥ 1`,
`L ≥ log N/log 2 - (1 + log(2K)/log 2)`; Section 2, the definition of `L`, as needed for
the exponent in Section 7. -/
theorem Lpar_ge_log {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    Real.log N / Real.log 2 - (1 + Real.log (2 * K) / Real.log 2) ≤ Lpar N K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := Nat.lt_floor_add_one (Real.log ((N : ℝ) / (2 * K)) / Real.log 2)
  rw [Real.log_div hn.ne' (by positivity), sub_div] at hh
  unfold Lpar
  rw [Real.log_div hn.ne' (by positivity), sub_div]
  linarith

/-- LEAF. Unit U-1530. The diagonal scale: for `N > 1` and `0 ≤ L ≤ log N/log 2`,
`L · N/log N ≤ N/log 2`; Section 5, the source of the term `1/log 2` in Lemma 8. -/
theorem diag_scale {N L : ℝ} (hN : 1 < N) (hL0 : 0 ≤ L) (hL : L ≤ Real.log N / Real.log 2) :
    L * (N / Real.log N) ≤ N / Real.log 2 := by
  have hn : 0 < Real.log N := Real.log_pos hN
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    L * (N / Real.log N) ≤ (Real.log N / Real.log 2) * (N / Real.log N) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = N / Real.log 2 := by field_simp

/-! ### Leaves: the off diagonal -/

/-- LEAF. Unit U-1530. For `ν < μ`, `h(2^μ - 2^ν) = h(2^{μ-ν} - 1)`, since `h` sees only odd
primes; Section 5, proof of Lemma 8. -/
theorem h_pow_sub {μ ν : ℕ} (hνμ : ν < μ) : h (2 ^ μ - 2 ^ ν) = h (2 ^ (μ - ν) - 1) := by
  unfold h
  congr 1
  have hpow : 1 < (2 : ℕ) ^ (μ - ν) := one_lt_pow₀ (by norm_num) (by omega)
  have hn : 2 ^ (μ - ν) - 1 ≠ 0 := by omega
  have hfac : 2 ^ μ - 2 ^ ν = 2 ^ ν * (2 ^ (μ - ν) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, show ν + (μ - ν) = μ by omega]
  rw [hfac, Nat.primeFactors_mul (by positivity) hn]
  ext p
  simp only [mem_filter, mem_union]
  constructor
  · intro hh
    rcases hh.1 with hp | hp
    · have hprime := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have h2 := hprime.dvd_of_dvd_pow hd
      have heq := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2
      rcases heq with heq | heq
      · exact False.elim (hprime.ne_one heq)
      · exact False.elim (hh.2 heq)
    · exact ⟨hp, hh.2⟩
  · exact fun hh => ⟨Or.inr hh.1, hh.2⟩

/-- LEAF. Unit U-1530. Grouping the off diagonal pairs by `l = |μ - ν|`: there are `2(L - l)`
ordered pairs in `[1, L]²` at distance `l`, so the sum of `f(|μ - ν|)` over `μ ≠ ν` is
`2 Σ_{1 ≤ l ≤ L} (L - l) f(l)`; Section 5, proof of Lemma 8. -/
theorem offdiag_grouping (f : ℕ → ℝ) (L : ℕ) :
    ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (if μ = ν then 0 else f (max μ ν - min μ ν)) =
      2 * ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * f l := by
  induction L with
  | zero => simp
  | succ L ih =>
    have href : ∑ i ∈ Icc 1 L, f (L + 1 - i) = ∑ i ∈ Icc 1 L, f i := by
      apply sum_bij (fun i _ => L + 1 - i)
      · intro i hi
        simp only [mem_Icc] at hi ⊢
        omega
      · intro i hi j hj heq
        simp only [mem_Icc] at hi hj
        omega
      · intro j hj
        refine ⟨L + 1 - j, ?_, ?_⟩
        · simp only [mem_Icc] at hj ⊢; omega
        · simp only [mem_Icc] at hj; omega
      · intro i hi; rfl
    have hcol (i : ℕ) (hi : i ∈ Icc 1 L) :
        (if i = L + 1 then 0 else f (max i (L + 1) - min i (L + 1))) = f (L + 1 - i) := by
      have hl := (mem_Icc.mp hi).2
      simp [show i ≠ L + 1 by omega, max_eq_right (by omega : i ≤ L + 1),
        min_eq_left (by omega : i ≤ L + 1)]
    have hrow (i : ℕ) (hi : i ∈ Icc 1 L) :
        (if L + 1 = i then 0 else f (max (L + 1) i - min (L + 1) i)) = f (L + 1 - i) := by
      have hl := (mem_Icc.mp hi).2
      simp [show L + 1 ≠ i by omega, max_eq_left (by omega : i ≤ L + 1),
        min_eq_right (by omega : i ≤ L + 1)]
    rw [sum_Icc_succ_top (by omega)]
    have hold : ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 (L + 1),
        (if μ = ν then 0 else f (max μ ν - min μ ν)) =
        (∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (if μ = ν then 0 else f (max μ ν - min μ ν))) +
          ∑ i ∈ Icc 1 L, f (L + 1 - i) := by
      simp_rw [sum_Icc_succ_top (show 1 ≤ L + 1 by omega)]
      rw [sum_add_distrib]
      congr 1
      exact sum_congr rfl hcol
    rw [hold, sum_Icc_succ_top (by omega)]
    simp only [ite_true, add_zero]
    rw [sum_congr rfl hrow, href, ih, sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, add_zero]
    rw [show (∑ l ∈ Icc 1 L, (((L : ℝ) + 1) - l) * f l) =
      (∑ l ∈ Icc 1 L, ((L : ℝ) - l) * f l) + ∑ l ∈ Icc 1 L, f l by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro l hl
        ring]
    ring

/-- LEAF. Unit U-1530. Swapping a divisor sum:
`Σ_{1 ≤ j ≤ J} Σ_{e ∣ j} κ(e) = Σ_{1 ≤ e ≤ J} κ(e) [J/e]`; Section 5, the step
`Σ_{j ≤ J} h(2^j - 1) = Σ_d k(d) [J/ε(d)]`. -/
theorem divisor_swap (κ : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ Icc 1 J, ∑ e ∈ j.divisors, κ e = ∑ e ∈ Icc 1 J, κ e * ((J / e : ℕ) : ℝ) := by
  let f : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else κ n, by simp⟩
  have hset : Icc 1 J = Ioc 0 J := by ext n; simp; omega
  rw [hset]
  have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f J
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at hh
  convert hh using 1
  · apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro d hd
    simp [f, (Nat.pos_of_mem_divisors hd).ne']
  · apply sum_congr rfl
    intro n hn
    simp [f, (mem_Ioc.mp hn).1.ne']

/-- `π(n) ≤ n/3 + 5`: primes other than `2` and `3` are coprime to `6`. -/
private theorem pcount_le (n : ℕ) : Nat.primeCounting n ≤ n / 3 + 5 := by
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> decide
  · have h6 : Nat.primeCounting 6 = 3 := by decide
    have ht : Nat.totient 6 = 2 := by decide
    have key := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) (by norm_num) (n - 6)
    rw [show 6 + (n - 6) = n by omega, h6, ht] at key
    have hd : 2 * ((n - 6) / 6 + 1) ≤ n / 3 := by omega
    omega

private theorem card_odd_primes_le {t : Finset ℕ} (hne : t.Nonempty)
    (hpr : ∀ p ∈ t, p.Prime) : t.card ≤ t.max' hne / 3 + 5 := by
  have hsub : t ⊆ Nat.primesLE (t.max' hne) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Finset.le_max' t p hp, hpr p hp⟩
  calc t.card ≤ (Nat.primesLE (t.max' hne)).card := Finset.card_le_card hsub
    _ = Nat.primeCounting (t.max' hne) := Nat.primesLE_card_eq_primeCounting _
    _ ≤ _ := pcount_le _

private noncomputable def Qprod (x : ℕ) : ℕ := ∏ k ∈ Icc 1 x, (2 ^ k - 1)

private theorem Qprod_ne_zero (x : ℕ) : Qprod x ≠ 0 := by
  rw [Qprod, Finset.prod_ne_zero_iff]
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  omega

private theorem Qprod_le (x : ℕ) : Qprod x ≤ 2 ^ (x * x) := by
  rw [Qprod]
  calc ∏ k ∈ Icc 1 x, (2 ^ k - 1) ≤ (2 ^ x) ^ (Icc 1 x).card :=
        Finset.prod_le_pow_card _ _ _ fun k hk => by
          have hk2 : k ≤ x := (Finset.mem_Icc.mp hk).2
          have h2 : 2 ^ k ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hk2
          exact (Nat.sub_le _ _).trans h2
    _ = 2 ^ (x * x) := by rw [Nat.card_Icc, ← pow_mul, show x + 1 - 1 = x by omega]

private theorem eps_pos_of_odd {d : ℕ} (hd : Odd d) : 0 < eps d := by
  have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
  have h1 : (2 : ZMod d) ^ Nat.totient d = 1 := by
    have := Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hd)
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
    simpa using this
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0), h1⟩)

private theorem dvd_two_pow_eps (d : ℕ) : d ∣ 2 ^ eps d - 1 := by
  have h1 : (2 : ZMod d) ^ eps d = 1 := pow_orderOf_eq_one _
  rw [← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [h1, sub_self]

private theorem dvd_Qprod {d x : ℕ} (hpos : 0 < eps d) (hle : eps d ≤ x) : d ∣ Qprod x :=
  (dvd_two_pow_eps d).trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hpos, hle⟩))

private theorem card_pf_le {P : ℕ} (hP : P ≠ 0) {k : ℕ} (hk : P ≤ 2 ^ k) :
    P.primeFactors.card ≤ k := by
  have h1 : 2 ^ P.primeFactors.card ≤ ∏ p ∈ P.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ P.primeFactors, p ≤ P :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.prod_primeFactors_dvd P)
  exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp (h1.trans (h2.trans hk))

private theorem sum_inv_sub_two_le : ∀ (m : ℕ) (t : Finset ℕ), t.card = m →
    (∀ p ∈ t, p.Prime) → 2 ∉ t →
    ∑ p ∈ t, 1 / ((p : ℝ) - 2) ≤ 2 / 5 * Real.log ((t.card : ℝ) + 4) + 200 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t hcard hpr h2mem
    rcases Nat.lt_or_ge m 61 with hm | hm
    · have hone : ∀ p ∈ t, 1 / ((p : ℝ) - 2) ≤ 1 := by
        intro p hp
        have hpp := hpr p hp
        have hp2 : p ≠ 2 := fun hh => h2mem (hh ▸ hp)
        have hp3 : (3 : ℕ) ≤ p := by
          have := hpp.two_le
          omega
        have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        rw [div_le_one (by linarith)]
        linarith
      have hsum : ∑ p ∈ t, 1 / ((p : ℝ) - 2) ≤ (t.card : ℝ) := by
        calc ∑ p ∈ t, 1 / ((p : ℝ) - 2) ≤ ∑ _p ∈ t, (1 : ℝ) := Finset.sum_le_sum hone
          _ = (t.card : ℝ) := by simp
      have hcl : (t.card : ℝ) ≤ 60 := by
        have h2 : t.card ≤ 60 := by omega
        exact_mod_cast h2
      have hlog0 : 0 ≤ Real.log ((t.card : ℝ) + 4) := by
        apply Real.log_nonneg
        have h2 : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
        linarith
      have hfin : (t.card : ℝ) ≤ 2 / 5 * Real.log ((t.card : ℝ) + 4) + 200 := by nlinarith
      linarith
    · have hm61 : 61 ≤ m := hm
      have hne : t.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
        omega
      set M := t.max' hne with hMdef
      have hMt : M ∈ t := Finset.max'_mem t hne
      have hMge : 3 * (m - 5) ≤ M := by
        have h1 := card_odd_primes_le hne hpr
        rw [hcard, ← hMdef] at h1
        have h2 : (m - 5) * 3 ≤ (M / 3) * 3 := by
          apply Nat.mul_le_mul_right
          omega
        have h3 : (M / 3) * 3 ≤ M := Nat.div_mul_le_self M 3
        omega
      have hMr : (3 : ℝ) * ((m : ℝ) - 5) ≤ (M : ℝ) := by
        have h1 : ((3 * (m - 5) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMge
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 5 ≤ m)] at h1
        push_cast at h1
        linarith
      have hmR : (61 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm61
      have hM2 : (0 : ℝ) < (M : ℝ) - 2 := by linarith
      have hcard' : (t.erase M).card = m - 1 := by
        rw [Finset.card_erase_of_mem hMt, hcard]
      have hpr' : ∀ p ∈ t.erase M, p.Prime := fun p hp => hpr p (Finset.mem_of_mem_erase hp)
      have h2' : 2 ∉ t.erase M := fun hh => h2mem (Finset.mem_of_mem_erase hh)
      have hih := ih (m - 1) (by omega) (t.erase M) hcard' hpr' h2'
      have hci2 : ((t.erase M).card : ℝ) + 4 = (m : ℝ) + 3 := by
        rw [hcard', Nat.cast_sub (by omega : 1 ≤ m)]
        push_cast
        ring
      rw [hci2] at hih
      have hsplit : ∑ p ∈ t, 1 / ((p : ℝ) - 2) =
          (∑ p ∈ t.erase M, 1 / ((p : ℝ) - 2)) + 1 / ((M : ℝ) - 2) :=
        (Finset.sum_erase_add _ _ hMt).symm
      have hstep : 1 / ((M : ℝ) - 2) ≤ 2 / (5 * ((m : ℝ) + 4)) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * ((m : ℝ) + 4)),
          div_mul_eq_mul_div, div_le_iff₀ hM2]
        nlinarith
      have hlog : 2 / (5 * ((m : ℝ) + 4)) ≤
          2 / 5 * Real.log (((m : ℝ) + 4) / ((m : ℝ) + 3)) := by
        have hx : (0 : ℝ) < ((m : ℝ) + 4) / ((m : ℝ) + 3) := by positivity
        have h1 := Real.one_sub_inv_le_log_of_pos hx
        have hinv : (((m : ℝ) + 4) / ((m : ℝ) + 3))⁻¹ = ((m : ℝ) + 3) / ((m : ℝ) + 4) := by
          rw [inv_div]
        rw [hinv] at h1
        have hone : (1 : ℝ) - ((m : ℝ) + 3) / ((m : ℝ) + 4) = 1 / ((m : ℝ) + 4) := by
          field_simp
          ring
        rw [hone] at h1
        have hval : 2 / (5 * ((m : ℝ) + 4)) = 2 / 5 * (1 / ((m : ℝ) + 4)) := by
          field_simp
        rw [hval]
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      have hlogadd : 2 / 5 * Real.log ((m : ℝ) + 3) +
          2 / 5 * Real.log (((m : ℝ) + 4) / ((m : ℝ) + 3)) =
          2 / 5 * Real.log ((m : ℝ) + 4) := by
        rw [Real.log_div (by positivity) (by positivity)]
        ring
      have hfinal : 2 / 5 * Real.log ((m : ℝ) + 3) + 200 + 2 / (5 * ((m : ℝ) + 4)) ≤
          2 / 5 * Real.log ((m : ℝ) + 4) + 200 := by linarith [hlog, hlogadd]
      rw [hsplit, hcard]
      linarith [hih, hstep, hfinal]

private theorem cast_h_le_exp (n : ℕ) :
    ((h n : ℚ) : ℝ) ≤
      Real.exp (∑ p ∈ n.primeFactors.filter (fun p => p ≠ 2), 1 / ((p : ℝ) - 2)) := by
  have hgt : ∀ p ∈ n.primeFactors.filter (fun p => p ≠ 2), (0 : ℝ) < (p : ℝ) - 2 := by
    intro p hp
    have hp2 : p ≠ 2 := (Finset.mem_filter.mp hp).2
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
    have hp3 : (3 : ℕ) ≤ p := by
      have := hpp.two_le
      omega
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hstep : ∀ p ∈ n.primeFactors.filter (fun p => p ≠ 2),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
    intro p hp
    have hp2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (hgt p hp)
    field_simp
    ring
  unfold h
  push_cast
  rw [Finset.prod_congr rfl hstep]
  calc ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2), (1 + 1 / ((p : ℝ) - 2))
      ≤ ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2), Real.exp (1 / ((p : ℝ) - 2)) := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
        · have h3 := hgt p hp
          have h4 : (0 : ℝ) < 1 / ((p : ℝ) - 2) := by positivity
          linarith
        · have h3 := Real.add_one_le_exp (1 / ((p : ℝ) - 2))
          linarith
    _ = Real.exp (∑ p ∈ n.primeFactors.filter (fun p => p ≠ 2), 1 / ((p : ℝ) - 2)) :=
        (Real.exp_sum _ _).symm

private theorem hQ_le (x : ℕ) (hx : 2 ≤ x) :
    ((h (Qprod x) : ℚ) : ℝ) ≤
      Real.exp 200 * Real.exp (2 / 5 * Real.log (2 * ((x : ℝ) ^ 2))) := by
  set t : Finset ℕ := (Qprod x).primeFactors.filter (fun p => p ≠ 2) with ht
  have hpr : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  have h2m : 2 ∉ t := by simp [ht]
  have hcast := cast_h_le_exp (Qprod x)
  have hkey := sum_inv_sub_two_le t.card t rfl hpr h2m
  have hcardle : t.card ≤ x * x := by
    have h1 : t.card ≤ (Qprod x).primeFactors.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := card_pf_le (Qprod_ne_zero x) (Qprod_le x)
    omega
  have hcardR : (t.card : ℝ) + 4 ≤ 2 * ((x : ℝ) ^ 2) := by
    have h1 : (t.card : ℝ) ≤ (x : ℝ) ^ 2 := by
      have h2 : ((t.card : ℕ) : ℝ) ≤ ((x * x : ℕ) : ℝ) := by exact_mod_cast hcardle
      push_cast at h2
      linarith
    have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    nlinarith
  calc ((h (Qprod x) : ℚ) : ℝ)
      ≤ Real.exp (∑ p ∈ (Qprod x).primeFactors.filter (fun p => p ≠ 2), 1 / ((p : ℝ) - 2)) :=
        hcast
    _ = Real.exp (∑ p ∈ t, 1 / ((p : ℝ) - 2)) := by rw [ht]
    _ ≤ Real.exp (2 / 5 * Real.log ((t.card : ℝ) + 4) + 200) := Real.exp_le_exp.mpr hkey
    _ = Real.exp 200 * Real.exp (2 / 5 * Real.log ((t.card : ℝ) + 4)) := by
        rw [show 2 / 5 * Real.log ((t.card : ℝ) + 4) + 200 =
          200 + 2 / 5 * Real.log ((t.card : ℝ) + 4) by ring, Real.exp_add]
    _ ≤ Real.exp 200 * Real.exp (2 / 5 * Real.log (2 * ((x : ℝ) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 200).le
        apply Real.exp_le_exp.mpr
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Real.log_le_log (by positivity) hcardR

private noncomputable def rho : ℝ := Real.exp (-(Real.log 2) / 5)

private theorem rho_pos : 0 < rho := Real.exp_pos _

private theorem rho_lt_one : rho < 1 := by
  rw [rho, show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  apply Real.exp_lt_exp.mpr
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

private theorem block_major (j : ℕ) :
    (1 / 2 : ℝ) ^ j *
        (Real.exp 200 * Real.exp (2 / 5 * Real.log (2 * ((2 : ℝ) ^ (j + 1)) ^ 2)))
      ≤ Real.exp 200 * 4 * rho ^ j := by
  have hxval : (2 : ℝ) * ((2 : ℝ) ^ (j + 1)) ^ 2 = (2 : ℝ) ^ (2 * j + 3) := by
    rw [pow_two, ← pow_add, mul_comm (2 : ℝ), ← pow_succ]
    congr 1
    omega
  have hlog2 : Real.log ((2 : ℝ) ^ (2 * j + 3)) = (2 * (j : ℝ) + 3) * Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  have hhalf : (1 / 2 : ℝ) ^ j = Real.exp (-((j : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div,
      inv_pow]
  have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hrho : rho ^ j = Real.exp (-((j : ℝ) * (Real.log 2 / 5))) := by
    rw [rho, ← Real.exp_nat_mul]
    congr 1
    ring
  have hL : (1 / 2 : ℝ) ^ j *
      (Real.exp 200 * Real.exp (2 / 5 * Real.log (2 * ((2 : ℝ) ^ (j + 1)) ^ 2))) =
      Real.exp (200 + (6 - (j : ℝ)) / 5 * Real.log 2) := by
    rw [hxval, hlog2, hhalf, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hR : Real.exp 200 * 4 * rho ^ j =
      Real.exp (200 + (10 - (j : ℝ)) / 5 * Real.log 2) := by
    rw [h4, hrho, hlog4, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hL, hR]
  apply Real.exp_le_exp.mpr
  have hpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

private theorem block_le (S : Finset ℕ) (j : ℕ) :
    ∑ d ∈ S.filter (fun d => Odd d ∧ Nat.log 2 (eps d) = j), C2Inputs.f d ≤
      Real.exp 200 * 4 * rho ^ j := by
  set T : Finset ℕ := S.filter (fun d => Odd d ∧ Nat.log 2 (eps d) = j) with hT
  have hpos : ∀ d ∈ T, 0 < eps d := fun d hd =>
    eps_pos_of_odd (Finset.mem_filter.mp hd).2.1
  have hle : ∀ d ∈ T, eps d ≤ 2 ^ (j + 1) := by
    intro d hd
    have hdj : Nat.log 2 (eps d) = j := (Finset.mem_filter.mp hd).2.2
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (eps d)
    rw [hdj] at hlt
    omega
  have hbase : ∀ d ∈ T, ((eps d : ℝ))⁻¹ ≤ (1 / 2 : ℝ) ^ j := by
    intro d hd
    have h2 : 2 ^ j ≤ eps d := by
      have hdj : Nat.log 2 (eps d) = j := (Finset.mem_filter.mp hd).2.2
      rw [← hdj]
      exact Nat.pow_log_le_self 2 (hpos d hd).ne'
    have h2R : (2 : ℝ) ^ j ≤ (eps d : ℝ) := by exact_mod_cast h2
    have hposR : (0 : ℝ) < (eps d : ℝ) := by exact_mod_cast hpos d hd
    have h3 : ((eps d : ℝ))⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
      (inv_le_inv₀ hposR (by positivity)).mpr h2R
    have h4 : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow]
    rw [h4]
    exact h3
  have hsub : ∑ d ∈ T, (k d : ℝ) ≤ ((h (Qprod (2 ^ (j + 1))) : ℚ) : ℝ) := by
    have hQ := Qprod_ne_zero (2 ^ (j + 1))
    have hdiv : ∀ d ∈ T, d ∈ (Qprod (2 ^ (j + 1))).divisors := by
      intro d hd
      exact Nat.mem_divisors.mpr ⟨dvd_Qprod (hpos d hd) (hle d hd), hQ⟩
    have hcast : ((h (Qprod (2 ^ (j + 1))) : ℚ) : ℝ) =
        ∑ d ∈ (Qprod (2 ^ (j + 1))).divisors, (k d : ℝ) := by
      rw [h_eq_sum_k _ hQ]
      push_cast
      rfl
    rw [hcast]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdiv (fun d _ _ => by
      have h3 := k_nonneg d
      exact_mod_cast h3)
  calc ∑ d ∈ T, C2Inputs.f d ≤ ∑ d ∈ T, (k d : ℝ) * (1 / 2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hkn : (0 : ℝ) ≤ (k d : ℝ) := by
          have h3 := k_nonneg d
          exact_mod_cast h3
        rw [C2Inputs.f, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (hbase d hd) hkn
    _ = (∑ d ∈ T, (k d : ℝ)) * (1 / 2 : ℝ) ^ j := by rw [Finset.sum_mul]
    _ ≤ ((h (Qprod (2 ^ (j + 1))) : ℚ) : ℝ) * (1 / 2 : ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_right hsub (by positivity)
    _ = (1 / 2 : ℝ) ^ j * ((h (Qprod (2 ^ (j + 1))) : ℚ) : ℝ) := by ring
    _ ≤ (1 / 2 : ℝ) ^ j *
          (Real.exp 200 * Real.exp (2 / 5 * Real.log (2 * ((2 : ℝ) ^ (j + 1)) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := hQ_le (2 ^ (j + 1)) (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
    _ ≤ Real.exp 200 * 4 * rho ^ j := block_major j

private theorem partial_le (S : Finset ℕ) :
    ∑ d ∈ S, C2Inputs.f d ≤ ∑' j : ℕ, (Real.exp 200 * 4 * rho ^ j) := by
  have hmaj : Summable fun j : ℕ => Real.exp 200 * 4 * rho ^ j :=
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left _
  have hzero : ∑ d ∈ S.filter (fun d => ¬ Odd d), C2Inputs.f d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hno : ¬ Odd d := (Finset.mem_filter.mp hd).2
    have hk : k d = 0 := by simp [k, hno]
    rw [C2Inputs.f, hk]
    simp
  have hsplit : ∑ d ∈ S, C2Inputs.f d = ∑ d ∈ S.filter (fun d => Odd d), C2Inputs.f d := by
    have h := Finset.sum_filter_add_sum_filter_not (s := S) (p := fun d => Odd d)
      (f := fun d => C2Inputs.f d)
    rw [hzero, add_zero] at h
    exact h.symm
  rw [hsplit]
  set U : Finset ℕ := S.filter (fun d => Odd d) with hU
  have hmaps : ∀ d ∈ U, Nat.log 2 (eps d) ∈ U.image (fun d => Nat.log 2 (eps d)) :=
    fun d hd => Finset.mem_image_of_mem _ hd
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun d => C2Inputs.f d)
  rw [← hfib]
  calc ∑ j ∈ U.image (fun d => Nat.log 2 (eps d)),
        ∑ d ∈ U.filter (fun d => Nat.log 2 (eps d) = j), C2Inputs.f d
      ≤ ∑ j ∈ U.image (fun d => Nat.log 2 (eps d)), (Real.exp 200 * 4 * rho ^ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have he : U.filter (fun d => Nat.log 2 (eps d) = j) =
            S.filter (fun d => Odd d ∧ Nat.log 2 (eps d) = j) := by
          ext d
          simp only [hU, Finset.mem_filter, and_assoc]
        rw [he]
        exact block_le S j
    _ ≤ ∑' j : ℕ, (Real.exp 200 * 4 * rho ^ j) :=
        hmaj.sum_le_tsum _ (fun j _ => by
          have h3 : (0 : ℝ) ≤ rho ^ j := pow_nonneg rho_pos.le j
          positivity)

/-- LEAF. Unit U-1530. The series `Σ_{e ≥ 1} κ(e)/e`, which is `C₂` regrouped, converges;
Section 5, display 35. -/
theorem C2_summable : Summable fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1) := by
  have hf : Summable fun d : ℕ => C2Inputs.f d :=
    summable_of_sum_range_le (fun d => C2Inputs.f_nonneg d) (fun n => partial_le (range n))
  have hinj : Function.Injective (fun p : (Σ e, {d // eps d = e}) => p.2.1) := by
    rintro ⟨e1, c1⟩ ⟨e2, c2⟩ heq
    simp only at heq
    have h1 : eps c1.1 = e1 := c1.2
    have h2 : eps c2.1 = e2 := c2.2
    have he : e1 = e2 := by rw [← h1, ← h2, heq]
    subst he
    have hc : c1 = c2 := Subtype.ext heq
    rw [hc]
  have hsig : Summable fun p : (Σ e, {d // eps d = e}) => C2Inputs.f p.2.1 :=
    hf.comp_injective hinj
  have hiff := summable_sigma_of_nonneg
    (f := fun p : (Σ e, {d // eps d = e}) => C2Inputs.f p.2.1)
    (fun p => C2Inputs.f_nonneg p.2.1)
  have hfib : Summable fun e : ℕ => ∑' c : {d // eps d = e}, C2Inputs.f c.1 := (hiff.mp hsig).2
  have hF : Summable fun e : ℕ => kappaTrue e / (e : ℝ) :=
    hfib.congr (fun e => C2Inputs.fiber_tsum e)
  have h2 := (summable_nat_add_iff 1).mpr hF
  simpa [Nat.cast_add, Nat.cast_one] using h2

/-- LEAF. Unit U-1530. Given convergence, `Σ_{1 ≤ e ≤ J} κ(e) [J/e] ≤ C₂ J`, from `[J/e] ≤ J/e`,
`κ ≥ 0` and the lab's `grouping`; Section 5, the upper half of
`Σ_{j ≤ J} h(2^j - 1) = C₂ J + O(J^{1/2})`. -/
theorem kappa_floor_le (hs : Summable fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1)) (J : ℕ) :
    ∑ e ∈ Icc 1 J, kappaTrue e * ((J / e : ℕ) : ℝ) ≤ C2 * J := by
  have hs' : Summable fun e : ℕ => kappaTrue e / (e : ℝ) := by
    apply (summable_nat_add_iff 1).mp
    simpa using hs
  have ht : ∑' e : ℕ, kappaTrue e / (e : ℝ) = C2 := by
    rw [grouping, tsum_eq_zero_add' (by simpa using hs)]
    simp
  have hp : ∑ e ∈ Icc 1 J, kappaTrue e / (e : ℝ) ≤ C2 := by
    rw [← ht]
    exact hs'.sum_le_tsum (Icc 1 J) (fun e he => div_nonneg (kappaTrue_nonneg e) (Nat.cast_nonneg e))
  calc
    _ ≤ ∑ e ∈ Icc 1 J, (kappaTrue e / (e : ℝ)) * J := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ kappaTrue e * ((J : ℝ) / e) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le (kappaTrue_nonneg e)
        _ = _ := by ring
    _ = (∑ e ∈ Icc 1 J, kappaTrue e / (e : ℝ)) * J := (sum_mul ..).symm
    _ ≤ C2 * J := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg J)

/-- LEAF. Unit U-1530. Partial summation:
`Σ_{1 ≤ l ≤ L} (L - l) a(l) = Σ_{1 ≤ J ≤ L-1} Σ_{1 ≤ j ≤ J} a(j)`; Section 5, proof of
Lemma 8. -/
theorem partial_summation (a : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * a l = ∑ J ∈ Icc 1 (L - 1), ∑ j ∈ Icc 1 J, a j := by
  induction L with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [sum_Icc_succ_top (by omega)]
      simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, add_zero, Nat.add_sub_cancel]
      rw [sum_Icc_succ_top (by omega) (fun J => ∑ j ∈ Icc 1 J, a j)]
      have he : ∑ l ∈ Icc 1 (m + 1), (((m : ℝ) + 1 + 1) - l) * a l =
          (∑ l ∈ Icc 1 (m + 1), (((m : ℝ) + 1) - l) * a l) + ∑ l ∈ Icc 1 (m + 1), a l := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro l hl
        ring
      rw [he]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using congrArg
        (fun x : ℝ => x + ∑ l ∈ Icc 1 (m + 1), a l) ih

/-- LEAF. Unit U-1530. `Σ_{1 ≤ J ≤ L-1} J ≤ L²/2`; Section 5, proof of Lemma 8. -/
theorem sum_id_le (L : ℕ) : ∑ J ∈ Icc 1 (L - 1), (J : ℝ) ≤ (L : ℝ) ^ 2 / 2 := by
  have hs : ∀ n : ℕ, (∑ J ∈ Icc 1 n, (J : ℝ)) * 2 = (n : ℝ) * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      nlinarith
  cases L with
  | zero => simp
  | succ n =>
    have hh := hs n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- LEAF. Unit U-1530. The off diagonal scale: for `C, D ≥ 0`, `N > 1`, `0 ≤ L ≤ log N/log 2`,
`2 C N/log² N · D L²/2 ≤ C D N/log² 2`; Section 5, the passage from `L²` to `1/log² 2`. -/
theorem offdiag_scale {C D N L : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 1 < N) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log N / Real.log 2) :
    2 * C * N / Real.log N ^ 2 * (D * L ^ 2 / 2) ≤ C * D * N / Real.log 2 ^ 2 := by
  have hn : 0 < Real.log N := Real.log_pos hN
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : L * Real.log 2 ≤ Real.log N := (le_div_iff₀ h2).mp hL
  have hsq : L ^ 2 * Real.log 2 ^ 2 ≤ Real.log N ^ 2 := by
    nlinarith [mul_le_mul hb hb (by positivity : 0 ≤ L * Real.log 2) hn.le]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ C * D * N by positivity)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hn 2) (pow_pos h2 2)]
  nlinarith

/-! ### Assemblies -/

theorem C2_nonneg' : 0 ≤ C2 :=
  tsum_nonneg fun d => div_nonneg (by exact_mod_cast k_nonneg d) (Nat.cast_nonneg _)

/-- ASSEMBLY, CONDITIONAL ON `partial_summation`, `divisor_swap`, `C2_summable`,
`kappa_floor_le` and `sum_id_le`, with the lab's proved `sum_kappaTrue_divisors`:
`Σ_{1 ≤ l ≤ L} (L - l) h(2^l - 1) ≤ C₂ L²/2`; Section 5, proof of Lemma 8. -/
theorem hsum_bound (L : ℕ) :
    ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * (h (2 ^ l - 1) : ℝ) ≤ C2 * (L : ℝ) ^ 2 / 2 := by
  rw [partial_summation]
  have inner : ∀ J : ℕ, ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ) ≤ C2 * J := by
    intro J
    have e : ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ) = ∑ j ∈ Icc 1 J, ∑ e ∈ j.divisors, kappaTrue e :=
      sum_congr rfl fun j hj => by
        rw [Finset.mem_Icc] at hj
        exact (sum_kappaTrue_divisors j (by omega)).symm
    rw [e, divisor_swap]
    exact kappa_floor_le C2_summable J
  calc ∑ J ∈ Icc 1 (L - 1), ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ)
      ≤ ∑ J ∈ Icc 1 (L - 1), C2 * (J : ℝ) := sum_le_sum fun J _ => inner J
    _ = C2 * ∑ J ∈ Icc 1 (L - 1), (J : ℝ) := by rw [mul_sum]
    _ ≤ C2 * ((L : ℝ) ^ 2 / 2) := mul_le_mul_of_nonneg_left (sum_id_le L) C2_nonneg'
    _ = C2 * (L : ℝ) ^ 2 / 2 := by ring

/-- ASSEMBLY, CONDITIONAL ON `offdiag_grouping` and the leaves of `hsum_bound`: the off diagonal
sum `Σ_{μ ≠ ν} h(2^{|μ - ν|} - 1) ≤ C₂ L²`; Section 5, proof of Lemma 8. -/
theorem offdiag_total (L : ℕ) :
    ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L,
      (if μ = ν then 0 else (h (2 ^ (max μ ν - min μ ν) - 1) : ℝ)) ≤ C2 * (L : ℝ) ^ 2 := by
  rw [offdiag_grouping (fun l => (h (2 ^ l - 1) : ℝ))]
  have := hsum_bound L
  linarith

/-- ASSEMBLY, CONDITIONAL ON `offdiag_scale` and the leaves of `hsum_bound`: with Chen's factor
`C₀ C₁ ≥ 0` and `L ≤ log N/log 2`,
`2 C₀C₁ N/log² N · Σ_{l ≤ L} (L - l) h(2^l - 1) ≤ C₀ C₁ C₂ N/log² 2`, the main term of
Lemma 8, Section 5. -/
theorem offdiag_main_term {C N : ℝ} (hC : 0 ≤ C) (hN : 1 < N) {L : ℕ}
    (hL : (L : ℝ) ≤ Real.log N / Real.log 2) :
    2 * C * N / Real.log N ^ 2 * ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * (h (2 ^ l - 1) : ℝ) ≤
      C * C2 * N / Real.log 2 ^ 2 := by
  have hpos : 0 ≤ 2 * C * N / Real.log N ^ 2 := by
    have : 0 ≤ N := by linarith
    positivity
  calc _ ≤ 2 * C * N / Real.log N ^ 2 * (C2 * (L : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hsum_bound L) hpos
    _ ≤ C * C2 * N / Real.log 2 ^ 2 :=
        offdiag_scale hC C2_nonneg' hN (Nat.cast_nonneg L) hL

end LeanLab.HeathBrownPuchta.Decomp1530b

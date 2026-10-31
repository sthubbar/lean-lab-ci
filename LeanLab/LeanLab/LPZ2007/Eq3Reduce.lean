/-
P0045 Languasco, Pintz, Zaccagnini 2007, (3) p.3: the circle method identity behind
`R''_k(N) = R''_𝔐(N) + R''_𝔪(N) + O(N L^{k−1/2} log log N)`.

Unit U-1225, T1 PROVE, PC run 20261020T1203Z-6833.

Source: P0045 preprint p.3. With `S(α) = Σ_{m ≤ X} Λ(m) e(mα)` and `G(α) = Σ_{ν ≤ L'} e(2^ν α)`,
`∫_{Q⁻¹}^{1+Q⁻¹} S² G^k e(−Nα) dα` counts the representations with every `ν ≤ L' = L − √L`;
(3) adds the error from the `ν` in `(L', L]`.

What is here, PROVED unconditional unless said:
* `int_e`: `∫_a^{a+1} e(nx) dx = [n = 0]` for every integer `n` and real `a`.
* `Gx_pow`: `G(α)^k = Σ_{ν ∈ [1, L']^k} e((2^{ν₁} + ... + 2^{ν_k}) α)`.
* `circle_identity`: `∫_a^{a+1} S² G^k e(−Nα) dα = R'_k(N)`, the count with `ν ∈ [1, L']^k`,
  `Rpp'`, for every `a`.
* `majorArcs_subset`: for `P > 0` and `P(P + 1) ≤ X` the major arcs lie in `[P/X, 1 + P/X]`;
  `prange_ok`: this holds for `X ≥ 64` and `P ∈ [X^0.4, X^0.41]`.
* `split_identity`: `R''_𝔐(N) + R''_𝔪(N) = R'_k(N)` under that condition.
* `TailBound`: `|R''_k(N) − R'_k(N)| ≪ N L^{k−1/2} log log N`, the part of (3) that the paper
  takes from the bound `R(n) ≪ n log log n`. `eq3_of_tail`: `TailBound → Eq3`, so the cited (3) is
  replaced by this purely arithmetic input. CONDITIONAL ON `TailBound`, as an implication.
* `RgUpper`: the classical bound quoted on p.3, every `R_X(n)` with `n ≤ N` is `≤ C N log log N`
  for `N ≥ 16`, cited. `tail_of_rgUpper`: `RgUpper → TailBound`, by `R''_k − R'_k` as a sum over
  `ν ∈ [1,L]^k \ [1,L']^k`, at most `⌊L⌋^k − ⌊L'⌋^k ≤ 2k L^{k−1/2}` such `ν`, `pow_sub_pow_le`.
* `eq3_of_rgUpper`: the cited (3) now follows from `RgUpper` alone.
* `mainJ_twoC0_of_inputs`: the repaired P0045 Theorem, constant `2c₀ C(k, N)`, from three
  classical inputs: `RgUpper`, the minor arc sup bound `MinorBound` and the repaired (25).

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.MinorBessel
import LeanLab.LPZ2007.MainSigma

namespace LeanLab.LPZ2007.Eq3Reduce

open Finset Real MeasureTheory LeanLab.LPZ2007 LeanLab.LPZ2007.MinorBessel
open LeanLab.LPZ2007.ExceptionalOfSup
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

theorem e_add (u v : ℝ) : e u * e v = e (u + v) := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `∫_a^{a+1} e(nx) dx = [n = 0]`. -/
theorem int_e (a : ℝ) (n : ℤ) : ∫ x in a..a + 1, e (n * x) = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [e]
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast h
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero, h1]
    have hf : (fun x : ℝ => e (n * x)) = fun x : ℝ => Complex.exp ((2 * π * Complex.I * n) * x) := by
      funext x; unfold e; congr 1; push_cast; ring
    rw [hf, integral_exp_mul_complex hc]
    have hper : Complex.exp ((2 * π * Complex.I * n) * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp ((2 * π * Complex.I * n) * (a : ℂ)) := by
      have : (2 * π * Complex.I * n) * ((a + 1 : ℝ) : ℂ) =
          (2 * π * Complex.I * n) * (a : ℂ) + n * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]

theorem continuous_ce (c : ℂ) (n : ℤ) : Continuous fun x : ℝ => c * e (n * x) :=
  continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

/-- `G(α)^k` as a sum over `ν ∈ [1, L']^k`. -/
theorem Gx_pow (X α : ℝ) (k : ℕ) :
    Gx X α ^ k = ∑ ν ∈ tuples k ⌊Lp X⌋₊, e (pow2sum ν * α) := by
  unfold Gx tuples
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold e pow2sum
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]

/-- `S(α)²` as a double sum. -/
theorem Sx_sq (X α : ℝ) :
    Sx X α ^ 2 = ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
      ((Λ m1 : ℂ) * (Λ m2 : ℂ)) * e ((m1 + m2 : ℕ) * α) := by
  unfold Sx
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m1 _ => Finset.sum_congr rfl fun m2 _ => ?_
  rw [show ((Λ m1 : ℂ) * e (m1 * α)) * ((Λ m2 : ℂ) * e (m2 * α)) =
      ((Λ m1 : ℂ) * (Λ m2 : ℂ)) * (e (m1 * α) * e (m2 * α)) by ring, e_add]
  congr 2; push_cast; ring

/-- `R'_k(N)`: the count of `R''_k(N)` with `ν ∈ [1, L']^k`, `L' = L − √L`. -/
def Rpp' (k : ℕ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊, ∑ ν ∈ tuples k ⌊Lp X⌋₊,
    if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else 0

/-- The integrand expanded. -/
theorem Fk_mul_e (k : ℕ) (X : ℝ) (N : ℕ) (x : ℝ) :
    Fk k X x * e (-(N * x)) = ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊, ∑ ν ∈ tuples k ⌊Lp X⌋₊,
      ((Λ m1 : ℂ) * (Λ m2 : ℂ)) * e ((((m1 + m2 + pow2sum ν : ℕ) : ℤ) - N : ℤ) * x) := by
  unfold Fk
  rw [Sx_sq, Gx_pow, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m1 _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m2 _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_assoc, mul_assoc, e_add, e_add]
  congr 2
  push_cast
  ring

/-- **The circle method identity**: `∫_a^{a+1} S² G^k e(−Nα) dα = R'_k(N)`. -/
theorem circle_identity (k : ℕ) (X : ℝ) (N : ℕ) (a : ℝ) :
    ∫ x in a..a + 1, Fk k X x * e (-(N * x)) = (Rpp' k X N : ℂ) := by
  simp_rw [Fk_mul_e]
  rw [intervalIntegral.integral_finsetSum fun m1 _ => (continuous_finsetSum _ fun m2 _ =>
    continuous_finsetSum _ fun ν _ => continuous_ce _ _).intervalIntegrable _ _]
  unfold Rpp'
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m1 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun m2 _ => (continuous_finsetSum _ fun ν _ =>
    continuous_ce _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m2 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun ν _ => (continuous_ce _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [intervalIntegral.integral_const_mul, int_e]
  by_cases h : m1 + m2 + pow2sum ν = N
  · rw [if_pos (by rw [h]; ring), if_pos h, mul_one]; push_cast; ring
  · rw [if_neg (by intro h'; apply h; omega), if_neg h, mul_zero]; push_cast; ring

/-! ### Major and minor arcs fill `[P/X, 1 + P/X]` -/

theorem majorArcs_subset {X P : ℝ} (hP : 0 < P) (hPX : P * (P + 1) ≤ X) :
    majorArcs X P ⊆ Set.Icc (P / X) (P / X + 1) := by
  intro α hα
  obtain ⟨q, a, hq1, hqP, ha1, haq, _, hlo, hhi⟩ := hα
  have hX : 0 < X := by nlinarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have haq' : (a : ℝ) ≤ q := by exact_mod_cast haq
  have hQ : (1 : ℝ) / (q * (X / P)) = P / (q * X) := by field_simp
  rw [hQ] at hlo hhi
  have hdiv : (a : ℝ) / q ≤ 1 := (div_le_one hq0).2 haq'
  have hPq : P / (q * X) ≤ P / X := by
    apply div_le_div_of_nonneg_left hP.le hX; nlinarith
  constructor
  · -- `a/q − P/(qX) ≥ 1/q − P/(qX) ≥ P/X` since `X ≥ P(q + 1)`
    have h1 : 1 / q ≤ (a : ℝ) / q := by gcongr
    have h2 : P / X ≤ 1 / q - P / (q * X) := by
      rw [div_le_iff₀ hX, sub_mul, div_mul_eq_mul_div, one_mul,
        show P / (q * X) * X = P / q by field_simp, ← sub_div, le_div_iff₀ hq0]
      nlinarith
    linarith
  · linarith

theorem prange_ok {X P : ℝ} (hX : 64 ≤ X) (hP : PRange X P) : 0 < P ∧ P * (P + 1) ≤ X := by
  obtain ⟨hlo, hhi⟩ := hP
  have hX0 : 0 < X := by linarith
  have hP1 : 1 ≤ P := le_trans (Real.one_le_rpow (by linarith) (by norm_num)) hlo
  refine ⟨by linarith, ?_⟩
  have hsq : P ^ 2 ≤ X ^ (0.82 : ℝ) := by
    calc P ^ 2 ≤ (X ^ (0.41 : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) hhi 2
      _ = X ^ (0.82 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have h18 : 2 ≤ X ^ (0.18 : ℝ) := by
    have h64 : (64 : ℝ) ^ (0.18 : ℝ) ≤ X ^ (0.18 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hX (by norm_num)
    have : (64 : ℝ) ^ (0.18 : ℝ) = 2 ^ (1.08 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    have h2 : (2 : ℝ) ≤ 2 ^ (1.08 : ℝ) := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
        _ ≤ 2 ^ (1.08 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hsplit : X = X ^ (0.82 : ℝ) * X ^ (0.18 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have h82 : 0 ≤ X ^ (0.82 : ℝ) := by positivity
  nlinarith

/-- **`R''_𝔐(N) + R''_𝔪(N) = R'_k(N)`** when the major arcs lie in `[P/X, 1 + P/X]`. -/
theorem split_identity (k : ℕ) {X P : ℝ} (hP : 0 < P) (hPX : P * (P + 1) ≤ X) (N : ℕ) :
    RMpp k X P N + Rmpp k X P N = (Rpp' k X N : ℂ) := by
  rw [← circle_identity k X N (P / X), intervalIntegral.integral_of_le (by linarith)]
  have hM := measurableSet_majorArcs X P
  have hint : IntegrableOn (fun x => Fk k X x * e (-(N * x))) (Set.Ioc (P / X) (P / X + 1)) :=
    ((continuous_Fk k X).mul (continuous_e.comp (by fun_prop))).integrableOn_Ioc
  rw [← integral_inter_add_sdiff hM hint]
  have hsub := majorArcs_subset hP hPX
  have h1 : (Set.Ioc (P / X) (P / X + 1) ∩ majorArcs X P : Set ℝ) =ᵐ[volume]
      (Set.Icc (P / X) (P / X + 1) ∩ majorArcs X P : Set ℝ) :=
    (Ioc_ae_eq_Icc).inter (ae_eq_refl _)
  rw [Set.inter_eq_right.mpr hsub] at h1
  have h2 : (Set.Ioc (P / X) (P / X + 1) \ majorArcs X P : Set ℝ) =ᵐ[volume]
      (Set.Icc (P / X) (P / X + 1) \ majorArcs X P : Set ℝ) :=
    (Ioc_ae_eq_Icc).diff (ae_eq_refl _)
  have hm : minorArcs X P = Set.Icc (P / X) (P / X + 1) \ majorArcs X P := by
    unfold minorArcs; congr 1; ext x; simp only [Set.mem_Icc]; constructor <;>
      rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← hm] at h2
  rw [setIntegral_congr_set h1, setIntegral_congr_set h2]
  rfl

/-! ### (3) from the tail bound -/

/-- The arithmetic part of (3): the `ν` with some `ν_i ∈ (L', L]` contribute
`≪ N L^{k−1/2} log log N`, for even `N ∈ J(X)`. -/
def TailBound : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
    |Rpp k X N - Rpp' k X N| ≤ B * N * Lg X ^ ((k : ℝ) - 1 / 2) * Real.log (Real.log N)

/-- **(3) from the tail bound**, PROVED unconditional as an implication: `TailBound → Eq3`. -/
theorem eq3_of_tail (h : TailBound) : Eq3 := by
  intro k hk
  obtain ⟨B, X0, hB⟩ := h k hk
  refine ⟨B, max X0 64, fun X hX P hP N hN hJ => ?_⟩
  obtain ⟨hP0, hPX⟩ := prange_ok (le_trans (le_max_right _ _) hX) hP
  rw [split_identity k hP0 hPX N, Complex.ofReal_re]
  exact hB X (le_trans (le_max_left _ _) hX) N hN hJ


/-! ### The tail bound from the Goldbach upper bound `R(n) ≪ n log log n` -/

/-- The classical upper bound quoted on p.3 of P0045, in the weak form used: every `R_X(n)`
with `n ≤ N` is `≤ C N log log N`, for `N ≥ 16`. It follows from the sieve bound
`R(n) ≪ 𝔖(n) n` and `𝔖(n) ≪ log log n`. Cited, not proved here. -/
def RgUpper : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, ∀ n N : ℕ, n ≤ N → 16 ≤ N → Rg X n ≤ C * N * Real.log (Real.log N)

/-- `a^{n+1} − b^{n+1} ≤ (n+1)(a − b) a^n` for `0 ≤ b ≤ a`. -/
theorem pow_sub_pow_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * (a - b) * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : 0 ≤ a := le_trans hb hab
    have hbn : b ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hb hab _
    have e1 : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b) := by ring
    rw [e1]
    have i1 : a * (a ^ (n + 1) - b ^ (n + 1)) ≤ a * ((n + 1) * (a - b) * a ^ n) :=
      mul_le_mul_of_nonneg_left ih ha
    have i2 : b ^ (n + 1) * (a - b) ≤ a ^ (n + 1) * (a - b) :=
      mul_le_mul_of_nonneg_right hbn (by linarith)
    push_cast
    have : a * ((n + 1) * (a - b) * a ^ n) + a ^ (n + 1) * (a - b) =
        ((n : ℝ) + 1 + 1) * (a - b) * a ^ (n + 1) := by ring
    linarith

/-- `R''_k − R'_k` is the sum over the `ν` with some `ν_i > ⌊L'⌋` of the inner counts. -/
theorem Rpp_sub (k : ℕ) (X : ℝ) (N : ℕ) (hsub : tuples k ⌊Lp X⌋₊ ⊆ tuples k ⌊Lg X⌋₊) :
    Rpp k X N - Rpp' k X N = ∑ ν ∈ tuples k ⌊Lg X⌋₊ \ tuples k ⌊Lp X⌋₊,
      ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
        if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else 0 := by
  have swap : ∀ T : Finset (Fin k → ℕ),
      (∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊, ∑ ν ∈ T,
        if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) =
      ∑ ν ∈ T, ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
        if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else 0 := by
    intro T
    exact (Finset.sum_congr rfl fun m1 _ => Finset.sum_comm).trans Finset.sum_comm
  unfold Rpp Rpp'
  rw [swap, swap, ← Finset.sum_sdiff hsub]
  ring

/-- **The tail bound from `RgUpper`**, PROVED unconditional as an implication. -/
theorem tail_of_rgUpper (h : RgUpper) : TailBound := by
  obtain ⟨C, hC⟩ := h
  intro k hk
  set C' := max C 0 with hC'
  refine ⟨2 * k * C', 24, fun X hX N _ hJ => ?_⟩
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ Lg X := one_le_Lg (by linarith)
  set L := Lg X with hLdef
  have hN16 : 16 ≤ N := by
    have := hJ.1
    have : (16 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hll : 0 ≤ Real.log (Real.log N) := by
    apply Real.log_nonneg
    have : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h16 : (1 : ℝ) < Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set Mx : ℕ := ⌊L⌋₊ with hMx
  set Mp : ℕ := ⌊Lp X⌋₊ with hMp
  have hLp0 : 0 ≤ Lp X := by
    unfold Lp; rw [← hLdef]
    have : Real.sqrt L ≤ L := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  have hLpL : Lp X ≤ L := by unfold Lp; rw [← hLdef]; linarith [Real.sqrt_nonneg L]
  have hMpMx : Mp ≤ Mx := Nat.floor_le_floor hLpL
  have hsub : tuples k Mp ⊆ tuples k Mx := by
    intro ν hν
    simp only [tuples, Fintype.mem_piFinset, mem_Icc] at hν ⊢
    exact fun i => ⟨(hν i).1, (hν i).2.trans hMpMx⟩
  -- each inner count is at most `C' N log log N` and nonnegative
  have hinner : ∀ ν : Fin k → ℕ,
      0 ≤ ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
        (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) ∧
      ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
        (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) ≤
          C' * N * Real.log (Real.log N) := by
    intro ν
    have hnn : 0 ≤ ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
        (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) := by
      refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
      split_ifs
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
      · exact le_refl 0
    refine ⟨hnn, ?_⟩
    by_cases hp : pow2sum ν ≤ N
    · have heq : ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
          (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) = Rg X (N - pow2sum ν) := by
        unfold Rg
        refine Finset.sum_congr rfl fun m1 _ => Finset.sum_congr rfl fun m2 _ => ?_
        have : (m1 + m2 + pow2sum ν = N) ↔ (m1 + m2 = N - pow2sum ν) := by omega
        simp only [this]
      rw [heq]
      calc Rg X (N - pow2sum ν) ≤ C * N * Real.log (Real.log N) := hC X _ N (Nat.sub_le _ _) hN16
        _ ≤ C' * N * Real.log (Real.log N) := by
            gcongr
            exact le_max_left _ _
    · have hz : ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
          (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun m1 _ => Finset.sum_eq_zero fun m2 _ => ?_
        rw [if_neg (by omega)]
      rw [hz]; positivity
  rw [Rpp_sub k X N hsub]
  have hS0 : 0 ≤ ∑ ν ∈ tuples k Mx \ tuples k Mp, ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊,
      (if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else (0 : ℝ)) :=
    Finset.sum_nonneg fun ν _ => (hinner ν).1
  rw [abs_of_nonneg hS0]
  have hS1 := Finset.sum_le_card_nsmul (tuples k Mx \ tuples k Mp) _ _ (fun ν _ => (hinner ν).2)
  rw [nsmul_eq_mul, Finset.card_sdiff_of_subset hsub, card_tuples, card_tuples] at hS1
  -- the count of `ν`
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hMxL : (Mx : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hMpL : Lp X < (Mp : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdiff : (Mx : ℝ) - Mp ≤ Real.sqrt L + 1 := by
    have : Lp X = L - Real.sqrt L := by unfold Lp; rw [← hLdef]
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL1
  have hcount : ((Mx ^ (j + 1) - Mp ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (j + 1) * L ^ ((((j + 1 : ℕ) : ℝ)) - 1 / 2) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hMpMx _)]
    push_cast
    have h1 := pow_sub_pow_le (Nat.cast_nonneg Mp) (by exact_mod_cast hMpMx : (Mp : ℝ) ≤ Mx) j
    have h2 : (Mx : ℝ) ^ j ≤ L ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hMxL j
    have hL0 : 0 < L := by linarith
    have h3 : L ^ (((j : ℝ) + 1) - 1 / 2) = Real.sqrt L * L ^ j := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hL0]; congr 1; ring
    rw [h3]
    have hMxMp : 0 ≤ (Mx : ℝ) - Mp := by
      have : (Mp : ℝ) ≤ Mx := by exact_mod_cast hMpMx
      linarith
    calc (Mx : ℝ) ^ (j + 1) - (Mp : ℝ) ^ (j + 1) ≤ (j + 1) * ((Mx : ℝ) - Mp) * (Mx : ℝ) ^ j := h1
      _ ≤ (j + 1) * (Real.sqrt L + 1) * L ^ j := by gcongr
      _ ≤ (j + 1) * (2 * Real.sqrt L) * L ^ j := by gcongr; linarith
      _ = 2 * (j + 1) * (Real.sqrt L * L ^ j) := by ring
  have hpos : 0 ≤ C' * N * Real.log (Real.log N) := by positivity
  calc _ ≤ ((Mx ^ (j + 1) - Mp ^ (j + 1) : ℕ) : ℝ) * (C' * N * Real.log (Real.log N)) := hS1
    _ ≤ (2 * (j + 1) * L ^ ((((j + 1 : ℕ) : ℝ)) - 1 / 2)) * (C' * N * Real.log (Real.log N)) :=
        mul_le_mul_of_nonneg_right hcount hpos
    _ = 2 * ((j + 1 : ℕ) : ℝ) * C' * N * L ^ ((((j + 1 : ℕ) : ℝ)) - 1 / 2) *
          Real.log (Real.log N) := by push_cast; ring

/-- (3) CONDITIONAL ON the Goldbach upper bound `RgUpper` only. -/
theorem eq3_of_rgUpper (h : RgUpper) : Eq3 := eq3_of_tail (tail_of_rgUpper h)

/-- **The repaired P0045 Theorem on `J(X)`**, constant `2c₀ C(k, N)`, as an implication from
three classical inputs: `RgUpper`, the minor arc sup bound `MinorBound` and the repaired (25). -/
theorem mainJ_twoC0_of_inputs (hR : RgUpper) (hm : MinorBound)
    (h25 : Eq25C (fun k N => twoC0 * Ckn k N)) : MainJ_twoC0 :=
  mainJ_twoC0_of_minorBound (eq3_of_rgUpper hR) hm h25

end

end LeanLab.LPZ2007.Eq3Reduce

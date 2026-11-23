/-
P0068 Zhan 1991, the LEAF `line_shift_leaf` of SPLIT_eq31_1122d.lean, page 264, proved.
Source: papers/P0068.pdf. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.

The definitions `Vline_ls` and `LineShift_ls` are copies of `Vline` and `LineShift` of
SPLIT_eq31_1122d.lean, character for character apart from the name, since that module is not
built here. `lineShift_proof_ls` is PROVED with no LEAF: Cauchy's theorem on the rectangle
`a ≤ Re s ≤ b`, `|Im s| ≤ T` with the trivial bound of the horizontal sides, the triangle
inequality for `F`, the dyadic factor bound `Σ_{n ∈ I_j} |a_j(n)| n^{-σ} ≤ 3 (1 + log(2^22 N))
N_j^{1-σ}`, the product bound under (3.5), `L^{20} ≪ N^ε`, `|u^s - (N-A)^s| ≤ 2 N^σ`, `|s| ≥ T`,
and the assembly.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline_ls {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))

/-- The shift of the line of integration from `Re s = c` to `Re s = 1/2`, page 264, with error
`O(N^{1+ε}/T + max_{1/2 ≤ σ ≤ c} N^σ N^{1-σ}/T)`. -/
def LineShift_ls : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ‖Vline_ls Nv χ N A (1 + 1 / Real.log N) T u - Vline_ls Nv χ N A (1 / 2) T u‖
      ≤ K * (N : ℝ) ^ (1 + ε) / T

/-- The integrand `F(s,χ) (u^s - (N-A)^s) / s` of (3.4), page 264. -/
def Gint_ls {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ)
    (s : ℂ) : ℂ :=
  Fprod Nv χ s * (((u : ℂ) ^ s - (((N : ℝ) - A : ℝ) : ℂ) ^ s) / s)

/-- PROVED: page 264, "moving the line of integration to Re s = 1/2": the integrand
`F(s)(u^s-(N-A)^s)/s` is holomorphic on the rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ T` with
`a > 0`, so by Cauchy's theorem the two vertical integrals differ by the two horizontal ones,
each bounded by its length `b - a` times a bound `M` of the integrand. Class MEDIUM. -/
theorem rect_shift_leaf_ls {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (A a b T u M : ℝ) (ha : 0 < a) (hab : a ≤ b) (_hT : 0 < T) (hu : 0 < u)
    (hNA : 0 < (N : ℝ) - A)
    (hM : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖Gint_ls Nv χ N A u ((σ : ℂ) + T * Complex.I)‖ ≤ M ∧
      ‖Gint_ls Nv χ N A u ((σ : ℂ) - T * Complex.I)‖ ≤ M) :
    ‖Vline_ls Nv χ N A b T u - Vline_ls Nv χ N A a T u‖ ≤ (b - a) * M / π := by
  set G := Gint_ls Nv χ N A u with hG
  have hdiff : DifferentiableOn ℂ G (Set.uIcc a b ×ℂ Set.uIcc (-T) T) := by
    intro s hs
    have hre : a ≤ s.re := by
      have := (Complex.mem_reProdIm.mp hs).1
      rw [Set.uIcc_of_le hab] at this
      exact this.1
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    apply DifferentiableAt.differentiableWithinAt
    unfold G Gint_ls Fprod fj
    apply DifferentiableAt.mul
    · apply DifferentiableAt.fun_finsetProd
      intro j _
      apply DifferentiableAt.fun_sum
      intro n hn
      have hn1 : (n : ℂ) ≠ 0 := by
        have : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        exact_mod_cast (by omega : n ≠ 0)
      exact (differentiableAt_id.neg.const_cpow (Or.inl hn1)).const_mul _
    · apply DifferentiableAt.div _ differentiableAt_id hs0
      apply DifferentiableAt.sub
      · exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hu.ne'))
      · exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hNA.ne'))
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    ((a : ℂ) - T * Complex.I) ((b : ℂ) + T * Complex.I) (by simpa using hdiff)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.sub_im, Complex.mul_im,
    Complex.add_im] at hC
  simp only [mul_zero, sub_zero, mul_one, zero_mul, add_zero, zero_sub, zero_add] at hC
  set Hlo := ∫ x : ℝ in a..b, G (x + (-T : ℝ) * Complex.I) with hHlo
  set Hhi := ∫ x : ℝ in a..b, G (x + T * Complex.I) with hHhi
  have hV : ∀ σ : ℝ, Vline_ls Nv χ N A σ T u =
      (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, G ((σ : ℂ) + t * Complex.I) := fun σ => rfl
  have key : Vline_ls Nv χ N A b T u - Vline_ls Nv χ N A a T u =
      (1 / (2 * π) : ℂ) * (Complex.I * (Hlo - Hhi)) := by
    rw [hV, hV, ← mul_sub]
    congr 1
    have hC' : Hlo - Hhi + Complex.I * ((∫ y : ℝ in (-T)..T, G (b + y * Complex.I)) -
        ∫ y : ℝ in (-T)..T, G (a + y * Complex.I)) = 0 := by
      rw [smul_eq_mul, smul_eq_mul] at hC; linear_combination hC
    have : (∫ y : ℝ in (-T)..T, G (b + y * Complex.I)) -
        ∫ y : ℝ in (-T)..T, G (a + y * Complex.I) =
        Complex.I * (Hlo - Hhi) := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (-Complex.I) * hC' + ((∫ y : ℝ in (-T)..T, G (b + y * Complex.I)) -
        ∫ y : ℝ in (-T)..T, G (a + y * Complex.I)) * hI
    exact this
  have hlo : ‖Hlo‖ ≤ M * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have e : (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = (x : ℂ) - T * Complex.I := by
      push_cast; ring
    rw [e]; exact (hM x hx.1.le hx.2).2
  have hhi : ‖Hhi‖ ≤ M * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact (hM x hx.1.le hx.2).1
  rw [key, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hpi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  rw [abs_of_nonneg (by linarith : 0 ≤ b - a)] at hlo hhi
  have := norm_sub_le Hlo Hhi
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- PROVED: page 264, one factor of the trivial bound of `F`: for `n ∈ I_j = (N_j, 2N_j]`,
`|a_j(n)| ≤ 1 + log n ≤ 1 + log(2^22 N)`, `n^{-σ} ≤ N_j^{-σ}` and `#I_j ≤ N_j + 1 ≤ 3 N_j`, with
`N_j ≤ 2^19 N` from (3.5). -/
theorem factor_bound_leaf_ls : ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (σ : ℝ) (j : Fin 20),
    2 ≤ N → Cond35 N Nv → 1 / 2 ≤ σ → σ ≤ 2 →
    ∑ n ∈ dyad (Nv j), ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ)
      ≤ 3 * (1 + Real.log (2 ^ 22 * N)) * Nv j ^ (1 - σ) := by
  intro N Nv σ j hN hC hσ1 hσ2
  obtain ⟨h1, h2, h3, -⟩ := hC
  set x := Nv j with hx
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hxpos : 0 < x := by linarith [h1 j]
  -- `x ≤ 2^19 N`
  have hxN : x ≤ 2 ^ 19 * N := by
    have hsplit := Finset.mul_prod_erase Finset.univ Nv (Finset.mem_univ j)
    have hrest : (1 / 2 : ℝ) ^ 19 ≤ ∏ i ∈ Finset.univ.erase j, Nv i := by
      have := Finset.prod_le_prod₀ (s := Finset.univ.erase j) (f := fun _ => (1 / 2 : ℝ))
        (g := Nv) (fun _ _ => by norm_num) (fun i _ => h1 i)
      simpa [Finset.prod_const, Finset.card_erase_of_mem] using this
    have : x * (1 / 2 : ℝ) ^ 19 ≤ N := by
      calc x * (1 / 2 : ℝ) ^ 19 ≤ x * ∏ i ∈ Finset.univ.erase j, Nv i :=
            mul_le_mul_of_nonneg_left hrest hxpos.le
        _ = ∏ i, Nv i := hsplit
        _ ≤ N := h3
    have e : x = x * (1 / 2 : ℝ) ^ 19 * 2 ^ 19 := by ring
    rw [e]; nlinarith
  set Lg := 1 + Real.log (2 ^ 22 * N) with hLg
  have hlog0 : 0 ≤ Real.log (2 ^ 22 * N) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by norm_num)
      (by have : (2 : ℝ) ≤ N := by exact_mod_cast hN
          linarith))
  have hterm : ∀ n ∈ dyad x, ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ) ≤ Lg * x ^ (-σ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hxn : x < n := hn'.2
    have hn2 : (n : ℝ) ≤ 2 * x := by
      have := (Finset.mem_Icc.mp hn'.1).2
      have h2x : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
      have : (n : ℝ) ≤ ⌊2 * x⌋₊ := by exact_mod_cast this
      linarith
    have hn1 : (1 : ℝ) ≤ n := by
      have := (Finset.mem_Icc.mp hn'.1).1
      exact_mod_cast this
    have ha : ‖aj (j.val + 1) n‖ ≤ Lg := by
      unfold aj
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1)]
        have : Real.log n ≤ Real.log (2 ^ 22 * N) :=
          Real.log_le_log (by linarith) (by nlinarith)
        linarith
      · simp; linarith
      · have : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        linarith
    have hp : (n : ℝ) ^ (-σ) ≤ x ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hxpos hxn.le (by linarith)
    exact mul_le_mul ha hp (by positivity) (by linarith)
  have hcard : ((dyad x).card : ℝ) ≤ 3 * x := by
    have hsub : dyad x ⊆ Finset.Icc (⌊x⌋₊ + 1) ⌊2 * x⌋₊ := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hn'.1).2⟩
      have : ⌊x⌋₊ < n := (Nat.floor_lt hxpos.le).mpr hn'.2
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hf1 : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
    have hf2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have : ((dyad x).card : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) - ⌊x⌋₊ := by
      have hfl : ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_le_floor (by linarith)
      have : (dyad x).card + ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by omega
      have : ((dyad x).card : ℝ) + ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by exact_mod_cast this
      linarith
    linarith [h1 j]
  calc ∑ n ∈ dyad x, ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ dyad x, Lg * x ^ (-σ) := Finset.sum_le_sum hterm
    _ = (dyad x).card * (Lg * x ^ (-σ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * x) * (Lg * x ^ (-σ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 * Lg * (x * x ^ (-σ)) := by ring
    _ = 3 * Lg * x ^ (1 - σ) := by
        congr 1
        rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add hxpos, Real.rpow_one]

/-- PROVED: the elementary estimate `L^{20} ≪ N^ε`, used on page 264 to absorb the logarithms
of `a_1(n) = log n` into `N^ε`. -/
theorem logpow_leaf_ls : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
    (3 * (1 + Real.log (2 ^ 22 * N))) ^ 20 ≤ K * (N : ℝ) ^ ε := by
  intro ε hε
  set δ := ε / 20 with hδ
  have hδpos : 0 < δ := by positivity
  set C := 1 + (2 ^ 22 : ℝ) ^ δ / δ with hC
  refine ⟨(3 * C) ^ 20, 1, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNd : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδpos.le
  have hlog0 : 0 ≤ Real.log (2 ^ 22 * N) := Real.log_nonneg (by nlinarith)
  have hl := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 2 ^ 22 * N) hδpos
  rw [Real.mul_rpow (by positivity) hNpos.le] at hl
  have hB : 3 * (1 + Real.log (2 ^ 22 * N)) ≤ 3 * C * (N : ℝ) ^ δ := by
    have : (2 ^ 22 : ℝ) ^ δ * (N : ℝ) ^ δ / δ = (2 ^ 22 : ℝ) ^ δ / δ * (N : ℝ) ^ δ := by ring
    rw [this] at hl
    have hq : 0 ≤ (2 ^ 22 : ℝ) ^ δ / δ := by positivity
    rw [hC]; nlinarith
  calc (3 * (1 + Real.log (2 ^ 22 * N))) ^ 20 ≤ (3 * C * (N : ℝ) ^ δ) ^ 20 :=
        pow_le_pow_left₀ (by positivity) hB 20
    _ = (3 * C) ^ 20 * ((N : ℝ) ^ δ) ^ (20 : ℕ) := by ring
    _ = (3 * C) ^ 20 * (N : ℝ) ^ ε := by
        rw [← Real.rpow_mul_natCast hNpos.le]
        congr 2; rw [hδ]; push_cast; ring

/-- Condition (3.5) gives `(N₁⋯N₂₀)^{1-σ} ≤ 2^21 N^{1-σ}` for `σ ≤ 1 + 1/L ≤ 2`. -/
theorem prodpow_le_ls (N : ℕ) (Nv : Fin 20 → ℝ) (σ : ℝ) (hN : 2 ≤ N) (hC : Cond35 N Nv)
    (hσ : σ ≤ 2) :
    (∏ j, Nv j) ^ (1 - σ) ≤ 2 ^ 21 * (N : ℝ) ^ (1 - σ) := by
  obtain ⟨h1, h2, h3, -⟩ := hC
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlo : 0 < (N : ℝ) / 2 ^ 21 := by positivity
  have hP : 0 < ∏ j, Nv j := lt_of_lt_of_le hlo h2
  have hNp : 0 ≤ (N : ℝ) ^ (1 - σ) := by positivity
  rcases le_or_gt σ 1 with h | h
  · have := Real.rpow_le_rpow hP.le h3 (by linarith : 0 ≤ 1 - σ)
    nlinarith
  · calc (∏ j, Nv j) ^ (1 - σ) ≤ ((N : ℝ) / 2 ^ 21) ^ (1 - σ) :=
          Real.rpow_le_rpow_of_nonpos hlo h2 (by linarith)
      _ = (N : ℝ) ^ (1 - σ) * ((2 : ℝ) ^ 21) ^ (σ - 1) := by
          rw [Real.div_rpow hNpos.le (by positivity), div_eq_mul_inv,
            ← Real.rpow_neg (by positivity)]
          ring_nf
      _ ≤ (N : ℝ) ^ (1 - σ) * ((2 : ℝ) ^ 21) ^ (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hNp
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 ^ 21 * (N : ℝ) ^ (1 - σ) := by rw [Real.rpow_one]; ring

/-- The trivial bound of `F(σ + it, χ)` by the product of the absolute dyadic sums, page 264,
`Π_j Σ_{N_j<n≤2N_j} |a_j(n)| n^{-σ} ≪ L^{20} Π_j N_j^{1-σ} ≪ N^{1-σ+ε}` for
`1/2 ≤ σ ≤ c = 1 + L⁻¹` under (3.5). -/
theorem absprod_bound_leaf_ls : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (σ : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 / 2 ≤ σ → σ ≤ 1 + 1 / Real.log N →
      ∏ j : Fin 20, ∑ n ∈ dyad (Nv j), ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ)
        ≤ K * (N : ℝ) ^ (1 - σ + ε) := by
  intro ε hε
  obtain ⟨K1, N1, hK1, hL⟩ := logpow_leaf_ls ε hε
  refine ⟨2 ^ 21 * K1, max N1 8, by positivity, ?_⟩
  intro N Nv σ hN0 hC hσ1 hσ2
  have hN8 : (8 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    linarith [Real.exp_one_lt_d9]
  have hσ2' : σ ≤ 2 := by
    have : 1 / Real.log N ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog
    linarith
  set B := 3 * (1 + Real.log (2 ^ 22 * N)) with hB
  have hBpos : 0 ≤ B := by
    have : 0 ≤ Real.log (2 ^ 22 * N) := Real.log_nonneg (by nlinarith)
    positivity
  have hNvpos : ∀ j, 0 < Nv j := fun j => by linarith [hC.1 j]
  calc ∏ j : Fin 20, ∑ n ∈ dyad (Nv j), ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ)
      ≤ ∏ j : Fin 20, (B * Nv j ^ (1 - σ)) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun n hn => by positivity)
          (fun j _ => factor_bound_leaf_ls N Nv σ j hN2 hC hσ1 hσ2')
    _ = B ^ 20 * (∏ j, Nv j) ^ (1 - σ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.finsetProd_rpow _ _ (fun j _ => (hNvpos j).le)]
    _ ≤ (K1 * (N : ℝ) ^ ε) * (2 ^ 21 * (N : ℝ) ^ (1 - σ)) := by
        apply mul_le_mul (hL N (le_trans (le_max_left _ _) hN0))
          (prodpow_le_ls N Nv σ hN2 hC hσ2')
          (Real.rpow_nonneg (Finset.prod_nonneg fun j _ => (hNvpos j).le) _) (by positivity)
    _ = 2 ^ 21 * K1 * ((N : ℝ) ^ (1 - σ) * (N : ℝ) ^ ε) := by ring
    _ = 2 ^ 21 * K1 * (N : ℝ) ^ (1 - σ + ε) := by rw [← Real.rpow_add hNpos]

/-- The triangle inequality for `F(s, χ) = Π f_j(s, χ)`, display (3.6), page 264, with
`|χ(n)| ≤ 1` and `|n^{-s}| = n^{-σ}`. -/
theorem fprod_le_absprod_ls {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (σ t : ℝ) :
    ‖Fprod Nv χ ((σ : ℂ) + t * Complex.I)‖ ≤
      ∏ j : Fin 20, ∑ n ∈ dyad (Nv j), ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ) := by
  unfold Fprod fj
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : (0 : ℝ) < n := by
    have : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    exact_mod_cast this
  rw [norm_mul, norm_mul]
  have hc : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos hn1]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  have h0 : 0 ≤ ‖aj (j.val + 1) n‖ * (n : ℝ) ^ (-σ) := by positivity
  nlinarith [norm_nonneg (aj (j.val + 1) n), Real.rpow_nonneg hn1.le (-σ)]

/-- The bound `F(σ + it, χ) ≪ N^{1-σ+ε}`, page 264. -/
theorem fprod_bound_leaf_ls : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧
    ∀ (N : ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ) (σ t : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 / 2 ≤ σ → σ ≤ 1 + 1 / Real.log N →
      ‖Fprod Nv χ ((σ : ℂ) + t * Complex.I)‖ ≤ K * (N : ℝ) ^ (1 - σ + ε) := by
  intro ε hε
  obtain ⟨K, N₀, hK, h⟩ := absprod_bound_leaf_ls ε hε
  exact ⟨K, N₀, hK, fun N q χ Nv σ t h1 h2 h3 h4 =>
    (fprod_le_absprod_ls Nv χ σ t).trans (h N Nv σ h1 h2 h3 h4)⟩

/-- The bound of the horizontal integrand, page 264: `|u^s - (N-A)^s| ≤ 2 N^σ`, `|s| ≥ T`. -/
theorem gint_bound_ls {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (A u σ T K ε : ℝ) (s : ℂ) (hs : s.re = σ) (hT : 0 < T) (hsT : T ≤ |s.im|)
    (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hNA : 0 < (N : ℝ) - A) (hu0 : (N : ℝ) - A ≤ u) (huN : u ≤ N)
    (hF : ‖Fprod Nv χ s‖ ≤ K * (N : ℝ) ^ (1 - σ + ε)) :
    ‖Gint_ls Nv χ N A u s‖ ≤ 2 * K * (N : ℝ) ^ (1 + ε) / T := by
  have hN : (0 : ℝ) < N := by linarith
  have hu : 0 < u := by linarith
  have hK : 0 ≤ K * (N : ℝ) ^ (1 - σ + ε) := le_trans (norm_nonneg _) hF
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hT (hsT.trans (Complex.abs_im_le_norm s))
  have hdiff : ‖(u : ℂ) ^ s - (((N : ℝ) - A : ℝ) : ℂ) ^ s‖ ≤ 2 * (N : ℝ) ^ σ := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_cpow_eq_rpow_re_of_pos hNA, hs]
    have h1 : u ^ σ ≤ (N : ℝ) ^ σ := Real.rpow_le_rpow hu.le huN hσ
    have h2 : ((N : ℝ) - A) ^ σ ≤ (N : ℝ) ^ σ := Real.rpow_le_rpow hNA.le (by linarith) hσ
    linarith
  unfold Gint_ls
  rw [norm_mul, norm_div]
  have hpow : (N : ℝ) ^ (1 - σ + ε) * (N : ℝ) ^ σ = (N : ℝ) ^ (1 + ε) := by
    rw [← Real.rpow_add hN]; ring_nf
  calc ‖Fprod Nv χ s‖ * (‖(u : ℂ) ^ s - (((N : ℝ) - A : ℝ) : ℂ) ^ s‖ / ‖s‖)
      ≤ (K * (N : ℝ) ^ (1 - σ + ε)) * (2 * (N : ℝ) ^ σ / T) := by
        apply mul_le_mul hF _ (by positivity) hK
        calc ‖(u : ℂ) ^ s - (((N : ℝ) - A : ℝ) : ℂ) ^ s‖ / ‖s‖
            ≤ 2 * (N : ℝ) ^ σ / ‖s‖ := div_le_div_of_nonneg_right hdiff hs0.le
          _ ≤ 2 * (N : ℝ) ^ σ / T :=
            div_le_div_of_nonneg_left (by positivity) hT
              (hsT.trans (Complex.abs_im_le_norm s))
    _ = 2 * K * ((N : ℝ) ^ (1 - σ + ε) * (N : ℝ) ^ σ) / T := by ring
    _ = 2 * K * (N : ℝ) ^ (1 + ε) / T := by rw [hpow]

/-- The shift of the line, page 264. -/
theorem lineShift_proof_ls : LineShift_ls := by
  intro ε hε
  obtain ⟨K1, N1, hK1, hF⟩ := fprod_bound_leaf_ls ε hε
  refine ⟨2 * K1, max N1 8, by positivity, ?_⟩
  intro N A T u q χ Nv hN0 hA0 hA hC hT2 hTN hu0 huN
  have hN8 : (8 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
  have hN1 : N1 ≤ N := le_trans (le_max_left _ _) hN0
  have hNpos : (0 : ℝ) < N := by linarith
  have hlt : (N : ℝ) ^ (2 / 3 : ℝ) < N := Real.rpow_lt_self_of_one_lt (by linarith) (by norm_num)
  have hNA : 0 < (N : ℝ) - A := by linarith
  have hT : 0 < T := by linarith
  have hlog : 2 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 2.7182818286 * 2.7182818286 := by
          apply mul_lt_mul'' this this (Real.exp_pos 1).le (Real.exp_pos 1).le
        _ < 8 := by norm_num
    linarith
  have hlogpos : 0 < Real.log N := by linarith
  have hc1 : 1 / Real.log N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hlogpos (by norm_num)]; linarith
  have hcpos : 0 < 1 / Real.log N := by positivity
  set c := 1 + 1 / Real.log N with hc
  have hM : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ c →
      ‖Gint_ls Nv χ N A u ((σ : ℂ) + T * Complex.I)‖ ≤ 2 * K1 * (N : ℝ) ^ (1 + ε) / T ∧
      ‖Gint_ls Nv χ N A u ((σ : ℂ) - T * Complex.I)‖ ≤ 2 * K1 * (N : ℝ) ^ (1 + ε) / T := by
    intro σ h1 h2
    constructor
    · refine gint_bound_ls Nv χ N A u σ T K1 ε _ (by simp) hT (by simp [abs_of_pos hT])
        (by linarith) hA0 hNA hu0 huN (hF N q χ Nv σ T hN1 hC h1 h2)
    · have e : (σ : ℂ) - T * Complex.I = (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e]
      refine gint_bound_ls Nv χ N A u σ T K1 ε _ (by simp) hT (by simp [abs_of_pos hT])
        (by linarith) hA0 hNA hu0 huN (hF N q χ Nv σ (-T) hN1 hC h1 h2)
  have hR := rect_shift_leaf_ls Nv χ N A (1 / 2) c T u (2 * K1 * (N : ℝ) ^ (1 + ε) / T)
    (by norm_num) (by linarith) hT (by linarith) hNA hM
  have hMnn : 0 ≤ 2 * K1 * (N : ℝ) ^ (1 + ε) / T := by positivity
  calc _ ≤ (c - 1 / 2) * (2 * K1 * (N : ℝ) ^ (1 + ε) / T) / π := hR
    _ ≤ (c - 1 / 2) * (2 * K1 * (N : ℝ) ^ (1 + ε) / T) := by
        apply div_le_self (mul_nonneg (by linarith) hMnn)
        linarith [Real.pi_gt_three]
    _ ≤ 1 * (2 * K1 * (N : ℝ) ^ (1 + ε) / T) := by
        apply mul_le_mul_of_nonneg_right _ hMnn; linarith
    _ = 2 * K1 * (N : ℝ) ^ (1 + ε) / T := one_mul _

end

end LeanLab.Zhan1991

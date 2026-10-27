/-
Unit U-1529, run 20261025T2003Z-426, DECOMPOSE of the GRH inputs of P0011,
Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104.

File b: Perron's formula, the truncated explicit formula, and the GRH bound
`|ψ(x, χ) - δ_χ x| ≤ c √x log²(qx)`.
* `perronI y c T = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, Perron's truncated integral.
* `psiChi χ x = ∑_{n ≤ x} χ(n) Λ(n)`, complex valued.
Leaves: Perron's kernel lemma in its three cases, the truncated Perron formula for `ψ`, the
tail bound, the contour shift, a good height `T` avoiding ordinates, the explicit formula for
`ψ` with an explicit constant, and the explicit formula for `ψ(x, χ)` under GRH.
Assembly `psiChi_bound_of_GRH`, PROVED from leaves here and in Decomp1529a, zero sorry in its
own proof, CONDITIONAL ON GRH and the leaves `explicit_formula_chi_GRH`, `LZeros_finite`,
`LZeros_recip_sum`.

Source when the original is not at hand: Davenport, Multiplicative Number Theory, 3rd ed.,
ch. 17 (Perron, explicit formula for ψ) and ch. 19-20 (ψ(x, χ), the GRH bound, p. 125).
P0011 page 101 uses only the `q = 1` case, through Schoenfeld 1976 (6.1).
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.DERZ1997.Decomp1529a
import LeanLab.DERZ1997.Kernel136
import LeanLab.DERZ1997.Perron136
import LeanLab.PNTPort.ZetaZeros.GoodHeight

namespace LeanLab.DERZ1997.Decomp1529b
open Complex LeanLab.DERZ1997.Decomp1529a

/-- The twisted Chebyshev function `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The truncated Perron integral of `-ζ'/ζ = ∑ Λ(n) n^{-s}` against `x^s/s` on `Re s = c`. -/
noncomputable def perronPsi (x c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) *
      (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-! ### Perron's formula -/

/-- LEAF. Perron kernel, `y > 1`: for `c > 0`, `T > 0`,
`|(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds - 1| ≤ y^c min(1, 1/(T log y))`. Shift left past the pole at
0 along a rectangle (bound `y^c/(πT log y)`) or along a circular arc (bound `y^c`).
Davenport ch. 17, Lemma, p. 105. Unit U-1529. -/
theorem perron_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI y c T - 1‖ ≤ y ^ c * min 1 (1 / (T * Real.log y)) := by
  by_cases hlarge : 1 ≤ T * Real.log y
  · exact LeanLab.DERZ1997.Perron136.perron_gt_one_large hy hc hT hlarge
  · have hs : T * Real.log y ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * Real.log y := mul_pos hT (Real.log_pos hy)
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact LeanLab.DERZ1997.Perron136.perron_gt_one_small hy hc hT hs

/-- LEAF. Perron kernel, `0 < y < 1`: for `c > 0`, `T > 0`,
`|(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds| ≤ y^c min(1, 1/(T |log y|))`, by shifting right.
Davenport ch. 17, Lemma, p. 105. Unit U-1529. -/
theorem perron_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronI y c T‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  by_cases hlarge : 1 ≤ T * |Real.log y|
  · exact LeanLab.DERZ1997.Perron136.perron_lt_one_large hy0 hy hc hT hlarge
  · have hs : T * |Real.log y| ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * |Real.log y| := mul_pos hT
      (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy0 (ne_of_lt hy)))
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact LeanLab.DERZ1997.Perron136.perron_norm_small hy0 hc hT hs

/-- LEAF. Perron kernel, `y = 1`: `|(1/2π) ∫_{-T}^{T} dt/(c+it) - 1/2| ≤ c/T`; the integral is
`arctan(T/c)/π` and `1/2 - arctan(T/c)/π = arctan(c/T)/π`. Davenport ch. 17, p. 105.
Unit U-1529. -/
theorem perron_one {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronI 1 c T - 1 / 2‖ ≤ c / T := by
  have hval : perronI 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
    have hn : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := by
      intro t h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hcont : Continuous (fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I)) := by
      exact continuous_const.div (by fun_prop) hn
    have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
    have hre : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).re =
        2 * Real.arctan (T / c) := by
      calc
        _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).re :=
          (Complex.reCLM.intervalIntegral_comp_comm hint).symm
        _ = ∫ t : ℝ in (-T)..T, c / (c ^ 2 + t ^ 2) := by
          congr 1
          funext t
          simp [Complex.div_re, Complex.normSq_apply, pow_two]
        _ = _ := by rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]; ring
    have him : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).im = 0 := by
      calc
        _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).im :=
          (Complex.imCLM.intervalIntegral_comp_comm hint).symm
        _ = ∫ t : ℝ in (-T)..T, -(t / (c ^ 2 + t ^ 2)) := by
          congr 1
          funext t
          simp [Complex.div_im, Complex.normSq_apply, pow_two, neg_div]
        _ = _ := by
          rw [intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc.ne']
          simp
    unfold perronI
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [hfac]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero, hre]
      ring
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero, him]
  have hdiff : perronI 1 c T - 1 / 2 =
      ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    rw [hval]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hupper : Real.arctan (T / c) / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  rw [abs_of_nonpos (by linarith)]
  have hinv : Real.arctan (c / T) = Real.pi / 2 - Real.arctan (T / c) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos hT hc)
  have heq : -(Real.arctan (T / c) / Real.pi - 1 / 2) =
      Real.arctan (c / T) / Real.pi := by
    rw [hinv]
    field_simp
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right (Real.arctan_le_self (by positivity))
    Real.pi_pos.le).trans (div_le_self (by positivity) (by linarith [Real.pi_gt_three]))

/-- LEAF. Truncated Perron formula for `ψ`: for `x ≥ 2` not an integer, `c > 1`, `T > 0`,
`|ψ(x) - (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds| ≤ ∑_n Λ(n) (x/n)^c min(1, 1/(T|log(x/n)|))`.
Expand `-ζ'/ζ(s) = ∑ Λ(n) n^{-s}`, which converges absolutely on `Re s = c`, integrate
term by term, and apply `perron_gt_one` for `n < x`, `perron_lt_one` for `n > x`.
Davenport ch. 17, (2)-(3), p. 105-106. Unit U-1529. -/
theorem perron_psi {x c T : ℝ} (hx : 2 ≤ x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hc : 1 < c)
    (hT : 0 < T) :
    ‖(Chebyshev.psi x : ℂ) - perronPsi x c T‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (x / n) ^ c *
        min 1 (1 / (T * |Real.log (x / n)|)) := by
  sorry

/-- LEAF. Tail of the truncated Perron formula: there is an absolute `C` such that for
`x = N + 1/2` with `N ≥ 2`, `c = 1 + 1/log x`, `T ≥ 2`,
`∑_n Λ(n) (x/n)^c min(1, 1/(T|log(x/n)|)) ≤ C (x log² x / T + log x)`. Split `n` by
`|n - x| ≥ x/4`, the range `x/2 ≤ n ≤ 2x` by `|n - x|`, and use `∑ Λ(n) n^{-c} ≪ log x`.
Davenport ch. 17, p. 106-107. Unit U-1529. -/
theorem perron_tail : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 2 ≤ T →
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (((N : ℝ) + 1 / 2) / n) ^
        (1 + 1 / Real.log ((N : ℝ) + 1 / 2)) *
      min 1 (1 / (T * |Real.log (((N : ℝ) + 1 / 2) / n)|)) ≤
      C * (((N : ℝ) + 1 / 2) * Real.log ((N : ℝ) + 1 / 2) ^ 2 / T +
        Real.log ((N : ℝ) + 1 / 2)) := by
  sorry

/-! ### Contour shift and the explicit formula -/

/-- LEAF. A good height: for every `T ≥ 2` there is `T' ∈ [T, T + 1]` at distance at least
`1/(100 log T')` from every ordinate of a zero with `|γ| ≤ T' + 1`. The bad set is covered by
intervals of length `2/(100 log T)` around at most `2 (2 log (T + 1) + 5)` ordinates
(`window_count`), total length below 1. Davenport ch. 17, p. 108. Unit U-1529. -/
theorem good_height {T : ℝ} (hT : 2 ≤ T) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ ρ ∈ zetaZeros (T' + 1), 1 / (100 * Real.log T') ≤ |ρ.im - T'| := by
  classical
  by_cases hsmall : T < 4
  · refine ⟨T, le_rfl, by linarith, ?_⟩
    intro ρ hρ
    rw [zetaZeros_eq_empty (by linarith : T + 1 < 14)] at hρ
    exact False.elim hρ
  have hlarge : 4 ≤ T := le_of_not_gt hsmall
  have hfin (j : Fin 3) : (zetaZerosWindow (T - 1 + j)).Finite := by
    apply (zetaZeros_finite (T + 2)).subset
    intro z hz
    refine ⟨hz.1, hz.2.1, hz.2.2.1, ?_⟩
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
    rw [abs_of_pos (by linarith [hz.2.2.2.1])]
    linarith [hz.2.2.2.2]
  let W : Fin 3 → Finset ℂ := fun j => (hfin j).toFinset
  have hWz (j : Fin 3) (z : ℂ) (hz : z ∈ W j) : z ∈ zetaZeros (T + 2) := by
    have hz := (Set.Finite.mem_toFinset (hfin j)).mp hz
    refine ⟨hz.1, hz.2.1, hz.2.2.1, ?_⟩
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
    rw [abs_of_pos (by linarith [hz.2.2.2.1])]
    linarith [hz.2.2.2.2]
  have hcardW (j : Fin 3) : ((W j).card : ℝ) ≤ 2 * Real.log (T + 1) + 5 := by
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hc := window_count (T := T - 1 + j)
      (by have := Real.exp_one_lt_d9; linarith) (hfin j)
    have hle : Real.log (T - 1 + j) ≤ Real.log (T + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    calc
      ((W j).card : ℝ) = ∑ _z ∈ W j, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ W j, (zetaMult z : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        exact_mod_cast one_le_zetaMult (hWz j z hz)
      _ ≤ _ := by exact hc.trans (by linarith)
  let U : Finset ℂ := Finset.univ.biUnion W
  let G : Finset ℝ := U.image Complex.im
  have hGc : (G.card : ℝ) ≤ 3 * (2 * Real.log (T + 1) + 5) := by
    have h1 : G.card ≤ U.card := Finset.card_image_le
    have h2 : U.card ≤ ∑ j : Fin 3, (W j).card := Finset.card_biUnion_le
    calc
      (G.card : ℝ) ≤ U.card := by exact_mod_cast h1
      _ ≤ ∑ j : Fin 3, ((W j).card : ℝ) := by exact_mod_cast h2
      _ ≤ ∑ _j : Fin 3, (2 * Real.log (T + 1) + 5) := Finset.sum_le_sum (fun j _ => hcardW j)
      _ = _ := by simp; ring
  obtain ⟨T', ⟨hlo, hhi⟩, hfar⟩ := LeanLab.PNTPort.ZetaZeros.exists_far G T
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogadd : Real.log (T + 1) ≤ Real.log T + 1 := by
    have h1 := Real.log_le_log (by linarith : (0 : ℝ) < T + 1)
      (by linarith : T + 1 ≤ 2 * T)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlog' : Real.log T ≤ Real.log T' := Real.log_le_log (by linarith) hlo
  have hden : 2 * ((G.card : ℝ) + 1) ≤ 100 * Real.log T' := by nlinarith
  have hrad : 1 / (100 * Real.log T') ≤ 1 / (2 * ((G.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hone : 1 / (100 * Real.log T') ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    linarith
  refine ⟨T', hlo, hhi, ?_⟩
  intro z hz
  by_cases hnear : T - 1 < z.im ∧ z.im ≤ T + 2
  · have hmem : z.im ∈ G := by
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      apply Finset.mem_biUnion.mpr
      have hx : z ∈ zetaZerosWindow (T - 1) ∨ z ∈ zetaZerosWindow T ∨
          z ∈ zetaZerosWindow (T + 1) := by
        rcases le_or_gt z.im T with h | h
        · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hnear.1, by linarith⟩
        · rcases le_or_gt z.im (T + 1) with h1 | h1
          · exact Or.inr (Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, h, h1⟩)
          · exact Or.inr (Or.inr ⟨hz.1, hz.2.1, hz.2.2.1, h1, by linarith [hnear.2]⟩)
      rcases hx with h | h | h
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        change z ∈ (hfin 0).toFinset
        simpa using h
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        change z ∈ (hfin 1).toFinset
        simpa using h
      · refine ⟨2, Finset.mem_univ _, ?_⟩
        change z ∈ (hfin 2).toFinset
        rw [Set.Finite.mem_toFinset]
        change z ∈ zetaZerosWindow (T - 1 + (2 : ℝ))
        convert h using 1 <;> ring
    exact hrad.trans (by simpa only [abs_sub_comm] using hfar z.im hmem)
  · have hdist : 1 ≤ |z.im - T'| := by
      rcases le_or_gt z.im (T - 1) with h | h
      · have := neg_le_abs (z.im - T')
        linarith
      · have h2 : T + 2 < z.im := lt_of_not_ge (fun h2 => hnear ⟨h, h2⟩)
        have := le_abs_self (z.im - T')
        linarith
    exact hone.trans hdist

/-- LEAF. Contour shift: there is an absolute `C` such that for `x ≥ 2`, `T ≥ 2` at distance
at least `1/(100 log T)` from every ordinate with `|γ| ≤ T + 1`, and `c = 1 + 1/log x`,
the truncated Perron integral of `-ζ'/ζ` equals
`x - ∑_{|γ| ≤ T} m_ρ x^ρ/ρ - log 2π - (1/2) log(1 - x^{-2})` up to `C x log² T / T`.
Residues at `1`, at the zeros, at `0` (`ζ'(0)/ζ(0) = log 2π`) and at `-2, -4, ...`;
horizontal sides bounded by `|ζ'/ζ(σ ± iT)| ≪ log² T`. Davenport ch. 17, p. 108-109.
Unit U-1529. -/
theorem contour_shift : ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    (∀ ρ ∈ zetaZeros (T + 1), 1 / (100 * Real.log T) ≤ |ρ.im - T|) →
    ∀ hfin : (zetaZeros T).Finite,
      ‖perronPsi x (1 + 1 / Real.log x) T -
          ((x : ℂ) - ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
            - Real.log (2 * Real.pi) - (1 / 2 : ℂ) * Real.log (1 - x ^ (-2 : ℤ)))‖ ≤
        C * (x * Real.log T ^ 2 / T) := by
  sorry

/-- LEAF. Truncated explicit formula for `ψ` with an explicit constant: for `x ≥ 2` and
`2 ≤ T ≤ x`, `|ψ(x) - x + ∑_{|γ| ≤ T} m_ρ x^ρ/ρ| ≤ 1000 (x log² x / T + log x)`.
From `perron_psi`, `perron_tail`, `contour_shift`, `good_height`, moving `x` to the nearest
half-integer (cost `≤ log x`) and `T` to a good height (cost `≤ (2 log T + 5) x/T` by
`window_count`). The constant 1000 is generous: Dudek 2016, Funct. Approx. 55, Theorem 1.3,
has `2 x log² x / T` for `x > e^60`, `50 < T < x`; Davenport ch. 17, (9)-(10), p. 109.
Unit U-1529. -/
theorem explicit_formula_zeta {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (hfin : (zetaZeros T).Finite) :
    ‖(Chebyshev.psi x : ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      1000 * (x * Real.log x ^ 2 / T + Real.log x) := by
  sorry

/-- LEAF. Truncated explicit formula for `ψ(x, χ)` under GRH: there is an absolute `C` such
that for every modulus `q`, every character `χ` mod `q`, `x ≥ 2`, `2 ≤ T ≤ x`,
`|ψ(x, χ) - δ_χ x + ∑_{|γ| ≤ T} m_ρ x^ρ/ρ| ≤ C (x log²(qx)/T + √x + log²(qx))`,
`δ_χ = 1` for the trivial character. GRH gives `|ρ| ≥ 1/2`, so the zeros with `|γ| < 1` and
the constant `b(χ)` cost `O(log q)`; an imprimitive `χ` differs from its primitive inducing
character by at most `log q log x`. Davenport ch. 19, (13)-(14), p. 120, and ch. 20, p. 125.
Unit U-1529. -/
theorem explicit_formula_chi_GRH : GRH → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x T : ℝ), 2 ≤ x → 2 ≤ T → T ≤ x →
    ∀ hfin : (LZeros χ T).Finite,
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        C * (x * Real.log (q * x) ^ 2 / T + √x + Real.log (q * x) ^ 2) := by
  sorry

/-! ### Assembly: the GRH bound for `ψ(x, χ)` -/

/-- Under the line hypothesis, each term of the sum over zeros has norm `m √x / |ρ|`. -/
theorem norm_zero_term {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ = √x * ((m : ℝ) / ‖ρ‖) := by
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ,
    ← Real.sqrt_eq_rpow]
  ring

/-- The sum over zeros of `L(s, χ)` up to height `T`, on the critical line, is at most
`√x ∑ m_ρ/|ρ|`. -/
theorem norm_zero_sum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x T : ℝ}
    (hx : 0 < x) (hfin : (LZeros χ T).Finite) (hline : ∀ ρ ∈ LZeros χ T, ρ.re = 1 / 2) :
    ‖∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      √x * ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun ρ hρ => ?_)
  exact norm_zero_term hx (hline ρ ((Set.Finite.mem_toFinset hfin).mp hρ)) _

/-- **GRH bound for `ψ(x, χ)`**: there is an absolute `c` with
`|ψ(x, χ) - δ_χ x| ≤ c √x log²(qx)` for every modulus `q`, character `χ` mod `q`, and
`x ≥ 2`. Davenport ch. 20, p. 125. PROVED from the leaves with `T = x`, zero sorry in this
proof; CONDITIONAL ON GRH and the leaves `explicit_formula_chi_GRH`, `LZeros_finite`,
`LZeros_recip_sum`. -/
theorem psiChi_bound_of_GRH (hG : GRH) : ∃ c : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ c * √x * Real.log (q * x) ^ 2 := by
  obtain ⟨C, hC⟩ := explicit_formula_chi_GRH hG
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  refine ⟨227 + 5 * C', ?_⟩
  intro q _ χ x hx
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hx0 : 0 < x := by linarith
  have hfin := LZeros_finite χ x
  have hline := L_re_eq_half_of_GRH hG χ (T := x)
  have h1 := hC q χ x x hx hx le_rfl hfin
  have h2 := norm_zero_sum_le χ hx0 hfin hline
  have h3 := LZeros_recip_sum χ (by linarith : (1 : ℝ) ≤ x) hfin hline
  set L := Real.log (q * x) with hL
  set S := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  set R := ∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖
  -- elementary facts
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL069 : 0.69 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
    linarith
  have hlogx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsx : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
  have hxL : x * L ^ 2 / x = L ^ 2 := by field_simp
  rw [hxL] at h1
  have hR : R ≤ L * Real.log x + 10 * L + 100 := h3
  have hRL : R ≤ 227 * L ^ 2 := by nlinarith
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun ρ _ => by positivity
  -- triangle inequality
  have htri : ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + S‖ + ‖S‖ := by
    have := norm_sub_le (psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + S) S
    simpa using this
  have hE : C * (L ^ 2 + √x + L ^ 2) ≤ C' * (2 * L ^ 2 + √x) := by
    have : 0 ≤ L ^ 2 + √x + L ^ 2 := by positivity
    nlinarith
  have hL2 : 1 ≤ 2.11 * L ^ 2 := by nlinarith
  have hsxL : √x ≤ 2.11 * √x * L ^ 2 := by nlinarith
  have hLL : L ^ 2 ≤ √x * L ^ 2 := by nlinarith [sq_nonneg L]
  have hSR : √x * R ≤ 227 * √x * L ^ 2 := by nlinarith
  have hfin' : C' * (2 * L ^ 2 + √x) ≤ 5 * C' * √x * L ^ 2 := by nlinarith
  nlinarith

/-- Vacuity: the hypotheses `2 ≤ x`, `2 ≤ T ≤ x` of the explicit formulas hold at
`x = T = 2`, and `x = 5/2` is a non-integer with `x ≥ 2` for `perron_psi`. -/
example : (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2 ∧ (∀ n : ℕ, (n : ℝ) ≠ 5 / 2) := by
  refine ⟨le_rfl, le_rfl, fun n h => ?_⟩
  have h2 : (n : ℝ) * 2 = 5 := by rw [h]; norm_num
  have : n * 2 = 5 := by exact_mod_cast h2
  omega

end LeanLab.DERZ1997.Decomp1529b

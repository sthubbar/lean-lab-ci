/-
Burst S89 burst-20261122 feed1122, split of `explicit_formula_zeta` in Decomp1529b.
Source: Davenport, Multiplicative Number Theory, 3rd ed., ch. 17, (9)-(10), p. 109, and
ch. 15, p. 98, corollary (b); the parent docstring proof sketch: Perron's formula with the
proved arbitrary-x tail bound, contour shift at a good height `U ∈ [T, T + 1]`, transfer of
the zero sum from `U` to `T` through the unit window count, integers by a right limit.
The coefficient 1000 is the parent's; Dudek 2016, Funct. Approx. 55, Theorem 1.3 has 2 for
`x > e^60`.
Leaves:
* `zeta_contour_explicit1122`, HARD: the contour shift to the left at a good height with an
  explicit coefficient 500, including the trivial zeros and `log 2π`.
* the low windows above heights in `[2, e]` are empty by the existing `zetaZeros_eq_empty`.
The unit window count for `T ≥ e` is the existing leaf `window_count` of Decomp1529a.
AI-written Lean code, Claude, 2026-11-22. Binary Goldbach is OPEN.
-/
import LeanLab.DERZ1997.Decomp1529b

namespace LeanLab.DERZ1997.Decomp1529b
open Complex LeanLab.DERZ1997.Decomp1529a
open Real MeasureTheory Set
open Filter Topology
open LeanLab.DERZ1997.Decomp1529b2

/-- LEAF: contour shift of Davenport ch. 17, p. 108-109, displays (9)-(10), at a good height.
For `x ≥ 2` and `2 ≤ T ≤ x` there is a height `U ∈ [T, T + 1]` at which the truncated Perron
integral on `Re s = 1 + 1/log x` equals `x - ∑_{|γ| ≤ U} m_ρ x^ρ/ρ` up to an error at most
`500 (x log² x / T + log x)`. The error collects `log 2π`, the trivial zeros
`-(1/2) log(1 - x^{-2})`, the two horizontal integrals at the good height where
`|ζ'/ζ| ≪ log² U`, and the vanishing far-left edge. Class HARD: an explicit good-height bound
for `ζ'/ζ` and the explicit horizontal integral budget. -/
theorem zeta_contour_explicit1122 {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x) :
    ∃ U ∈ Set.Icc T (T + 1), ∀ hf : (zetaZeros U).Finite,
      ‖perronPsi x (1 + 1 / Real.log x) U -
        ((x : ℂ) - ∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ)‖ ≤
        500 * (x * Real.log x ^ 2 / T + Real.log x) := by
  sorry

/-- Low windows: for `2 ≤ T ≤ e` the zeros with `T < γ ≤ T + 1` carry multiplicity at most 5,
in fact none. Derived from the existing `zetaZeros_eq_empty` of Decomp1529a, no zero below
height 14; Davenport ch. 15, p. 98. -/
theorem zeta_low_window_mass1122 {T : ℝ} (hT : 2 ≤ T) (hTe : T ≤ Real.exp 1)
    (hfin : (zetaZerosWindow T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤ 5 := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hempty : hfin.toFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro ρ hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hfin.mem_toFinset.mp hρ
    have hmem : ρ ∈ zetaZeros (T + 1) :=
      ⟨hz, hr0, hr1, by rw [abs_of_pos (by linarith)]; exact hhi⟩
    rw [zetaZeros_eq_empty (by linarith)] at hmem
    exact hmem
  rw [hempty, Finset.sum_empty]
  norm_num

/-- Unit window mass for every `T ≥ 2`, from `window_count` above `e` and the low leaf. -/
theorem zeta_window_mass1122 {T : ℝ} (hT : 2 ≤ T) (hfin : (zetaZerosWindow T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤ 2 * Real.log T + 5 := by
  rcases le_total (Real.exp 1) T with he | he
  · exact window_count he hfin
  · have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    linarith [zeta_low_window_mass1122 hT he hfin]

/-- The explicit formula at noninteger `x` with coefficient 1000, from the Perron bound,
`zeta_contour_explicit1122` and the height transfer. Davenport ch. 17, p. 105-109. -/
theorem explicit_formula_zeta_noninteger1122 {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T)
    (hTx : T ≤ x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hfin : (zetaZeros T).Finite) :
    ‖(Chebyshev.psi x : ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      1000 * (x * Real.log x ^ 2 / T + Real.log x) := by
  classical
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  let M : ℝ := x * Real.log x ^ 2 / T
  let L : ℝ := Real.log x
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlog : 1 / 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  obtain ⟨U, hU, hco⟩ := zeta_contour_explicit1122 hx hT hTx
  let hfU := zetaZeros_finite U
  let c : ℝ := 1 + 1 / Real.log x
  let ZU : ℂ := ∑ ρ ∈ hfU.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let ZT : ℂ := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  change ‖(Chebyshev.psi x : ℂ) - x + ZT‖ ≤ 1000 * (M + L)
  have hper : ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ ≤ 432 * M + 32 * L := by
    have hc : 1 < c := by dsimp [c]; linarith [one_div_pos.mpr (by linarith : 0 < Real.log x)]
    have hp' := (perron_psi hx hxn hc (show 0 < U by linarith [hU.1])).trans
      (perron_tail_arbitrary266 hx (hT.trans hU.1))
    have hratio : x * Real.log x ^ 2 / U ≤ M :=
      div_le_div_of_nonneg_left (by positivity) hT0 hU.1
    change ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ ≤ _ at hp'
    exact hp'.trans (by dsimp [L]; linarith)
  have hfW : (zetaZerosWindow T).Finite := by
    apply (zetaZeros_finite (T + 1)).subset
    intro ρ hρ
    obtain ⟨hz, hr0, hr1, hlo, hhi⟩ := hρ
    exact ⟨hz, hr0, hr1, by rw [abs_of_pos (by linarith : 0 < ρ.im)]; exact hhi⟩
  have hwindow := zeta_window_mass1122 hT hfW
  have htransfer := zeta_height_transfer266 (by linarith : 1 ≤ x) hT0 hU.1 hU.2
    hfin hfU hfW hwindow
  have hlogTx : Real.log T ≤ Real.log x := Real.log_le_log hT0 hTx
  have hdiff : ‖ZU - ZT‖ ≤ 48 * M := by
    refine htransfer.trans ?_
    have hb : 2 * (2 * Real.log T + 5) ≤ 48 * Real.log x ^ 2 := by nlinarith
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hx0.le) hT0.le
    dsimp [M]
    calc 2 * (2 * Real.log T + 5) * x / T ≤ 48 * Real.log x ^ 2 * x / T := hh
      _ = 48 * (x * Real.log x ^ 2 / T) := by ring
  have hco' : ‖perronPsi x c U - ((x : ℂ) - ZU)‖ ≤ 500 * (M + L) := hco hfU
  have htri : ‖(Chebyshev.psi x : ℂ) - x + ZT‖ ≤
      ‖(Chebyshev.psi x : ℂ) - perronPsi x c U‖ +
      ‖perronPsi x c U - ((x : ℂ) - ZU)‖ + ‖ZU - ZT‖ := by
    have he : (Chebyshev.psi x : ℂ) - x + ZT =
        ((Chebyshev.psi x : ℂ) - perronPsi x c U) +
        (perronPsi x c U - ((x : ℂ) - ZU)) - (ZU - ZT) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  linarith

/-- Split of `explicit_formula_zeta`, statement copied verbatim. Noninteger `x` is
`explicit_formula_zeta_noninteger1122`; an integer `x` is reached by a right limit, since
`ψ` is constant on `[N, N + 1)` and both sides are continuous in `x` there. -/
theorem explicit_formula_zeta_split {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    (hfin : (zetaZeros T).Finite) :
    ‖(Chebyshev.psi x : ℂ) - x + ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      1000 * (x * Real.log x ^ 2 / T + Real.log x) := by
  by_cases hnat : ∃ N : ℕ, (N : ℝ) = x
  · obtain ⟨N, rfl⟩ := hnat
    have hlocal : ∀ y : ℝ, (N : ℝ) < y → y < (N : ℝ) + 1 →
        ‖(Chebyshev.psi y : ℂ) - y + ∑ ρ ∈ hfin.toFinset,
          (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
          1000 * (y * Real.log y ^ 2 / T + Real.log y) := by
      intro y hy hy1
      apply explicit_formula_zeta_noninteger1122 (by linarith) hT (by linarith) _ hfin
      intro n hn
      have h0 : N < n := by exact_mod_cast (show (N : ℝ) < n by simpa only [hn] using hy)
      have h1 : n < N + 1 := by
        exact_mod_cast (show (n : ℝ) < (N : ℝ) + 1 by simpa only [hn] using hy1)
      omega
    have hN0 : (0 : ℝ) < N := by linarith
    have hpow (ρ : ℂ) : ContinuousAt (fun y : ℝ => (y : ℂ) ^ ρ) (N : ℝ) :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hN0)).comp
        Complex.continuous_ofReal.continuousAt
    have hsum : ContinuousAt (fun y : ℝ => ∑ ρ ∈ hfin.toFinset,
        (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ) (N : ℝ) := by
      apply tendsto_finsetSum hfin.toFinset
      intro ρ hρ
      exact (continuousAt_const.mul (hpow ρ)).div_const ρ
    have hleft : ContinuousAt (fun y : ℝ =>
        ‖(Chebyshev.psi N : ℂ) - y + ∑ ρ ∈ hfin.toFinset,
          (zetaMult ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖) (N : ℝ) :=
      ((continuousAt_const.sub Complex.continuous_ofReal.continuousAt).add hsum).norm
    have hright : ContinuousAt (fun y : ℝ =>
        1000 * (y * Real.log y ^ 2 / T + Real.log y)) (N : ℝ) := by
      fun_prop (disch := exact hN0.ne')
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (N : ℝ)) (hleft.tendsto.mono_left inf_le_left)
      (hright.tendsto.mono_left inf_le_left)
    filter_upwards [Ioo_mem_nhdsGT (show (N : ℝ) < N + 1 by linarith)] with y hy
    have hfloor : ⌊y⌋₊ = N :=
      (Nat.floor_eq_iff (by linarith [hy.1, Nat.cast_nonneg (α := ℝ) N])).mpr ⟨hy.1.le, hy.2⟩
    have hpsi : Chebyshev.psi y = Chebyshev.psi N := by
      rw [Chebyshev.psi_eq_psi_coe_floor, hfloor]
    simpa only [hpsi] using hlocal y hy.1 hy.2
  · apply explicit_formula_zeta_noninteger1122 hx hT hTx _ hfin
    intro n hn
    exact hnat ⟨n, hn⟩

end LeanLab.DERZ1997.Decomp1529b

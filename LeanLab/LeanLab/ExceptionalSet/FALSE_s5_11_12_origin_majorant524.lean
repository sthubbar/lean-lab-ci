import LeanLab.ExceptionalSet.SPLIT_leaf_majorant_small_width524

/-!
Counterexamples to the two origin-interval LEAFs of
`LeanLab.ExceptionalSet.SPLIT_leaf_majorant_small_width524`, units S5-11 and S5-12 of
CLOUD S5 burst-20261127.

Both LEAFs ask for a pure cosine polynomial `P x = c₀ + ∑_{1 ≤ h ≤ H} A h cos (2 π h x)`
dominating the indicator of `[0, w)` mod one, with `c₀ ≤ w + 4 / (H + 1)`. A pure cosine
polynomial is even, so it also dominates the indicator of `(-w, 0]` mod one, and it is
nonnegative. Its mean over one period is `c₀`, hence `c₀ ≥ 2 w` in the limit, which exceeds
`w + 4 / (H + 1)` once `H + 1 > 4 / w`. The proof below uses the exact discrete mean over the
`N`-th roots of unity, `N > H`, in place of the integral: `N c₀ = ∑_{j < N} P (j / N)`, and at
least `2 K + 1` of the sample points lie in `(-w, w)` mod one.

Concrete instances: `w = 1 / 3`, `H = 16`, sampled at `N = 17` with `K = 5`, refutes the wide
band; `w = 1 / 6`, `H = 40`, sampled at `N = 41` with `K = 6`, refutes the narrow band.
In both the hypotheses of the LEAF hold.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.Decomp524a.FalseS5

open Real Finset

/-- Orthogonality over the `N`-th roots of unity: for `0 < h < N` the sum of
`cos (2 π h j / N)` over `j < N` vanishes. -/
theorem sum_cos_range_eq_zero (N h : ℕ) (h0 : 0 < h) (hhN : h < N) :
    ∑ j ∈ range N, cos (2 * π * ((h : ℝ) * ((j : ℝ) / N))) = 0 := by
  have hN : (N : ℝ) ≠ 0 := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hhN
    exact_mod_cast this.ne'
  set θ : ℝ := 2 * π * h / N with hθ
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζ
  have hζN : ζ ^ N = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    refine Complex.exp_eq_one_iff.mpr ⟨h, ?_⟩
    rw [hθ]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    push_cast
    field_simp
  have hζ1 : ζ ≠ 1 := by
    intro e
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e
    have him := congrArg Complex.im hn
    simp at him
    -- him : θ = n * (2 * π)
    have hpi : 0 < π := Real.pi_pos
    have hq : (h : ℝ) / N = n := by
      have : 2 * π * h / N = n * (2 * π) := him
      field_simp at this ⊢
      nlinarith [this]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hhN)
    have hpos : (0 : ℝ) < (h : ℝ) / N := by
      apply div_pos _ hNpos
      exact_mod_cast h0
    have hlt : (h : ℝ) / N < 1 := by
      rw [div_lt_one hNpos]
      exact_mod_cast hhN
    rw [hq] at hpos hlt
    have h1 : (0 : ℤ) < n := by exact_mod_cast hpos
    have h2 : n < (1 : ℤ) := by exact_mod_cast hlt
    omega
  have hgeom : ∑ j ∈ range N, ζ ^ j = 0 := by
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]
  have hre := congrArg Complex.re hgeom
  rw [Complex.re_sum] at hre
  simp only [Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hζ, ← Complex.exp_nat_mul,
    show (j : ℂ) * ((θ : ℂ) * Complex.I) = ((j * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, hθ]
  congr 1
  field_simp

/-- The discrete mean of a cosine polynomial of degree `H` over `N > H` equally spaced
points is its constant term. -/
theorem sum_cosPoly_range (N H : ℕ) (hHN : H < N) (c₀ : ℝ) (A : ℕ → ℝ) :
    ∑ j ∈ range N, (c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * ((j : ℝ) / N))))
      = N * c₀ := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_comm]
  have : ∑ h ∈ Icc 1 H, ∑ j ∈ range N, A h * cos (2 * π * ((h : ℝ) * ((j : ℝ) / N))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h hh
    rw [Finset.mem_Icc] at hh
    rw [← Finset.mul_sum, sum_cos_range_eq_zero N h (by omega) (by omega), mul_zero]
  rw [this, add_zero]

/-- A pure cosine term takes the same value at `j / N` and at `(N - j) / N`. -/
theorem cos_reflect (N h j : ℕ) (hN : 0 < N) (hj : j ≤ N) :
    cos (2 * π * ((h : ℝ) * ((j : ℝ) / N)))
      = cos (2 * π * ((h : ℝ) * (((N - j : ℕ) : ℝ) / N))) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_sub hj]
  have : 2 * π * ((h : ℝ) * (((N : ℝ) - j) / N))
      = (h : ℕ) * (2 * π) - 2 * π * ((h : ℝ) * ((j : ℝ) / N)) := by
    field_simp
  rw [this, Real.cos_nat_mul_two_pi_sub]

/-- The general obstruction: if `N > H`, `2 K < N`, `K < w N` and
`w + 4 / (H + 1) < (2 K + 1) / N`, no cosine polynomial of degree `H` with constant term at
most `w + 4 / (H + 1)` dominates the indicator of `[0, w)` mod one. The coefficient bound
plays no role. -/
theorem no_cos_majorant (w : ℝ) (H N K : ℕ) (hHN : H < N) (h2K : 2 * K < N)
    (hK : (K : ℝ) < w * N) (hbad : w + 4 / ((H : ℝ) + 1) < (2 * K + 1) / N) :
    ¬ ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)) := by
  rintro ⟨c₀, A, hc₀, -, hdom⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set P : ℕ → ℝ := fun j =>
    c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * ((j : ℝ) / N))) with hP
  have hnn : ∀ j, 0 ≤ P j := by
    intro j
    have := hdom ((j : ℝ) / N)
    refine le_trans ?_ this
    split_ifs <;> norm_num
  have hone : ∀ k, k ≤ K → 1 ≤ P k := by
    intro k hk
    have hkr : (k : ℝ) ≤ K := by exact_mod_cast hk
    have hkN : k < N := by omega
    have hkNr : (k : ℝ) < N := by exact_mod_cast hkN
    have h0 : 0 ≤ (k : ℝ) / N := by positivity
    have h1 : (k : ℝ) / N < 1 := by rw [div_lt_one hNr]; exact hkNr
    have hfr : Int.fract ((k : ℝ) / N) = (k : ℝ) / N := Int.fract_eq_self.mpr ⟨h0, h1⟩
    have hw : (k : ℝ) / N < w := by
      rw [div_lt_iff₀ hNr]
      linarith
    have := hdom ((k : ℝ) / N)
    rw [hfr, if_pos ⟨h0, hw⟩] at this
    exact this
  have hone' : ∀ j ∈ Ico (N - K) N, 1 ≤ P j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hrefl : P j = P (N - j) := by
      simp only [hP]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro h _
      rw [cos_reflect N h j hNpos hj.2.le]
    rw [hrefl]
    exact hone (N - j) (by omega)
  have hsum := sum_cosPoly_range N H hHN c₀ A
  have hsplit : ∑ j ∈ range (N - K), P j + ∑ j ∈ Ico (N - K) N, P j = ∑ j ∈ range N, P j :=
    Finset.sum_range_add_sum_Ico P (by omega)
  have hA : ((K : ℝ) + 1) ≤ ∑ j ∈ range (N - K), P j := by
    calc ((K : ℝ) + 1) = ∑ j ∈ range (K + 1), (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ range (K + 1), P j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          rw [Finset.mem_range] at hj
          exact hone j (by omega)
      _ ≤ ∑ j ∈ range (N - K), P j := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hnn j)
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
  have hB : (K : ℝ) ≤ ∑ j ∈ Ico (N - K) N, P j := by
    calc (K : ℝ) = ∑ j ∈ Ico (N - K) N, (1 : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          congr 1
          omega
      _ ≤ ∑ j ∈ Ico (N - K) N, P j := Finset.sum_le_sum hone'
  have htot : (2 * (K : ℝ) + 1) ≤ N * c₀ := by
    rw [← hsum]
    have : ∑ j ∈ range N, P j = ∑ j ∈ range N,
        (c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * ((j : ℝ) / N)))) := rfl
    linarith
  have hc : (2 * (K : ℝ) + 1) / N ≤ c₀ := by
    rw [div_le_iff₀ hNr]
    linarith
  linarith

/-- S5-12 is FALSE: the wide band LEAF fails at `w = 1 / 3`, `H = 16`. -/
theorem leaf_majorant_origin_wide524_false :
    ¬ (∀ (w : ℝ) (H : ℕ), 0 < w → 1 / 6 < w → w ≤ 1 / 3 → 4 ≤ H →
      w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) := by
  intro hall
  have hcos : cos (π * (1 / 3 : ℝ)) = 1 / 2 := by
    rw [show π * (1 / 3 : ℝ) = π / 3 by ring, Real.cos_pi_div_three]
  have hH : ((16 : ℕ) : ℝ) = 16 := by norm_num
  refine no_cos_majorant (1 / 3) 16 17 5 (by norm_num) (by norm_num) ?_ ?_
    (hall (1 / 3) 16 (by norm_num) (by norm_num) le_rfl (by norm_num) ?_ ?_)
  · norm_num
  · rw [hH]; norm_num
  · rw [hH]; norm_num
  · rw [hH, hcos]; norm_num

/-- S5-11 is FALSE: the narrow band LEAF fails at `w = 1 / 6`, `H = 40`. -/
theorem leaf_majorant_origin_narrow524_false :
    ¬ (∀ (w : ℝ) (H : ℕ), 0 < w → w ≤ 1 / 6 → 4 ≤ H →
      w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) := by
  intro hall
  have hcos : cos (π * (1 / 6 : ℝ)) ≤ 1 := Real.cos_le_one _
  have hH : ((40 : ℕ) : ℝ) = 40 := by norm_num
  refine no_cos_majorant (1 / 6) 40 41 6 (by norm_num) (by norm_num) ?_ ?_
    (hall (1 / 6) 40 (by norm_num) le_rfl (by norm_num) ?_ ?_)
  · norm_num
  · rw [hH]; norm_num
  · rw [hH]; norm_num
  · rw [hH]
    have hpos : (0 : ℝ) < 1 / 6 + 4 / (40 + 1) := by norm_num
    calc (1 / 6 + 4 / ((40 : ℝ) + 1)) * (1 + cos (π * (1 / 6)))
        ≤ (1 / 6 + 4 / ((40 : ℝ) + 1)) * 2 := by
          apply mul_le_mul_of_nonneg_left _ hpos.le; linarith
      _ < 1 := by norm_num

/-- The negations are of the LEAF statements exactly. -/
example : ¬ type_of% @LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_origin_wide524 :=
  leaf_majorant_origin_wide524_false

example : ¬ type_of% @LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_origin_narrow524 :=
  leaf_majorant_origin_narrow524_false

end LeanLab.ExceptionalSet.Decomp524a.FalseS5

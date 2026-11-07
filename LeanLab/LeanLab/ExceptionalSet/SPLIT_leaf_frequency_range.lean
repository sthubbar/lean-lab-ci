import LeanLab.ExceptionalSet.Decomp446c

/-!
Split of the frequency range step of the distant phase input, page 366 of the source.

The target `leaf_frequency_range` is a pure scaling statement about the scale
`F γ N = exp ((log N) ^ γ)` at the two index sizes `2 * (N / 2)` and `N / 2`.
The scale is increasing in `γ` and in the index, so both conclusions follow from a
comparison of the exponents after taking logarithms: the lower conclusion needs
`(1 - 3 δ) * (log N) ^ γ ≤ (1 - 2 δ) * (log (2 * (N / 2))) ^ γ`, the upper conclusion
needs `log 2 + 6 δ * (log N) ^ γ ≤ 12 δ * (log (N / 2)) ^ γ`.  Both comparisons
hold once `log N` is large enough, because `γ > 1` makes the gap between
`(log N) ^ γ` and `(log (N / 2)) ^ γ` grow without bound, while the loss in
doubling the coefficient is only the fixed ratio `(1 - 2 δ) / (1 - 3 δ) < 1`
respectively the fixed `δ / 2`.  The elementary input to that comparison is the
tangent line bound `1 - r * t ≤ (1 - t) ^ r` for `r ≥ 1`, which transfers
`(log N - c) ^ γ ≥ (log N) ^ γ - γ * c * (log N) ^ (γ - 1)`.

Nothing here concludes anything about an exponential sum.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF. The tangent line bound at `1` for a real power: for `1 ≤ r` and `0 ≤ t ≤ 1` the
power `(1 - t) ^ r` lies above the line `1 - r * t`.  This is the single elementary
estimate behind both log-power gap leaves below; it is false for `r < 1` at `t = 1`. -/
theorem leaf_one_sub_rpow_lower (r t : ℝ) (hr : 1 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - r * t ≤ (1 - t) ^ r := by
  have h := one_add_mul_self_le_rpow_one_add (s := -t) (p := r) (by linarith) hr
  have hb : (1 : ℝ) + -t = 1 - t := by ring
  have hrw : 1 + r * -t = 1 - r * t := by ring
  rw [hb, hrw] at h
  exact h

/-- Auxiliary algebra for `leaf_log_gap_lower`: if `1 ≤ L` and `(1 - 2 δ) γ log 2 ≤ δ L`, the
tangent line bound turns `L ^ γ` into `(L - log 2) ^ γ` at a cost of `δ` of `L ^ γ`. -/
private lemma rpow_gap_lower_core (γ δ L : ℝ) (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ12 : δ ≤ 1 / 12)
    (hL : 1 ≤ L) (hkey : (1 - 2 * δ) * γ * Real.log 2 ≤ δ * L) :
    (1 - 3 * δ) * L ^ γ ≤ (1 - 2 * δ) * (L - Real.log 2) ^ γ := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2le : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have ht1 : Real.log 2 / L ≤ 1 := by
    rw [div_le_one hLpos]
    exact hlog2le.trans hL
  have hApos : (0 : ℝ) < L ^ γ := Real.rpow_pos_of_pos hLpos γ
  have hBnn : (0 : ℝ) ≤ L ^ (γ - 1) := Real.rpow_nonneg hLpos.le _
  have hpow : L ^ γ = L * L ^ (γ - 1) := by
    have h := Real.rpow_add hLpos 1 (γ - 1)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (γ - 1) = γ by ring] at h
    exact h
  have hdiv : L ^ (γ - 1) = L ^ γ / L := by
    rw [Real.rpow_sub hLpos γ 1, Real.rpow_one]
  have hsplit : L ^ γ * (1 - γ * (Real.log 2 / L)) = L ^ γ - γ * Real.log 2 * L ^ (γ - 1) := by
    rw [hdiv]
    field_simp
  have hbern : 1 - γ * (Real.log 2 / L) ≤ (1 - Real.log 2 / L) ^ γ :=
    leaf_one_sub_rpow_lower γ (Real.log 2 / L) hγ (div_nonneg hlog2pos.le hLpos.le) ht1
  have hstep : L ^ γ * (1 - γ * (Real.log 2 / L)) ≤ (L - Real.log 2) ^ γ := by
    have h1m : (0 : ℝ) ≤ 1 - Real.log 2 / L := by linarith
    have hmul : L ^ γ * (1 - Real.log 2 / L) ^ γ = (L * (1 - Real.log 2 / L)) ^ γ :=
      (Real.mul_rpow hLpos.le h1m).symm
    have hbase : L * (1 - Real.log 2 / L) = L - Real.log 2 := by field_simp
    rw [← hbase, ← hmul]
    exact mul_le_mul_of_nonneg_left hbern hApos.le
  have hkeyB : (1 - 2 * δ) * γ * Real.log 2 * L ^ (γ - 1) ≤ δ * L ^ γ := by
    have h := mul_le_mul_of_nonneg_right hkey hBnn
    rwa [mul_assoc δ L (L ^ (γ - 1)), ← hpow] at h
  have h1 : L ^ γ - γ * Real.log 2 * L ^ (γ - 1) ≤ (L - Real.log 2) ^ γ := by
    rw [← hsplit]
    exact hstep
  have hc : (0 : ℝ) ≤ 1 - 2 * δ := by linarith
  have h2 : (1 - 2 * δ) * (L ^ γ - γ * Real.log 2 * L ^ (γ - 1))
      ≤ (1 - 2 * δ) * (L - Real.log 2) ^ γ := mul_le_mul_of_nonneg_left h1 hc
  have h3 : (1 - 3 * δ) * L ^ γ
      ≤ (1 - 2 * δ) * (L ^ γ - γ * Real.log 2 * L ^ (γ - 1)) := by
    have hexp : (1 - 2 * δ) * (L ^ γ - γ * Real.log 2 * L ^ (γ - 1))
        = (1 - 2 * δ) * L ^ γ - (1 - 2 * δ) * γ * Real.log 2 * L ^ (γ - 1) := by ring
    have hsh : (1 - 3 * δ) * L ^ γ = (1 - 2 * δ) * L ^ γ - δ * L ^ γ := by ring
    rw [hexp, hsh]
    exact sub_le_sub_left hkeyB ((1 - 2 * δ) * L ^ γ)
  exact le_trans h3 h2

/-- LEAF. Lower log-power gap.  Eventually the log-power at the doubled half index, scaled
by `1 - 2 δ`, dominates the log-power at `N` scaled by `1 - 3 δ`.  This is the estimate
that puts the lower threshold `F γ N ^ (3 δ - 1)` above `F γ (2 * (N / 2)) ^ (-(1 - 2 δ))`:
the floor in `N / 2` costs only a bounded change of the logarithm, the exponent gap
`- (1 - 3 δ) + (1 - 2 δ) = - δ` costs a factor `δ` of `(log N) ^ γ`, and `γ > 1` makes
`(log N) ^ γ` grow faster than `(log N) ^ (γ - 1)`. -/
theorem leaf_log_gap_lower (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 - 3 * δ) * Real.log N ^ γ ≤
        (1 - 2 * δ) * Real.log (2 * ((N / 2 : ℕ) : ℝ)) ^ γ := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      max ((1 - 2 * δ) * γ * Real.log 2 / δ) 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max ((1 - 2 * δ) * γ * Real.log 2 / δ) 1))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine Filter.eventually_atTop.mpr ⟨max N₀ 2, fun N hN => ?_⟩
  have hgb := hN₀ N (le_trans (le_max_left _ _) hN)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hlog2le : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hL1 : 1 ≤ Real.log N := (le_max_right _ _).trans hgb
  have hkey : (1 - 2 * δ) * γ * Real.log 2 ≤ δ * Real.log N := by
    have hC : (1 - 2 * δ) * γ * Real.log 2 / δ ≤ Real.log N := (le_max_left _ _).trans hgb
    have hmul : ((1 - 2 * δ) * γ * Real.log 2 / δ) * δ = (1 - 2 * δ) * γ * Real.log 2 := by
      field_simp
    rw [← hmul]
    have h := mul_le_mul_of_nonneg_right hC hδ.le
    rwa [mul_comm (Real.log N) δ] at h
  have hδ12 : δ ≤ 1 / 12 := le_of_lt (lt_of_lt_of_le hδsmall (min_le_right _ _))
  have hcore := rpow_gap_lower_core γ δ (Real.log N) h1.le hδ hδ12 hL1 hkey
  have harg : (0 : ℝ) ≤ Real.log N - Real.log 2 := by linarith
  have hmono : Real.log N - Real.log 2 ≤ Real.log (2 * ((N / 2 : ℕ) : ℝ)) := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hdiv : N - 1 ≤ 2 * (N / 2) := by omega
    have hcast1 : ((N - 1 : ℕ) : ℝ) ≤ ((2 * (N / 2) : ℕ) : ℝ) := by exact_mod_cast hdiv
    have hcast2 : ((2 * (N / 2) : ℕ) : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    rw [hcast2, hsub] at hcast1
    have hlogle := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ) - 1) hcast1
    have hhalf : (N : ℝ) / 2 ≤ (N : ℝ) - 1 := by linarith
    have hlogN2 := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) / 2) hhalf
    have hlogdiv : Real.log ((N : ℝ) / 2) = Real.log N - Real.log 2 :=
      Real.log_div (by positivity) (by norm_num)
    rw [hlogdiv] at hlogN2
    linarith
  have hγpos : (0 : ℝ) ≤ γ := by linarith
  have hrpow := Real.rpow_le_rpow harg hmono hγpos
  have hc : (0 : ℝ) ≤ 1 - 2 * δ := by linarith
  exact le_trans hcore (mul_le_mul_of_nonneg_left hrpow hc)

/-- Auxiliary algebra for `leaf_log_gap_upper`: if `L - (log 2 + 1) ≤ L'`, `4 γ (log 2 + 1) ≤ L`
and `log 2 ≤ 3 δ L ^ γ`, then `6 δ L ^ γ + log 2 ≤ 12 δ L' ^ γ`. -/
private lemma rpow_gap_upper_core (γ δ L L' : ℝ) (hγ : 1 ≤ γ) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hLL' : L - (Real.log 2 + 1) ≤ L')
    (hkey1 : 2 * γ * (Real.log 2 + 1) ≤ L / 2)
    (hkey2 : Real.log 2 ≤ 3 * δ * L ^ γ) :
    6 * δ * L ^ γ + Real.log 2 ≤ 12 * δ * L' ^ γ := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2le : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hcpos : (0 : ℝ) < Real.log 2 + 1 := by linarith
  have hcL : Real.log 2 + 1 ≤ L := by
    have h2c : (0 : ℝ) ≤ 2 * (Real.log 2 + 1) := by linarith
    have h4 : 2 * (Real.log 2 + 1) ≤ 2 * γ * (Real.log 2 + 1) := by
      calc 2 * (Real.log 2 + 1) = 1 * (2 * (Real.log 2 + 1)) := by ring
        _ ≤ γ * (2 * (Real.log 2 + 1)) := mul_le_mul_of_nonneg_right hγ h2c
        _ = 2 * γ * (Real.log 2 + 1) := by ring
    linarith [hkey1]
  have ht1 : (Real.log 2 + 1) / L ≤ 1 := by
    rw [div_le_one hLpos]
    exact hcL
  have hApos : (0 : ℝ) < L ^ γ := Real.rpow_pos_of_pos hLpos γ
  have hBnn : (0 : ℝ) ≤ L ^ (γ - 1) := Real.rpow_nonneg hLpos.le _
  have hpow : L ^ γ = L * L ^ (γ - 1) := by
    have h := Real.rpow_add hLpos 1 (γ - 1)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (γ - 1) = γ by ring] at h
    exact h
  have hdiv : L ^ (γ - 1) = L ^ γ / L := by
    rw [Real.rpow_sub hLpos γ 1, Real.rpow_one]
  have hsplit : L ^ γ * (1 - γ * ((Real.log 2 + 1) / L))
      = L ^ γ - γ * (Real.log 2 + 1) * L ^ (γ - 1) := by
    rw [hdiv]
    field_simp
  have hstep : L ^ γ * (1 - γ * ((Real.log 2 + 1) / L)) ≤ (L - (Real.log 2 + 1)) ^ γ := by
    have h1m : (0 : ℝ) ≤ 1 - (Real.log 2 + 1) / L := by linarith
    have hmul : L ^ γ * (1 - (Real.log 2 + 1) / L) ^ γ = (L * (1 - (Real.log 2 + 1) / L)) ^ γ :=
      (Real.mul_rpow hLpos.le h1m).symm
    have hbase : L * (1 - (Real.log 2 + 1) / L) = L - (Real.log 2 + 1) := by field_simp
    have hbern : 1 - γ * ((Real.log 2 + 1) / L) ≤ (1 - (Real.log 2 + 1) / L) ^ γ :=
      leaf_one_sub_rpow_lower γ ((Real.log 2 + 1) / L) hγ (div_nonneg hcpos.le hLpos.le) ht1
    rw [← hbase, ← hmul]
    exact mul_le_mul_of_nonneg_left hbern hApos.le
  have hbase_nn : (0 : ℝ) ≤ L - (Real.log 2 + 1) := by linarith
  have hstep2 : L ^ γ - γ * (Real.log 2 + 1) * L ^ (γ - 1) ≤ L' ^ γ := by
    rw [← hsplit]
    exact le_trans hstep (Real.rpow_le_rpow hbase_nn hLL' (by linarith))
  have h12pos : (0 : ℝ) ≤ 12 * δ := by linarith
  have h12 : 12 * δ * (L ^ γ - γ * (Real.log 2 + 1) * L ^ (γ - 1)) ≤ 12 * δ * L' ^ γ :=
    mul_le_mul_of_nonneg_left hstep2 h12pos
  have hBmult : 2 * γ * (Real.log 2 + 1) * L ^ (γ - 1) ≤ L ^ γ / 2 := by
    have h := mul_le_mul_of_nonneg_right hkey1 hBnn
    have h2 : (L / 2) * L ^ (γ - 1) = L ^ γ / 2 := by
      calc (L / 2) * L ^ (γ - 1) = L * L ^ (γ - 1) / 2 := by ring
        _ = L ^ γ / 2 := by rw [← hpow]
    exact le_trans h (le_of_eq h2)
  have hk1 : (0 : ℝ) ≤ 6 * δ := by linarith
  have hkeyB : 12 * δ * γ * (Real.log 2 + 1) * L ^ (γ - 1) ≤ 3 * δ * L ^ γ := by
    have h := mul_le_mul_of_nonneg_left hBmult hk1
    calc 12 * δ * γ * (Real.log 2 + 1) * L ^ (γ - 1)
        = 6 * δ * (2 * γ * (Real.log 2 + 1) * L ^ (γ - 1)) := by ring
      _ ≤ 6 * δ * (L ^ γ / 2) := h
      _ = 3 * δ * L ^ γ := by ring
  have hlog : 6 * δ * L ^ γ + Real.log 2 ≤ 9 * δ * L ^ γ := by
    have h := add_le_add_left hkey2 (6 * δ * L ^ γ)
    have he : 3 * δ * L ^ γ + 6 * δ * L ^ γ = 9 * δ * L ^ γ := by ring
    rw [he] at h
    simpa [add_comm] using h
  have hnonneg : (0 : ℝ) ≤ 3 * δ * L ^ γ - 12 * δ * γ * (Real.log 2 + 1) * L ^ (γ - 1) :=
    sub_nonneg.2 hkeyB
  have hfin : 6 * δ * L ^ γ + Real.log 2
      ≤ 12 * δ * (L ^ γ - γ * (Real.log 2 + 1) * L ^ (γ - 1)) := by
    have hexp : 12 * δ * (L ^ γ - γ * (Real.log 2 + 1) * L ^ (γ - 1))
        = 9 * δ * L ^ γ + (3 * δ * L ^ γ - 12 * δ * γ * (Real.log 2 + 1) * L ^ (γ - 1)) := by
      ring
    rw [hexp]
    exact hlog.trans (le_add_of_nonneg_right hnonneg)
  exact le_trans hfin h12

/-- LEAF. Upper log-power gap.  Eventually the log-power at `N / 2`, scaled by `12 δ`,
dominates `log 2 + 6 δ * (log N) ^ γ`.  This is the estimate that absorbs the factor `2`
of the hypothesis `|t| ≤ 2 * F γ N ^ (6 δ)` into the doubling of the exponent at the
half index. -/
theorem leaf_log_gap_upper (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      6 * δ * Real.log N ^ γ + Real.log 2 ≤
        12 * δ * Real.log (((N / 2 : ℕ)) : ℝ) ^ γ := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      max (max (4 * γ * (Real.log 2 + 1)) (Real.log 2 / (3 * δ))) 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max (max (4 * γ * (Real.log 2 + 1)) (Real.log 2 / (3 * δ))) 1))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine Filter.eventually_atTop.mpr ⟨max N₀ 4, fun N hN => ?_⟩
  have hgb := hN₀ N (le_trans (le_max_left _ _) hN)
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) hN
  have hL1 : 1 ≤ Real.log N := (le_max_right _ _).trans hgb
  have hlog2le : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have ha : 4 * γ * (Real.log 2 + 1) ≤ Real.log N :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hgb)
  have hb : Real.log 2 / (3 * δ) ≤ Real.log N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hgb)
  have hkey1 : 2 * γ * (Real.log 2 + 1) ≤ Real.log N / 2 := by linarith
  have h3δ : (0 : ℝ) < 3 * δ := by linarith
  have hkey2 : Real.log 2 ≤ 3 * δ * Real.log N ^ γ := by
    have hmul : 3 * δ * (Real.log 2 / (3 * δ)) = Real.log 2 := by
      field_simp
    have hlog : Real.log 2 ≤ 3 * δ * Real.log N := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left hb h3δ.le
    have h2 : 3 * δ * Real.log N ≤ 3 * δ * Real.log N ^ γ :=
      mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_one_le hL1 h1.le) h3δ.le
    exact hlog.trans h2
  have hmono : Real.log N - (Real.log 2 + 1) ≤ Real.log (((N / 2 : ℕ)) : ℝ) := by
    have hquarter : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
      have h : N ≤ 4 * (N / 2) := by omega
      have hc : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hlogle := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) / 4) hquarter
    have hlogdiv : Real.log ((N : ℝ) / 4) = Real.log N - Real.log 4 :=
      Real.log_div (by positivity) (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlogdiv, hlog4] at hlogle
    linarith
  exact rpow_gap_upper_core γ δ (Real.log N) (Real.log (((N / 2 : ℕ)) : ℝ)) h1.le hδ hL1 hmono hkey1 hkey2

/-- LEAF. Power identity for the scale `F`: raising `F γ x` to a real power multiplies the
log-power by that power, `F γ x ^ c = exp (c * (log x) ^ γ)`.  This is the identity that
carries the two log-power gap estimates over to the statement in terms of `F`. -/
theorem leaf_F_rpow_exp (γ x c : ℝ) :
    F γ x ^ c = Real.exp (c * Real.log x ^ γ) := by
  rw [show F γ x = Real.exp (Real.log x ^ γ) from rfl]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]

/-- Assembly of the frequency range step from the four leaves: take `N₀` beyond both
eventual thresholds, then the lower conclusion is the first gap leaf followed by the
strict lower hypothesis, and the upper conclusion is the upper hypothesis followed by
the factor `2 = exp (log 2)` folded into the second gap leaf. -/
theorem leaf_frequency_range_split (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
      F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
        F γ (2 * (N / 2 : ℕ)) ^ (-(1 - 2 * δ)) ≤ |t| ∧
          |t| ≤ F γ (N / 2 : ℕ) ^ (12 * δ) := by
  obtain ⟨Nl, hl⟩ := Filter.eventually_atTop.mp (leaf_log_gap_lower γ δ h1 h2 hδ hδsmall)
  obtain ⟨Nu, hu⟩ := Filter.eventually_atTop.mp (leaf_log_gap_upper γ δ h1 h2 hδ hδsmall)
  refine ⟨max Nl Nu, fun N hN t htlow hthigh => ⟨?_, ?_⟩⟩
  · have hgap := hl N ((le_max_left _ _).trans hN)
    rw [leaf_F_rpow_exp] at htlow ⊢
    refine le_trans (Real.exp_le_exp.mpr ?_) htlow.le
    linarith
  · have hgap := hu N ((le_max_right _ _).trans hN)
    rw [leaf_F_rpow_exp] at hthigh
    refine hthigh.trans ?_
    rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
      ← Real.exp_add, leaf_F_rpow_exp]
    exact Real.exp_le_exp.mpr (by linarith)

end LeanLab.ExceptionalSet.Decomp446c

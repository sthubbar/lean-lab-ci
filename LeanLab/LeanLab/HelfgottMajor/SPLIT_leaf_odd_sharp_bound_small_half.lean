import LeanLab.HelfgottMajor.S2G5OddSharpReflect

/-!
Split of `leaf_odd_sharp_bound_small_half` of `HelfgottMajor/S2G5OddSharpReflect.lean`,
burst-20261127 session S2, unit S2-07. Binary Goldbach is open. AI wrote this Lean code.

The parent is the finite range `8 <= q <= 1200` of the cutoff free sharp odd
Polya-Vinogradov bound `||S(n)|| <= sqrt q / pi * (1/2 log q + log log q + 17/10)`, half period
`2 n < q`, an input of P0014, the explicit Polya-Vinogradov step of the major arc chapter of
Helfgott arXiv 1305.2897v4. The split peels off the modulus `q = 8`, where the trivial bound
`||S(n)|| <= n <= 3` already lies below the right side, about `3.126`, removes the moduli `q = 2 mod 4`, which carry
no primitive character, and leaves the moduli `9 <= q <= 1200`, `q` not `2 mod 4`, as the finite
computation.

Numerical check, S2-07, numpy, double precision: over every modulus `8 <= q <= 1200`, every odd
primitive character and every `n` with `2 n < q`, the ratio of `||S(n)||` to the right side is at
most `0.754`, reached at `q = 11`. The trivial bound `n <= (q - 1) / 2` beats the right side
only at `q = 8`.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real Finset

/-- The trivial bound: a partial sum of a Dirichlet character over `Icc 1 n` has norm at most
`n`, from `||χ a|| <= 1`. -/
theorem s2_07_trivial_partial_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ n := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 n, ‖χ (m : ZMod q)‖ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => DirichletCharacter.norm_le_one χ _
    _ = n := by simp

/-- The right side of the sharp odd bound at `q = 8` is at least `3`: `log 8 = 3 log 2`,
`log log 8 >= log 2` since `log 8 >= 2`, `sqrt 8 >= 2.828` and `pi < 3.1416`. -/
theorem s2_07_rhs_eight_ge :
    (3 : ℝ) ≤ sqrt (8 : ℝ) / π * (1 / 2 * log (8 : ℝ) + log (log (8 : ℝ)) + 17 / 10) := by
  have hl2 := Real.log_two_gt_d9
  have hl8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hll : log 2 ≤ log (log (8 : ℝ)) :=
    Real.log_le_log (by norm_num) (by rw [hl8]; linarith)
  have hs : (2.828 : ℝ) ≤ sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi0]
  nlinarith

/-- PROVED: the modulus `q = 8` of the parent, by the trivial bound, since `2 n < 8` forces
`n <= 3`. -/
theorem leaf_odd_sharp_bound_small_half_eight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : q = 8) (n : ℕ) (hn : 2 * n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
  have hqR : (q : ℝ) = 8 := by exact_mod_cast hq
  rw [hqR]
  exact (s2_07_trivial_partial_sum χ n).trans (hn3.trans s2_07_rhs_eight_ge)

/-- The reduction of unit groups from modulus `2 m` to modulus `m` is injective for `m` odd,
the Chinese remainder theorem with `(ZMod 2)ˣ` trivial. -/
theorem s2_07_unitsMap_injective {m : ℕ} (hm : m % 2 = 1) (x : (ZMod (2 * m))ˣ)
    (hx : ZMod.unitsMap (show m ∣ 2 * m from Dvd.intro_left 2 rfl) x = 1) : x = 1 := by
  have hm1 : 1 ≤ m := by omega
  have : NeZero (2 * m) := ⟨by omega⟩
  have : Fact (1 < 2 * m) := ⟨by omega⟩
  have hcop := ZMod.val_coe_unit_coprime x
  set v := (x : ZMod (2 * m)).val with hv
  have hvlt : v < 2 * m := ZMod.val_lt _
  have hc : ((x : ZMod (2 * m)).cast : ZMod m) = 1 := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hx
    simpa [ZMod.unitsMap_def] using this
  rw [ZMod.cast_eq_val] at hc
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [← hv, h] at hc
      simp at hc
      have : m = 1 := by simpa using (ZMod.one_eq_zero_iff.mp hc.symm)
      subst this
      exact absurd hcop (by rw [h]; decide)
    · exact h
  have hdm : m ∣ v - 1 := by
    have : ((v - 1 : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_sub hv1, hc, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  have hodd : v % 2 = 1 := by
    by_contra h
    have h2 : 2 ∣ v := by omega
    have := Nat.Coprime.coprime_dvd_left h2 hcop
    rw [Nat.coprime_mul_iff_right] at this
    exact absurd this.1 (by decide)
  have hd2 : 2 ∣ v - 1 := by omega
  have hcop2 : Nat.Coprime 2 m := by
    rw [Nat.coprime_two_left]; exact Nat.odd_iff.2 hm
  have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 hd2 hdm
  have h0 : v - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  have hv' : v = 1 := by omega
  apply Units.ext
  apply ZMod.val_injective
  rw [← hv, hv', Units.val_one, ZMod.val_one]

/-- PROVED: no primitive character has modulus `q = 2 mod 4`: every character modulo `2 m`, `m`
odd, factors through modulus `m`, so its conductor is at most `m`. -/
theorem s2_07_no_primitive_two_mod_four {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : q % 4 = 2) :
    ¬ χ.IsPrimitive := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, q = 2 * m ∧ m % 2 = 1 := ⟨q / 2, by omega, by omega⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  intro hχ
  have hFT : DirichletCharacter.FactorsThrough χ m := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (Dvd.intro_left 2 rfl)]
    intro x hx
    have hx1 : x = 1 := s2_07_unitsMap_injective hm x hx
    simp [hx1]
  have hcond : χ.conductor ≤ m :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 2 * m := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF: the finite computation of `leaf_odd_sharp_bound_small_half` on the moduli
`9 <= q <= 1200`, half period `2 n < q`: for each such modulus, each odd primitive character and
each `n <= (q - 1) / 2`, the partial sum is compared with
`sqrt q / pi * (1/2 log q + log log q + 17/10)`; the moduli `q = 2 mod 4`, which carry no
primitive character, are excluded. HARD, a large certified finite computation over characters. -/
theorem leaf_odd_sharp_bound_small_half_nine {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq9 : 9 ≤ q) (hq : q ≤ 1200) (hq4 : q % 4 ≠ 2)
    (n : ℕ) (hn : 2 * n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- Assembly: exactly the statement of `leaf_odd_sharp_bound_small_half`, from the proved modulus
`q = 8`, the proved absence of primitive characters modulo `q = 2 mod 4`, and the LEAF `leaf_odd_sharp_bound_small_half_nine`. -/
theorem leaf_odd_sharp_bound_small_half_of_leaves {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q)
    (hq : q ≤ 1200) (n : ℕ) (hn : 2 * n < q) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  rcases Nat.lt_or_ge q 9 with h | h
  · exact leaf_odd_sharp_bound_small_half_eight χ (by omega) n hn
  · by_cases h4 : q % 4 = 2
    · exact absurd hχ (s2_07_no_primitive_two_mod_four χ h4)
    · exact leaf_odd_sharp_bound_small_half_nine χ hχ h_odd h hq h4 n hn

example : type_of% @leaf_odd_sharp_bound_small_half_of_leaves =
    type_of% @leaf_odd_sharp_bound_small_half := rfl

end LeanLab.HelfgottMajor.PolyaVinogradov123

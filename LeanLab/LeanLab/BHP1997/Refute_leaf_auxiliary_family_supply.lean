/-
P0069, pages 24 to 27. FABLE PROVE SPRINT S9, unit BHP1997/SPLIT_lower_mean_value_supply.
Refutations of two open leaves of the split chain below `lower_mean_value_supply`.
No statement on main is changed, no definition is added, and no sorry is used.

1. `leaf_principal_reference_average` in SPLIT_leaf_auxiliary_family_supply is FALSE as
   stated. It quantifies over every real `u0` and every family `c0` with no hypothesis,
   so one family would have reference density `0 / log x` and `1 / log x` at once.
   Proved here unconditionally.
2. `leaf_auxiliary_family_supply` in SPLIT_lower_mean_value_supply is FALSE as stated,
   CONDITIONAL on the statement of the Perron transfer `perron_transfer` at exponent 1,
   which is taken as a hypothesis and never used as a theorem. The counterexample is
   `c0 = 0`: the auxiliary family would be negligible on the window I and still have
   density `u0 / log x` there.

The targets are named through `type_of%`, so the refuted statements are exactly the
ones on main. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- Standard real analysis. No constant bounds `log x` for all large `x`. -/
theorem exists_large_log_gt (C X : ℝ) : ∃ x : ℝ, X ≤ x ∧ 3 ≤ x ∧ C < Real.log x := by
  refine ⟨max (max X 3) (Real.exp (C + 1)), ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · have h1 : Real.exp (C + 1) ≤ max (max X 3) (Real.exp (C + 1)) := le_max_right _ _
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith

/-- Standard real analysis. A bound `u / log x ≤ C (log x)^(-2)` for all large `x`
is impossible for positive `u`. This is the contradiction used by both refutations
with logarithmic saving `A = 2`. -/
theorem no_log_saving_two {u : ℝ} (hu : 0 < u) (C X : ℝ)
    (h : ∀ x : ℝ, X ≤ x → 3 ≤ x → u / Real.log x ≤ C * Real.log x ^ (-(2 : ℝ))) : False := by
  obtain ⟨x, hX, h3, hC⟩ := exists_large_log_gt (max (C / u) 1) X
  have hl1 : 1 < Real.log x := (le_max_right _ _).trans_lt hC
  have hl0 : 0 < Real.log x := by linarith
  have hCu : C / u < Real.log x := (le_max_left _ _).trans_lt hC
  have hb := h x hX h3
  have e : Real.log x ^ (-(2 : ℝ)) = (Real.log x ^ 2)⁻¹ := by
    rw [Real.rpow_neg hl0.le]
    norm_num
  rw [e, div_le_iff₀ hl0] at hb
  have e2 : C * (Real.log x ^ 2)⁻¹ * Real.log x = C / Real.log x := by
    field_simp
  rw [e2, le_div_iff₀ hl0] at hb
  have : C < u * Real.log x := by
    have := (div_lt_iff₀ hu).mp hCu
    linarith
  linarith

/-- FALSE as stated: `leaf_principal_reference_average`, the third leaf of the split
of the auxiliary supply leaf. Pages 24 to 27. The leaf asserts the principal reference
density `u0 / log x` for every real `u0` and every family `c0`. Applied to one family
at `u0 = 0` and at `u0 = 1`, with `A = 2`, `q = 1` and the principal character, the
triangle inequality gives `1 / log x ≤ (C₀ + C₁) (log x)^(-2)` for all large `x`,
which fails. No hypothesis is used. -/
theorem leaf_principal_reference_average_false :
    ¬ (type_of% @leaf_principal_reference_average) := by
  intro H
  obtain ⟨C0, X0, h0⟩ := H 0 (fun _ _ => 0) 2 (by norm_num)
  obtain ⟨C1, X1, h1⟩ := H 1 (fun _ _ => 0) 2 (by norm_num)
  refine no_log_saving_two (u := 1) one_pos (C0 + C1) (max X0 X1) ?_
  intro x hx h3
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (2 : ℝ) := by
    have := Real.one_le_rpow hlog1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have a0 := h0 x ((le_max_left _ _).trans hx) 1 le_rfl hq 1 rfl
  have a1 := h1 x ((le_max_right _ _).trans hx) 1 le_rfl hq 1 rfl
  set r : ℂ := referenceAverage (section4SiftedFamily fun _ _ => (0 : ℝ)) x
    (1 : DirichletCharacter ℂ 1) with hr
  have hl0 : (0 : ℝ) < Real.log x := by linarith
  have key : ‖((1 : ℝ) : ℂ) / (Real.log x : ℂ)‖ ≤
      ‖r - ((0 : ℝ) : ℂ) / (Real.log x : ℂ)‖ + ‖r - ((1 : ℝ) : ℂ) / (Real.log x : ℂ)‖ := by
    have e : (r - ((0 : ℝ) : ℂ) / (Real.log x : ℂ)) - (r - ((1 : ℝ) : ℂ) / (Real.log x : ℂ)) =
        ((1 : ℝ) : ℂ) / (Real.log x : ℂ) := by
      push_cast
      ring
    have hn := norm_sub_le (r - ((0 : ℝ) : ℂ) / (Real.log x : ℂ))
      (r - ((1 : ℝ) : ℂ) / (Real.log x : ℂ))
    rwa [e] at hn
  have hn : ‖((1 : ℝ) : ℂ) / (Real.log x : ℂ)‖ = 1 / Real.log x := by
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [hn] at key
  linarith

/-- FALSE as stated, CONDITIONAL on the Perron transfer: `leaf_auxiliary_family_supply`,
the third leaf of the split of `lower_mean_value_supply`. Pages 24 to 27, Lemma 11 and
displays 4.1 to 4.5. The hypothesis `hP` is the statement of `perron_transfer` at
exponent 1. The counterexample is `c0 = 0` with `B0 = 1` and `u0 = 1`. An auxiliary
family `b` would have the mean value 4.1, so by the transfer and the two proved
lemmas `distribution_of_reference` and `distribution_of_approximation` the zero family
would have density `1 / log x` on the window I. At `A = 2`, `q = 1`, the principal
character and `t = x` this reads `card I / log x ≤ C x^(11/20+ε) (log x)^(-2)`, and
`card I ≥ x^(11/20+ε)`, which fails for large `x`. -/
theorem leaf_auxiliary_family_supply_false_of_perron
    (hP : ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ a : ℝ → ℕ → ℝ,
        (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (1 : ℝ)) →
        MeanValue41 ε a → RelativeDistribution ε a) :
    ¬ (type_of% @leaf_auxiliary_family_supply) := by
  intro H
  obtain ⟨η, hη, hP⟩ := hP
  set ε : ℝ := min (η / 2) (1 / 10) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεη : ε < η := (min_le_left _ _).trans_lt (by linarith)
  have hε10 : ε ≤ 1 / 10 := min_le_right _ _
  have hz : ∀ x k, section4SiftedFamily (fun _ _ => (0 : ℝ)) x k = 0 := by
    intro x k
    simp [section4SiftedFamily]
  obtain ⟨b, hb, hm, hd, happ⟩ := H 1 le_rfl ε hε hε10 1 (by norm_num) le_rfl
    (fun _ _ => 0) ⟨0, fun x k => by simp [hz]⟩
  have hr := hP ε hε hεη b hb hm
  have hcd : CharacterDistribution ε 1 (section4SiftedFamily fun _ _ => (0 : ℝ)) :=
    distribution_of_approximation happ (distribution_of_reference hε.le hr hd)
  obtain ⟨C, hC⟩ := hcd 2 (by norm_num)
  refine no_log_saving_two (u := 1 / 2) (by norm_num) C C ?_
  intro x hx h3
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans h3
  have hl0 : (0 : ℝ) < Real.log x := by linarith
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (2 : ℝ) := by
    have := Real.one_le_rpow hlog1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have hmain := hC x hx 1 le_rfl hq 1 x le_rfl
  -- the filter keeps the whole window
  have hfil : (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ x) = leftInterval ε x := by
    apply Finset.filter_true_of_mem
    intro k hk
    have hk2 := (Finset.mem_Ioc.mp hk).2
    exact (Nat.cast_le.mpr hk2).trans (Nat.floor_le hx0.le)
  have hterm : ∀ k ∈ leftInterval ε x,
      ((section4SiftedFamily (fun _ _ => (0 : ℝ)) x k : ℂ) *
        (1 : DirichletCharacter ℂ 1) (k : ZMod 1) -
        Thm2.delta (1 : DirichletCharacter ℂ 1) * (1 : ℝ) / Real.log x) =
      -(((1 / Real.log x : ℝ)) : ℂ) := by
    intro k _
    rw [hz]
    simp [Thm2.delta]
  rw [hfil, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, norm_mul,
    norm_neg, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at hmain
  -- the window holds at least x^(11/20+ε) integers
  set Y : ℝ := x ^ (11 / 20 + ε) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith) (by linarith)
  have hYx : Y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x)
      (by linarith : 11 / 20 + ε ≤ 1)
    rwa [Real.rpow_one] at this
  have hfY : Y / 2 ≤ (⌊Y⌋₊ : ℝ) := by
    have h1 : Y - 1 < (⌊Y⌋₊ : ℝ) := Nat.sub_one_lt_floor Y
    have h2 : (1 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
      exact_mod_cast Nat.floor_pos.mpr hY1
    linarith
  have hfx : (⌊Y⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_le.mpr (Nat.floor_le_floor hYx)
  have hcard : Y / 2 ≤ ((leftInterval ε x).card : ℝ) := by
    rw [leftInterval, Nat.card_Ioc]
    have hle : ⌊x - 2 * Y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
    rw [Nat.cast_sub hle]
    have h1 : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
    have h2 : (⌊x - 2 * Y⌋₊ : ℝ) ≤ max (x - 2 * Y) 0 := by
      rcases le_total 0 (x - 2 * Y) with h | h
      · exact (Nat.floor_le h).trans (le_max_left _ _)
      · rw [Nat.floor_of_nonpos h]
        simp
    rcases max_cases (x - 2 * Y) 0 with ⟨hm1, _⟩ | ⟨hm1, hm2⟩
    · rw [hm1] at h2
      linarith
    · rw [hm1] at h2
      linarith
  have hYpos : 0 < Y := by linarith
  have hlogpow : 0 ≤ Real.log x ^ (-(2 : ℝ)) := Real.rpow_nonneg hl0.le _
  have hstep : Y / 2 * (1 / Real.log x) ≤ C * Y * Real.log x ^ (-(2 : ℝ)) :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hmain
  have : Y * (1 / 2 / Real.log x) ≤ Y * (C * Real.log x ^ (-(2 : ℝ))) := by
    calc Y * (1 / 2 / Real.log x) = Y / 2 * (1 / Real.log x) := by ring
      _ ≤ C * Y * Real.log x ^ (-(2 : ℝ)) := hstep
      _ = Y * (C * Real.log x ^ (-(2 : ℝ))) := by ring
  exact le_of_mul_le_mul_left this hYpos

/-- FALSE as stated: `leaf_auxiliary_family_supply`. Pages 24 to 27. The Perron
transfer `perron_transfer` of Decomp312a, Lemma 11 with displays 4.1 to 4.5, supplies
the hypothesis of the conditional refutation above at exponent 1. The axiom report
in build/ records what this depends on through `perron_transfer`. -/
theorem leaf_auxiliary_family_supply_false :
    ¬ (type_of% @leaf_auxiliary_family_supply) :=
  leaf_auxiliary_family_supply_false_of_perron (perron_transfer 1)

/-- FALSE as stated: `leaf_nonprincipal_reference_average`, the second leaf of the
split of the auxiliary supply leaf. Pages 24 to 27. The leaf asserts cancellation of
the reference average at every non-principal character for every family `c0`, with no
size hypothesis. Counterexample: `c0 x k = x` at `k = ⌊x⌋` and zero elsewhere, read at
a large prime `x = p`, modulus 4 and the non-principal character `χ₄`. The prime `p`
passes the sifted weight, the reference sum is the single term `p χ₄(p)` of norm `p`,
and the reference width is at most `p`, so the average has norm at least 1. -/
theorem leaf_nonprincipal_reference_average_false :
    ¬ (type_of% @leaf_nonprincipal_reference_average) := by
  intro H
  obtain ⟨C, X, h⟩ := H (fun x k => if k = ⌊x⌋₊ then x else 0) 2 (by norm_num)
  obtain ⟨p, hpge, hp⟩ :=
    Nat.exists_infinite_primes ⌈max (max X 8) (Real.exp (|C| + 2))⌉₊
  have hxge : max (max X 8) (Real.exp (|C| + 2)) ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hpge)
  have hX : X ≤ (p : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hxge
  have h8 : (8 : ℝ) ≤ (p : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hxge
  have hexp : Real.exp (|C| + 2) ≤ (p : ℝ) := (le_max_right _ _).trans hxge
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : |C| + 2 ≤ Real.log (p : ℝ) := (Real.le_log_iff_exp_le hp0).mpr hexp
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hlog1 : 1 ≤ Real.log (p : ℝ) := by linarith
  have hl0 : 0 < Real.log (p : ℝ) := by linarith
  have hq : ((4 : ℕ) : ℝ) ≤ Real.log (p : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    push_cast
    nlinarith
  -- the non-principal character modulo 4
  let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := by
    intro hχ1
    have h3 : χ (3 : ZMod 4) = -1 := by
      show (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (3 : ZMod 4) = -1
      rw [MulChar.ringHomComp_apply]
      have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
      rw [this]
      simp
    have hu : IsUnit (3 : ZMod 4) := IsUnit.of_mul_eq_one (3 : ZMod 4) (by decide)
    rw [hχ1, MulChar.one_apply hu] at h3
    norm_num at h3
  have hp8 : 8 ≤ p := by exact_mod_cast h8
  have hcop : Nat.Coprime p 4 := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hχp : ‖χ ((p : ℕ) : ZMod 4)‖ = 1 := by
    rw [← ZMod.coe_unitOfCoprime p hcop]
    exact χ.unit_norm_eq_one _
  have a := h (p : ℝ) hX 4 (by norm_num) hq χ hχ
  -- the sifted weight keeps the prime p
  have hsw : siftedWeight p ⌈Real.exp (Real.log (p : ℝ) ^ (9 / 10 : ℝ))⌉₊ = 1 := by
    unfold siftedWeight
    rw [if_pos]
    right
    rw [hp.minFac_eq, Nat.ceil_le]
    have h1 : Real.log (p : ℝ) ^ (9 / 10 : ℝ) ≤ Real.log (p : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num : (9 / 10 : ℝ) ≤ 1)
      rwa [Real.rpow_one] at this
    calc Real.exp (Real.log (p : ℝ) ^ (9 / 10 : ℝ)) ≤ Real.exp (Real.log (p : ℝ)) :=
          Real.exp_le_exp.mpr h1
      _ = (p : ℝ) := Real.exp_log hp0
  have hw0 : 0 < referenceWidth (p : ℝ) := referenceWidth_pos hp0
  have hwle : referenceWidth (p : ℝ) ≤ (p : ℝ) := referenceWidth_le_x (by linarith)
  have hmem : p ∈ Finset.Ioc ⌊(p : ℝ) - referenceWidth (p : ℝ)⌋₊ ⌊(p : ℝ)⌋₊ := by
    rw [Nat.floor_natCast, Finset.mem_Ioc]
    refine ⟨?_, le_rfl⟩
    rw [Nat.floor_lt' hp.ne_zero]
    linarith
  have hsum : (∑ k ∈ Finset.Ioc ⌊(p : ℝ) - referenceWidth (p : ℝ)⌋₊ ⌊(p : ℝ)⌋₊,
      ((section4SiftedFamily (fun x k => if k = ⌊x⌋₊ then x else 0) (p : ℝ) k : ℝ) : ℂ) *
        χ (k : ZMod 4)) = ((p : ℝ) : ℂ) * χ ((p : ℕ) : ZMod 4) := by
    rw [Finset.sum_eq_single_of_mem p hmem]
    · simp only [section4SiftedFamily, Nat.floor_natCast, ite_true, hsw, mul_one]
    · intro k _ hk
      simp only [section4SiftedFamily, Nat.floor_natCast, if_neg hk, zero_mul,
        Complex.ofReal_zero]
  unfold referenceAverage at a
  rw [hsum, norm_div, norm_mul, hχp, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp0, abs_of_pos hw0] at a
  have hone : (1 : ℝ) ≤ (p : ℝ) / referenceWidth (p : ℝ) := (one_le_div hw0).mpr hwle
  have e : Real.log (p : ℝ) ^ (-(2 : ℝ)) = (Real.log (p : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hl0.le]
    norm_num
  rw [e] at a
  have hsq : 0 < Real.log (p : ℝ) ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ |C| * (Real.log (p : ℝ) ^ 2)⁻¹ :=
    (hone.trans a).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hsq.le))
  rw [le_mul_inv_iff₀ hsq] at h1
  nlinarith

end LeanLab.BHP1997.Decomp312a

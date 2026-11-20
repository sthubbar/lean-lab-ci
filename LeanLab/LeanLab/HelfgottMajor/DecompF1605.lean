import LeanLab.HelfgottMajor.DecompF662

/-!
Splitting the exponential counting comparison `DecompF662.exp_count_tsum_le` into smaller
steps, FREE-nv-step task1605.

The step bounds the total exponential weight of the zeros of `L(s, χ)` inside the critical
strip above height `T` by the density weighted exponential tail integral
`expTailIntegral`. The split separates

* the reduction of the zero sum to a discrete shell series via the zero count,
* the comparison of the shell series with the tail integral,

and `exp_count_tsum_le_F1605` assembles them. Each leaf is one inequality, strictly weaker
than the assembled statement. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- A zero of `L(·, χ)` inside the open strip has multiplicity at least one: `L(·, χ)` is analytic
on `{1}ᶜ`, does not vanish at `2`, and the set where the vanishing order is infinite is clopen. -/
private theorem one_le_mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (_h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 ≤ ZeroCount1623.mult χ ρ := by
  have hne1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro s hs
    exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hρmem : ρ ∈ ({1}ᶜ : Set ℂ) := by simpa using hne1
  have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) ≠ ⊤ := by
    have hz : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2)
        (Or.inr (by norm_num)) (by norm_num)
    have hzero : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) = 0 :=
      (han 2 h2mem).analyticOrderAt_eq_zero.mpr hz
    rw [hzero]; exact ENat.zero_ne_top
  have hρtop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected hpc h2mem hρmem h2
  have hρzero : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    have ha := han ρ hρmem
    rw [ha.analyticOrderAt_ne_zero, hρ]
  have hcast : (ZeroCount1623.mult χ ρ : ℕ∞) = analyticOrderAt (DirichletCharacter.LFunction χ) ρ :=
    Nat.cast_analyticOrderNatAt hρtop
  have hge : (1 : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    rcases eq_or_ne (analyticOrderAt (DirichletCharacter.LFunction χ) ρ) 0 with h | h
    · exact absurd h hρzero
    · exact Order.one_le_iff_ne_zero.mpr h
  have : (1 : ℕ∞) ≤ (ZeroCount1623.mult χ ρ : ℕ∞) := by rw [hcast]; exact hge
  exact_mod_cast this


/-- The plain cardinality of a finite set of strip zeros of a primitive character is at most the
multiplicity weighted count, hence at most the main term plus the error of `strip_count`. -/
private theorem card_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {X : ℝ} (hX : 1 ≤ X) (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ ZeroCount1623.stripZeros χ X) :
    (s.card : ℝ) ≤ 1600 * (X * (Real.log ((q : ℝ) * X) + 1)) := by
  classical
  have hF : (ZeroCount1623.stripZeros χ X).Finite := ZeroCount1623.stripZeros_finite χ X
  have hsub : s ⊆ hF.toFinset := by
    intro z hz
    exact hF.mem_toFinset.mpr (hs z hz)
  have hcard : (s.card : ℝ) ≤ ∑ ρ ∈ hF.toFinset, (ZeroCount1623.mult χ ρ : ℝ) := by
    have h1 : (s.card : ℝ) = ∑ ρ ∈ s, (1 : ℝ) := by simp
    rw [h1]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le_one)).trans ?_
    refine Finset.sum_le_sum (fun ρ hρ => ?_)
    have hmem := hF.mem_toFinset.mp hρ
    exact_mod_cast one_le_mult χ hmem.1 hmem.2.1 hmem.2.2.1
  have htsum := ZeroCount1623.strip_count χ hχ X hX
  have hEq : (∑' ρ : ZeroCount1623.ZeroIdx χ X, (ZeroCount1623.mult χ ρ.val : ℝ)) =
      ∑ ρ ∈ hF.toFinset, (ZeroCount1623.mult χ ρ : ℝ) :=
    ZeroCount1623.tsum_zeroIdx χ X (fun z => (ZeroCount1623.mult χ z : ℝ))
  rw [hEq] at htsum
  -- numeric comparison of the count estimate with `1600 * (X * (log (q*X) + 1))`
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q; exact_mod_cast this
  have hpos : (0 : ℝ) < (q : ℝ) * X := by positivity
  have hL : 0 ≤ Real.log ((q : ℝ) * X) := Real.log_nonneg (by nlinarith)
  have hX0 : (0 : ℝ) < X := by linarith
  set L : ℝ := Real.log ((q : ℝ) * X) with hLdef
  have h2pie : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by
    nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9]
  have hlog_le : Real.log ((q : ℝ) * X / (2 * Real.pi * Real.exp 1)) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2pie hpos.le]
  have hpiinv : X / Real.pi ≤ 0.32 * X := by
    have h1 : X * (1 / Real.pi) ≤ X * 0.32 := by
      apply mul_le_mul_of_nonneg_left _ hX0.le
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d4]
    calc X / Real.pi = X * (1 / Real.pi) := by ring
      _ ≤ X * 0.32 := h1
      _ = 0.32 * X := by ring
  -- (a) the main term
  have ha : X / Real.pi * Real.log ((q : ℝ) * X / (2 * Real.pi * Real.exp 1)) ≤ 0.32 * (X * (L + 1)) := by
    have s2 : X / Real.pi * Real.log ((q : ℝ) * X / (2 * Real.pi * Real.exp 1)) ≤ X / Real.pi * L :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    have s3 : X / Real.pi * L ≤ (0.32 * X) * L := mul_le_mul_of_nonneg_right hpiinv hL
    have s4 : (0.32 * X) * L ≤ 0.32 * (X * (L + 1)) := by
      have : X * L ≤ X * (L + 1) := by nlinarith
      nlinarith
    linarith
  -- (b) the half log term
  have hb : 0.5 * L ≤ 0.5 * (X * (L + 1)) := by
    have hXL : L ≤ X * L := by nlinarith [mul_le_mul_of_nonneg_right hX hL]
    have h1 : L ≤ X * (L + 1) := by nlinarith
    nlinarith
  -- (c) the constant term
  have hc : (17.7 : ℝ) ≤ 17.7 * (X * (L + 1)) := by
    have h1 : (1 : ℝ) ≤ X * (L + 1) := by
      nlinarith [mul_le_mul hX (by linarith : (1:ℝ) ≤ L + 1) (by norm_num) hX0.le]
    nlinarith
  have hfin : (18.6 : ℝ) * (X * (L + 1)) ≤ 1600 * (X * (L + 1)) :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hnn : (0 : ℝ) ≤ X * (L + 1) := by positivity
  linarith [ha, hb, hc, hfin]

/-! ## The shell sum

The zeros above height `T` are grouped by the integer part of their height. The `n`-th shell
holds at most `card_le_count` zeros, and the exponential weight on the shell is at most
`exp (-0.1598 n)`, so the weight sum is dominated by a series of `n^2 exp (-0.1598 n)`. -/


/-- The polynomial comparison behind the shell sum:
`1600 exp (-c n) (n+1) (log (q (n+1)) + 1) ≤ 6400 (q+1) (n^2+1) exp (-c n)`. -/
private theorem shell_weight_le {q : ℕ} [NeZero q] (n : ℕ) :
    Real.exp (-0.1598 * (n : ℝ)) *
        (1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)))
      ≤ 6400 * ((q : ℝ) + 1) *
        (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q; exact_mod_cast this
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have harg : (0 : ℝ) < (q : ℝ) * ((n : ℝ) + 1) := by positivity
  have hlog : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ≤ (q : ℝ) * ((n : ℝ) + 1) := by
    have := Real.log_le_sub_one_of_pos harg
    linarith
  have step1 : Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1 ≤ (q : ℝ) * ((n : ℝ) + 1) + 1 := by
    linarith
  have step2 : (q : ℝ) * ((n : ℝ) + 1) + 1 ≤ ((q : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith
  have step3 : ((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1) ≤
      ((q : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (step1.trans step2) hn1.le
    calc ((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)
        ≤ ((n : ℝ) + 1) * (((q : ℝ) + 1) * ((n : ℝ) + 1)) := h
      _ = ((q : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 := by ring
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * ((n : ℝ) ^ 2 + 1) := by nlinarith
  have hmid : 1600 * (((q : ℝ) + 1) * ((n : ℝ) + 1) ^ 2) ≤
      6400 * ((q : ℝ) + 1) * ((n : ℝ) ^ 2 + 1) := by
    have h0 : (0 : ℝ) ≤ ((q : ℝ) + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq h0]
  have hexppos : (0 : ℝ) ≤ Real.exp (-0.1598 * (n : ℝ)) := (Real.exp_pos _).le
  have h1 : Real.exp (-0.1598 * (n : ℝ)) *
        (1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)))
      ≤ Real.exp (-0.1598 * (n : ℝ)) * (1600 * (((q : ℝ) + 1) * ((n : ℝ) + 1) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hexppos
    exact mul_le_mul_of_nonneg_left step3 (by norm_num)
  have h2 : Real.exp (-0.1598 * (n : ℝ)) * (1600 * (((q : ℝ) + 1) * ((n : ℝ) + 1) ^ 2))
      ≤ Real.exp (-0.1598 * (n : ℝ)) * (6400 * ((q : ℝ) + 1) * ((n : ℝ) ^ 2 + 1)) := by
    apply mul_le_mul_of_nonneg_left hmid hexppos
  have h3 : Real.exp (-0.1598 * (n : ℝ)) * (6400 * ((q : ℝ) + 1) * ((n : ℝ) ^ 2 + 1))
      = 6400 * ((q : ℝ) + 1) * (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
    ring
  linarith [h1, h2, h3.le, h3.ge]


/-- The finite shell bound: any finite family of strip zeros of `χ` above height `T` has its
exponential weight sum bounded by the full `n^2 exp (-c n)` series, provided the strip zeros of
`χ` are among the strip zeros of a primitive character `ψ` of level at most the level of `χ`.
This is the finite-sum core of the shell grouping, stated in the form `Real.tsum_le_of_sum_le`
consumes. -/
private theorem shell_finset_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ.IsPrimitive) (T : ℝ)
    (hz : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      DirichletCharacter.LFunction ψ ρ = 0)
    (hQq : (Q : ℝ) ≤ (q : ℝ))
    (u : Finset {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ T < |ρ.im|}) :
    ∑ ρ ∈ u, Real.exp (-0.1598 * |ρ.val.im|) ≤
      6400 * ((q : ℝ) + 1) *
        (∑' n : ℕ, ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
  classical
  classical
  have hHsum : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-0.1598 * (n : ℝ))) := by
      simpa [Nat.cast_pow] using
        Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 0.1598)
    have h0 : Summable (fun n : ℕ => Real.exp (-0.1598 * (n : ℝ))) := by
      simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 0.1598)
    have hsum := h1.add h0
    simpa [add_mul, one_mul] using hsum
  set k : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} → ℕ
    := fun ρ => ⌊|ρ.val.im|⌋₊ with hk
  have hk_le : ∀ ρ, (k ρ : ℝ) ≤ |ρ.val.im| := fun ρ => Nat.floor_le (abs_nonneg _)
  have hk_lt : ∀ ρ, |ρ.val.im| < (k ρ : ℝ) + 1 := by
    intro ρ
    have h := Nat.lt_succ_floor (|ρ.val.im|)
    simpa [hk, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using h
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image k) (g := k)
    (f := fun ρ => Real.exp (-0.1598 * |ρ.val.im|)) (fun ρ hρ => Finset.mem_image_of_mem k hρ)]
  calc ∑ n ∈ u.image k, ∑ ρ ∈ u.filter (fun ρ => k ρ = n), Real.exp (-0.1598 * |ρ.val.im|)
      ≤ ∑ n ∈ u.image k, ∑ ρ ∈ u.filter (fun ρ => k ρ = n), Real.exp (-0.1598 * (n : ℝ)) := by
        refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun ρ hρ => ?_))
        have hkn : k ρ = n := (Finset.mem_filter.mp hρ).2
        have hle : (n : ℝ) ≤ |ρ.val.im| := by rw [← hkn]; exact hk_le ρ
        exact Real.exp_le_exp.mpr (by nlinarith)
    _ = ∑ n ∈ u.image k,
          Real.exp (-0.1598 * (n : ℝ)) * ((u.filter (fun ρ => k ρ = n)).card : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ n ∈ u.image k, 6400 * ((q : ℝ) + 1) *
          (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        have hcardn : ((u.filter (fun ρ => k ρ = n)).card : ℝ) ≤
            1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) := by
          have himg : ∀ z ∈ (u.filter (fun ρ => k ρ = n)).image Subtype.val,
              z ∈ ZeroCount1623.stripZeros ψ ((n : ℝ) + 1) := by
            intro z hzmem
            obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hzmem
            have hkn : k ρ = n := (Finset.mem_filter.mp hρ).2
            have hlt := hk_lt ρ
            rw [hkn] at hlt
            exact ⟨hz ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1, ρ.property.2.1,
              ρ.property.2.2.1, by linarith⟩
          have hce : ((u.filter (fun ρ => k ρ = n)).card : ℝ) =
              (((u.filter (fun ρ => k ρ = n)).image Subtype.val).card : ℝ) := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective]
          rw [hce]
          have hnX : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
          refine (card_le_count ψ hψ hnX _ himg).trans ?_
          have hX0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
          have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
          have hQX : (0 : ℝ) < (Q : ℝ) * ((n : ℝ) + 1) := by positivity
          have hmono : Real.log ((Q : ℝ) * ((n : ℝ) + 1)) ≤ Real.log ((q : ℝ) * ((n : ℝ) + 1)) := by
            apply Real.log_le_log hQX
            nlinarith
          have hstep : ((n : ℝ) + 1) * (Real.log ((Q : ℝ) * ((n : ℝ) + 1)) + 1) ≤
              ((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1) := by
            have h1 := mul_le_mul_of_nonneg_left hmono hX0.le
            linarith
          nlinarith [hstep, hX0]
        calc Real.exp (-0.1598 * (n : ℝ)) * ((u.filter (fun ρ => k ρ = n)).card : ℝ)
            ≤ Real.exp (-0.1598 * (n : ℝ)) *
                (1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1))) :=
              mul_le_mul_of_nonneg_left hcardn (Real.exp_pos _).le
          _ ≤ 6400 * ((q : ℝ) + 1) *
                (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := shell_weight_le n
    _ ≤ ∑' n : ℕ, 6400 * ((q : ℝ) + 1) *
          (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        have hnonneg : ∀ n ∉ u.image k, 0 ≤ 6400 * ((q : ℝ) + 1) *
            (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
          intro n _; positivity
        exact Summable.sum_le_tsum _ hnonneg (hHsum.mul_left _)
    _ = 6400 * ((q : ℝ) + 1) *
          (∑' n : ℕ, ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        rw [tsum_mul_left]


private theorem LFunction_primitive_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) := by
  have h := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
    χ.conductor_dvd_level χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter] at h
  exact h

/-- No factor of the Euler product is a zero function in the open strip: a vanishing factor
would force `p ^ (-re s) ≥ 1`, hence `re s ≤ 0`. -/
private theorem euler_factor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))) ≠ 0 := by
  classical
  rw [Finset.prod_ne_zero_iff]
  intro p hp hzero
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℕ) ≤ p := hpprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by linarith : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by linarith : 1 < p)
  have hc : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have hn1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one (χ := χ.primitiveCharacter) (p : ZMod χ.conductor)
  have heq : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * (p : ℝ) ^ (-s.re) = 1 := by
    rw [← hnorm, ← norm_mul, hc, norm_one]
  have hple : (1 : ℝ) ≤ (p : ℝ) ^ (-s.re) := by
    have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-s.re) := (Real.rpow_pos_of_pos hp0 _).le
    calc (1 : ℝ) = ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * (p : ℝ) ^ (-s.re) := heq.symm
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := by
          simpa using mul_le_mul_of_nonneg_right hn1 hpos
      _ = (p : ℝ) ^ (-s.re) := one_mul _
  have h0le : (0 : ℝ) ≤ -s.re := by
    have h1' : (p : ℝ) ^ (0 : ℝ) ≤ (p : ℝ) ^ (-s.re) := by simpa using hple
    exact (Real.rpow_le_rpow_left_iff hp1).mp h1'
  linarith

/-- `χ` and its primitive character have the same zeros in the open strip. -/
private theorem strip_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ ρ = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
  have hs : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  rw [LFunction_primitive_factor χ hs]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (euler_factor_ne_zero χ h0 h1)
  · intro h; rw [h, zero_mul]


/-- LEAF. The zero sum is bounded by a discrete shell series: grouping the zeros by the
integer part of `|Im ρ|`, the total exponential weight is at most the sum over shells of
`6400 * (q+1) * (n²+1) * exp (-0.1598 * n)`. This is the counting input from the zero
density, and it reduces the continuous zero set to a summable series over `ℕ`. -/
theorem exp_count_tsum_le_shell_series (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      6400 * ((q : ℝ) + 1) * (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ)))) := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcond : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    have h : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    exact_mod_cast h
  refine Real.tsum_le_of_sum_le
    (f := fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => Real.exp (-0.1598 * |ρ.val.im|))
    (fun _ => (Real.exp_pos _).le) (fun u => ?_)
  exact shell_finset_le χ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive T
    (fun ρ hz h0 h1 => (strip_zero_iff χ h0 h1).mp hz) hcond u

/-- LEAF. The shell series is bounded by the tail integral: for `T ≥ 100`, the series
`6400 * (q+1) * ∑' n (n²+1) * exp (-0.1598 * n)` is at most `expTailIntegral q T`.
This is the comparison of the discrete shell series with the continuous density weighted
integral, closing the argument. -/
theorem shell_series_le_expTailIntegral (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    6400 * ((q : ℝ) + 1) * (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ)))) ≤
      expTailIntegral q T := by
  sorry

/-- The exponential counting comparison, with the statement after the name repeated
character for character from `DecompF662.exp_count_tsum_le`. The assembly chains the
two leaves: the zero sum is bounded by the shell series, and the shell series is bounded
by the tail integral. -/
theorem exp_count_tsum_le_F1605 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      expTailIntegral q T := by
  have h1 := exp_count_tsum_le_shell_series q χ T hT hs
  have h2 := shell_series_le_expTailIntegral q T hT
  exact le_trans h1 h2

end LeanLab.HelfgottMajor.Decomp269c

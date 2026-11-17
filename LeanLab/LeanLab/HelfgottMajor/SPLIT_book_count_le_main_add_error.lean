import LeanLab.HelfgottMajor.SPLIT_zero_multiplicity_subexponential

/-!
Split of `book_count_le_main_add_error` of `HelfgottMajor`.

The target is the one sided explicit zero count of book page 431: for every character of modulus
`q`, primitive or not, and every height `T` at least `100`, the multiplicity weighted count of
the zeros of `L (·, χ)` in the open strip up to height `T` is at most the main term `bookMain q T`
plus the error `bookError q T`.

For a primitive character the count is the two sided estimate `ZeroCount1623.book_zero_count`,
which puts the count within `bookError` of `bookMain`; the one sided form is its upper half and it
is the first leaf.

The remaining content is the character. The target quantifies over imprimitive characters as
well. An imprimitive character of modulus `q` is induced from its primitive character of
conductor `c = χ.conductor`, which divides `q`, and the two L functions differ by the finitely
many Euler factors `1 - χ₀ p ^ (-s)` at the primes dividing `q` but not `c`. Each of those
factors is nonzero on the open right half plane, so it removes no zero and adds none: the strip
zeros agree as sets, leaf two, and with multiplicity, leaf three. The conductor is at most the
modulus, and both the main term and the error are nondecreasing in the modulus at a fixed height
of at least `100`, leaf four, so the count at the conductor is dominated by the count at the
modulus.

The assembly is the case split on primitivity. The primitive case is the first leaf; the
imprimitive case transports the count at the conductor to the modulus with leaves two and three,
estimates it with the first leaf at the conductor, and dominates the result with leaf four.
`book_count_le_main_add_error` itself is not used.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-! Private helpers. Inducing a character from its conductor to the modulus multiplies the `L`
function by the finitely many Euler factors of the primes dividing the new level, each of which is
nonzero and analytic in the open right half plane; so the induced character has the same strip zeros
with the same multiplicities. -/

private lemma euler_factor_ne_of_re_pos {r : ℕ} (χ : DirichletCharacter ℂ r) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ (p : ZMod r) * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hn : ‖χ (p : ZMod r) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
    calc
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right
        (DirichletCharacter.norm_le_one χ _) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  intro hz
  have hh : χ (p : ZMod r) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [hh, norm_one] at hn
  exact (lt_irrefl 1) hn

private lemma euler_product_ne_of_re_pos {r : ℕ} (χ : DirichletCharacter ℂ r) (Q : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    (∏ p ∈ Q.primeFactors, (1 - χ (p : ZMod r) * (p : ℂ) ^ (-s))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact euler_factor_ne_of_re_pos χ (Nat.prime_of_mem_primeFactors hp) hs

/-- Inducing a character preserves every zero in the open critical strip. -/
private lemma lfunction_changeLevel_eq_zero {r q : ℕ} [NeZero r] [NeZero q]
    (hd : r ∣ q) (χ : DirichletCharacter ℂ r) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ) s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  have hs : s ≠ 1 := by intro h; simp [h] at hs1
  rw [DirichletCharacter.LFunction_changeLevel hd χ (Or.inr hs),
    mul_eq_zero, or_iff_left (euler_product_ne_of_re_pos χ q hs0)]

/-- Inducing a character preserves analytic orders in the open critical strip. -/
private lemma analyticOrderNatAt_changeLevel {r q : ℕ} [NeZero r] [NeZero q]
    (hd : r ∣ q) (χ : DirichletCharacter ℂ r) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ)) s =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) s := by
  let P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors,
    (1 - χ (p : ZMod r) * (p : ℂ) ^ (-z))
  have hs : s ≠ 1 := by intro h; simp [h] at hs1
  have hP : AnalyticAt ℂ P s := by
    apply Finset.analyticAt_fun_prod
    intro p hp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hps : (p : ℂ) ∈ Complex.slitPlane := Complex.natCast_mem_slitPlane.mpr
      (Nat.prime_of_mem_primeFactors hp).ne_zero
    fun_prop
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
    apply DifferentiableOn.analyticAt (s := {1}ᶜ) _
      (isOpen_compl_singleton.mem_nhds hs)
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ) =ᶠ[nhds s]
      (fun z => DirichletCharacter.LFunction χ z * P z) := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact DirichletCharacter.LFunction_changeLevel hd χ (Or.inr hz)
  unfold analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr he]
  change analyticOrderAt (DirichletCharacter.LFunction χ * P) s = _
  have hP0 : P s ≠ 0 := euler_product_ne_of_re_pos χ q hs0
  have hPo : analyticOrderAt P s = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hP0)
  rw [analyticOrderAt_mul hL hP, hPo, add_zero]

/-- Inducing a character from its conductor preserves the zeros in the open critical strip. -/
private lemma lfunction_primitiveCharacter_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have h : DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter) s = 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s = 0 :=
    lfunction_changeLevel_eq_zero (χ := χ.primitiveCharacter) χ.conductor_dvd_level hs0 hs1
  rwa [DirichletCharacter.changeLevel_primitiveCharacter] at h

/-- LEAF. The primitive case: the one sided count. For a primitive character of modulus `q` and
height at least `100` the multiplicity weighted strip count is at most the main term plus the
error. This is the upper half of the two sided explicit estimate, which is stated for heights at
least one, so it applies here; no zero of `L` is exhibited. -/
theorem book_count_le_main_add_error_of_isPrimitive (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 100 ≤ T) :
    ZeroCount1623.bookCount χ T ≤ ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  have h := (abs_le.mp (ZeroCount1623.book_zero_count χ hχ (T := T) (by linarith))).2
  linarith

/-- LEAF. The strip zero sets of an imprimitive character and of the primitive character that
induces it coincide. The two L functions differ by the Euler factors of the primes dividing the
modulus but not the conductor, and each of those factors is nonzero on the open right half
plane, so a point of the open strip is a zero of one exactly when it is a zero of the other. -/
theorem stripZeros_primitiveCharacter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (T : ℝ) :
    ZeroCount1623.stripZeros χ T = ZeroCount1623.stripZeros χ.primitiveCharacter T := by
  ext ρ
  simp only [ZeroCount1623.stripZeros]
  exact ⟨fun h => ⟨(lfunction_primitiveCharacter_eq_zero χ h.2.1 h.2.2.1).mp h.1, h.2⟩,
    fun h => ⟨(lfunction_primitiveCharacter_eq_zero χ h.2.1 h.2.2.1).mpr h.1, h.2⟩⟩

/-- LEAF. The multiplicities of a strip zero of an imprimitive character and of the same point as
a zero of the inducing primitive character agree. The extra Euler factors are analytic and
nonzero at the point, so multiplying by them changes no order of vanishing. -/
theorem mult_eq_primitiveCharacter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ZeroCount1623.mult χ ρ = ZeroCount1623.mult χ.primitiveCharacter ρ := by
  show analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
    analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) ρ
  have h := analyticOrderNatAt_changeLevel (χ := χ.primitiveCharacter) χ.conductor_dvd_level hre0 hre1
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  exact h

/-- LEAF. The main term plus the error is nondecreasing in the modulus. At a fixed height of at
least `100` both the main term `T / (2 π)` times a logarithm of a positive multiple of `q` and
the error `0.15` times a logarithm of a positive multiple of `q` increase with `q`, so raising
the modulus raises the bound. -/
theorem bookMain_add_bookError_mono {q₀ q : ℕ} {T : ℝ} (hq0 : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hT : 100 ≤ T) :
    ZeroCount1623.bookMain q₀ T + ZeroCount1623.bookError q₀ T ≤
      ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hc : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have hcast : (q₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0R : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast (by omega : 0 < q₀)
  have harg : (q₀ : ℝ) * T ≤ (q : ℝ) * T := by
    exact mul_le_mul_of_nonneg_right hcast hT0.le
  have hle1 : (q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1) ≤
      (q : ℝ) * T / (2 * Real.pi * Real.exp 1) := by
    exact div_le_div_of_nonneg_right harg hc.le
  have hpos0 : (0 : ℝ) < (q₀ : ℝ) * T := mul_pos hq0R hT0
  have hpos : (0 : ℝ) < (q : ℝ) * T := mul_pos (lt_of_lt_of_le hq0R hcast) hT0
  have hlog1 : Real.log ((q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1)) ≤
      Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) :=
    Real.log_le_log (div_pos hpos0 hc) hle1
  have hmain : T / (2 * Real.pi) * Real.log ((q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1)) ≤
      T / (2 * Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) :=
    mul_le_mul_of_nonneg_left hlog1 (div_nonneg hT0.le (by positivity))
  have hlog2 : Real.log ((q₀ : ℝ) * T) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hpos0 harg
  have herr : 0.15 * Real.log ((q₀ : ℝ) * T) + 3.389 ≤ 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
    linarith [mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 0.15)]
  unfold ZeroCount1623.bookMain ZeroCount1623.bookError
  linarith [hmain, herr]

/-- The target, from the four steps. For a primitive character it is the first leaf. Otherwise
the conductor is a positive divisor of the modulus, so the primitive character of the conductor is
primitive, its count equals the count at the modulus by the two zero set leaves, and the bound at
the conductor is at most the bound at the modulus by the monotonicity leaf. -/
theorem book_count_le_main_add_error_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 100 ≤ T) :
    ZeroCount1623.bookCount χ T ≤ ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  by_cases hχ : χ.IsPrimitive
  · exact book_count_le_main_add_error_of_isPrimitive q χ hχ T hT
  · have hcond : χ.conductor ≠ 0 := χ.conductor_ne_zero
    haveI : NeZero χ.conductor := ⟨hcond⟩
    have hcount : ZeroCount1623.bookCount χ T =
        ZeroCount1623.bookCount χ.primitiveCharacter T := by
      have hset := stripZeros_primitiveCharacter q χ T
      have hfin : (ZeroCount1623.stripZeros_finite χ T).toFinset =
          (ZeroCount1623.stripZeros_finite χ.primitiveCharacter T).toFinset := by
        ext ρ
        simp only [Set.Finite.mem_toFinset, hset]
      unfold ZeroCount1623.bookCount
      rw [hfin]
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hmemχ : ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset := by
        have h := (Finset.mem_filter.mp hρ).1
        simpa only [hfin] using h
      have hmem : ρ ∈ ZeroCount1623.stripZeros χ T :=
        (ZeroCount1623.stripZeros_finite χ T).mem_toFinset.mp hmemχ
      rw [mult_eq_primitiveCharacter q χ hmem.2.1 hmem.2.2.1 hmem.1]
    rw [hcount]
    have hle := book_count_le_main_add_error_of_isPrimitive χ.conductor χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive T hT
    refine le_trans hle (bookMain_add_bookError_mono ?_ ?_ hT)
    · exact Nat.pos_of_ne_zero hcond
    · exact Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

end LeanLab.HelfgottMajor.Decomp269c

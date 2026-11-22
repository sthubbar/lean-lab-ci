import LeanLab.HelfgottMajor.DecompF547
import LeanLab.HardyLittlewood1923.U1482ZeroCount

/-!
Split of the exponential branch counting step `exp_branch_count_le` of DecompF547.lean,
FREE-nv-minimax task1602. No existing file is edited.

The target bounds the one sided multiplicity weighted exponential decay of the zero heights
of `L(·, χ)` inside the critical strip above height `T` against the exponential tail integral
`expTailIntegral`. The proof runs in three steps, and this file carries one leaf per step.

1. Shell counting. The zeros with positive imaginary part in a unit window above `T` number
   at most a logarithmic multiple of the window index, weighted by the analytic multiplicity.
2. Summability. The multiplicity weighted exponential decay series over those zeros is
   summable, because the shell count is logarithmic against the geometric decay.
3. Comparison. The total of the weighted series is at most the exponential tail integral,
   whose integrand is the same exponential decay against the zero density.

The shell count is proved here with no input: Jensen's inequality on the disc of radius `7/5`
about `3/2 + iτ` counts the strip zeros right of the critical line, zeros left of it reflect to
zeros of the inverse character by the functional equation, and the lower bound `1/Z` on
`L(3/2 + iτ, χ)` with `Z` less than three is proved from the telescoping comparison
`n^(-3/2) <= 2 (n^(-1/2) - (n+1)^(-1/2))`. The one import is `HardyLittlewood1923.U1482ZeroCount`,
which supplies `rw_count_all`, `sum_le_RW`, `mult_le_reflect`, `reflect_zero` and `log_bound`;
its whole closure is free of `sorry`, and the axioms of the theorems used are checked below.
Steps 1 and 2 are proved; step 3 is a leaf which is false as cut (see the report).

The assembly `exp_branch_count_le_F1602` has the statement of the target character for
character and is proved from the three leaves with no gap of its own. AI wrote this Lean
code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real
open Filter Topology

section DecompF1602

/-! ### Private helpers: the explicit book count for an arbitrary character

The zero count is stated for a primitive character. The lemmas below carry it to an arbitrary
character of modulus `q`: inducing from the conductor multiplies the `L` function by the Euler
factors of the primes dividing `q` but not the conductor, each of which is analytic and nonzero
on the open right half plane, so the strip zeros and their multiplicities agree. -/

/-! ### Private helpers: the explicit book count for an arbitrary character

`ZeroCount1623.book_zero_count` is stated for a primitive character only. The lemmas below carry
it to an arbitrary character of modulus `q`: inducing from the conductor multiplies the `L`
function by the Euler factors of the primes dividing `q` but not the conductor, each of which is
analytic and nonzero on the open right half plane, so the strip zeros and their multiplicities
agree, and the main term plus the error is nondecreasing in the modulus. These are private copies
of the proved lemmas of `SPLIT_book_count_le_main_add_error`, which is not in the import closure
of this file. Only the modules already imported by this file are used. -/


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

open LeanLab.PNTPort.DirichletZF (Z one_le_Z Z_pos summable_Z)

/-- The norm of the `Z` term at `s = 3/2`. -/
private lemma Z_term_norm (n : ℕ) :
    ‖LSeries.term 1 ((3 : ℂ) / 2) n‖ = (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [LSeries.term]
  · rw [LSeries.term_def, if_neg h.ne']
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hre : (((3 : ℂ) / 2)).re = 3 / 2 := by simp
    have hcast : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
    rw [norm_div, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hre]
    simp only [Pi.one_apply, norm_one]
    rw [one_div, ← Real.rpow_neg (le_of_lt hpos)]

/-- The telescoping step: `(n+2)^(-3/2) ≤ 2 ((n+1)^(-1/2) - (n+2)^(-1/2))`. -/
private lemma Z_step_le (n : ℕ) :
    ((n : ℝ) + 2) ^ (-(3 / 2) : ℝ) ≤
      2 * (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ)) := by
  set A : ℝ := Real.sqrt ((n : ℝ) + 1) with hA
  set B : ℝ := Real.sqrt ((n : ℝ) + 2) with hB
  have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr hpos1
  have hB0 : 0 < B := by rw [hB]; exact Real.sqrt_pos.mpr hpos2
  have hA2 : A ^ 2 = (n : ℝ) + 1 := by rw [hA]; exact Real.sq_sqrt hpos1.le
  have hB2 : B ^ 2 = (n : ℝ) + 2 := by rw [hB]; exact Real.sq_sqrt hpos2.le
  have hAB : A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
  have e3 : ((n : ℝ) + 2) ^ (-(3 / 2) : ℝ) = 1 / (B * B * B) := by
    have h2 : ((n : ℝ) + 2) ^ (3 / 2 : ℝ) = B * B * B := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos2, Real.rpow_one,
        ← Real.sqrt_eq_rpow, ← hB, ← hB2]
      ring
    rw [Real.rpow_neg hpos2.le, h2, one_div]
  have e1 : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = 1 / A := by
    rw [Real.rpow_neg hpos1.le, ← Real.sqrt_eq_rpow, ← hA, one_div]
  have e2 : ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) = 1 / B := by
    rw [Real.rpow_neg hpos2.le, ← Real.sqrt_eq_rpow, ← hB, one_div]
  rw [e1, e2, e3]
  have hsq : (B - A) * (B + A) = 1 := by nlinarith
  have hBA : B - A = 1 / (A + B) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have key : 2 * (1 / A - 1 / B) = 2 / (A * B * (A + B)) := by
    have h1 : 1 / A - 1 / B = (B - A) / (A * B) := by
      field_simp
    rw [h1, hBA]
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmain : A * (A + B) ≤ 2 * B ^ 2 := by nlinarith [hAB, hA2, hB2]
  have h2 := mul_le_mul_of_nonneg_right hmain hB0.le
  nlinarith [h2]

/-- `g n = (n+1)^(-1/2)`: the decrement `g n - g (n+1)` lies between `0` and `(n+1)^(-3/2)`. -/
private lemma g_diff_bounds (n : ℕ) :
    ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) ≤
      ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by
  set A : ℝ := Real.sqrt ((n : ℝ) + 1) with hA
  set B : ℝ := Real.sqrt ((n : ℝ) + 2) with hB
  have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr hpos1
  have hB0 : 0 < B := by rw [hB]; exact Real.sqrt_pos.mpr hpos2
  have hA2 : A ^ 2 = (n : ℝ) + 1 := by rw [hA]; exact Real.sq_sqrt hpos1.le
  have hB2 : B ^ 2 = (n : ℝ) + 2 := by rw [hB]; exact Real.sq_sqrt hpos2.le
  have e1 : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = 1 / A := by
    rw [Real.rpow_neg hpos1.le, ← Real.sqrt_eq_rpow, ← hA, one_div]
  have e2 : ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) = 1 / B := by
    rw [Real.rpow_neg hpos2.le, ← Real.sqrt_eq_rpow, ← hB, one_div]
  have e3 : ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ) = 1 / (A * A * A) := by
    have h2 : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) = A * A * A := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos1, Real.rpow_one,
        ← Real.sqrt_eq_rpow, ← hA, ← hA2]
      ring
    rw [Real.rpow_neg hpos1.le, h2, one_div]
  rw [e1, e2, e3]
  have hBA : B - A = 1 / (A + B) := by
    rw [eq_div_iff (by positivity)]
    nlinarith
  have h1 : 1 / A - 1 / B = (B - A) / (A * B) := by
    field_simp
  have hrhs : 1 / A - 1 / B = 1 / ((A + B) * A * B) := by
    rw [h1, hBA]
    field_simp
  rw [hrhs]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hA2, hB2, hA0, hB0])

/-- `g n = (n+1)^(-1/2)`: the decrement `g n - g (n+1)` is nonnegative. -/
private lemma g_diff_nonneg (n : ℕ) :
    0 ≤ ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) := by
  set A : ℝ := Real.sqrt ((n : ℝ) + 1) with hA
  set B : ℝ := Real.sqrt ((n : ℝ) + 2) with hB
  have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hA0 : 0 < A := by rw [hA]; exact Real.sqrt_pos.mpr hpos1
  have hAB : A ≤ B := by rw [hA, hB]; exact Real.sqrt_le_sqrt (by linarith)
  have e1 : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = 1 / A := by
    rw [Real.rpow_neg hpos1.le, ← Real.sqrt_eq_rpow, ← hA, one_div]
  have e2 : ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) = 1 / B := by
    rw [Real.rpow_neg hpos2.le, ← Real.sqrt_eq_rpow, ← hB, one_div]
  rw [e1, e2]
  have := one_div_le_one_div_of_le hA0 hAB
  linarith

/-- The series of `(n+1)^(-3/2)` is summable. -/
private lemma shift_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Real.summable_nat_rpow).mpr (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) 1).mpr h
  simpa only [Nat.cast_add, Nat.cast_one] using h2

/-- The telescoping series of `g`-differences is summable. -/
private lemma g_diff_summable : Summable (fun n : ℕ =>
    ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ)) := by
  exact Summable.of_nonneg_of_le (fun n => g_diff_nonneg n) (fun n => g_diff_bounds n)
    shift_summable

/-- The telescoping series of `g`-differences sums to one. -/
private lemma g_telescope :
    (∑' n : ℕ, (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ))) = 1 := by
  have key : ∀ n : ℕ, (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ)) =
      ((fun k : ℕ => ((k : ℝ) + 1) ^ (-(1 / 2) : ℝ)) n -
        (fun k : ℕ => ((k : ℝ) + 1) ^ (-(1 / 2) : ℝ)) (n + 1)) := by
    intro n
    have h : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    simp only [h]
  rw [show (∑' n : ℕ, (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ))) =
      ∑' n : ℕ, ((fun k : ℕ => ((k : ℝ) + 1) ^ (-(1 / 2) : ℝ)) n -
        (fun k : ℕ => ((k : ℝ) + 1) ^ (-(1 / 2) : ℝ)) (n + 1)) from tsum_congr key]
  set G : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ (-(1 / 2) : ℝ) with hG
  have hgs : Summable (fun n : ℕ => G n - G (n + 1)) := by
    have h := g_diff_summable
    refine (summable_congr (fun n => ?_)).mp h
    show ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ) = G n - G (n + 1)
    simp only [hG]
    congr 1
    push_cast
    ring
  have hps : ∀ N : ℕ, ∑ i ∈ Finset.range N, (G i - G (i + 1)) = G 0 - G N := by
    intro N
    have h : ∑ i ∈ Finset.range N, (G i - G (i + 1)) =
        -∑ i ∈ Finset.range N, (G (i + 1) - G i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h, Finset.sum_range_sub]
    ring
  have hGtend : Tendsto G atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
    exact h1.comp h2
  have hsum : HasSum (fun n : ℕ => G n - G (n + 1)) (G 0) := by
    rw [hgs.hasSum_iff_tendsto_nat]
    simp only [hps]
    have h3 : Tendsto (fun _ : ℕ => G 0) atTop (nhds (G 0)) := tendsto_const_nhds
    simpa using h3.sub hGtend
  have hG0 : G 0 = 1 := by simp [hG]
  have := hsum.tsum_eq
  rw [this, hG0]

/-- `((n+2) : ℕ)` cast to `ℝ` is `n + 2`. -/
private lemma cast_two (n : ℕ) : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring

/-- The series of `(n+2)^(-3/2)` is summable. -/
private lemma shift2_summable : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-(3 / 2) : ℝ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Real.summable_nat_rpow).mpr (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) 2).mpr h
  refine (summable_congr (fun n => ?_)).mp h2
  rw [cast_two]

/-- `Z = ∑ n^(-3/2)` is at most `3`. -/
private lemma Z_le_three : Z ≤ 3 := by
  have ha : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Real.summable_nat_rpow).mpr (by norm_num)
  have hZ : Z = ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    simp only [Z, Z_term_norm]
  rw [hZ, Summable.tsum_eq_zero_add ha]
  have h0 : ((0 : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) = 0 := by simp
  rw [h0, zero_add]
  -- `∑ (n+1)^(-3/2) = 1 + ∑ (n+2)^(-3/2)`
  have hstep : (∑' b : ℕ, (((b + 1 : ℕ) : ℝ)) ^ (-(3 / 2) : ℝ)) =
      (∑' b : ℕ, ((b : ℝ) + 1) ^ (-(3 / 2) : ℝ)) :=
    tsum_congr (fun b => by
      congr 1
      push_cast
      ring)
  rw [hstep, Summable.tsum_eq_zero_add shift_summable]
  have h0' : (((0 : ℕ) : ℝ) + 1) ^ (-(3 / 2) : ℝ) = 1 := by norm_num
  rw [h0']
  have hstep2 : (∑' b : ℕ, ((((b + 1 : ℕ) : ℝ)) + 1) ^ (-(3 / 2) : ℝ)) =
      (∑' b : ℕ, ((b : ℝ) + 2) ^ (-(3 / 2) : ℝ)) := by
    refine tsum_congr (fun b => ?_)
    have h : (((b + 1 : ℕ) : ℝ)) + 1 = (b : ℝ) + 2 := by push_cast; ring
    rw [h]
  rw [hstep2]
  have hle : (∑' n : ℕ, ((n : ℝ) + 2) ^ (-(3 / 2) : ℝ)) ≤
      ∑' n : ℕ, 2 * (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) - ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ)) :=
    Summable.tsum_le_tsum (fun n => Z_step_le n) shift2_summable (g_diff_summable.mul_left 2)
  have h2 : (∑' n : ℕ, 2 * (((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) -
      ((n : ℝ) + 2) ^ (-(1 / 2) : ℝ))) = 2 := by
    rw [tsum_mul_left, g_telescope]
    norm_num
  linarith



/-! ### The window count for a primitive character, with an explicit constant

Jensen's inequality on the disc of radius `7/5` about `3/2 + iτ` counts the strip zeros right of
the critical line; the ones left of it reflect, by the functional equation, to zeros of the
inverse character right of it, with multiplicity not dropping. The constant is `308 = 4 · 7 · 11`,
from `4` windows, `1/log(7/6) <= 7` and `log(122 Z)/log 2 + 2 <= 11`, which needs only `Z <= 3`. -/

open LeanLab.HardyLittlewood1923.U1482
open LeanLab.PNTPort.DirichletZF.U1482 (RW)
open LeanLab.HardyLittlewood1923.U1479 (IsNTZero reflect_zero)

/-- `Z` is at most three. -/
private lemma log_coef_le_eleven : Real.log (122 * Z) / Real.log 2 + 2 ≤ 11 := by
  have hZ3 : Z ≤ 3 := Z_le_three
  have hZ1 : (1 : ℝ) ≤ Z := one_le_Z
  have h366 : 122 * Z ≤ 366 := by linarith
  have hlog6 : Real.log (122 * Z) ≤ 6 := by
    have h1 : (0 : ℝ) < 122 * Z := by linarith
    have h3 : (366 : ℝ) ≤ Real.exp 6 := by
      have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h4 : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) he.le 6
      have h5 : (366 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      have h6 : (Real.exp 1) ^ 6 = Real.exp 6 := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      linarith [h4, h5, h6.le]
    calc Real.log (122 * Z) ≤ Real.log (Real.exp 6) := Real.log_le_log h1 (h366.trans h3)
      _ = 6 := Real.log_exp 6
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hquot : Real.log (122 * Z) / Real.log 2 ≤ 9 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- `log (7/6)` is at least `1/7`. -/
private lemma one_seventh_le_log : (1 : ℝ) / 7 ≤ Real.log (7 / 6) := by
  have h1 : Real.log (6 / 7 : ℝ) ≤ 6 / 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (7 / 6 : ℝ) = -Real.log (6 / 7) := by
    rw [← Real.log_inv]
    norm_num
  linarith

/-- **Window count for a primitive character.** The strip zeros `t ≤ |Im ρ| ≤ t + 1` of `L(·, χ)`
with multiplicity number at most `308 log (q (t + 2))`. -/
private lemma window_count_primitive (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 0 ≤ t) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1) :
    (∑ ρ ∈ s, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
      308 * Real.log ((q : ℝ) * (t + 2)) := by
  classical
  have hq : q = 1 ∨ χ ≠ 1 := by
    by_cases h : q = 1
    · exact Or.inl h
    · right; intro h1; apply h
      have hprim := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
  have hq' : q = 1 ∨ χ⁻¹ ≠ 1 := hq.imp_right (fun h => inv_ne_one.mpr h)
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  set τ : ℝ := t + 1 / 2 with hτ
  have habs1 : |τ| = |t + 1 / 2| := by rw [hτ]
  have habs2 : |-τ| = |t + 1 / 2| := by rw [abs_neg, hτ]
  set B : ℝ := Real.log (24 * Z * (q : ℝ) * (|t + 1 / 2| + 4) ^ 2) / Real.log (7 / 6) with hB
  let W : ℂ → Prop := fun ρ => IsNTZero χ ρ ∧ t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1
  have hW : ∀ ρ ∈ s, W ρ := by
    intro ρ hρ
    obtain ⟨hL, h0, h1, h2, h3⟩ := hs ρ hρ
    exact ⟨⟨hL, h0, h1⟩, h2, h3⟩
  have mem_hp : ∀ ρ, W ρ → 1 / 2 ≤ ρ.re → 0 ≤ ρ.im →
      ρ ∈ RW (DirichletCharacter.LFunction χ) τ := fun ρ h hr hi =>
    ⟨h.1.1, hr, h.1.2.2, im_window_pos h.2.1 h.2.2 hi⟩
  have mem_hn : ∀ ρ, W ρ → 1 / 2 ≤ ρ.re → ρ.im < 0 →
      ρ ∈ RW (DirichletCharacter.LFunction χ) (-τ) := fun ρ h hr hi =>
    ⟨h.1.1, hr, h.1.2.2, im_window_neg h.2.1 h.2.2 hi⟩
  have mem_lp : ∀ ρ, W ρ → ρ.re < 1 / 2 → 0 ≤ ρ.im →
      1 - ρ ∈ RW (DirichletCharacter.LFunction χ⁻¹) (-τ) := by
    intro ρ h hr hi
    have hz := reflect_zero hχ h.1
    refine ⟨hz.1, by simp; linarith, hz.2.2, ?_⟩
    have e : (1 - ρ).im - -τ = -(ρ.im - τ) := by simp; ring
    rw [e, abs_neg]; exact im_window_pos h.2.1 h.2.2 hi
  have mem_ln : ∀ ρ, W ρ → ρ.re < 1 / 2 → ρ.im < 0 →
      1 - ρ ∈ RW (DirichletCharacter.LFunction χ⁻¹) τ := by
    intro ρ h hr hi
    have hz := reflect_zero hχ h.1
    refine ⟨hz.1, by simp; linarith, hz.2.2, ?_⟩
    have e : (1 - ρ).im - τ = -(ρ.im - -τ) := by simp; ring
    rw [e, abs_neg]; exact im_window_neg h.2.1 h.2.2 hi
  have hmr : ∀ ρ, W ρ → (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) : ℝ) := by
    intro ρ h
    have hρ1 : ρ ≠ 1 := by intro e; have := h.1.2.2; rw [e] at this; simp at this
    have h1ρ : 1 - ρ ≠ 1 := by
      intro e
      have : (1 - ρ).re = 1 := by rw [e]; simp
      simp at this; linarith [h.1.2.1]
    exact mult_le_reflect hχ h.1.2.1 h.1.2.2 (L_analyticAt χ hρ1) (L_ord_ne_top χ⁻¹ hq' h1ρ)
  have inj1 : ∀ S : Finset ℂ, Set.InjOn (fun z : ℂ => 1 - z) (S : Set ℂ) := by
    intro S a _ b _ hab; simpa using hab
  have inj0 : ∀ S : Finset ℂ, Set.InjOn (fun z : ℂ => z) (S : Set ℂ) := by
    intro S a _ b _ hab; simpa using hab
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => 1 / 2 ≤ ρ.re),
    ← Finset.sum_filter_add_sum_filter_not (s.filter fun ρ => 1 / 2 ≤ ρ.re) (fun ρ => 0 ≤ ρ.im),
    ← Finset.sum_filter_add_sum_filter_not (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re) (fun ρ => 0 ≤ ρ.im)]
  have p1 : ∑ ρ ∈ (s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ B := by
    have := sum_le_RW χ hq τ ((s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im))
      (fun z => z) (inj0 _) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact mem_hp ρ (hW ρ hρ.1.1) hρ.1.2 hρ.2)
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) (fun ρ _ => le_rfl)
    rwa [habs1] at this
  have p2 : ∑ ρ ∈ (s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ B := by
    have := sum_le_RW χ hq (-τ) ((s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im))
      (fun z => z) (inj0 _) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact mem_hn ρ (hW ρ hρ.1.1) hρ.1.2 (lt_of_not_ge hρ.2))
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) (fun ρ _ => le_rfl)
    rwa [habs2] at this
  have p3 : ∑ ρ ∈ (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ B := by
    have := sum_le_RW χ⁻¹ hq' (-τ) ((s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im))
      (fun z => 1 - z) (inj1 _) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact mem_lp ρ (hW ρ hρ.1.1) (lt_of_not_ge hρ.1.2) hρ.2)
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
      (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact hmr ρ (hW ρ hρ.1.1))
    rwa [habs2] at this
  have p4 : ∑ ρ ∈ (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤ B := by
    have := sum_le_RW χ⁻¹ hq' τ ((s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im))
      (fun z => 1 - z) (inj1 _) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact mem_ln ρ (hW ρ hρ.1.1) (lt_of_not_ge hρ.1.2) (lt_of_not_ge hρ.2))
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
      (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        exact hmr ρ (hW ρ hρ.1.1))
    rwa [habs1] at this
  have h4B : 4 * B ≤ 308 * Real.log ((q : ℝ) * (t + 2)) := by
    have hlog := log_bound hq1 ht
    have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
    have hlogpos : 0 ≤ Real.log ((q : ℝ) * (t + 2)) :=
      Real.log_nonneg (by nlinarith)
    have hstep : Real.log (24 * Z * (q : ℝ) * (|t + 1 / 2| + 4) ^ 2) ≤
        11 * Real.log ((q : ℝ) * (t + 2)) := by
      refine hlog.trans ?_
      exact mul_le_mul_of_nonneg_right log_coef_le_eleven hlogpos
    have hinv : 1 / Real.log (7 / 6) ≤ 7 := by
      rw [div_le_iff₀ hl76]
      linarith [one_seventh_le_log]
    rw [hB, div_eq_mul_one_div]
    have h4 : (0 : ℝ) ≤ 4 * Real.log ((q : ℝ) * (t + 2)) := by linarith
    calc 4 * (Real.log (24 * Z * (q : ℝ) * (|t + 1 / 2| + 4) ^ 2) * (1 / Real.log (7 / 6)))
        ≤ 4 * ((11 * Real.log ((q : ℝ) * (t + 2))) * 7) := by
          have := mul_le_mul hstep hinv (by positivity) (by positivity)
          nlinarith [this, h4]
      _ = 308 * Real.log ((q : ℝ) * (t + 2)) := by ring
  linarith


/-- LEAF. Shell counting step. The multiplicity weighted number of strip zeros of `L(·, χ)`
with positive imaginary part in the unit window `[n, n+1)` above height `T` is at most
`1600 * ((n+1) * (log (q*(n+1)) + 1))`. This is the one sided analogue of the shell count
used in the two sided exponential counting step, restricted to the positive imaginary part. -/
theorem exp_branch_shell_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (n : ℕ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ T < ρ.im ∧ ⌊ρ.im⌋₊ = n) :
    (∑ ρ ∈ s, (ZeroCount1623.mult χ ρ : ℝ)) ≤
      1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) := by
  classical
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set X : ℝ := (n : ℝ) + 1 with hX
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- the count only sees the primitive character inducing `χ`
  have hsum_eq : (∑ ρ ∈ s, (ZeroCount1623.mult χ ρ : ℝ)) =
      ∑ ρ ∈ s, (analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) ρ : ℝ) := by
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    obtain ⟨hL, h0, h1, _h2, _h3, _h4⟩ := hs ρ hρ
    have hm := mult_eq_primitiveCharacter q χ h0 h1 hL
    rw [hm]
  rw [hsum_eq]
  have hwin : ∀ ρ ∈ s, DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ (n : ℝ) + 1 := by
    intro ρ hρ
    obtain ⟨hL, h0, h1, h2, _h3, h4⟩ := hs ρ hρ
    refine ⟨(lfunction_primitiveCharacter_eq_zero χ h0 h1).mp hL, h0, h1, ?_, ?_⟩
    · rw [abs_of_pos h2]
      have hfl := Nat.floor_le (le_of_lt h2)
      rw [h4] at hfl
      exact hfl
    · rw [abs_of_pos h2]
      have hlt := Nat.lt_succ_floor ρ.im
      rw [h4] at hlt
      have hcast : ((n.succ : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hlt
      linarith
  have hcount := window_count_primitive χ.conductor χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive (n : ℝ) (Nat.cast_nonneg n) s hwin
  -- monotonicity in the modulus
  have hqle : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hmono : 308 * Real.log ((χ.conductor : ℝ) * ((n : ℝ) + 2)) ≤
      308 * Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by
    have hcR : ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqle
    have hpos : (0 : ℝ) < (χ.conductor : ℝ) * ((n : ℝ) + 2) := by
      have : (0 : ℝ) < (χ.conductor : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      positivity
    have hle : (χ.conductor : ℝ) * ((n : ℝ) + 2) ≤ (q : ℝ) * ((n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hcR (by positivity)
    have := Real.log_le_log hpos hle
    linarith
  -- final arithmetic against the leaf's constant
  have hfinal : 308 * Real.log ((q : ℝ) * ((n : ℝ) + 2)) ≤
      1600 * (X * (Real.log ((q : ℝ) * X) + 1)) := by
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hX0 : (0 : ℝ) < X := by linarith
    have hqX : (0 : ℝ) < (q : ℝ) * X := mul_pos hq0 hX0
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlogX : 0 ≤ Real.log ((q : ℝ) * X) := Real.log_nonneg (by nlinarith)
    have harg : (q : ℝ) * ((n : ℝ) + 2) ≤ 2 * ((q : ℝ) * X) := by
      rw [hX]; nlinarith
    have hlog2 : Real.log ((q : ℝ) * ((n : ℝ) + 2)) ≤ Real.log ((q : ℝ) * X) + 1 := by
      have hle := Real.log_le_log (by positivity) harg
      rw [Real.log_mul (by norm_num) hqX.ne'] at hle
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      linarith
    have h308 : (308 : ℝ) ≤ 1600 * X := by nlinarith
    have hL1 : (0 : ℝ) ≤ Real.log ((q : ℝ) * X) + 1 := by linarith
    have hstep := mul_le_mul_of_nonneg_right h308 hL1
    nlinarith [hlog2, hstep]
  linarith

/-- The polynomial comparison behind the shell series. -/
private theorem shell_weight_le (q : ℕ) [NeZero q] (n : ℕ) :
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

/-- LEAF. Summability step. The multiplicity weighted exponential decay series over the
strip zeros of `L(·, χ)` with positive imaginary part above height `T` is summable. The
absolute convergence comes from the logarithmic shell count against the geometric decay
`exp (-0.1598 * n)`; this step says nothing about the size of the total. -/
theorem exp_branch_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) := by
  classical
  have hHsum : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-0.1598 * (n : ℝ))) := by
      simpa [Nat.cast_pow] using
        Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 0.1598)
    have h0 : Summable (fun n : ℕ => Real.exp (-0.1598 * (n : ℝ))) := by
      simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 0.1598)
    have hsum := h1.add h0
    simpa [add_mul, one_mul] using hsum
  refine summable_of_sum_le (c := 6400 * ((q : ℝ) + 1) *
      (∑' n : ℕ, ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))))
    (fun _ => by positivity) (fun u => ?_)
  set k : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ T < ρ.im} → ℕ := fun ρ => ⌊ρ.val.im⌋₊ with hk
  have hkapp : ∀ ρ, k ρ = ⌊ρ.val.im⌋₊ := fun _ => rfl
  have hshell : ∀ n : ℕ, (∑ ρ ∈ u.filter (fun ρ => k ρ = n),
        (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))
      ≤ 1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) *
          Real.exp (-0.1598 * (n : ℝ)) := by
    intro n
    have hcount : (∑ ρ ∈ u.filter (fun ρ => k ρ = n), (ZeroCount1623.mult χ ρ.val : ℝ))
        ≤ 1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) := by
      have himg : (∑ z ∈ (u.filter (fun ρ => k ρ = n)).image Subtype.val,
            (ZeroCount1623.mult χ z : ℝ))
          = ∑ ρ ∈ u.filter (fun ρ => k ρ = n), (ZeroCount1623.mult χ ρ.val : ℝ) :=
        Finset.sum_image (fun x _ y _ h => Subtype.val_injective h)
      rw [← himg]
      refine exp_branch_shell_count q χ T n _ (fun z hz => ?_)
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      have hkn : k ρ = n := (Finset.mem_filter.mp hρ).2
      exact ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, ρ.property.2.2.2.1,
        ρ.property.2.2.2.2, by rw [← hkapp ρ]; exact hkn⟩
    have hw : (∑ ρ ∈ u.filter (fun ρ => k ρ = n),
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))
        ≤ Real.exp (-0.1598 * (n : ℝ)) *
            ∑ ρ ∈ u.filter (fun ρ => k ρ = n), (ZeroCount1623.mult χ ρ.val : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun ρ hρ => ?_)
      have hkn : k ρ = n := (Finset.mem_filter.mp hρ).2
      have him : (n : ℝ) ≤ ρ.val.im := by
        rw [← hkn, hkapp ρ]
        exact Nat.floor_le (le_of_lt ρ.property.2.2.2.1)
      have hexp : Real.exp (-0.1598 * ρ.val.im) ≤ Real.exp (-0.1598 * (n : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hm0 : (0 : ℝ) ≤ (ZeroCount1623.mult χ ρ.val : ℝ) := by positivity
      calc (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)
          ≤ (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp hm0
        _ = Real.exp (-0.1598 * (n : ℝ)) * (ZeroCount1623.mult χ ρ.val : ℝ) := by ring
    have hpos : (0 : ℝ) ≤ Real.exp (-0.1598 * (n : ℝ)) := (Real.exp_pos _).le
    calc (∑ ρ ∈ u.filter (fun ρ => k ρ = n),
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))
        ≤ Real.exp (-0.1598 * (n : ℝ)) *
            ∑ ρ ∈ u.filter (fun ρ => k ρ = n), (ZeroCount1623.mult χ ρ.val : ℝ) := hw
      _ ≤ Real.exp (-0.1598 * (n : ℝ)) *
            (1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1))) :=
          mul_le_mul_of_nonneg_left hcount hpos
      _ = 1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) *
            Real.exp (-0.1598 * (n : ℝ)) := by ring
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image k) (g := k)
    (f := fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))
    (fun ρ hρ => Finset.mem_image_of_mem k hρ)]
  calc ∑ n ∈ u.image k, ∑ ρ ∈ u.filter (fun ρ => k ρ = n),
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)
      ≤ ∑ n ∈ u.image k, 6400 * ((q : ℝ) + 1) *
          (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        have hsw := shell_weight_le q n
        rw [mul_comm (Real.exp (-0.1598 * (n : ℝ)))] at hsw
        exact (hshell n).trans hsw
    _ ≤ ∑' n : ℕ, 6400 * ((q : ℝ) + 1) *
          (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        have hnonneg : ∀ n ∉ u.image k, (0 : ℝ) ≤ 6400 * ((q : ℝ) + 1) *
            (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
          intro n _; positivity
        exact Summable.sum_le_tsum _ hnonneg (hHsum.mul_left _)
    _ = 6400 * ((q : ℝ) + 1) *
          (∑' n : ℕ, ((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ))) := by
        rw [tsum_mul_left]

/-- LEAF. Comparison step. The total of the multiplicity weighted exponential decay series
over the strip zeros of `L(·, χ)` with positive imaginary part above height `T` is at most
the exponential tail integral `expTailIntegral q T`, whose integrand is the same exponential
decay against the density `1/(2π) * log(q t / 2π) + 1/(4t)`. This is the quantitative half
of the branch, and it takes the summability of the weights as a hypothesis so that it is
only the size of the total. -/
theorem exp_branch_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
      TailIntegral123.expTailIntegral q T := by
  sorry

/-- Assembly of the split, FREE-nv-minimax task1602. The statement of
`exp_branch_count_le` character for character, proved from the three leaves with no gap
of its own: the summability leaf gives the first conjunct, and the comparison leaf closes
the second conjunct against `expTailIntegral`. -/
theorem exp_branch_count_le_F1602 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
      TailIntegral123.expTailIntegral q T := by
  classical
  have hs := exp_branch_summable q χ T
  exact ⟨hs, exp_branch_tsum_le q χ T hs⟩

end DecompF1602

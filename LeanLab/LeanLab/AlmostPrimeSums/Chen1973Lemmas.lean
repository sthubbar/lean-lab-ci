/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2217Z-cloud52, unit U-6758, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, read from the lab copy papers/P0002.pdf,
page images. This file continues `Chen1973Own.lean` with Chen's Lemma 4, p. 161:
for `m ≠ 1` and squarefree odd `k`, `|∑*_{χ_k} χ_k(m)| ≤ |(m - 1, k)|`, the sum over primitive
characters mod `k`. Proved here for a PRIME modulus `k = p`, which is the factor Chen's proof
on p. 162 multiplies together: `Z(m, k) = ∏ Z(m, pⱼ)`.
Second, display (28) of Lemma 8, p. 172: `∫_{1/10}^{1/3} log(2 - 3α) / (α(1 - α)) dα ≤ 0.49254`,
proved rigorously by splitting at `1/8`, reusing the lab's PROVED `C2Bound` of P0010 on
`[1/8, 1/3]` and Chen's own tangent-line device `log y ≤ log c + y/c - 1` on `[1/10, 1/8]`.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.C2Bound

open Finset

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Lemmas

/-! ### Lemma 4 for a prime modulus -/

section Lemma4

variable {p : ℕ} [hp : Fact p.Prime]

/-- For a prime modulus, a Dirichlet character is primitive iff it is not trivial. -/
theorem isPrimitive_iff_ne_one_of_prime (χ : DirichletCharacter ℂ p) :
    χ.IsPrimitive ↔ χ ≠ 1 := by
  rw [DirichletCharacter.isPrimitive_def, Ne, DirichletCharacter.eq_one_iff_conductor_eq_one]
  rcases hp.out.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h | h
  · rw [h]; simp [hp.out.one_lt.ne]
  · rw [h]; simp [hp.out.one_lt.ne']

open Classical in
/-- **Chen's sum over primitive characters mod a prime, exact value**:
`∑*_{χ mod p} χ(a) = p - 2` if `a = 1`, `0` if `a = 0`, and `-1` otherwise. This is Chen's
`Z(m, p)` on p. 162 before taking absolute values. -/
theorem sum_primitive_prime (a : ZMod p) :
    ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive), χ a =
      if a = 1 then (p : ℂ) - 2 else if a = 0 then 0 else -1 := by
  classical
  have hfilt : univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive) = univ.erase 1 := by
    ext χ; simp [isPrimitive_iff_ne_one_of_prime]
  rw [hfilt, sum_erase_eq_sub (mem_univ _), DirichletCharacter.sum_characters_eq ℂ a,
    Nat.totient_prime hp.out]
  have hp1 : (1 : ℕ) ≤ p := hp.out.one_lt.le
  split_ifs with h1 h0
  · subst h1; rw [map_one]; push_cast [hp1]; ring
  · subst h0; simpa using MulChar.map_nonunit (1 : DirichletCharacter ℂ p) not_isUnit_zero
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr h0
    rw [MulChar.one_apply hu]; ring

open Classical in
/-- **Chen 1973, Lemma 4, for a prime modulus**: for every integer `m` and prime `p`,
`|∑*_{χ mod p} χ(m)| ≤ (m - 1, p)`. Chen assumes `m ≠ 1` and `k` odd; neither is needed for a
prime modulus, since for `m = 1` the sum is `p - 2 ≤ p = (0, p)`. -/
theorem chen_lemma4_prime (m : ℤ) :
    ‖∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive), χ (m : ZMod p)‖ ≤
      (Int.gcd (m - 1) p : ℝ) := by
  rw [sum_primitive_prime]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hgpos : 1 ≤ Int.gcd (m - 1) p :=
    Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hp.out.ne_zero)
  split_ifs with h1 h0
  · -- `m ≡ 1 (mod p)`: the gcd is `p`
    have hdvd : (p : ℤ) ∣ m - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1, sub_self]
    have hg : Int.gcd (m - 1) p = p := by
      rw [Int.gcd, Int.natAbs_natCast]
      exact Nat.gcd_eq_right (Int.natCast_dvd.mp hdvd)
    rw [hg, show (p : ℂ) - 2 = ((p - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · simp only [norm_zero]; positivity
  · rw [norm_neg, norm_one]; exact_mod_cast hgpos

/-- Vacuity check, `p = 5`, `m = 6`: the bound reads `‖5 - 2‖ ≤ 5`. -/
example : (Int.gcd (6 - 1) 5 : ℝ) = 5 := by norm_num

end Lemma4

/-! ### Display (28), Lemma 8 -/

section Display28

open Real intervalIntegral

/-- Chen's integrand in (28). -/
def f28 (α : ℝ) : ℝ := log (2 - 3 * α) / (α * (1 - α))

lemma f28_cont {a b : ℝ} (ha : 0 < a) (hb : b < 1 / 2) (hab : a ≤ b) :
    ContinuousOn f28 (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro x hx; linarith [hx.2]
  · fun_prop
  · intro x hx
    have : 0 < x * (1 - x) := by apply mul_pos <;> linarith [hx.1, hx.2]
    exact this.ne'

/-- **Chen's tangent bound, pointwise**: for `c > 0`, `0 < α < 2/3`, `α < 1`,
`f28 α ≤ (log c - 1 + 2/c)/α + (log c - 1 - 1/c)/(1 - α)`, from `log y ≤ log c + y/c - 1`. -/
lemma f28_le_tangent {c α : ℝ} (hc : 0 < c) (h0 : 0 < α) (h1 : α < 2 / 3) :
    f28 α ≤ (log c - 1 + 2 / c) / α + (log c - 1 - 1 / c) / (1 - α) := by
  have hy : 0 < 2 - 3 * α := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hl : log (2 - 3 * α) ≤ log c + (2 - 3 * α) / c - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy hc)
    rw [Real.log_div hy.ne' hc.ne'] at this
    linarith
  have hd : 0 < α * (1 - α) := mul_pos h0 h1α
  have e : (log c - 1 + 2 / c) / α + (log c - 1 - 1 / c) / (1 - α) =
      (log c + (2 - 3 * α) / c - 1) / (α * (1 - α)) := by
    field_simp; ring
  rw [f28, e]
  exact div_le_div_of_nonneg_right hl hd.le

/-- The integral of the tangent bound in closed form. -/
lemma integral_tangent {a b A B : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∫ α in a..b, (A / α + B / (1 - α)) = A * log (b / a) + B * log ((1 - a) / (1 - b)) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x ∧ 0 < 1 - x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; constructor <;> linarith [hx.1, hx.2]
  have hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => A * log x - B * log (1 - x)) (A / x + B / (1 - x)) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := hpos x hx
    have h1' : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have := ((Real.hasDerivAt_log h0.ne').const_mul A).sub ((h1'.log h1.ne').const_mul B)
    convert this using 1
    field_simp; ring
  have hcont : ContinuousOn (fun x : ℝ => A / x + B / (1 - x)) (Set.uIcc a b) := by
    intro x hx
    obtain ⟨h0, h1⟩ := hpos x hx
    exact ((continuousAt_const.div continuousAt_id h0.ne').add
      (continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1.ne')).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable,
    Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
  ring

/-- Rational bounds for `-log(1 - x)` from the series, `0 ≤ x < 1`. -/
lemma neg_log_one_sub_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (i + 1) / (i + 1) - x ^ (n + 1) / (1 - x) ≤ -log (1 - x) ∧
      -log (1 - x) ≤ ∑ i ∈ range n, x ^ (i + 1) / (i + 1) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have z := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0, abs_le] at z
  constructor <;> linarith [z.1, z.2]

/-- **Chen (28) on `[1/10, 1/8]`**, the tangent bound at `c = 133/80`:
`∫_{1/10}^{1/8} f28 ≤ 0.12794`. The true value is about `0.127920`. -/
theorem integral28_low : ∫ α in (1 / 10 : ℝ)..(1 / 8), f28 α ≤ 0.12794 := by
  set c : ℝ := 133 / 80
  have hmono := integral_mono_on (μ := MeasureTheory.volume) (a := (1 / 10 : ℝ)) (b := 1 / 8)
    (by norm_num) ((f28_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
    (f := f28) (g := fun α => (log c - 1 + 2 / c) / α + (log c - 1 - 1 / c) / (1 - α))
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      intro x hx
      have h0 : x ≠ 0 := by linarith [hx.1]
      have h1 : 1 - x ≠ 0 := by linarith [hx.2]
      exact ((continuousAt_const.div continuousAt_id h0).add
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1)).continuousWithinAt)
    (fun α hα => f28_le_tangent (by norm_num) (by linarith [hα.1]) (by linarith [hα.2]))
  rw [integral_tangent (by norm_num) (by norm_num) (by norm_num)] at hmono
  -- logarithm bounds
  have eL : log c = -log (1 - 53 / 133) := by
    rw [show (1 : ℝ) - 53 / 133 = c⁻¹ by norm_num, Real.log_inv, neg_neg]
  have eV : log ((1 / 8 : ℝ) / (1 / 10)) = -log (1 - 1 / 5) := by
    rw [show (1 / 8 : ℝ) / (1 / 10) = (1 - 1 / 5)⁻¹ by norm_num, Real.log_inv]
  have eW : log ((1 - 1 / 10 : ℝ) / (1 - 1 / 8)) = -log (1 - 1 / 36) := by
    rw [show (1 - 1 / 10 : ℝ) / (1 - 1 / 8) = (1 - 1 / 36)⁻¹ by norm_num, Real.log_inv]
  obtain ⟨L1, L2⟩ := neg_log_one_sub_bounds (x := 53 / 133) (by norm_num) (by norm_num) 24
  obtain ⟨V1, V2⟩ := neg_log_one_sub_bounds (x := 1 / 5) (by norm_num) (by norm_num) 12
  obtain ⟨W1, W2⟩ := neg_log_one_sub_bounds (x := 1 / 36) (by norm_num) (by norm_num) 6
  rw [eL, eV, eW] at hmono
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at L1 L2 V1 V2 W1 W2
  norm_num at L1 L2 V1 V2 W1 W2 hmono ⊢
  generalize log (80 / 133 : ℝ) = a at *
  generalize log (4 / 5 : ℝ) = b at *
  generalize log (35 / 36 : ℝ) = d at *
  nlinarith [L1, L2, V1, V2, W1, W2]

/-- **Chen 1973, display (28), PROVED**:
`∫_{1/10}^{1/3} log(2 - 3α) / (α(1 - α)) dα ≤ 0.49254`. Split at `1/8`: the lower piece by
`integral28_low`, at most `0.12794`, the upper piece by the lab's PROVED `C2Bound` of P0010,
below `0.36309`; the sum is below `0.49103`. The true value is about `0.490995`. -/
theorem chen_display28 :
    ∫ α in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * α) / (α * (1 - α)) ≤ 0.49254 := by
  have hc2 := LeanLab.ChenExplicit.Yamada.c2Bound
  unfold LeanLab.ChenExplicit.Yamada.C2Bound LeanLab.ChenExplicit.Yamada.c2 at hc2
  have hsplit := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (a := (1 / 10 : ℝ))
    (b := 1 / 8) (c := 1 / 3) (f := f28)
    ((f28_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
    ((f28_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
  have hlow := integral28_low
  unfold f28 at hsplit hlow
  rw [← hsplit]
  norm_num at hc2 hlow ⊢
  linarith

/-- Lemma 8's constant from the integral: `8 · ∫ ≤ 8 · 0.49254 ≤ 3.9404`, the value Chen uses
in (27) to get `Ω ≤ 3.9404 x C_x / (log x)²`. -/
theorem lemma8_from_display28 :
    8 * ∫ α in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * α) / (α * (1 - α)) ≤ 3.9404 := by
  have := chen_display28
  linarith

end Display28

/-! ### Display (25), the first equality, pointwise -/

section Display25

open ArithmeticFunction

/-- **Chen's rewriting in (25), pointwise**: for squarefree `k`,
`∏_{p ∣ k} (1/(p-1))(1 + 1/(p-2)) = ∑_{q r = k} 1/(ψ(q) φ(q)) · 1/φ(r)` with, on squarefree
arguments, `1/(ψ(q)φ(q)) = ∏_{p ∣ q} 1/((p-2)(p-1))` and `1/φ(r) = ∏_{p ∣ r} 1/(p-1)`. With
`chen_inv_totient` this is Chen's `μ²(k)/φ(k) ∏_{p∣k}(1 + 1/(p-2)) = ∑_{q ∣ k} μ²(q)/(ψ(q)φ(q)) ·
μ²(k/q)/φ(k/q)`, the step from the first to the second expression of `S` on p. 171. -/
theorem chen25_pointwise {k : ℕ} (hk : Squarefree k) :
    ∏ p ∈ k.primeFactors, (1 / ((p : ℝ) - 1) * (1 + 1 / ((p : ℝ) - 2))) =
      ∑ x ∈ k.divisorsAntidiagonal,
        (∏ p ∈ x.1.primeFactors, 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) *
          ∏ p ∈ x.2.primeFactors, 1 / ((p : ℝ) - 1) := by
  have h := IsMultiplicative.prodPrimeFactors_add_of_squarefree
    (IsMultiplicative.prodPrimeFactors (fun p : ℕ => 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))))
    (IsMultiplicative.prodPrimeFactors (fun p : ℕ => 1 / ((p : ℝ) - 1))) hk
  rw [prodPrimeFactors_apply hk.ne_zero, mul_apply] at h
  have hl : ∀ p ∈ k.primeFactors,
      ((prodPrimeFactors fun p : ℕ => 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) +
        (prodPrimeFactors fun p : ℕ => 1 / ((p : ℝ) - 1))) p =
        1 / ((p : ℝ) - 1) * (1 + 1 / ((p : ℝ) - 2)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [ArithmeticFunction.add_apply, prodPrimeFactors_apply hpp.ne_zero, prodPrimeFactors_apply hpp.ne_zero,
      hpp.primeFactors, prod_singleton, prod_singleton]
    have h1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      linarith
    by_cases h2 : (p : ℝ) - 2 = 0
    · rw [h2]; simp
    · field_simp; ring
  rw [prod_congr rfl hl] at h
  rw [h]
  refine sum_congr rfl fun x hx => ?_
  have hx1 : x.1 ≠ 0 := by
    rintro h0; have := Nat.fst_mem_divisors_of_mem_antidiagonal hx; simp [h0] at this
  have hx2 : x.2 ≠ 0 := by
    rintro h0; have := Nat.snd_mem_divisors_of_mem_antidiagonal hx; simp [h0] at this
  rw [prodPrimeFactors_apply hx1, prodPrimeFactors_apply hx2]

/-- For squarefree `n`, `1/φ(n) = ∏_{p ∣ n} 1/(p-1)`, the reading of the factors in
`chen25_pointwise`. -/
theorem chen_inv_totient {n : ℕ} (hn : Squarefree n) :
    1 / (n.totient : ℝ) = ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have h' : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [mul_comm] at h; exact Nat.eq_of_mul_eq_mul_left hn0 h
  rw [h', Nat.cast_prod, one_div, ← prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  have := (Nat.prime_of_mem_primeFactors hp).one_le
  push_cast [this]; rw [one_div]

end Display25

end LeanLab.AlmostPrimeSums.Chen1973Lemmas

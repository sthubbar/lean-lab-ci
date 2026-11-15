/-
P0069 Baker, Harman and Pintz 1997, pages 16, 26, 27, 41 and 42, read from the page images
papers/P0069-original.pdf.
Three small genuine steps on the route to upper_mean_value_supply of Decomp312b.
Page 26 to 27: the truncation step "It now suffices to prove 4.10, 4.11, 4.12".
Page 42: the sentence after the proof of Lemma 28, "We can therefore give an asymptotic
formula if n6 >= x^0.18", against Lemma 3 iii of page 16, and the domain of the displayed
five dimensional integral of the discarded regions.
Nothing here proves upper_mean_value_supply, which stays a hypothesis of its consumers.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp529a

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex DecompC165b

/-- P0069 Baker Harman Pintz 1997, page 26, the display before 4.10 and the sentence
"It now suffices to prove 4.10, 4.11, 4.12", with page 27 display 4.13.
The page splits the sum of c_k chi(k) as the sum of c'_k chi(k) plus O of the sum of the
nonnegative c''_k. Here c is the actual coefficient, a is the truncated one c', and e is a
nonnegative majorant of the pointwise error, a constant times c''. If the sum of e over
I = (x - 2Y, x] is O(Y L^(-A)) for every A, which is what 4.11 and 4.12 give together, then c
and a agree on I in the absolute sense of ShortApproximation.
The hypothesis hsmall is condition i of page 3, display 1.7, with density 0. Only its case
q = 1, trivial character, t = x is used, so hsmall is stronger than the printed 4.11 with 4.12.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `|c(k) - a(k)| ≤ e(k)` on I and `Σ_{k ∈ I} e(k) ≪ Y L^(-A)` give
`Σ_{k ∈ I} |c(k) - a(k)| ≪ Y L^(-A)`. -/
theorem short_approximation_of_majorant {ε : ℝ} {c a e : ℝ → ℕ → ℝ}
    (hmaj : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ k ∈ leftInterval ε x, |c x k - a x k| ≤ e x k)
    (hsmall : Decomp312c.CharacterDistribution ε 0 e) :
    Decomp312c.ShortApproximation ε c a := by
  intro A hA
  obtain ⟨X, hX⟩ := hmaj
  obtain ⟨C0, hC0⟩ := hsmall A hA
  refine ⟨C0, max (max C0 X) (Real.exp 1), fun x hx => ?_⟩
  have hxC : C0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxX : X ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hlogA : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hlog1 hA.le
  have hh := hC0 x hxC 1 le_rfl (by simpa using hlogA) 1 x le_rfl
  have hfilter : (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ x) = leftInterval ε x := by
    apply Finset.filter_true_of_mem
    intro k hk
    have hk2 : k ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hk).2
    exact (Nat.cast_le.mpr hk2).trans (Nat.floor_le hx0.le)
  have he : (∑ k ∈ leftInterval ε x,
      ((e x k : ℂ) * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) -
        Thm2.delta (1 : DirichletCharacter ℂ 1) * ((0 : ℝ) : ℂ) / (Real.log x : ℂ))) =
      ((∑ k ∈ leftInterval ε x, e x k : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : (k : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [h1, map_one]
    ring
  rw [hfilter, he, Complex.norm_real, Real.norm_eq_abs] at hh
  calc ∑ k ∈ leftInterval ε x, |c x k - a x k|
      ≤ ∑ k ∈ leftInterval ε x, e x k := Finset.sum_le_sum fun k hk => hX x hxX k hk
    _ ≤ |∑ k ∈ leftInterval ε x, e x k| := le_abs_self _
    _ ≤ C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hh

/-- P0069 Baker Harman Pintz 1997, page 42, the two sentences after the proof of Lemma 28,
"Note that in a region C5 with n1 n2 n3 >= x^0.46 we have n4 >= x^0.15. We can therefore give
an asymptotic formula if n6 >= x^0.18", checked against Lemma 3 iii of page 16 with its
standing conditions LMNR = X, 3.23 qT <= X^(0.45 - eps/2) and 3.24 M >= qT. Page 16 prints
iii as N >> X^0.15, R^2 L >> X^0.45, L >> X^0.18.
Exponents in units of log x, ordered a <= b <= c <= d <= e as in Lemma 28 of page 41, with
the roles M = n1 n2 n3, N = n4, R = n5, L = n6. The page does not name the roles; this is
the reading under which all four exponent conditions hold. No positivity is needed.
Only the exponent arithmetic is checked here, not conditions 3.1 and 3.2 of Lemma 3.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `0.46 ≤ a+b+c` and `0.18 ≤ f` give `a+b+c > 0.45`, `d ≥ 0.15`,
`2e + f ≥ 0.45`, `f ≥ 0.18`, and the four exponents sum to 1. -/
theorem c5_asymptotic_of_n6 {a b c d e f : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e + f = 1) (h3 : 0.46 ≤ a + b + c)
    (h6 : 0.18 ≤ f) :
    (0.45 : ℝ) < a + b + c ∧ 0.15 ≤ d ∧ 0.45 ≤ 2 * e + f ∧ 0.18 ≤ f ∧
      (a + b + c) + d + e + f = 1 := by
  refine ⟨by linarith, by linarith, by linarith, h6, by linarith⟩

/-- P0069 Baker Harman Pintz 1997, page 42, the domain printed under the displayed five
dimensional integral of the discarded regions:
alpha1 <= alpha2 <= alpha3 <= alpha4 <= alpha5 <= 1 - alpha1 - ... - alpha5 < 0.18 with
0.46 <= alpha1 + alpha2 + alpha3 <= 0.5.
For six ordered exponents with sum 1, 0.46 <= a + b + c and f < 0.18, which is the discarded
case complementary to c5_asymptotic_of_n6, the first five exponents lie in the region
upperFiveRegion of Decomp529a. The printed upper bound 0.5 is not assumed: it follows from
the ordering and the sum, since a + b + c <= d + e + f.
PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `a ≤ b ≤ c ≤ d ≤ e ≤ f`, `a+b+c+d+e+f = 1`, `0.46 ≤ a+b+c`, `f < 0.18`
give `(a,b,c,d,e) ∈ upperFiveRegion`. -/
theorem discarded_c5_mem_upperFiveRegion {a b c d e f : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hde : d ≤ e) (hef : e ≤ f) (hs : a + b + c + d + e + f = 1)
    (h3 : 0.46 ≤ a + b + c) (h6 : f < 0.18) :
    (![a, b, c, d, e] : Fin 5 → ℝ) ∈ Decomp529a.upperFiveRegion := by
  have hsum : (∑ i, (![a, b, c, d, e] : Fin 5 → ℝ) i) = a + b + c + d + e := by
    simp [Fin.sum_univ_succ]
    ring
  have hf : 1 - (∑ i, (![a, b, c, d, e] : Fin 5 → ℝ) i) = f := by
    rw [hsum]
    linarith
  change a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧
    e ≤ 1 - (∑ i, (![a, b, c, d, e] : Fin 5 → ℝ) i) ∧
    1 - (∑ i, (![a, b, c, d, e] : Fin 5 → ℝ) i) < 0.18 ∧
    0.46 ≤ a + b + c ∧ a + b + c ≤ 0.5
  rw [hf]
  exact ⟨hab, hbc, hcd, hde, hef, h6, h3, by linarith⟩

end LeanLab.BHP1997.Upper312Route

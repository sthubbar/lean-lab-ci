/-
Split of the sealed statement `lemma10` of `LeanLab.ExceptionalSet.State1539`, which is
Lemma 10 of J. Brudern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst.
Fourier 48 (1998), p. 370-371, along the proof of its source:

A. A. Karacuba, Estimates of trigonometric sums by the method of I. M. Vinogradov and their
applications, Trudy Mat. Inst. Steklov 112 (1971) 241-255, Russian original, in the lab
at `papers/Karacuba1971-TrudyMIAN112.pdf`. Chapter I, section 1 lists Lemmas 1 to 5 on
p. 243-244; section 2 states Theorem 1 on p. 244 and proves it on p. 245-248.

Brudern-Perelli p. 371: "This is Theorem 1 of Karacuba [K], with a change of notation, our
k is Karacuba's n + 1, c0 = δ, c1 = Θ0 etc." All formulas below were read from the page
images rendered at 160 and 300 dpi, not from the OCR.

Structure.
* `KaracubaTheorem1`: Theorem 1 of p. 244, in Karacuba's own notation.
* `lemma10_of_thm1`: PROVED. The notation bridge: `Lemma10` from `KaracubaTheorem1` and
  `LeafS1Case`, the one case of the lab class that Karacuba's Theorem 1 does not cover,
  `S = {1}`, see the QUESTION on `LeafS1Case`.
* `karacubaTheorem1_of_cases`: PROVED. Theorem 1 from its two cases, p. 245 `n ≥ n0` and
  p. 248 `2 ≤ n < n0`, each under the reduction "it suffices to treat `P ≥ e^{c n²}`",
  p. 245 line 1, which is proved here too.
* Leaves: Lemma 1, Vinogradov's mean value theorem, CITED; Lemma 2, Vinogradov's Weyl sum
  estimate, CITED; Lemma 3, a classical elementary sum, LEAF; the bound on `W(a)` in the
  large `n` case, p. 245-248, as a deduction from Lemmas 1, 3 and 4, LEAF; the small `n`
  case, p. 248, as a deduction from Lemma 2, LEAF; and `LeafS1Case`, QUESTION.
* The large `n` case from the bound on `W(a)`: display (3), the shift by `yz`, and the
  summation over `a`, with the endpoint repair noted at `KarWBound`: PROVED.
* Lemma 4, Holder's inequalities a and b, p. 244: PROVED.

Wired 2026-11-12, coordinator decision 5: the content of this file now lives in
`KaracubaCore.lean`, below State1539, whose `lemma10` is `KaracubaCore.lemma10_of_karacuba`.
Each leaf of this file is discharged one for one by the leaf of the same name in
KaracubaCore, statements unchanged, so every leaf has one open copy, in KaracubaCore. There
`leaf_small_case` is proved from the narrower LEAF `KaracubaCore.leaf_T_bound` with the
endpoint repair of p. 248 explicit, and `KaracubaCore.Lemma10Kar` gives a route that avoids
`leaf_s1_case`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.KaracubaCore

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Karacuba's notation -/

/-- The hypotheses of Karacuba's Theorem 1, p. 244, for the interval `N ≤ x ≤ N + P` with
`N, P` integers, here `N` natural, `n ≥ 2` and the set `T = {s_1, ..., s_r}`:
`f^{(n+1)}` continuous, asked here as `C^{n+1}` on an open set around the interval;
a) `|f^{(n+1)}(x)/(n+1)!| ≤ P^{-c1 (n+1)}`;
`2 ≤ s_j ≤ n`, `c0 n ≤ r`; b) `P^{-c2 s_j} ≤ |f^{(s_j)}(x)/s_j!| ≤ P^{-c3 s_j}`.
Karacuba does not say that the `s_j` are distinct, but his proof uses it, p. 245 line -4,
`s_1 + ... + s_r ≥ 0.25 c0² n²`; a `Finset` makes them distinct. `r ≤ n` follows from
`T ⊆ [2, n]`. -/
def KarHyp (c0 c1 c2 c3 : ℝ) (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) : Prop :=
  (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1 : ℕ) f U) ∧
  (∀ x ∈ Set.Icc (N : ℝ) (N + P),
      |iteratedDeriv (n + 1) f x / (n + 1).factorial| ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ)))) ∧
  T ⊆ Finset.Icc 2 n ∧ c0 * n ≤ T.card ∧
  ∀ s ∈ T, ∀ x ∈ Set.Icc (N : ℝ) (N + P),
    (P : ℝ) ^ (-(c2 * s)) ≤ |iteratedDeriv s f x / s.factorial| ∧
    |iteratedDeriv s f x / s.factorial| ≤ (P : ℝ) ^ (-(c3 * s))

/-- Theorem 1 of Karacuba, chapter I section 2, p. 244: for positive constants
`c0, ..., c4` with `c0 < 1`, `c1 < 1`, `c2 + c4 < c1` there are `A, γ > 0` such that, under
`KarHyp`, for every integer `0 < P₁ ≤ P`,
`|Σ_{x=N}^{N+P₁-1} e(f(x))| ≤ A P^{1-γ/n²}`. "Absolute constants" in the paper means
depending on `c0, ..., c4` only, so `A, γ` come after the `c`'s. -/
def KaracubaTheorem1 : Prop :=
  ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
    c0 < 1 → c1 < 1 → c2 + c4 < c1 →
    ∃ A γ : ℝ, 0 < A ∧ 0 < γ ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n → ∀ (f : ℝ → ℝ) (T : Finset ℕ),
      KarHyp c0 c1 c2 c3 N P n f T → ∀ P₁ : ℕ, 0 < P₁ → P₁ ≤ P →
        ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ A * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2)

/-- One case of Theorem 1, for the `n` with `pred n`, after the reduction of p. 245 line 1:
"it suffices to treat `P ≥ e^{c n²}`, `c > 0` some absolute constant". -/
def KarCase (c0 c1 c2 c3 : ℝ) (pred : ℕ → Prop) : Prop :=
  ∃ A γ cc : ℝ, 0 < A ∧ 0 < γ ∧ 0 < cc ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n → pred n →
    Real.exp (cc * (n : ℝ) ^ 2) ≤ P → ∀ (f : ℝ → ℝ) (T : Finset ℕ),
      KarHyp c0 c1 c2 c3 N P n f T → ∀ P₁ : ℕ, 0 < P₁ → P₁ ≤ P →
        ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ A * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2)

/-- `n0 = max(12, 1/√c1, 1/∛(c1 - (c2 + c4)))`, p. 245. -/
noncomputable def karN0 (c1 c2 c4 : ℝ) : ℝ :=
  max 12 (max (1 / Real.sqrt c1) (1 / (c1 - (c2 + c4)) ^ ((1 : ℝ) / 3)))

/-! ### Karacuba's Lemmas 1 to 4, chapter I section 1, p. 243-244 -/

/-- Lemma 1, p. 243, Vinogradov's mean value theorem, Karacuba's reference [1]: for
`n ≥ 12` put `D_t = (20n)^{n(n+1)t/2}`, `b_t = nt + [n(n+1)/4 + 1]`; then for `l > 0` and
integer `b ≥ b_l`,
`∫_{[0,1]^n} |Σ_{x=1}^P e(α_n x^n + ... + α_1 x)|^{2b} dα < D_l P^{2b - n(n+1)/2 + n(n+1)/2 (1-1/n)^l}`.
`l` is a positive integer, as in its one use, p. 245; `α j` is `α_{j+1}`. -/
def KarLemma1 : Prop :=
  ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ b : ℕ,
    n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ ≤ b → ∀ P : ℕ, 0 < P →
    ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * b)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * b : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l)

/-- Karacuba's `τ` of Lemma 2, p. 243: `q = P^τ` if `1 < q ≤ P`; `τ = 1` if
`P < q ≤ P^{r-1}`; `q = P^{r-τ}` if `P^{r-1} < q < P^r`. -/
noncomputable def karTau (P q : ℝ) (r : ℕ) : ℝ :=
  if q ≤ P then Real.log q / Real.log P
  else if q ≤ P ^ (r - 1) then 1 else r - Real.log q / Real.log P

/-- Lemma 2, p. 243-244, Vinogradov, Karacuba's reference [2]: for positive integers
`m, P`, `f(x) = α_{n+1} x^{n+1} + ... + α_1 x`, `n ≥ 1`, `r` one of `2, ..., n+1`,
`α_r = a/q + θ/q²`, `(a, q) = 1`, `1 < q < P^r`, `|θ| ≤ 1` by the paper's convention p. 241,
with `τ` as in `karTau`, `l = log(12 n (n+1)/τ)`, `ρ = τ/(3 n² l)`:
`|Σ_{x=1}^P e(m f(x))| < (8n)^{0.5 n l} m^{2ρ/τ} P^{1-ρ}`. -/
def KarLemma2 : Prop :=
  ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ)

/-- The distance `(γ)` from `γ` to the nearest integer, p. 244. -/
noncomputable def nint (γ : ℝ) : ℝ := min (Int.fract γ) (1 - Int.fract γ)

/-- Lemma 3, p. 244, Karacuba's reference [2]: for `U > 0`, `q ≥ 1`, `α = a/q + θ/q²`,
`(a, q) = 1`, `|θ| ≤ 1`, every real `β`:
`Σ_{x=1}^P min(U, 1/(αx + β)) ≤ 6 (U + q log q)(P/q + 1)`. Where `(αx + β) = 0` Lean's
`1/0 = 0` makes the summand `0`, which only weakens the statement. -/
def KarLemma3 : Prop :=
  ∀ (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ), 0 < U → 1 ≤ q → Int.gcd a q = 1 → |θ| ≤ 1 →
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1)

/-- Lemma 4, p. 244, Holder's inequalities: for nonnegative `u_ν, v_ν`, `ν = 1, ..., P`, and
integer `k ≥ 1`: a) `(Σ u)^k ≤ P^{k-1} Σ u^k`; b) `(Σ u v)^k ≤ (Σ u)^{k-1} Σ u v^k`. -/
def KarLemma4 : Prop :=
  ∀ (P k : ℕ) (u v : ℕ → ℝ), 1 ≤ k → (∀ ν, 0 ≤ u ν) → (∀ ν, 0 ≤ v ν) →
    (∑ ν ∈ Finset.Icc 1 P, u ν) ^ k ≤ (P : ℝ) ^ (k - 1) * ∑ ν ∈ Finset.Icc 1 P, u ν ^ k ∧
    (∑ ν ∈ Finset.Icc 1 P, u ν * v ν) ^ k ≤
      (∑ ν ∈ Finset.Icc 1 P, u ν) ^ (k - 1) * ∑ ν ∈ Finset.Icc 1 P, u ν * v ν ^ k

/-! ### Lemma 4, proved -/

/-- Holder in weighted form on any finite set, the core of Lemma 4 b. -/
theorem holder_weighted {ι : Type*} (s : Finset ι) (k : ℕ) (hk : 1 ≤ k) (u v : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    (∑ i ∈ s, u i * v i) ^ k ≤ (∑ i ∈ s, u i) ^ (k - 1) * ∑ i ∈ s, u i * v i ^ k := by
  set U := ∑ i ∈ s, u i with hUdef
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => hu i)
  rcases hU0.eq_or_lt with hU | hU
  · have hzero : ∀ i ∈ s, u i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hu i)).1 hU.symm
    have h1 : ∑ i ∈ s, u i * v i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul])
    have h2 : ∑ i ∈ s, u i * v i ^ k = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul])
    rw [h1, h2, zero_pow (by omega), mul_zero]
  · have hw : ∀ i ∈ s, 0 ≤ u i / U := fun i _ => div_nonneg (hu i) hU.le
    have hw1 : ∑ i ∈ s, u i / U = 1 := by
      rw [← Finset.sum_div, ← hUdef, div_self hU.ne']
    have key := Real.pow_arith_mean_le_arith_mean_pow s (fun i => u i / U) v hw hw1
      (fun i _ => hv i) k
    simp only [div_mul_eq_mul_div] at key
    rw [← Finset.sum_div, ← Finset.sum_div, div_pow] at key
    have hUk : 0 < U ^ k := pow_pos hU k
    rw [div_le_div_iff₀ hUk hU] at key
    have hpow : U ^ k = U ^ (k - 1) * U := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow] at key
    have := le_of_mul_le_mul_right (by linarith [key] : (∑ i ∈ s, u i * v i) ^ k * U ≤
      (U ^ (k - 1) * ∑ i ∈ s, u i * v i ^ k) * U) hU
    linarith

/-- PROVED. Lemma 4 of Karacuba, p. 244, both parts; part a is part b with `u = 1`. -/
theorem karLemma4 : KarLemma4 := by
  intro P k u v hk hu hv
  refine ⟨?_, holder_weighted _ k hk u v hu hv⟩
  have h := holder_weighted (Finset.Icc 1 P) k hk (fun _ => (1 : ℝ)) u (fun _ => zero_le_one) hu
  simpa using h

/-! ### Leaves -/

/-- LEAF, CITED. Karacuba's Lemma 1, p. 243, the mean value theorem of Vinogradov, his
reference [1], I. M. Vinogradov, The method of trigonometric sums in the theory of numbers,
in the exact form stated there. It is the one input of the large `n` case from outside.
The modern work of Wooley and of Bourgain, Demeter and Guth is related, but it carries
ε-losses and non explicit constants, so it does not give this explicit form; not ported. -/
theorem leaf_karLemma1_mvt : KarLemma1 := KaracubaCore.leaf_karLemma1_mvt

/-- LEAF, CITED. Karacuba's Lemma 2, p. 243-244, Vinogradov's estimate of a Weyl sum from a
rational approximation of one coefficient, his reference [2]. Used only in the small `n`
case, p. 248. -/
theorem leaf_karLemma2 : KarLemma2 := KaracubaCore.leaf_karLemma2

/-- LEAF. Karacuba's Lemma 3, p. 244, his reference [2]: the classical bound for
`Σ min(U, 1/(αx+β))`. Now PROVED in KaracubaCore by `karL3_main`. -/
theorem leaf_karLemma3 : KarLemma3 := KaracubaCore.leaf_karLemma3

/-- `P2 = [P^{0.5 c1 - 0.5/(n²(n+1))}]`, Karacuba p. 245. -/
noncomputable def karP2 (c1 : ℝ) (n P : ℕ) : ℕ :=
  ⌊(P : ℝ) ^ (c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))))⌋₊

/-- `W(a) = Σ_{y=0}^{P2} Σ_{z=0}^{P2} e(f(a + yz))`, Karacuba p. 245, with `M = P2`. -/
noncomputable def karW (f : ℝ → ℝ) (M a : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1), eC (f ((a + y * z : ℕ) : ℝ))

/-- The bound on `|W(a)|` that the case `n ≥ n0` of Theorem 1 proves, p. 245-248, in the form
`|W(a)| ≤ A (P2+1)² P^{-γ/n²}` for `N ≤ a` and `a + P2² ≤ N + P`, under `P ≥ e^{cn²}`.
The condition `a + P2² ≤ N + P` keeps every point `a + yz` inside `[N, N+P]`, where the
hypotheses hold; Karacuba's Taylor step writes `N ≤ ξ ≤ N + P₁ - 1`, p. 245, which misses
that `a + yz` can pass `N + P`; the last `P2²` values of `a` are handled trivially in
`leaf_large_case` below. -/
def KarWBound (c0 c1 c2 c3 c4 : ℝ) : Prop :=
  ∃ A γ cc : ℝ, 0 < A ∧ 0 < γ ∧ 0 < cc ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n → karN0 c1 c2 c4 ≤ n →
    Real.exp (cc * (n : ℝ) ^ 2) ≤ P → ∀ (f : ℝ → ℝ) (T : Finset ℕ),
      KarHyp c0 c1 c2 c3 N P n f T → ∀ a : ℕ, N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
        ‖karW f (karP2 c1 n P) a‖ ≤
          A * ((karP2 c1 n P : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2))

/-- LEAF. The bound on `W(a)` in the case `n ≥ n0` of the proof of Theorem 1, Karacuba
p. 245-248 to the line "получаем утверждение теоремы при n ≥ n0", as a deduction from
Lemmas 1, 3 and 4: Taylor's formula to order `n` with `|R| ≤ P^{-1/n²}` and
`W = W_1 + 2π(P2+1)² θ_1 P^{-1/n²}`, display (4); the choice of `l` with
`n(n+1)(1-1/n)^l ≤ ρ(s_1+...+s_r) < n(n+1)(1-1/n)^{l-1}`, `ρ = min(c1/3, c3, c4)`, and
`k = nl + [n(n+1)/4 + 1]`; Lemma 4 a and b with the integrals `J_k(λ)`, displays (5), (6);
Lemma 3 on the sums `𝔖_s`, `s = s_j`, display (7); Lemma 1 and the bound (8),
`|W_1(a)| ≤ B_1 P2² P^{-ρ(s_1+...+s_r)/(8k²)}`; and the "simple computations" of p. 248
that turn (8) and (4) into `A (P2+1)² P^{-γ/n²}`. Display (3) and the summation over `a`
are proved in `leaf_large_case`. -/
theorem leaf_W_bound (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 :=
  KaracubaCore.leaf_W_bound h1 h3 h4

/-- LEAF. The case `2 ≤ n < n0` of the proof of Theorem 1, Karacuba p. 248: with `γ1, γ2`
small so that `c2 + γ2/n³ < c1 < 1 - γ1/n²` and `P2 = [P^{c1 - γ2/n³}]`, shift by `y`,
Taylor's formula with `|R| ≤ 2P^{-γ2/n²}`, and Lemma 2 at one `s`, `2 ≤ s ≤ n`, with
`B_s = 1/Q_s + θ_s/Q_s²`, `Q_s ≤ P^{c2 s} < P2^s`; `τ` is bounded below since `n < n0`.
As on p. 245, the points `x + y` can pass `N + P` where the hypotheses stop; a proof must bound
the last `P2` values of `x` trivially, cost `P2 ≤ P^{1-γ/n²}`. A gap in the write up only. -/
theorem leaf_small_case (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) :=
  KaracubaCore.leaf_small_case h2

/-- The one case of the lab's `KClass` outside Karacuba's Theorem 1: `S = {1}`, possible only
when `δ k ≤ 1`. In Lean: `k ≥ 3`, `f` of class `C^k` around `[N, 2N]`, the `k`th derivative
bound, `δ k ≤ 1` and `N^{-θ} ≤ |f'(x)| ≤ N^{-Θ}` on `[N, 2N]`. -/
def LeafS1Case : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
        |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
      δ * k ≤ 1 →
      (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
        (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
        |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- LEAF, QUESTION. `LeafS1Case`. Brudern-Perelli's class lets `S ⊆ {1, ..., k-1}` contain
`s = 1`; Karacuba asks `s_j ≥ 2`, p. 244, and his small `n` case needs it, since Lemma 2
needs `r ≥ 2`. When `S` has an element `s ≥ 2` the bridge below reaches Theorem 1 with
`c0 = δ/2`; only `S = {1}` is left. Not in Karacuba. Not known to be false: the resonance
example `1/f' ≈ A(1 + ε cos 2πf)` gives only `|Σ| ≈ εN` with `ε ≈ N^{-k(Θ0-θ)}`, which the
`c` of the statement absorbs. Not used by Brudern-Perelli, whose `k` tends to infinity. -/
theorem leaf_s1_case : LeafS1Case := KaracubaCore.leaf_s1_case

/-! ### Proved assembly -/

theorem norm_sum_Ico_le (N P₁ : ℕ) (f : ℝ → ℝ) :
    ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ P₁ := by
  calc ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖
      ≤ ∑ x ∈ Finset.Ico N (N + P₁), ‖eC (f x)‖ := norm_sum_le _ _
    _ = ∑ x ∈ Finset.Ico N (N + P₁), (1 : ℝ) := Finset.sum_congr rfl (fun x _ => norm_eC _)
    _ = P₁ := by simp

/-- PROVED. The reduction of p. 245 line 1: for `P < e^{c n²}` the trivial bound
`|S| ≤ P₁ ≤ P ≤ e^{cγ} P^{1-γ/n²}` holds, so a case under `P ≥ e^{c n²}` gives the case
for every `P`. -/
theorem drop_large_P {c0 c1 c2 c3 : ℝ} {pred : ℕ → Prop} (h : KarCase c0 c1 c2 c3 pred) :
    ∃ A γ : ℝ, 0 < A ∧ 0 < γ ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n → pred n →
      ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T → ∀ P₁ : ℕ, 0 < P₁ → P₁ ≤ P →
        ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ A * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := by
  obtain ⟨A, γ, cc, hA, hγ, hcc, hb⟩ := h
  refine ⟨max A (Real.exp (cc * γ)), γ, lt_max_of_lt_left hA, hγ, ?_⟩
  intro N P n hP hn hpred f T hH P₁ hP₁ hP₁P
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hrp : 0 ≤ (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := Real.rpow_nonneg hPr.le _
  by_cases hbig : Real.exp (cc * (n : ℝ) ^ 2) ≤ P
  · calc _ ≤ A * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := hb N P n hP hn hpred hbig f T hH P₁ hP₁ hP₁P
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hrp
  · push Not at hbig
    have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have hsplit : (P : ℝ) = (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) * (P : ℝ) ^ (γ / (n : ℝ) ^ 2) := by
      rw [← Real.rpow_add hPr]; simp
    have hsmall : (P : ℝ) ^ (γ / (n : ℝ) ^ 2) ≤ Real.exp (cc * γ) := by
      calc (P : ℝ) ^ (γ / (n : ℝ) ^ 2) ≤ (Real.exp (cc * (n : ℝ) ^ 2)) ^ (γ / (n : ℝ) ^ 2) :=
            Real.rpow_le_rpow hPr.le hbig.le (by positivity)
        _ = Real.exp (cc * γ) := by
            rw [← Real.exp_mul]; congr 1; field_simp
    calc ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ P₁ := norm_sum_Ico_le N P₁ f
      _ ≤ P := by exact_mod_cast hP₁P
      _ = (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) * (P : ℝ) ^ (γ / (n : ℝ) ^ 2) := hsplit
      _ ≤ (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) * Real.exp (cc * γ) :=
          mul_le_mul_of_nonneg_left hsmall hrp
      _ = Real.exp (cc * γ) * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hrp

/-- `P^{1-γ/n²}` grows when `γ` shrinks, for `P ≥ 1`. -/
theorem rpow_gamma_mono {P : ℕ} (hP : 0 < P) (n : ℕ) {γ γ' : ℝ} (h : γ' ≤ γ) :
    (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) ≤ (P : ℝ) ^ (1 - γ' / (n : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP)
  have : γ' / (n : ℝ) ^ 2 ≤ γ / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right h (by positivity)
  linarith

/-- PROVED. Theorem 1 from its two cases, p. 245 and p. 248. -/
theorem karacubaTheorem1_of_cases
    (hL : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarCase c0 c1 c2 c3 (fun n => karN0 c1 c2 c4 ≤ n))
    (hS : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4)) :
    KaracubaTheorem1 := by
  intro c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 h01 h11 h241
  obtain ⟨A1, γ1, hA1, hγ1, hb1⟩ := drop_large_P (hL c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 h01 h11 h241)
  obtain ⟨A2, γ2, hA2, hγ2, hb2⟩ := drop_large_P (hS c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 h01 h11 h241)
  refine ⟨A1 + A2, min γ1 γ2, by positivity, lt_min hγ1 hγ2, ?_⟩
  intro N P n hP hn f T hH P₁ hP₁ hP₁P
  have hpow1 := rpow_gamma_mono hP n (min_le_left γ1 γ2)
  have hpow2 := rpow_gamma_mono hP n (min_le_right γ1 γ2)
  have hr0 : 0 ≤ (P : ℝ) ^ (1 - min γ1 γ2 / (n : ℝ) ^ 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hc : karN0 c1 c2 c4 ≤ n
  · have := hb1 N P n hP hn hc f T hH P₁ hP₁ hP₁P
    nlinarith
  · push Not at hc
    have := hb2 N P n hP hn hc f T hH P₁ hP₁ hP₁P
    nlinarith

/-- The lab sum over `(N, 2N]` differs from Karacuba's sum over `N ≤ x ≤ 2N - 1` by
`e(f(2N)) - e(f(N))`. -/
theorem sum_Ioc_eq (N : ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc N (2 * N), g n = ∑ x ∈ Finset.Ico N (N + N), g x + g (2 * N) - g N := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  have h1 : ∑ x ∈ Finset.Ico N (2 * N + 1), g x = ∑ x ∈ Finset.Ico N (2 * N), g x + g (2 * N) :=
    Finset.sum_Ico_succ_top (by omega) g
  have h2 : ∑ x ∈ Finset.Ico N (2 * N + 1), g x = g N + ∑ x ∈ Finset.Ico (N + 1) (2 * N + 1), g x :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) g
  rw [Finset.Ico_add_one_add_one_eq_Ioc] at h2
  rw [show N + N = 2 * N by ring]
  linear_combination h2.symm.trans h1

/-- PROVED. The notation bridge, Brudern-Perelli p. 371: `Lemma10` from Karacuba's
Theorem 1 with `n = k - 1`, `P = P₁ = N`, `c0 = δ/2`, `c1 = Θ₀`, `c2 = θ`, `c3 = Θ`,
`c4 = (Θ₀ - θ)/2`, `T = S ∩ [2, k-1]`, and the case `S = {1}` from `LeafS1Case`. -/
theorem lemma10_of_thm1 (hK : KaracubaTheorem1) (hS1 : LeafS1Case) : Lemma10 := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨A, γ, hA, hγ, hKb⟩ := hK (δ / 2) Θ₀ θ Θ ((Θ₀ - θ) / 2) (by positivity)
    (by linarith) (by linarith) hΘ0 (by linarith) (by linarith) hΘ₀1 (by linarith)
  obtain ⟨B1, c1, hB1, hc1, hS1b⟩ := hS1 θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  refine ⟨A + 2 + B1, min (min γ c1) 1, by positivity, by positivity, ?_⟩
  intro N hN f k hf
  obtain ⟨hk3, hsm, hder, S, hSsub, hScard, hSb⟩ := hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set c := min (min γ c1) 1 with hcdef
  have hcγ : c ≤ γ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc1 : c ≤ c1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1' : c ≤ 1 := min_le_right _ _
  have hc0 : 0 < c := by positivity
  have hk9 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    nlinarith
  have hexp0 : 0 ≤ 1 - c / (k : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hX1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := Real.one_le_rpow hNr hexp0
  set T := S.filter (fun s => 2 ≤ s) with hTdef
  by_cases hT : T.Nonempty
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hn2 : 2 ≤ n := by omega
    have hI : Set.Icc (N : ℝ) (N + N) = Set.Icc (N : ℝ) (2 * N) := by rw [two_mul]
    have hcardT : δ / 2 * n ≤ T.card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun s => 2 ≤ s)
      have hneg : (S.filter (fun s => ¬ 2 ≤ s)).card ≤ 1 := by
        apply Finset.card_le_one.2
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        have := Finset.mem_Icc.1 (hSsub ha.1)
        have := Finset.mem_Icc.1 (hSsub hb.1)
        omega
      have hT1 : 1 ≤ T.card := Finset.card_pos.2 hT
      have hle : (S.card : ℝ) ≤ T.card + 1 := by
        rw [← hsplit]; push_cast
        have : ((S.filter (fun s => ¬ 2 ≤ s)).card : ℝ) ≤ 1 := by exact_mod_cast hneg
        linarith
      have hT1r : (1 : ℝ) ≤ T.card := by exact_mod_cast hT1
      push_cast at hScard
      by_cases hbig : 2 ≤ δ * (n + 1)
      · nlinarith
      · push Not at hbig
        nlinarith
    have hKH : KarHyp (δ / 2) Θ₀ θ Θ N N n f T := by
      refine ⟨?_, ?_, ?_, hcardT, ?_⟩
      · rw [hI]; exact hsm
      · rw [hI]; exact hder
      · intro s hs
        rw [hTdef, Finset.mem_filter] at hs
        have := Finset.mem_Icc.1 (hSsub hs.1)
        exact Finset.mem_Icc.2 ⟨hs.2, by omega⟩
      · intro s hs x hx
        rw [hTdef, Finset.mem_filter] at hs
        rw [hI] at hx
        exact hSb s hs.1 x hx
    have hb := hKb N N n (by omega) hn2 f T hKH N (by omega) le_rfl
    have hexpK : (N : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 - c / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hNr
      have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity
      have h1 : c / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ γ / ((n + 1 : ℕ) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcγ (by positivity)
      have h2 : γ / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ γ / (n : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left hγ.le hn0
        push_cast; nlinarith
      linarith
    rw [sum_Ioc_eq N (fun x => eC (f x))]
    have hn1 : ‖eC (f ((2 * N : ℕ) : ℝ))‖ = 1 := norm_eC _
    have hn2' : ‖eC (f (N : ℝ))‖ = 1 := norm_eC _
    calc ‖∑ x ∈ Finset.Ico N (N + N), eC (f x) + eC (f ((2 * N : ℕ) : ℝ)) - eC (f N)‖
        ≤ ‖∑ x ∈ Finset.Ico N (N + N), eC (f x)‖ + ‖eC (f ((2 * N : ℕ) : ℝ))‖ + ‖eC (f N)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ A * (N : ℝ) ^ (1 - c / ((n + 1 : ℕ) : ℝ) ^ 2) + 2 := by
          rw [hn1, hn2']
          have := mul_le_mul_of_nonneg_left hexpK hA.le
          linarith
      _ ≤ (A + 2 + B1) * (N : ℝ) ^ (1 - c / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          nlinarith
  · -- `S ⊆ {1}`, so `S = {1}` and `δ k ≤ 1`.
    have hS1mem : ∀ s ∈ S, s = 1 := by
      intro s hs
      have h2 : ¬ 2 ≤ s := fun h2 => hT ⟨s, by rw [hTdef, Finset.mem_filter]; exact ⟨hs, h2⟩⟩
      have := Finset.mem_Icc.1 (hSsub hs)
      omega
    have hSpos : 0 < S.card := by
      have : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hScard
      exact_mod_cast this
    obtain ⟨s0, hs0⟩ := Finset.card_pos.1 hSpos
    have h1S : 1 ∈ S := by rw [← hS1mem s0 hs0]; exact hs0
    have hcard1 : S.card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
      rw [hS1mem a ha, hS1mem b hb])
    have hδk : δ * k ≤ 1 := hScard.trans (by exact_mod_cast hcard1)
    have hb := hS1b N hN f k hk3 hsm hder hδk (fun x hx => hSb 1 h1S x hx)
    have hexpS : (N : ℝ) ^ (1 - c1 / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hNr
      have : c / (k : ℝ) ^ 2 ≤ c1 / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcc1 (by positivity)
      linarith
    calc _ ≤ B1 * (N : ℝ) ^ (1 - c1 / (k : ℝ) ^ 2) := hb
      _ ≤ B1 * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hexpS hB1.le
      _ ≤ (A + 2 + B1) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by nlinarith

/-- One shift by `h` changes a sum of `P₁` unimodular terms by at most `2h`. -/
theorem shift_step (g : ℕ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (N P₁ h : ℕ) :
    ‖∑ k ∈ Finset.range P₁, g (N + k) - ∑ k ∈ Finset.range P₁, g (N + k + h)‖ ≤ 2 * h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have htel : ∑ k ∈ Finset.range P₁, g (N + k + h) - ∑ k ∈ Finset.range P₁, g (N + k + (h + 1))
        = g (N + h) - g (N + P₁ + h) := by
      rw [← Finset.sum_sub_distrib]
      have hc : ∀ k ∈ Finset.range P₁, g (N + k + h) - g (N + k + (h + 1)) =
          (fun j => g (N + j + h)) k - (fun j => g (N + j + h)) (k + 1) := by
        intro k _
        simp only
        rw [show N + k + (h + 1) = N + (k + 1) + h by omega]
      rw [Finset.sum_congr rfl hc, Finset.sum_range_sub']
      simp
    have hstep : ‖g (N + h) - g (N + P₁ + h)‖ ≤ 2 := by
      calc _ ≤ ‖g (N + h)‖ + ‖g (N + P₁ + h)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hg _) (hg _)
        _ = 2 := by norm_num
    calc _ = ‖(∑ k ∈ Finset.range P₁, g (N + k) - ∑ k ∈ Finset.range P₁, g (N + k + h)) +
            (∑ k ∈ Finset.range P₁, g (N + k + h) -
              ∑ k ∈ Finset.range P₁, g (N + k + (h + 1)))‖ := by rw [sub_add_sub_cancel]
      _ ≤ 2 * h + 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [htel]
          exact add_le_add ih hstep
      _ = 2 * ((h + 1 : ℕ) : ℝ) := by push_cast; ring

/-- PROVED. Display (3), Karacuba p. 245: shifting the sum by `yz`, `0 ≤ y, z ≤ M`, and
averaging, `S = (M+1)^{-2} Σ_x W(x) + θ'` with `|θ'| ≤ 2M²`; the paper has `θ M²`, the
factor 2 here is a cruder count and harmless. -/
theorem shift_average (g : ℕ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (N P₁ M : ℕ) :
    ‖∑ k ∈ Finset.range P₁, g (N + k) - (((M : ℂ) + 1) ^ 2)⁻¹ *
      ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        g (N + k + y * z)‖ ≤ 2 * (M : ℝ) ^ 2 := by
  set S := ∑ k ∈ Finset.range P₁, g (N + k)
  have hM : ((M : ℂ) + 1) ≠ 0 := by
    have : ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero M
  have hswap : ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        g (N + k + y * z) = ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
          ∑ k ∈ Finset.range P₁, g (N + k + y * z) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_comm]
  have hD : S - (((M : ℂ) + 1) ^ 2)⁻¹ * ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1),
        ∑ z ∈ Finset.range (M + 1), g (N + k + y * z) =
      (((M : ℂ) + 1) ^ 2)⁻¹ * ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        (S - ∑ k ∈ Finset.range P₁, g (N + k + y * z)) := by
    rw [hswap]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hD, norm_mul]
  have hinv : ‖(((M : ℂ) + 1) ^ 2)⁻¹‖ = (((M : ℝ) + 1) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    congr 2
    have : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hinv]
  have hbound : ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
      (S - ∑ k ∈ Finset.range P₁, g (N + k + y * z))‖ ≤ ((M : ℝ) + 1) ^ 2 * (2 * (M : ℝ) ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        (S - ∑ k ∈ Finset.range P₁, g (N + k + y * z))‖ ≤ ((M : ℝ) + 1) * (2 * (M : ℝ) ^ 2) := by
      intro y hy
      refine (norm_sum_le _ _).trans ?_
      have : ∀ z ∈ Finset.range (M + 1),
          ‖S - ∑ k ∈ Finset.range P₁, g (N + k + y * z)‖ ≤ 2 * (M : ℝ) ^ 2 := by
        intro z hz
        refine (shift_step g hg N P₁ (y * z)).trans ?_
        have hy' : y ≤ M := by have := Finset.mem_range.1 hy; omega
        have hz' : z ≤ M := by have := Finset.mem_range.1 hz; omega
        have : ((y * z : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
          have : y * z ≤ M * M := Nat.mul_le_mul hy' hz'
          calc ((y * z : ℕ) : ℝ) ≤ ((M * M : ℕ) : ℝ) := by exact_mod_cast this
            _ = (M : ℝ) ^ 2 := by push_cast; ring
        linarith
      refine (Finset.sum_le_sum this).trans ?_
      simp
    refine (Finset.sum_le_sum this).trans ?_
    simp; ring_nf; rfl
  calc _ ≤ (((M : ℝ) + 1) ^ 2)⁻¹ * (((M : ℝ) + 1) ^ 2 * (2 * (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * (M : ℝ) ^ 2 := by field_simp

/-- PROVED. The case `n ≥ n0` of Theorem 1 from the bound on `W(a)`: display (3), the
`a` with `a + P2² ≤ N + P` by `KarWBound`, the last `P2²` values of `a` trivially, and
`P2² ≤ P^{c1} ≤ P^{1-γ/n²}`. -/
theorem largeCase_of_W {c0 c1 c2 c3 c4 : ℝ} (hc1 : c1 < 1) (hW : KarWBound c0 c1 c2 c3 c4) :
    KarCase c0 c1 c2 c3 (fun n => karN0 c1 c2 c4 ≤ n) := by
  obtain ⟨A, γ, cc, hA, hγ, hcc, hb⟩ := hW
  refine ⟨A + 3, min γ (1 - c1), cc, by positivity, lt_min hγ (by linarith), hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH P₁ hP₁ hP₁P
  set M := karP2 c1 n P with hMdef
  set γf := min γ (1 - c1)
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1r : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hn0 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
  set g : ℕ → ℂ := fun x => eC (f x) with hgdef
  have hg : ∀ x, ‖g x‖ ≤ 1 := fun x => (norm_eC _).le
  have hS : ∑ x ∈ Finset.Ico N (N + P₁), eC (f x) = ∑ k ∈ Finset.range P₁, g (N + k) := by
    rw [Finset.sum_Ico_eq_sum_range]; simp [hgdef]
  have hWk : ∀ k, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1), g (N + k + y * z) =
      karW f M (N + k) := fun k => rfl
  set X := ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
    g (N + k + y * z) with hXdef
  have h3 := shift_average g hg N P₁ M
  -- bound on each `W`
  have hWtriv : ∀ a, ‖karW f M a‖ ≤ ((M : ℝ) + 1) ^ 2 := by
    intro a
    unfold karW
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun y _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun z _ => (norm_eC _).le)))).trans ?_
    simp; ring_nf; rfl
  set E := (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) with hEdef
  have hE0 : 0 ≤ E := Real.rpow_nonneg hPr.le _
  have hWk' : ∀ k ∈ Finset.range P₁, ‖karW f M (N + k)‖ ≤
      A * ((M : ℝ) + 1) ^ 2 * E +
        ((M : ℝ) + 1) ^ 2 * (if P < k + M ^ 2 then 1 else 0) := by
    intro k hk
    by_cases hkP : P < k + M ^ 2
    · rw [if_pos hkP]
      have : 0 ≤ A * ((M : ℝ) + 1) ^ 2 * E := by positivity
      linarith [hWtriv (N + k)]
    · rw [if_neg hkP, mul_zero, add_zero]
      have hMM : M ^ 2 = karP2 c1 n P ^ 2 := rfl
      have hk' := Finset.mem_range.1 hk
      exact hb N P n hP hn hpred hbig f T hH (N + k) (by omega) (by omega)
  have hcount : ∑ k ∈ Finset.range P₁, (if P < k + M ^ 2 then (1 : ℝ) else 0) ≤ (M : ℝ) ^ 2 := by
    rw [Finset.sum_boole]
    have hsub : (Finset.range P₁).filter (fun k => P < k + M ^ 2) ⊆ Finset.Ico (P₁ - M ^ 2) P₁ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ico]; omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    have : ((Finset.range P₁).filter (fun k => P < k + M ^ 2)).card ≤ M ^ 2 := by omega
    exact_mod_cast this
  have hXb : ‖X‖ ≤ P₁ * (A * ((M : ℝ) + 1) ^ 2 * E) + ((M : ℝ) + 1) ^ 2 * (M : ℝ) ^ 2 := by
    rw [hXdef]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hWk').trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ ((M : ℝ) + 1) ^ 2)
    linarith
  have hinv : ‖(((M : ℂ) + 1) ^ 2)⁻¹‖ = (((M : ℝ) + 1) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    congr 2
    have : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmain : ‖∑ k ∈ Finset.range P₁, g (N + k)‖ ≤ P₁ * A * E + 3 * (M : ℝ) ^ 2 := by
    have hsplit : ∑ k ∈ Finset.range P₁, g (N + k) =
        (∑ k ∈ Finset.range P₁, g (N + k) - (((M : ℂ) + 1) ^ 2)⁻¹ * X) +
          (((M : ℂ) + 1) ^ 2)⁻¹ * X := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hinv]
    have hM1 : (0 : ℝ) < ((M : ℝ) + 1) ^ 2 := by positivity
    have h2 : (((M : ℝ) + 1) ^ 2)⁻¹ * ‖X‖ ≤ P₁ * A * E + (M : ℝ) ^ 2 := by
      rw [inv_mul_le_iff₀ hM1]
      nlinarith [hXb]
    linarith
  -- powers of `P`
  have hγf : γf ≤ γ := min_le_left _ _
  have hγf1 : γf ≤ 1 - c1 := min_le_right _ _
  have hPE : (P₁ : ℝ) * E ≤ (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by
    have hP1 : (P₁ : ℝ) ≤ P := by exact_mod_cast hP₁P
    calc (P₁ : ℝ) * E ≤ P * E := mul_le_mul_of_nonneg_right hP1 hE0
      _ = (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2) := by
          rw [hEdef, sub_eq_add_neg, Real.rpow_add hPr, Real.rpow_one]
      _ ≤ _ := rpow_gamma_mono hP n hγf
  have hM2 : (M : ℝ) ^ 2 ≤ (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by
    set e := c1 / 2 - 1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))
    have hMle : (M : ℝ) ≤ (P : ℝ) ^ e := Nat.floor_le (Real.rpow_nonneg hPr.le _)
    have hn1 : (0 : ℝ) < 2 * ((n : ℝ) ^ 2 * (n + 1)) := by positivity
    have he : e * (2 : ℕ) ≤ 1 - γf / (n : ℝ) ^ 2 := by
      have : 0 ≤ 1 / (2 * ((n : ℝ) ^ 2 * (n + 1))) := by positivity
      have hq : γf / (n : ℝ) ^ 2 ≤ γf := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ γf := le_min hγ.le (by linarith)
        nlinarith
      push_cast
      have : e * 2 = c1 - 2 * (1 / (2 * ((n : ℝ) ^ 2 * (n + 1)))) := by ring
      linarith
    calc (M : ℝ) ^ 2 ≤ ((P : ℝ) ^ e) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hMle 2
      _ = (P : ℝ) ^ (e * (2 : ℕ)) := (Real.rpow_mul_natCast hPr.le e 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1r he
  rw [hS]
  calc _ ≤ P₁ * A * E + 3 * (M : ℝ) ^ 2 := hmain
    _ = A * ((P₁ : ℝ) * E) + 3 * (M : ℝ) ^ 2 := by ring
    _ ≤ A * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) + 3 * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hPE hA.le
        linarith
    _ = (A + 3) * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by ring

/-- PROVED from `leaf_W_bound`. The case `n ≥ n0` of the proof of Theorem 1, Karacuba
p. 245-248, as a deduction from Lemmas 1, 3 and 4. -/
theorem leaf_large_case (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => karN0 c1 c2 c4 ≤ n) := by
  intro c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  exact largeCase_of_W h11 (leaf_W_bound h1 h3 h4 c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241)

/-- Karacuba's Theorem 1 from the leaves, with Lemma 4 proved. -/
theorem karacubaTheorem1 : KaracubaTheorem1 :=
  karacubaTheorem1_of_cases
    (leaf_large_case leaf_karLemma1_mvt leaf_karLemma3 karLemma4)
    (leaf_small_case leaf_karLemma2)

/-- `Lemma10` of State1539 from the leaves of this file. CONDITIONAL on the CITED
`leaf_karLemma1_mvt` and `leaf_karLemma2`, the LEAF `leaf_W_bound`, and the QUESTION leaf
`leaf_s1_case`; `leaf_karLemma3` and `leaf_small_case` are now PROVED in KaracubaCore. -/
theorem lemma10_of_karacuba : Lemma10 := lemma10_of_thm1 karacubaTheorem1 leaf_s1_case

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

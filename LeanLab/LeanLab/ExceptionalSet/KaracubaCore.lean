/-
KaracubaCore: the Karacuba split of Lemma 10 of J. Brudern and A. Perelli, Goldbach numbers
in sparse sequences, Ann. Inst. Fourier 48 (1998), p. 370-371, placed BELOW State1539 so that
State1539 can import it without an import cycle. Coordinator decision 5, 2026-11-12.

Source: A. A. Karacuba, Estimates of trigonometric sums by the method of I. M. Vinogradov and
their applications, Trudy Mat. Inst. Steklov 112 (1971) 241-255, Russian original, in the lab
at `papers/Karacuba1971-TrudyMIAN112.pdf`, chapter I, Theorem 1 on p. 244, proved on
p. 245-248. All formulas were read from page images, not from the OCR.

This file holds the content of `KaracubaSplit.lean`, which now imports this file and
discharges each of its leaves one for one by the leaf of the same name here, so every leaf
has exactly one open copy. Changes against `KaracubaSplit.lean`:
* Decision 2, the endpoint gap of p. 248: `leaf_small_case` is PROVED here from the new
  LEAF `leaf_T_bound`, the bound on Karacuba's `T(x) = Σ_{y=0}^{P2} e(f(x+y))` only for the
  `x` with `x + P2 ≤ N + P`, where all points stay inside `[N, N+P]`. The last `P2` values
  of `x` are bounded trivially in the proved `smallCase_of_T`.
* Decision 1: `KClassKar` and `Lemma10Kar`, the lab Lemma 10 with `S ⊆ [2, k-1]`, matching
  Karacuba's `s_j ≥ 2`, and `lemma10Kar_of_karacuba`, which does NOT use `leaf_s1_case`.
  `Lemma10` and `KClass` are unchanged.
* `lemma10_of_karacuba : Lemma10`, used by State1539, still uses the QUESTION leaf
  `leaf_s1_case` for the case `S = {1}`.

Leaves here: `leaf_karLemma1_mvt` and `leaf_karLemma2`, CITED; `leaf_W_bound`, LEAF;
`leaf_s1_case`, QUESTION, not on the Lemma10Kar route. Part 4 of 2026-11-12:
`leaf_karLemma3` is PROVED by `karL3_main`, and `leaf_T_bound` is PROVED from Lemma 2 alone
by `karTBound_of_split`, the Taylor step and the application of Lemma 2 of p. 248.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.Decomp1539a

namespace LeanLab.ExceptionalSet.U1539.KaracubaCore

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
theorem leaf_karLemma1_mvt : KarLemma1 := by sorry

/-- LEAF, CITED. Karacuba's Lemma 2, p. 243-244, Vinogradov's estimate of a Weyl sum from a
rational approximation of one coefficient, his reference [2]. Used only in the small `n`
case, p. 248. -/
theorem leaf_karLemma2 : KarLemma2 := by sorry

section KarL3

open Finset

/-- `(γ) ≥ 0`. -/
theorem karL3_nint_nonneg (z : ℝ) : 0 ≤ nint z :=
  le_min (Int.fract_nonneg z) (by linarith [Int.fract_lt_one z])

/-- A lower bound for every `|z - n|`, `n` an integer, is a lower bound for `(z)`. -/
theorem karL3_le_nint {z L : ℝ} (h : ∀ n : ℤ, L ≤ |z - n|) : L ≤ nint z := by
  unfold nint
  refine le_min ?_ ?_
  · have h1 := h ⌊z⌋
    rw [abs_of_nonneg (by linarith [Int.floor_le z])] at h1
    rw [Int.fract]; exact h1
  · have h1 := h (⌊z⌋ + 1)
    push_cast at h1
    rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one z])] at h1
    rw [Int.fract]; linarith

/-- For `0 ≤ y < 1` and every integer `n`, `min(y, 1-y) ≤ |y - n|`. -/
theorem karL3_min_le_abs_sub_int {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℤ) :
    min y (1 - y) ≤ |y - n| := by
  rcases le_or_gt n 0 with hn | hn
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    exact (min_le_left _ _).trans (by rw [abs_of_nonneg (by linarith)]; linarith)
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (min_le_right _ _).trans (by rw [abs_of_nonpos (by linarith)]; linarith)

/-- `Σ_{i=2}^{q} 1/i ≤ log q`, from `log x ≤ x - 1`. -/
theorem karL3_harm_le_log (q : ℕ) (hq : 1 ≤ q) :
    ∑ i ∈ range (q + 1), (if 2 ≤ i then (1 : ℝ) / i else 0) ≤ Real.log q := by
  induction q, hq using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ q hq ih =>
    rw [Finset.sum_range_succ, if_pos (by omega)]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have key : (1 : ℝ) / ((q + 1 : ℕ) : ℝ) ≤ Real.log ((q + 1 : ℕ) : ℝ) - Real.log q := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q / (q + 1) by positivity)
      rw [Real.log_div hq0.ne' (by positivity)] at h
      push_cast
      have : (q : ℝ) / (q + 1) - 1 = -(1 / (q + 1)) := by field_simp; ring
      linarith
    linarith

/-- Splitting `[0, qM)` into `M` blocks of `q` consecutive integers. -/
theorem karL3_sum_range_mul_split (F : ℕ → ℝ) (q M : ℕ) :
    ∑ x ∈ range (q * M), F x = ∑ b ∈ range M, ∑ t ∈ range q, F (q * b + t) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- One block of `q` consecutive `x`, the heart of Lemma 3: for every real `C`,
`Σ_{t=0}^{q-1} min(U, 1/(αt + C)) ≤ 4U + 4 q log q`. Write `qC = m + e`, `0 ≤ e < 1`, and
`at + m = qk + i`, `0 ≤ i < q`; then `αt + C = k + (i+e)/q + θt/q²` with `|θt/q²| ≤ 1/q`,
and `t ↦ i` is injective on `[0, q)` because `(a, q) = 1`. The four `i` in
`{0, 1, q-2, q-1}` get `U`; every other `i` gets at most `2q/i + 2q/(q-1-i)`. -/
theorem karL3_block_bound (U : ℝ) (hU : 0 < U) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (ha : Int.gcd a q = 1) (θ : ℝ) (hθ : |θ| ≤ 1) (C : ℝ) :
    ∑ t ∈ range q, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C))
      ≤ 4 * U + 4 * q * Real.log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  set m : ℤ := ⌊(q : ℝ) * C⌋ with hm
  set e : ℝ := Int.fract ((q : ℝ) * C) with he
  have hme : (m : ℝ) + e = q * C := Int.floor_add_fract _
  have he0 : 0 ≤ e := Int.fract_nonneg _
  have he1 : e < 1 := Int.fract_lt_one _
  let σ : ℕ → ℕ := fun t => ((a * t + m) % (q : ℤ)).toNat
  let h1 : ℕ → ℝ := fun i => if 2 ≤ i then (1 : ℝ) / i else 0
  let g : ℕ → ℝ := fun i => 2 * q * h1 i
  have h1_nonneg : ∀ i, 0 ≤ h1 i := fun i => by
    simp only [h1]; split_ifs <;> positivity
  have g_nonneg : ∀ i, 0 ≤ g i := fun i => by simp only [g]; have := h1_nonneg i; positivity
  let H : ℕ → ℝ := fun i => (if 2 ≤ i ∧ i + 3 ≤ q then 0 else U) + g i + g (q - 1 - i)
  have H_nonneg : ∀ i, 0 ≤ H i := fun i => by
    simp only [H]
    have := g_nonneg i; have := g_nonneg (q - 1 - i)
    split_ifs <;> linarith
  have hσ_eq : ∀ t : ℕ, ((σ t : ℕ) : ℤ) = (a * t + m) % (q : ℤ) := fun t =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have hmaps : ∀ t ∈ range q, σ t ∈ range q := fun t _ => by
    rw [mem_range]
    have := hσ_eq t
    have := Int.emod_lt_of_pos (a * t + m) hqz
    omega
  have hinj : ∀ t₁ ∈ range q, ∀ t₂ ∈ range q, σ t₁ = σ t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ h
    rw [mem_range] at ht₁ ht₂
    have h' : (a * t₁ + m) % (q : ℤ) = (a * t₂ + m) % (q : ℤ) := by
      rw [← hσ_eq, ← hσ_eq, h]
    have hd : (q : ℤ) ∣ (a * t₂ + m) - (a * t₁ + m) := Int.ModEq.dvd h'
    have hd' : (q : ℤ) ∣ a * ((t₂ : ℤ) - t₁) := by
      have : (a * t₂ + m) - (a * t₁ + m) = a * ((t₂ : ℤ) - t₁) := by ring
      rwa [this] at hd
    have hcop : IsCoprime (q : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact ha
    have hd2 : (q : ℤ) ∣ ((t₂ : ℤ) - t₁) := hcop.dvd_of_dvd_mul_left hd'
    have := Int.eq_zero_of_abs_lt_dvd hd2 (by rw [abs_lt]; constructor <;> omega)
    omega
  have hpt : ∀ t ∈ range q,
      min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C)) ≤ H (σ t) := by
    intro t ht
    rw [mem_range] at ht
    set i := σ t with hi
    have hiq : i < q := mem_range.1 (hmaps t (mem_range.2 ht))
    set k : ℤ := (a * t + m) / (q : ℤ) with hk
    have hdiv : (q : ℤ) * k + (i : ℤ) = a * t + m := by
      rw [hσ_eq]; exact Int.mul_ediv_add_emod _ _
    have hdivR : (q : ℝ) * k + (i : ℝ) = a * t + m := by exact_mod_cast hdiv
    set y : ℝ := ((i : ℝ) + e) / q with hy
    have hy0 : 0 ≤ y := by positivity
    have hiqR : (i : ℝ) + 1 ≤ q := by exact_mod_cast hiq
    have hy1 : y < 1 := by rw [hy, div_lt_one hq0]; linarith
    have harg : (a / q + θ / (q : ℝ) ^ 2) * t + C = k + y + θ * t / (q : ℝ) ^ 2 := by
      rw [hy]
      field_simp
      linear_combination (-(q : ℝ)) * hdivR + (-(q:ℝ)) * hme
    have hεb : |θ * t / (q : ℝ) ^ 2| ≤ 1 / q := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t),
        abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2), div_le_div_iff₀ (by positivity) hq0]
      have htq : (t : ℝ) ≤ q := by exact_mod_cast ht.le
      have h0 := abs_nonneg θ
      have h5 : |θ| * t ≤ q := by
        calc |θ| * t ≤ 1 * q := mul_le_mul hθ htq (by positivity) zero_le_one
          _ = q := one_mul _
      nlinarith
    set M := min y (1 - y) with hM
    have hL : M - 1 / q ≤ nint ((a / q + θ / (q : ℝ) ^ 2) * t + C) := by
      apply karL3_le_nint
      intro n
      rw [harg]
      have h2 := karL3_min_le_abs_sub_int hy0 hy1 (n - k)
      push_cast at h2
      have h3 : |y - (n - k)| ≤ |(k + y + θ * t / (q : ℝ) ^ 2) - n| + |θ * t / (q : ℝ) ^ 2| := by
        have : y - (n - k) = ((k + y + θ * t / (q : ℝ) ^ 2) - n) - θ * t / (q : ℝ) ^ 2 := by ring
        rw [this]; exact abs_sub _ _
      linarith
    by_cases hc : 2 ≤ i ∧ i + 3 ≤ q
    · have hi2 : (2 : ℝ) ≤ i := by exact_mod_cast hc.1
      have hi3 : (i : ℝ) + 3 ≤ q := by exact_mod_cast hc.2
      have hyl : (i : ℝ) / q ≤ y := by rw [hy]; gcongr; linarith
      have hyr : ((q : ℝ) - 1 - i) / q ≤ 1 - y := by
        rw [hy, le_sub_iff_add_le, ← add_div, div_le_one hq0]; linarith
      have hil : (2 : ℝ) / q ≤ (i : ℝ) / q := by gcongr
      have hir : (2 : ℝ) / q ≤ ((q : ℝ) - 1 - i) / q := by gcongr; linarith
      have hM2 : 2 / q ≤ M := le_min (hil.trans hyl) (hir.trans hyr)
      have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM2
      have hhalf : M / 2 ≤ M - 1 / q := by
        have : (1 : ℝ) / q ≤ M / 2 := by
          have : (2 : ℝ) / q = 2 * (1 / q) := by ring
          linarith
        linarith
      have hn : M / 2 ≤ nint ((a / q + θ / (q : ℝ) ^ 2) * t + C) := hhalf.trans hL
      have hinv : 1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C) ≤ 2 / M := by
        rw [show (2 : ℝ) / M = 1 / (M / 2) by field_simp]
        exact one_div_le_one_div_of_le (by positivity) hn
      have hg1 : g i = 2 * q / i := by
        simp only [g, h1, if_pos hc.1]; field_simp
      have hcast : ((q - 1 - i : ℕ) : ℝ) = (q : ℝ) - 1 - i := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      have hg2 : g (q - 1 - i) = 2 * q / ((q : ℝ) - 1 - i) := by
        simp only [g, h1, if_pos (show 2 ≤ q - 1 - i by omega), hcast]; field_simp
      have hipos : (0 : ℝ) < i := by linarith
      have hjpos : (0 : ℝ) < (q : ℝ) - 1 - i := by linarith
      have hbound : 2 / M ≤ g i + g (q - 1 - i) := by
        rw [hg1, hg2]
        have hA : 0 ≤ 2 * (q : ℝ) / i := by positivity
        have hB : 0 ≤ 2 * (q : ℝ) / ((q : ℝ) - 1 - i) := by positivity
        rcases min_choice y (1 - y) with hmin | hmin
        · rw [← hM] at hmin
          rw [hmin]
          have : 2 / y ≤ 2 * (q : ℝ) / i := by
            rw [div_le_div_iff₀ (by rw [← hmin]; exact hMpos) hipos]
            have := (div_le_iff₀ hq0).1 hyl
            nlinarith
          linarith
        · rw [← hM] at hmin
          rw [hmin]
          have : 2 / (1 - y) ≤ 2 * (q : ℝ) / ((q : ℝ) - 1 - i) := by
            rw [div_le_div_iff₀ (by rw [← hmin]; exact hMpos) hjpos]
            have := (div_le_iff₀ hq0).1 hyr
            nlinarith
          linarith
      calc min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C))
          ≤ 1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C) := min_le_right _ _
        _ ≤ 2 / M := hinv
        _ ≤ g i + g (q - 1 - i) := hbound
        _ = H i := by simp only [H, if_pos hc, zero_add]
    · calc min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * t + C)) ≤ U := min_le_left _ _
        _ ≤ H i := by
          simp only [H, if_neg hc]
          linarith [g_nonneg i, g_nonneg (q - 1 - i)]
  -- the sum of H
  have hU4 : ∑ i ∈ range q, (if 2 ≤ i ∧ i + 3 ≤ q then (0 : ℝ) else U) ≤ 4 * U := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have hsub : (range q).filter (fun i => ¬ (2 ≤ i ∧ i + 3 ≤ q)) ⊆ {0, 1, q - 2, q - 1} := by
      intro i hi
      simp only [Finset.mem_filter, mem_range] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcard := (card_le_card hsub).trans card_le_four
    have : (((range q).filter (fun i => ¬ (2 ≤ i ∧ i + 3 ≤ q))).card : ℝ) ≤ 4 := by
      exact_mod_cast hcard
    nlinarith
  have hg_sum : ∑ i ∈ range q, g i ≤ 2 * q * Real.log q := by
    have hsub : ∑ i ∈ range q, h1 i ≤ ∑ i ∈ range (q + 1), h1 i :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.le_succ q))
        (fun i _ _ => h1_nonneg i)
    have := karL3_harm_le_log q hq
    simp only [g, ← Finset.mul_sum]
    have h2q : (0 : ℝ) ≤ 2 * q := by positivity
    exact mul_le_mul_of_nonneg_left (hsub.trans this) h2q
  have hrefl : ∑ i ∈ range q, g (q - 1 - i) = ∑ i ∈ range q, g i :=
    Finset.sum_range_reflect g q
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  calc _ ≤ ∑ t ∈ range q, H (σ t) := sum_le_sum hpt
    _ = ∑ i ∈ (range q).image σ, H i := (sum_image hinj).symm
    _ ≤ ∑ i ∈ range q, H i :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.2 hmaps) (fun i _ _ => H_nonneg i)
    _ = ∑ i ∈ range q, (if 2 ≤ i ∧ i + 3 ≤ q then (0 : ℝ) else U)
          + ∑ i ∈ range q, g i + ∑ i ∈ range q, g (q - 1 - i) := by
        simp only [H, Finset.sum_add_distrib]
    _ ≤ 4 * U + 4 * q * Real.log q := by rw [hrefl]; linarith

/-- Lemma 3 of Karacuba, p. 244: sum over the `⌈P/q⌉ ≤ P/q + 1` blocks of `q` consecutive
`x` covering `[1, P]`, each bounded by `karL3_block_bound`, and `4U + 4q log q ≤ 6(U + q log q)`. -/
theorem karL3_main : KarLemma3 := by
  intro U P a q θ β hU hq ha hθ
  set α : ℝ := a / q + θ / (q : ℝ) ^ 2
  let F : ℕ → ℝ := fun x => min U (1 / nint (α * x + β))
  have hF : ∀ x, 0 ≤ F x := fun x =>
    le_min hU.le (by have := karL3_nint_nonneg (α * x + β); positivity)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set M := P / q + 1 with hMdef
  have hsub : Finset.Icc 1 P ⊆ range (q * M) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [mem_range, hMdef]
    have := Nat.lt_mul_div_succ P (show 0 < q by omega)
    omega
  have hblock : ∀ b ∈ range M, ∑ t ∈ range q, F (q * b + t) ≤ 4 * U + 4 * q * Real.log q := by
    intro b _
    have := karL3_block_bound U hU a q hq ha θ hθ (α * (q * b : ℕ) + β)
    convert this using 2 with t _
    simp only [F, α]
    congr 3
    push_cast; ring
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hMle : (M : ℝ) ≤ P / q + 1 := by
    rw [hMdef]; push_cast
    have := Nat.cast_div_le (m := P) (n := q) (α := ℝ)
    linarith
  calc ∑ x ∈ Finset.Icc 1 P, F x ≤ ∑ x ∈ range (q * M), F x :=
        sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF i)
    _ = ∑ b ∈ range M, ∑ t ∈ range q, F (q * b + t) := karL3_sum_range_mul_split F q M
    _ ≤ ∑ b ∈ range M, (4 * U + 4 * q * Real.log q) := sum_le_sum hblock
    _ = M * (4 * U + 4 * q * Real.log q) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (P / q + 1) * (6 * (U + q * Real.log q)) := by
        apply mul_le_mul hMle (by nlinarith) (by positivity) (by positivity)
    _ = 6 * (U + q * Real.log q) * (P / q + 1) := by ring

end KarL3

/-- PROVED, formerly LEAF. Karacuba's Lemma 3, p. 244, his reference [2]: the classical bound
for `Σ min(U, 1/(αx+β))`, proved in `karL3_main` from the spacing of `ax/q` in blocks of `q`
consecutive `x`, with the constant 6 as stated. AI wrote the Lean code. -/
theorem leaf_karLemma3 : KarLemma3 := karL3_main

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
are proved in `leaf_large_case`. Part 4 of 2026-11-12: `KaracubaWSplit.karWBound_of_split`
proves this exact statement from display (4), PROVED there in the sharp Lagrange form, and the
narrower LEAF `leafW1_bound`, the bound of `W_1(a)`; it lives in a file above this one, so this
sorry stays until that LEAF is proved and moved here. -/
theorem leaf_W_bound (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by sorry

/-- `P2 = [P^{c1 - γ2/n³}]`, the shift length of the small `n` case, Karacuba p. 248. -/
noncomputable def karP2s (c1 γ2 : ℝ) (n P : ℕ) : ℕ :=
  ⌊(P : ℝ) ^ (c1 - γ2 / (n : ℝ) ^ 3)⌋₊

/-- `T(x) = Σ_{y=0}^{P2} e(f(x + y))`, Karacuba p. 248, with `M = P2`. -/
noncomputable def karT (f : ℝ → ℝ) (M a : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (M + 1), eC (f ((a + y : ℕ) : ℝ))

/-- The bound on `|T(x)|` that the case `2 ≤ n < n0` of Theorem 1 proves, p. 248, in the form
`|T(a)| ≤ A (P2+1) P^{-γ/n²}` for `N ≤ a` and `a + P2 ≤ N + P`, under `P ≥ e^{cn²}`, with
`P2 = [P^{c1 - γ2/n³}]` for some `γ2 > 0`. The condition `a + P2 ≤ N + P` keeps every point
`a + y` inside `[N, N+P]`, where the hypotheses hold. -/
def KarTBound (c0 c1 c2 c3 c4 : ℝ) : Prop :=
  ∃ A γ cc γ2 : ℝ, 0 < A ∧ 0 < γ ∧ 0 < cc ∧ 0 < γ2 ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n →
    (n : ℝ) < karN0 c1 c2 c4 → Real.exp (cc * (n : ℝ) ^ 2) ≤ P → ∀ (f : ℝ → ℝ) (T : Finset ℕ),
      KarHyp c0 c1 c2 c3 N P n f T → ∀ a : ℕ, N ≤ a → a + karP2s c1 γ2 n P ≤ N + P →
        ‖karT f (karP2s c1 γ2 n P) a‖ ≤
          A * ((karP2s c1 γ2 n P : ℝ) + 1) * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2))

/-- `B_s(x) = f^{(s)}(x)/s!`, Karacuba p. 248. -/
noncomputable def karB (f : ℝ → ℝ) (s : ℕ) (x : ℝ) : ℝ := iteratedDeriv s f x / s.factorial

/-- `Σ_{y=0}^{M} e(B_0 + B_1 y + ... + B_n y^n)` with `B_s = B_s(a)`, the trigonometric sum
to which Karacuba applies Lemma 2 on p. 248. -/
noncomputable def karTpoly (f : ℝ → ℝ) (n M a : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (M + 1), eC (∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s)

/-- `|e(x) - e(y)| ≤ 2π |x - y|`. -/
theorem norm_eC_sub_le (x y : ℝ) : ‖eC x - eC y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : eC x - eC y = eC y * (Complex.exp (Complex.I * ((2 * Real.pi * (x - y) : ℝ) : ℂ)) - 1) := by
    simp only [eC]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h, norm_mul, norm_eC, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- PROVED. The Taylor step of p. 248, inside `[N, N+P]`: for `N ≤ a` and `a + y ≤ N + P`,
`|f(a + y) - Σ_{s=0}^{n} B_s(a) y^s| ≤ (n+1) P^{-c1(n+1)} y^{n+1}`. Karacuba's Lagrange form
has no factor `n + 1`; Mathlib's `taylor_mean_remainder_bound` gives it, and it costs only a
constant since `n < n0` in this case. -/
theorem leafT_taylor {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hK : KarHyp c0 c1 c2 c3 N P n f T) (a y : ℕ) (ha : N ≤ a) (hay : a + y ≤ N + P) :
    |f ((a + y : ℕ) : ℝ) - ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s| ≤
      (n + 1) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (y : ℝ) ^ (n + 1) := by
  obtain ⟨⟨U, hUo, hIU, hfU⟩, hD, -⟩ := hK
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [Finset.sum_range_succ', karB]
  have haR : (N : ℝ) ≤ a := by exact_mod_cast ha
  have hayR : (a : ℝ) + y ≤ N + P := by exact_mod_cast hay
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlt : (a : ℝ) < a + y := by linarith
  have hsub : Set.Icc (a : ℝ) (a + y) ⊆ Set.Icc (N : ℝ) (N + P) :=
    Set.Icc_subset_Icc haR hayR
  have hsubU : Set.Icc (a : ℝ) (a + y) ⊆ U := hsub.trans hIU
  have hcd : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Icc (a : ℝ) (a + y)) := hfU.mono hsubU
  have hat : ∀ z ∈ Set.Icc (a : ℝ) (a + y), ContDiffAt ℝ (n + 1 : ℕ) f z := fun z hz =>
    hfU.contDiffAt (hUo.mem_nhds (hsubU hz))
  have huniq : UniqueDiffOn ℝ (Set.Icc (a : ℝ) (a + y)) := uniqueDiffOn_Icc hlt
  have hC : ∀ z ∈ Set.Icc (a : ℝ) (a + y),
      ‖iteratedDerivWithin (n + 1) f (Set.Icc (a : ℝ) (a + y)) z‖ ≤
        (n + 1).factorial * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := by
    intro z hz
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hat z hz) hz, Real.norm_eq_abs]
    have h1 := hD z (hsub hz)
    rw [abs_div, Nat.abs_cast, div_le_iff₀ (by positivity)] at h1
    linarith
  have hmem : ((a + y : ℕ) : ℝ) ∈ Set.Icc (a : ℝ) (a + y) := by
    push_cast; exact ⟨by linarith, le_rfl⟩
  have hb := taylor_mean_remainder_bound (n := n) hlt.le (by exact_mod_cast hcd) hmem hC
  have htay : taylorWithinEval f n (Set.Icc (a : ℝ) (a + y)) a ((a + y : ℕ) : ℝ) =
      ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : s ≤ n + 1 := by rw [Finset.mem_range] at hs; omega
    have hleft : (a : ℝ) ∈ Set.Icc (a : ℝ) (a + y) := ⟨le_rfl, hlt.le⟩
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
      ((hat _ hleft).of_le (by exact_mod_cast hs')) hleft]
    simp only [karB, smul_eq_mul]
    push_cast
    ring
  rw [htay, Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  push_cast
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The rational approximation of p. 248, made exact: for `0 < |B| ≤ 1/2`, with `q` the
nearest integer to `1/|B|` and numerator `±1`, `B = a/q + θ/q²`, `(a, q) = 1`, `|θ| ≤ 1`.
Karacuba writes `B_s = 1/Q_s + θ_s/Q_s²` with `Q_s` not said to be an integer. -/
theorem karT_round (B : ℝ) (hB0 : B ≠ 0) (hB1 : |B| ≤ 1 / 2) :
    ∃ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 ∧ |θ| ≤ 1 ∧ B = a / q + θ / (q : ℝ) ^ 2 ∧
      1 / |B| - 1 / 2 ≤ q ∧ (q : ℝ) ≤ 1 / |B| + 1 / 2 := by
  have hBp : 0 < |B| := abs_pos.2 hB0
  set X := 1 / |B| with hX
  have hX2 : 2 ≤ X := by rw [hX, le_div_iff₀ hBp]; linarith
  set q := ⌊X + 1 / 2⌋₊ with hq
  have hq1 : (q : ℝ) ≤ X + 1 / 2 := Nat.floor_le (by linarith)
  have hq2 : X + 1 / 2 < q + 1 := Nat.lt_floor_add_one _
  have hqpos : (0 : ℝ) < q := by linarith
  have hXB : X * |B| = 1 := by rw [hX]; field_simp
  -- |q|B| - 1| ≤ |B|/2
  have hdist : |(q : ℝ) * |B| - 1| ≤ |B| / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  rcases lt_or_gt_of_ne hB0 with hneg | hpos
  · refine ⟨-1, q, (q : ℝ) ^ 2 * (B + 1 / q), by simp, ?_, ?_, by linarith, hq1⟩
    · have hBa : |B| = -B := abs_of_neg hneg
      have : (q : ℝ) ^ 2 * (B + 1 / q) = -(q * ((q : ℝ) * |B| - 1)) := by
        rw [hBa]; field_simp <;> ring
      rw [this, abs_neg, abs_mul, abs_of_pos hqpos]
      calc (q : ℝ) * |(q : ℝ) * |B| - 1| ≤ q * (|B| / 2) :=
            mul_le_mul_of_nonneg_left hdist hqpos.le
        _ ≤ (X + 1 / 2) * (|B| / 2) := by gcongr
        _ = (1 + |B| / 2) / 2 := by rw [add_mul, mul_div_assoc', hXB]; ring
        _ ≤ 1 := by linarith
    · push_cast; field_simp; ring
  · refine ⟨1, q, (q : ℝ) ^ 2 * (B - 1 / q), by simp, ?_, ?_, by linarith, hq1⟩
    · have hBa : |B| = B := abs_of_pos hpos
      have : (q : ℝ) ^ 2 * (B - 1 / q) = q * ((q : ℝ) * |B| - 1) := by
        rw [hBa]; field_simp
      rw [this, abs_mul, abs_of_pos hqpos]
      calc (q : ℝ) * |(q : ℝ) * |B| - 1| ≤ q * (|B| / 2) :=
            mul_le_mul_of_nonneg_left hdist hqpos.le
        _ ≤ (X + 1 / 2) * (|B| / 2) := by gcongr
        _ = (1 + |B| / 2) / 2 := by rw [add_mul, mul_div_assoc', hXB]; ring
        _ ≤ 1 := by linarith
    · push_cast; field_simp; ring

/-- `τ` of Lemma 2 lies in `[min(t1, t2), 1]` when `t1 log M ≤ log q ≤ (s - t2) log M`. -/
theorem karTau_bounds (M q : ℝ) (s : ℕ) (hs : 2 ≤ s) (hM : 1 < M) (hq : 1 < q) (t1 t2 : ℝ)
    (hlo : t1 * Real.log M ≤ Real.log q) (hhi : Real.log q ≤ (s - t2) * Real.log M) (ht2 : t2 ≤ 1) :
    min t1 t2 ≤ karTau M q s ∧ karTau M q s ≤ 1 := by
  have hlM : 0 < Real.log M := Real.log_pos hM
  have hlq : 0 < Real.log q := Real.log_pos hq
  unfold karTau
  split_ifs with h1 h2
  · have hle : Real.log q ≤ Real.log M := Real.log_le_log (by linarith) h1
    constructor
    · exact (min_le_left _ _).trans (by rw [le_div_iff₀ hlM]; exact hlo)
    · rw [div_le_one hlM]; exact hle
  · exact ⟨(min_le_right _ _).trans ht2, le_rfl⟩
  · push Not at h1 h2
    have hgt : Real.log (M ^ (s - 1)) < Real.log q := Real.log_lt_log (by positivity) h2
    rw [Real.log_pow, Nat.cast_sub (by omega)] at hgt
    push_cast at hgt
    constructor
    · refine (min_le_right _ _).trans ?_
      have : Real.log q / Real.log M ≤ s - t2 := by rw [div_le_iff₀ hlM]; exact hhi
      linarith
    · have : (s - 1 : ℝ) < Real.log q / Real.log M := by rw [lt_div_iff₀ hlM]; exact hgt
      linarith

/-- `e(x + y) = e(x) e(y)`. -/
theorem eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  simp only [eC, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `e(0) = 1`. -/
theorem eC_zero : eC 0 = 1 := by simp [eC]

/-- `Σ_{y=0}^{M} e(B_0 + ... + B_n y^n)` is at most `1 + |Σ_{x=1}^{M} e(α_1 x + ... + α_{n+1} x^{n+1})|`
with `α_j = B_j` for `j ≤ n` and `α_{n+1} = 0`, the form of Lemma 2 with `m = 1`. -/
theorem karTpoly_le (f : ℝ → ℝ) (n M a : ℕ) :
    ‖karTpoly f n M a‖ ≤ 1 + ‖∑ x ∈ Finset.Icc 1 M, eC (((1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.Icc 1 (n + 1), (if j ≤ n then karB f j a else 0) * (x : ℝ) ^ j)‖ := by
  set α : ℕ → ℝ := fun j => if j ≤ n then karB f j a else 0
  set u : ℕ → ℝ := fun y => ∑ j ∈ Finset.Icc 1 (n + 1), α j * (y : ℝ) ^ j
  have hu : ∀ y : ℕ, ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s = karB f 0 a + u y := by
    intro y
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    simp only [pow_zero, mul_one, u]
    congr 1
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [α, if_neg (show ¬ n + 1 ≤ n by omega), zero_mul, add_zero]
    exact Finset.sum_congr rfl (fun j hj => by
      rw [Finset.mem_Icc] at hj; simp only [if_pos hj.2])
  have hu0 : u 0 = 0 := by
    simp only [u]
    exact Finset.sum_eq_zero (fun j hj => by
      rw [Finset.mem_Icc] at hj; simp [zero_pow (show j ≠ 0 by omega)])
  have hsum : karTpoly f n M a = eC (karB f 0 a) * (1 + ∑ x ∈ Finset.Icc 1 M, eC (u x)) := by
    rw [karTpoly]
    simp_rw [hu, eC_add]
    rw [← Finset.mul_sum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    push_cast
    rw [hu0, eC_zero]
  rw [hsum, norm_mul, norm_eC, one_mul]
  simp only [Nat.cast_one, one_mul]
  refine (norm_add_le _ _).trans ?_
  simp [u, α]

/-- `[x] ≥ x/2` for `x ≥ 1`. -/
theorem nat_floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff _ |>.2 hx
  rcases le_or_gt x 2 with h | h
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
/-- PROVED, from Lemma 2 only, formerly LEAF. The application of Lemma 2 on p. 248, Karacuba: with `γ1, γ2 > 0` small so that
`c2 + γ2/n³ < c1 < 1 - γ1/n²` and `P2 = [P^{c1 - γ2/n³}]`, by the hypothesis b) there is an
`s`, `2 ≤ s ≤ n`, with `P^{-c2 s} ≤ |B_s(x)| ≤ P^{-c3 s}`, so `B_s = 1/Q_s + θ_s/Q_s²` with
`|Q_s| ≤ P^{c2 s} < P2^s`; `τ` of Lemma 2 is bounded below by a positive constant, and
Lemma 2 with `n < n0` gives `|Σ_{y=0}^{P2} e(B_0 + B_1 y + ... + B_n y^n)| ≤ A (P2+1) P^{-γ/n²}`.
Only the `a` with `a + P2 ≤ N + P` are asked, so `B_s(a)` is taken at a point of `[N, N+P]`.
Karacuba's `Q_s` is real; Lemma 2 needs an integer `q` with `(a, q) = 1`, which the nearest
integer to `1/|B_s|` with numerator `±1` supplies, `karT_round`. Constants: `γ2 = c4`, so
`c1 - γ2/n³ ≥ c2 + δ` with `δ = c1 - c2 - c4/8`; `τ ≥ min(c3, δ/2)` and `τ ≤ 1`; `n < n0`
bounds `l`, `ρ` and `(8n)^{0.5 n l}`. -/
theorem leafT_lemma2 (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A γ cc γ2 : ℝ, 0 < A ∧ 0 < γ ∧ 0 < cc ∧ 0 < γ2 ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n →
        (n : ℝ) < karN0 c1 c2 c4 → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
        ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
          ∀ a : ℕ, N ≤ a → a + karP2s c1 γ2 n P ≤ N + P →
            ‖karTpoly f n (karP2s c1 γ2 n P) a‖ ≤
              A * ((karP2s c1 γ2 n P : ℝ) + 1) * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
  intro c0 c1 c2 c3 c4 h0 h1 h2' h3 h4 h0' h1' hc
  set n0 := karN0 c1 c2 c4 with hn0def
  have hn0 : (12 : ℝ) ≤ n0 := le_max_left _ _
  set δ := c1 - c2 - c4 / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ < 1 := by rw [hδdef]; linarith
  set l2 := Real.log 2 with hl2def
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set cc := l2 * (1 / c2 + 1 / c3 + 1 / δ) with hccdef
  have hcc : 0 < cc := by positivity
  have hcc2 : l2 ≤ cc * c2 := by
    have : cc * c2 = l2 * (1 + c2 / c3 + c2 / δ) := by rw [hccdef]; field_simp
    rw [this]; have : 0 ≤ c2 / c3 + c2 / δ := by positivity
    nlinarith
  have hcc3 : l2 ≤ cc * c3 := by
    have : cc * c3 = l2 * (c3 / c2 + 1 + c3 / δ) := by rw [hccdef]; field_simp
    rw [this]; have : 0 ≤ c3 / c2 + c3 / δ := by positivity
    nlinarith
  have hccδ : l2 ≤ cc * δ := by
    have : cc * δ = l2 * (δ / c2 + δ / c3 + 1) := by rw [hccdef]; field_simp
    rw [this]; have : 0 ≤ δ / c2 + δ / c3 := by positivity
    nlinarith
  set τ0 := min c3 (δ / 2) with hτ0def
  have hτ0 : 0 < τ0 := lt_min h3 (by linarith)
  have hτ0le : τ0 ≤ δ / 2 := min_le_right _ _
  set l0 := Real.log (12 * n0 * (n0 + 1) / τ0) with hl0def
  set ρ0 := τ0 / (3 * n0 ^ 2 * l0) with hρ0def
  set K0 := (8 * n0) ^ (0.5 * n0 * l0) with hK0def
  have hK0 : 0 ≤ K0 := Real.rpow_nonneg (by linarith) _
  have hl0pos : 0 < l0 := by
    apply Real.log_pos
    rw [one_lt_div hτ0]
    have : τ0 < 1 := by linarith
    nlinarith
  have hρ0 : 0 < ρ0 := by positivity
  set ρ1 := min ρ0 1 with hρ1def
  have hρ1 : 0 < ρ1 := lt_min hρ0 one_pos
  refine ⟨1 + K0, c2 * ρ1, cc, c4, by linarith, by positivity, hcc, h4, ?_⟩
  intro N P n hP hn hnn0 hPe f T hK a ha hay
  set M := karP2s c1 c4 n P with hMdef
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log P with hLdef
  have hL : cc * (n : ℝ) ^ 2 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hPe
    rwa [Real.log_exp] at this
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul hnR hnR (by norm_num) (by positivity)
      _ = (n : ℝ) ^ 2 := by ring
  have hL4 : 4 * cc ≤ L := by
    have := mul_le_mul_of_nonneg_left hn4 hcc.le
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hc2L : 4 * l2 ≤ c2 * L := by
    have := mul_le_mul_of_nonneg_left hL4 h2'.le
    linarith
  have hc3L : 4 * l2 ≤ c3 * L := by
    have := mul_le_mul_of_nonneg_left hL4 h3.le
    linarith
  have hδL : 4 * l2 ≤ δ * L := by
    have := mul_le_mul_of_nonneg_left hL4 hδ.le
    linarith
  have hrp : ∀ x : ℝ, (P : ℝ) ^ x = Real.exp (x * L) := fun x => by
    rw [Real.rpow_def_of_pos hP0, mul_comm]
  -- the exponent of P2
  set e := c1 - c4 / (n : ℝ) ^ 3 with hedef
  have hn3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (8 : ℝ) = 2 * 4 := by norm_num
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul hnR hn4 (by norm_num) (by positivity)
      _ = (n : ℝ) ^ 3 := by ring
  have he1 : e ≤ c1 := by
    have : 0 ≤ c4 / (n : ℝ) ^ 3 := by positivity
    rw [hedef]; linarith
  have he2 : c2 + δ ≤ e := by
    rw [hedef, hδdef]
    have : c4 / (n : ℝ) ^ 3 ≤ c4 / 8 := div_le_div_of_nonneg_left h4.le (by norm_num) hn3
    linarith
  have heL : e * L ≤ L := mul_le_of_le_one_left hL0 (by linarith)
  have heL2 : (c2 + δ) * L ≤ e * L := mul_le_mul_of_nonneg_right he2 hL0
  have hM_le : (M : ℝ) ≤ (P : ℝ) ^ e := Nat.floor_le (Real.rpow_nonneg hP0.le _)
  have hPc2 : (2 : ℝ) ≤ (P : ℝ) ^ c2 := by
    rw [hrp, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact Real.exp_le_exp.2 (by linarith)
  have hPe2 : 2 * (P : ℝ) ^ c2 ≤ (P : ℝ) ^ e := by
    rw [hrp, hrp, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hM_ge : (P : ℝ) ^ c2 ≤ M := by
    have := nat_floor_ge_half (show (1 : ℝ) ≤ (P : ℝ) ^ e by linarith)
    rw [hMdef, karP2s]; linarith
  have hM2 : (2 : ℝ) ≤ M := hPc2.trans hM_ge
  set lam := Real.log M with hlamdef
  have hlam_hi : lam ≤ L := by
    have h := Real.log_le_log (by linarith) hM_le
    rw [Real.log_rpow hP0] at h
    linarith
  have hlam_lo : e * L - l2 ≤ lam := by
    have h := Real.log_le_log (by positivity) (show (P : ℝ) ^ e / 2 ≤ M by
      have := nat_floor_ge_half (show (1 : ℝ) ≤ (P : ℝ) ^ e by linarith)
      rw [hMdef, karP2s]; exact this)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hP0] at h
    exact h
  have hlam0 : 0 < lam := Real.log_pos (by linarith)
  -- the index s and the coefficient B
  obtain ⟨-, -, hTsub, hTcard, hTb⟩ := hK
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTcard
    exact_mod_cast this
  obtain ⟨s, hs⟩ := hTne
  have hs2 := Finset.mem_Icc.1 (hTsub hs)
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs2.1
  have hs3 : 2 * (c3 * L) ≤ s * (c3 * L) :=
    mul_le_mul_of_nonneg_right hsR (by positivity)
  have haI : (a : ℝ) ∈ Set.Icc (N : ℝ) (N + P) := by
    constructor
    · exact_mod_cast ha
    · have : a ≤ N + P := by omega
      exact_mod_cast this
  obtain ⟨hBlo, hBhi⟩ := hTb s hs a haI
  set B := iteratedDeriv s f a / s.factorial with hBdef
  have hBpos : 0 < |B| := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hBlo
  have hBhalf : |B| ≤ 1 / 2 := by
    refine hBhi.trans ?_
    rw [hrp, show (1 : ℝ) / 2 = Real.exp (-l2) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    exact Real.exp_le_exp.2 (by linarith)
  obtain ⟨a', q, θ, hgcd, hθ, hBeq, hqlo, hqhi⟩ := karT_round B (abs_pos.1 hBpos) hBhalf
  -- 1/|B| between P^{c3 s} and P^{c2 s}
  have hinvlo : (P : ℝ) ^ (c3 * s) ≤ 1 / |B| := by
    rw [le_div_iff₀ hBpos]
    have := mul_le_mul_of_nonneg_left hBhi (Real.rpow_nonneg hP0.le (c3 * s))
    rwa [← Real.rpow_add hP0, add_neg_cancel, Real.rpow_zero] at this
  have hinvhi : 1 / |B| ≤ (P : ℝ) ^ (c2 * s) := by
    rw [div_le_iff₀ hBpos]
    have := mul_le_mul_of_nonneg_left hBlo (Real.rpow_nonneg hP0.le (c2 * s))
    rwa [← Real.rpow_add hP0, add_neg_cancel, Real.rpow_zero] at this
  have hc3s : 2 * l2 ≤ c3 * s * L := by linarith
  have hPc3s : (2 : ℝ) ≤ (P : ℝ) ^ (c3 * s) := by
    rw [hrp, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact Real.exp_le_exp.2 (by linarith)
  have hq1 : (1 : ℝ) < q := by linarith
  have hqlo' : (P : ℝ) ^ (c3 * s) / 2 ≤ q := by linarith
  have hqhi' : (q : ℝ) ≤ 2 * (P : ℝ) ^ (c2 * s) := by
    have : (1 : ℝ) ≤ (P : ℝ) ^ (c2 * s) := by linarith
    linarith
  have hlogq_lo : c3 * s * L - l2 ≤ Real.log q := by
    have h := Real.log_le_log (by positivity) hqlo'
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_rpow hP0] at h
  have hlogq_hi : Real.log q ≤ l2 + c2 * s * L := by
    have h := Real.log_le_log (by linarith) hqhi'
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hP0] at h
  have ht1 : c3 * lam ≤ Real.log q := by
    have : c3 * lam ≤ c3 * L := mul_le_mul_of_nonneg_left hlam_hi h3.le
    linarith
  have ht2 : Real.log q ≤ (s - δ / 2) * lam := by
    have hs' : 0 ≤ (s : ℝ) - δ / 2 := by linarith
    have hstep : l2 + c2 * s * L ≤ (s - δ / 2) * (e * L - l2) := by
      have ha' := mul_le_mul_of_nonneg_left heL2 (by linarith : (0 : ℝ) ≤ s)
      have hb' := mul_le_mul_of_nonneg_left heL (by linarith : (0 : ℝ) ≤ δ / 2)
      have hc' : 0 ≤ ((s : ℝ) - 1 / 2) * (δ * L - 2 * l2) :=
        mul_nonneg (by linarith) (by linarith)
      have hd' : 0 ≤ ((s : ℝ) - 2) * l2 := mul_nonneg (by linarith) hl2.le
      have he' : 0 ≤ δ / 2 * l2 := by positivity
      linarith
    calc Real.log q ≤ l2 + c2 * s * L := hlogq_hi
      _ ≤ (s - δ / 2) * (e * L - l2) := hstep
      _ ≤ (s - δ / 2) * lam := mul_le_mul_of_nonneg_left hlam_lo hs'
  have hτ := karTau_bounds M q s hs2.1 (by linarith) hq1 c3 (δ / 2) ht1 ht2 (by linarith)
  have hqM : (q : ℝ) < (M : ℝ) ^ s := by
    rw [← Real.exp_log (show (0 : ℝ) < q by linarith),
      ← Real.exp_log (show (0 : ℝ) < (M : ℝ) ^ s by positivity), Real.exp_lt_exp,
      Real.log_pow]
    have := mul_pos (show (0 : ℝ) < δ / 2 by linarith) hlam0
    linarith
  -- Lemma 2
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast this
  have hL2 := h2 n 1 M (by omega) one_pos hMpos (fun j => if j ≤ n then karB f j a else 0) s
    hs2.1 (by omega) a' q θ hgcd (by exact_mod_cast hq1) hqM hθ
    (by simp only [if_pos hs2.2, karB]; exact hBeq)
  simp only at hL2
  set τ := karTau M q s with hτdef
  obtain ⟨hτlo, hτhi⟩ := hτ
  have hτlo' : τ0 ≤ τ := hτlo
  have hτpos : 0 < τ := lt_of_lt_of_le hτ0 hτlo'
  set l := Real.log (12 * n * (n + 1) / τ) with hldef
  have hlpos : 0 < l := by
    apply Real.log_pos
    rw [one_lt_div hτpos]
    have : (72 : ℝ) ≤ 12 * n * (n + 1) := by
      calc (72 : ℝ) = 12 * 2 * (2 + 1) := by norm_num
        _ ≤ 12 * n * (n + 1) := by gcongr
    linarith
  have hnn0' : (n : ℝ) ≤ n0 := hnn0.le
  have hll0 : l ≤ l0 := by
    apply Real.log_le_log (by positivity)
    refine div_le_div₀ (by positivity) ?_ hτ0 hτlo'
    have h5 : (n : ℝ) + 1 ≤ n0 + 1 := by linarith
    have h6 : (12 : ℝ) * n ≤ 12 * n0 := by linarith
    exact mul_le_mul h6 h5 (by positivity) (by positivity)
  set ρ := τ / (3 * (n : ℝ) ^ 2 * l) with hρdef
  have hρ0ρ : ρ0 ≤ ρ := by
    apply div_le_div₀ hτpos.le hτlo' (by positivity)
    have : (n : ℝ) ^ 2 ≤ n0 ^ 2 := pow_le_pow_left₀ (by positivity) hnn0' 2
    have : (n : ℝ) ^ 2 * l ≤ n0 ^ 2 * l0 := mul_le_mul this hll0 hlpos.le (by positivity)
    linarith
  have hK : (8 * (n : ℝ)) ^ (0.5 * n * l) ≤ K0 := by
    calc (8 * (n : ℝ)) ^ (0.5 * n * l) ≤ (8 * n0) ^ (0.5 * n * l) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (8 * n0) ^ (0.5 * n0 * l0) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          have : (n : ℝ) * l ≤ n0 * l0 := mul_le_mul hnn0' hll0 hlpos.le (by linarith)
          linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMρ : (M : ℝ) ^ (1 - ρ) ≤ M * (P : ℝ) ^ (-(c2 * ρ1 / (n : ℝ) ^ 2)) := by
    have hρ1ρ : ρ1 ≤ ρ := (min_le_left _ _).trans hρ0ρ
    calc (M : ℝ) ^ (1 - ρ) ≤ (M : ℝ) ^ (1 + -ρ1) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ = M * (M : ℝ) ^ (-ρ1) := by rw [Real.rpow_add (by linarith), Real.rpow_one]
      _ ≤ M * ((P : ℝ) ^ c2) ^ (-ρ1) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hM_ge (by linarith)
      _ = M * (P : ℝ) ^ (-(c2 * ρ1)) := by
          rw [← Real.rpow_mul hP0.le]; ring_nf
      _ ≤ M * (P : ℝ) ^ (-(c2 * ρ1 / (n : ℝ) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Real.rpow_le_rpow_of_exponent_le hP1
          rw [neg_le_neg_iff]
          apply div_le_self (by positivity)
          linarith
  have hone : (1 : ℝ) ≤ M * (P : ℝ) ^ (-(c2 * ρ1 / (n : ℝ) ^ 2)) := by
    have hexp : -(c2 * ρ1 / (n : ℝ) ^ 2) ≥ -c2 := by
      rw [ge_iff_le, neg_le_neg_iff]
      calc c2 * ρ1 / (n : ℝ) ^ 2 ≤ c2 * ρ1 := div_le_self (by positivity) (by linarith)
        _ ≤ c2 * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) h2'.le
        _ = c2 := mul_one _
    calc (1 : ℝ) = (P : ℝ) ^ c2 * (P : ℝ) ^ (-c2) := by
          rw [← Real.rpow_add hP0, add_neg_cancel, Real.rpow_zero]
      _ ≤ M * (P : ℝ) ^ (-(c2 * ρ1 / (n : ℝ) ^ 2)) :=
          mul_le_mul hM_ge (Real.rpow_le_rpow_of_exponent_le hP1 hexp)
            (Real.rpow_nonneg hP0.le _) (by linarith)
  have hm1 : ((1 : ℕ) : ℝ) ^ (2 * ρ / τ) = 1 := by simp
  rw [hm1, mul_one] at hL2
  set E := (P : ℝ) ^ (-(c2 * ρ1 / (n : ℝ) ^ 2)) with hEdef
  have hE0 : 0 ≤ E := Real.rpow_nonneg hP0.le _
  calc ‖karTpoly f n M a‖ ≤ 1 + _ := karTpoly_le f n M a
    _ ≤ M * E + K0 * (M * E) := by
        refine add_le_add hone (hL2.le.trans ?_)
        exact mul_le_mul hK hMρ (Real.rpow_nonneg (by linarith) _) hK0
    _ = (1 + K0) * M * E := by ring
    _ ≤ (1 + K0) * ((M : ℝ) + 1) * E := by
        gcongr
        linarith

/-- `P^{-c1(n+1)} P2^{n+1} ≤ P^{-γ2/n²}` for `P2 = [P^{c1 - γ2/n³}]`, `P ≥ 1`, p. 248. -/
theorem karP2s_taylor_err {c1 γ2 : ℝ} (hγ2 : 0 < γ2) {n P : ℕ} (hn : 1 ≤ n) (hP : 0 < P) :
    (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * ((karP2s c1 γ2 n P : ℕ) : ℝ) ^ (n + 1) ≤
      (P : ℝ) ^ (-(γ2 / (n : ℝ) ^ 2)) := by
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e := c1 - γ2 / (n : ℝ) ^ 3
  have hM : ((karP2s c1 γ2 n P : ℕ) : ℝ) ≤ (P : ℝ) ^ e :=
    Nat.floor_le (Real.rpow_nonneg hP0.le _)
  have hMp : ((karP2s c1 γ2 n P : ℕ) : ℝ) ^ (n + 1) ≤ (P : ℝ) ^ (e * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul hP0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
  calc (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * ((karP2s c1 γ2 n P : ℕ) : ℝ) ^ (n + 1)
      ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (P : ℝ) ^ (e * ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hMp (Real.rpow_nonneg hP0.le _)
    _ = (P : ℝ) ^ (-(γ2 * ((n : ℝ) + 1) / (n : ℝ) ^ 3)) := by
        rw [← Real.rpow_add hP0]
        congr 1
        simp only [e]
        push_cast
        ring
    _ ≤ (P : ℝ) ^ (-(γ2 / (n : ℝ) ^ 2)) := by
        apply Real.rpow_le_rpow_of_exponent_le hP1
        rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) ≤ γ2 * (n : ℝ) ^ 2 := by positivity
        nlinarith

/-- PROVED from the LEAF `leafT_lemma2` and the PROVED `leafT_taylor`: the exact statement of
`KaracubaCore.leaf_T_bound`, Karacuba p. 248. `T(x) = Σ_y e(B_0 + ... + B_n y^n)` plus an
error of at most `2π (n+1) (P2+1) P^{-γ2/n²}`, Karacuba's `4π θ_1 (P2 + 1) P^{-γ2/n²}` up to
the factor `(n+1)/2`, a constant since `n < n0`. -/
theorem karTBound_of_split (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarTBound c0 c1 c2 c3 c4 := by
  intro c0 c1 c2 c3 c4 h0 h1 h2' h3 h4 h0' h1' hc
  obtain ⟨A, γ, cc, γ2, hA, hγ, hcc, hγ2, hL⟩ :=
    leafT_lemma2 h2 c0 c1 c2 c3 c4 h0 h1 h2' h3 h4 h0' h1' hc
  have hN0 : (0 : ℝ) ≤ karN0 c1 c2 c4 := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨A + 2 * Real.pi * (karN0 c1 c2 c4 + 1), min γ γ2, cc, γ2, by positivity,
    lt_min hγ hγ2, hcc, hγ2, ?_⟩
  intro N P n hP hn hn0 hPe f T hK a ha hay
  set M := karP2s c1 γ2 n P with hMdef
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hpoly := hL N P n hP hn hn0 hPe f T hK a ha hay
  set E := (P : ℝ) ^ (-(min γ γ2 / (n : ℝ) ^ 2)) with hE
  have hEγ : (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hn2.le
  have hEγ2 : (P : ℝ) ^ (-(γ2 / (n : ℝ) ^ 2)) ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_right _ _) hn2.le
  have herr := karP2s_taylor_err (c1 := c1) hγ2 (by omega : 1 ≤ n) hP
  rw [← hMdef] at herr
  have hdiff : ‖karT f M a - karTpoly f n M a‖ ≤
      ((M : ℝ) + 1) * (2 * Real.pi * ((n : ℝ) + 1) * E) := by
    rw [karT, karTpoly, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hcard : ((M : ℝ) + 1) = ((Finset.range (M + 1)).card : ℝ) := by simp
    rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun y hy => ?_)
    have hyM : y ≤ M := by rw [Finset.mem_range] at hy; omega
    refine (norm_eC_sub_le _ _).trans ?_
    have ht := leafT_taylor hK a y ha (by omega)
    have hyp : (y : ℝ) ^ (n + 1) ≤ (M : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hyM) _
    have hPpos : (0 : ℝ) ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := Real.rpow_nonneg (by linarith) _
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have : |f ((a + y : ℕ) : ℝ) - ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s| ≤
        ((n : ℝ) + 1) * E := by
      refine ht.trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hn1
      calc (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (y : ℝ) ^ (n + 1)
          ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (M : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hyp hPpos
        _ ≤ _ := herr.trans hEγ2
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi * |f ((a + y : ℕ) : ℝ) - ∑ s ∈ Finset.range (n + 1), karB f s a * (y : ℝ) ^ s|
        ≤ 2 * Real.pi * (((n : ℝ) + 1) * E) := mul_le_mul_of_nonneg_left this h2pi
      _ = 2 * Real.pi * ((n : ℝ) + 1) * E := by ring
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by linarith) _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hnle : (n : ℝ) + 1 ≤ karN0 c1 c2 c4 + 1 := by linarith
  calc ‖karT f M a‖ ≤ ‖karTpoly f n M a‖ + ‖karT f M a - karTpoly f n M a‖ := by
        have := norm_add_le (karTpoly f n M a) (karT f M a - karTpoly f n M a)
        rwa [add_sub_cancel] at this
    _ ≤ A * ((M : ℝ) + 1) * E + ((M : ℝ) + 1) * (2 * Real.pi * ((n : ℝ) + 1) * E) := by
        gcongr
        exact hpoly.trans (mul_le_mul_of_nonneg_left hEγ (by positivity))
    _ ≤ (A + 2 * Real.pi * (karN0 c1 c2 c4 + 1)) * ((M : ℝ) + 1) * E := by
        have : 2 * Real.pi * ((n : ℝ) + 1) ≤ 2 * Real.pi * (karN0 c1 c2 c4 + 1) :=
          mul_le_mul_of_nonneg_left hnle (by positivity)
        have h3 : 0 ≤ ((M : ℝ) + 1) * E := mul_nonneg hM0 hE0
        nlinarith


/-- PROVED from the CITED Lemma 2 alone, p4 of 2026-11-12, by `karTBound_of_split`, formerly
LEAF. The bound on `T(x)` in the case `2 ≤ n < n0` of the proof of Theorem 1, Karacuba
p. 248, as a deduction from Lemma 2: with `γ1, γ2` small so that
`c2 + γ2/n³ < c1 < 1 - γ1/n²`, Taylor's formula `f(x+y) = B_0 + B_1 y + ... + B_n y^n + R`
with `|R| ≤ 2P^{-γ2/n²}`, so `T(x) = Σ_y e(B_0 + ... + B_n y^n) + 4π θ_1 (P2+1) P^{-γ2/n²}`,
and Lemma 2 at one `s`, `2 ≤ s ≤ n`, with `B_s = 1/Q_s + θ_s/Q_s²`, `Q_s ≤ P^{c2 s} < P2^s`;
`τ` is bounded below by a positive constant since `n < n0`. Only the `a` with
`a + P2 ≤ N + P` are asked, so Taylor's formula is used inside `[N, N+P]`; the rest of the
case, the shift and the last `P2` values of `x`, is proved in `smallCase_of_T`. -/
theorem leaf_T_bound (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarTBound c0 c1 c2 c3 c4 := karTBound_of_split h2

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
theorem leaf_s1_case : LeafS1Case := by sorry
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


/-! ### The small `n` case, p. 248, with the endpoint repair made explicit -/

/-- PROVED. The shift of p. 248: shifting the sum by `y`, `0 ≤ y ≤ M`, and averaging,
`S = (M+1)^{-1} Σ_x T(x) + θ'` with `|θ'| ≤ 2M`, as the paper's `2θP2`. -/
theorem shift_average1 (g : ℕ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (N P₁ M : ℕ) :
    ‖∑ k ∈ Finset.range P₁, g (N + k) - ((M : ℂ) + 1)⁻¹ *
      ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), g (N + k + y)‖ ≤ 2 * (M : ℝ) := by
  set S := ∑ k ∈ Finset.range P₁, g (N + k)
  have hM : ((M : ℂ) + 1) ≠ 0 := by
    have : ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero M
  have hswap : ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), g (N + k + y) =
      ∑ y ∈ Finset.range (M + 1), ∑ k ∈ Finset.range P₁, g (N + k + y) := Finset.sum_comm
  have hD : S - ((M : ℂ) + 1)⁻¹ * ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1),
        g (N + k + y) =
      ((M : ℂ) + 1)⁻¹ * ∑ y ∈ Finset.range (M + 1), (S - ∑ k ∈ Finset.range P₁, g (N + k + y)) := by
    rw [hswap]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hD, norm_mul]
  have hinv : ‖((M : ℂ) + 1)⁻¹‖ = ((M : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    have : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hinv]
  have hbound : ‖∑ y ∈ Finset.range (M + 1), (S - ∑ k ∈ Finset.range P₁, g (N + k + y))‖ ≤
      ((M : ℝ) + 1) * (2 * (M : ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ y ∈ Finset.range (M + 1),
        ‖S - ∑ k ∈ Finset.range P₁, g (N + k + y)‖ ≤ 2 * (M : ℝ) := by
      intro y hy
      refine (shift_step g hg N P₁ y).trans ?_
      have hy' : y ≤ M := by have := Finset.mem_range.1 hy; omega
      have : (y : ℝ) ≤ M := by exact_mod_cast hy'
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    simp
  calc _ ≤ ((M : ℝ) + 1)⁻¹ * (((M : ℝ) + 1) * (2 * (M : ℝ))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * (M : ℝ) := by field_simp

/-- PROVED. The case `2 ≤ n < n0` of Theorem 1 from the bound on `T(x)`, Karacuba p. 248,
with the endpoint repair made explicit: the shift of `shift_average1`, the `x` with
`x + P2 ≤ N + P` by `KarTBound`, the last `P2` values of `x`, where `x + y` can pass `N + P`,
trivially, at cost `P2`, and `P2 ≤ P^{c1} ≤ P^{1-γ/n²}`. -/
theorem smallCase_of_T {c0 c1 c2 c3 c4 : ℝ} (hc1 : c1 < 1) (hT : KarTBound c0 c1 c2 c3 c4) :
    KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) := by
  obtain ⟨A, γ, cc, γ2, hA, hγ, hcc, hγ2, hb⟩ := hT
  refine ⟨A + 3, min γ (1 - c1), cc, by positivity, lt_min hγ (by linarith), hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH P₁ hP₁ hP₁P
  set M := karP2s c1 γ2 n P with hMdef
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
  set X := ∑ k ∈ Finset.range P₁, ∑ y ∈ Finset.range (M + 1), g (N + k + y) with hXdef
  have h3 := shift_average1 g hg N P₁ M
  have hTk : ∀ k, ∑ y ∈ Finset.range (M + 1), g (N + k + y) = karT f M (N + k) := by
    intro k
    unfold karT
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [hgdef]
  have hTtriv : ∀ a, ‖karT f M a‖ ≤ (M : ℝ) + 1 := by
    intro a
    unfold karT
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun y _ => (norm_eC _).le)).trans ?_
    simp
  set E := (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) with hEdef
  have hE0 : 0 ≤ E := Real.rpow_nonneg hPr.le _
  have hTk' : ∀ k ∈ Finset.range P₁, ‖karT f M (N + k)‖ ≤
      A * ((M : ℝ) + 1) * E + ((M : ℝ) + 1) * (if P < k + M then 1 else 0) := by
    intro k hk
    by_cases hkP : P < k + M
    · rw [if_pos hkP]
      have : 0 ≤ A * ((M : ℝ) + 1) * E := by positivity
      linarith [hTtriv (N + k)]
    · rw [if_neg hkP, mul_zero, add_zero]
      exact hb N P n hP hn hpred hbig f T hH (N + k) (by omega) (by omega)
  have hcount : ∑ k ∈ Finset.range P₁, (if P < k + M then (1 : ℝ) else 0) ≤ (M : ℝ) := by
    rw [Finset.sum_boole]
    have hsub : (Finset.range P₁).filter (fun k => P < k + M) ⊆ Finset.Ico (P₁ - M) P₁ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ico]; omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    have : ((Finset.range P₁).filter (fun k => P < k + M)).card ≤ M := by omega
    exact_mod_cast this
  have hXb : ‖X‖ ≤ P₁ * (A * ((M : ℝ) + 1) * E) + ((M : ℝ) + 1) * (M : ℝ) := by
    rw [hXdef]
    refine (norm_sum_le _ _).trans ?_
    have hTk'' : ∀ k ∈ Finset.range P₁, ‖∑ y ∈ Finset.range (M + 1), g (N + k + y)‖ ≤
        A * ((M : ℝ) + 1) * E + ((M : ℝ) + 1) * (if P < k + M then 1 else 0) := by
      intro k hk; rw [hTk k]; exact hTk' k hk
    refine (Finset.sum_le_sum hTk'').trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)
    linarith
  have hinv : ‖((M : ℂ) + 1)⁻¹‖ = ((M : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    have : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmain : ‖∑ k ∈ Finset.range P₁, g (N + k)‖ ≤ P₁ * A * E + 3 * (M : ℝ) := by
    have hsplit : ∑ k ∈ Finset.range P₁, g (N + k) =
        (∑ k ∈ Finset.range P₁, g (N + k) - ((M : ℂ) + 1)⁻¹ * X) +
          ((M : ℂ) + 1)⁻¹ * X := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hinv]
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h2 : ((M : ℝ) + 1)⁻¹ * ‖X‖ ≤ P₁ * A * E + (M : ℝ) := by
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
  have hM1 : (M : ℝ) ≤ (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by
    set e := c1 - γ2 / (n : ℝ) ^ 3
    have hMle : (M : ℝ) ≤ (P : ℝ) ^ e := Nat.floor_le (Real.rpow_nonneg hPr.le _)
    have he : e ≤ 1 - γf / (n : ℝ) ^ 2 := by
      have h1 : 0 ≤ γ2 / (n : ℝ) ^ 3 := by positivity
      have hq : γf / (n : ℝ) ^ 2 ≤ γf := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ γf := le_min hγ.le (by linarith)
        nlinarith
      have : e = c1 - γ2 / (n : ℝ) ^ 3 := rfl
      linarith
    exact hMle.trans (Real.rpow_le_rpow_of_exponent_le hP1r he)
  rw [hS]
  calc _ ≤ P₁ * A * E + 3 * (M : ℝ) := hmain
    _ = A * ((P₁ : ℝ) * E) + 3 * (M : ℝ) := by ring
    _ ≤ A * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) + 3 * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hPE hA.le
        linarith
    _ = (A + 3) * (P : ℝ) ^ (1 - γf / (n : ℝ) ^ 2) := by ring

/-- PROVED from `leaf_T_bound`. The case `2 ≤ n < n0` of the proof of Theorem 1, Karacuba
p. 248, as a deduction from Lemma 2, with the endpoint repair explicit in `smallCase_of_T`. -/
theorem leaf_small_case (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) := by
  intro c0 c1 c2 c3 c4 h0 h1' h2' h3' h4' h01 h11 h241
  exact smallCase_of_T h11 (leaf_T_bound h2 c0 c1 c2 c3 c4 h0 h1' h2' h3' h4' h01 h11 h241)
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
`leaf_s1_case`; `leaf_karLemma3` and `leaf_T_bound` are PROVED. The route that avoids `leaf_s1_case`
is `lemma10Kar_of_karacuba` below. -/
theorem lemma10_of_karacuba : Lemma10 := lemma10_of_thm1 karacubaTheorem1 leaf_s1_case

/-! ### Lemma 10 with `S ⊆ [2, k-1]`, coordinator decision 1 -/

/-- The class `𝓕(N, θ, Θ, Θ₀, δ)` of Lemma 10 as in Karacuba's Theorem 1, p. 244: exactly
`KClass` of State1539Data264 except that `S ⊆ {2, ..., k-1}`, matching Karacuba's
`2 ≤ s_j ≤ n` with `n = k - 1`. P0082 p. 371 prints `S ⊆ {1, ..., k-1}`. -/
def KClassKar (N : ℕ) (θ Θ Θ₀ δ : ℝ) (f : ℝ → ℝ) (k : ℕ) : Prop :=
  3 ≤ k ∧ (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) ∧
  (∀ x ∈ Set.Icc (N : ℝ) (2 * N), |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) ∧
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 2 (k - 1) ∧ δ * k ≤ S.card ∧
    ∀ s ∈ S, ∀ x ∈ Set.Icc (N : ℝ) (2 * N),
      (N : ℝ) ^ (-(θ * s)) ≤ |iteratedDeriv s f x / s.factorial| ∧
      |iteratedDeriv s f x / s.factorial| ≤ (N : ℝ) ^ (-(Θ * s))

/-- Lemma 10 of P0082 with the class `KClassKar`, that is with `s ≥ 2` as in Karacuba's
Theorem 1. Exactly `Lemma10` of State1539Data264 with `KClass` replaced by `KClassKar`. -/
def Lemma10Kar : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      KClassKar N θ Θ Θ₀ δ f k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- PROVED. The notation bridge for `Lemma10Kar`, Brudern-Perelli p. 371: from Karacuba's
Theorem 1 with `n = k - 1`, `P = P₁ = N`, `c0 = δ`, `c1 = Θ₀`, `c2 = θ`, `c3 = Θ`,
`c4 = (Θ₀ - θ)/2` and `T = S`. No `S = {1}` case arises, so `LeafS1Case` is not used. -/
theorem lemma10Kar_of_thm1 (hK : KaracubaTheorem1) : Lemma10Kar := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨A, γ, hA, hγ, hKb⟩ := hK δ Θ₀ θ Θ ((Θ₀ - θ) / 2) hδ0
    (by linarith) (by linarith) hΘ0 (by linarith) hδ1 hΘ₀1 (by linarith)
  refine ⟨A + 2, min γ 1, by positivity, by positivity, ?_⟩
  intro N hN f k hf
  obtain ⟨hk3, hsm, hder, S, hSsub, hScard, hSb⟩ := hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set c := min γ 1 with hcdef
  have hcγ : c ≤ γ := min_le_left _ _
  have hc1' : c ≤ 1 := min_le_right _ _
  have hc0 : 0 < c := by positivity
  have hk9 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    nlinarith
  have hexp0 : 0 ≤ 1 - c / (k : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hX1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := Real.one_le_rpow hNr hexp0
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn2 : 2 ≤ n := by omega
  have hI : Set.Icc (N : ℝ) (N + N) = Set.Icc (N : ℝ) (2 * N) := by rw [two_mul]
  have hcardS : δ * n ≤ S.card := by
    push_cast at hScard
    nlinarith
  have hKH : KarHyp δ Θ₀ θ Θ N N n f S := by
    refine ⟨?_, ?_, ?_, hcardS, ?_⟩
    · rw [hI]; exact hsm
    · rw [hI]; exact hder
    · intro s hs
      have := Finset.mem_Icc.1 (hSsub hs)
      exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
    · intro s hs x hx
      rw [hI] at hx
      exact hSb s hs x hx
  have hb := hKb N N n (by omega) hn2 f S hKH N (by omega) le_rfl
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
    _ ≤ (A + 2) * (N : ℝ) ^ (1 - c / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        nlinarith

/-- `Lemma10Kar` from the leaves of this file. CONDITIONAL on the CITED `leaf_karLemma1_mvt`
and `leaf_karLemma2` and the LEAF `leaf_W_bound`; `leaf_karLemma3` and `leaf_T_bound` are PROVED; it does
NOT use the QUESTION leaf `leaf_s1_case`. -/
theorem lemma10Kar_of_karacuba : Lemma10Kar := lemma10Kar_of_thm1 karacubaTheorem1

/-- PROVED. A member of the lab class `KClass` with `δ k ≥ 2` is a member of `KClassKar`
with `δ/2`: drop `s = 1` from `S`, which costs at most one element, and
`δ k - 1 ≥ δ k / 2` when `δ k ≥ 2`. This is the fact the consumer of P0082 p. 377 needs,
where `k = [9 (log N)^{γ-1}] + 1` tends to infinity. -/
theorem kclassKar_of_kclass {N : ℕ} {θ Θ Θ₀ δ : ℝ} {f : ℝ → ℝ} {k : ℕ}
    (h : KClass N θ Θ Θ₀ δ f k) (hk : 2 ≤ δ * k) : KClassKar N θ Θ Θ₀ (δ / 2) f k := by
  obtain ⟨hk3, hsm, hder, S, hSsub, hScard, hSb⟩ := h
  refine ⟨hk3, hsm, hder, S.filter (fun s => 2 ≤ s), ?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_filter] at hs
    have := Finset.mem_Icc.1 (hSsub hs.1)
    exact Finset.mem_Icc.2 ⟨hs.2, this.2⟩
  · have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun s => 2 ≤ s)
    have hneg : (S.filter (fun s => ¬ 2 ≤ s)).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      have := Finset.mem_Icc.1 (hSsub ha.1)
      have := Finset.mem_Icc.1 (hSsub hb.1)
      omega
    have hle : (S.card : ℝ) ≤ (S.filter (fun s => 2 ≤ s)).card + 1 := by
      rw [← hsplit]; push_cast
      have : ((S.filter (fun s => ¬ 2 ≤ s)).card : ℝ) ≤ 1 := by exact_mod_cast hneg
      linarith
    linarith
  · intro s hs x hx
    rw [Finset.mem_filter] at hs
    exact hSb s hs.1 x hx


end LeanLab.ExceptionalSet.U1539.KaracubaCore

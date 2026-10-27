/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file b of three.

The linear sieve machinery behind Chen's theorem, part 2: Rosser's weights of level `D` with
`β = 2` (Iwaniec-Kowalski (6.30), Section 6.4; Friedlander-Iwaniec, Opera de Cribro, ch. 6 and
11), the upper and lower bound sieve inequalities they satisfy, the remainder bookkeeping, the
Jurkat-Richert / Iwaniec main term bounds with `F(s)`, `f(s)` (Iwaniec-Kowalski Theorem 11.13,
Halberstam-Richert ch. 8 Theorem 8.3 and 8.4), and the fundamental lemma (Iwaniec-Kowalski
Lemma 6.3 and Theorem 6.9). Sieve problems are Mathlib's `BoundingSieve`
(`Mathlib/NumberTheory/SelbergSieve.lean`): `X = totalMass`, `g = nu`, `r_d = rem d`,
`S(A, P) = siftedSum`, `V = ∏_{p ∣ P} (1 - g(p))`.

The two main-term leaves `jr_mainSum_upper`, `jr_mainSum_lower` are the deep ones; the
assemblies `jr_upper`, `jr_lower` derive the Jurkat-Richert sieve bounds from the leaves with
no sorry of their own.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527a

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
attribute [local instance] Classical.propDecidable

/-- The prime factors of `d` in decreasing order `p₁ > p₂ > ⋯ > p_r`. -/
noncomputable def decPrimes (d : ℕ) : List ℕ := d.primeFactors.sort (· ≥ ·)

/-- Rosser's weights with `β = 2` and level `D`: `λ_d = μ(d)` if `d = p₁⋯p_r` is squarefree,
`p₁ > ⋯ > p_r`, and `p₁⋯p_{m-1} p_m³ < D` for every `m` odd (upper, `upper = true`) or every
`m` even (lower, `upper = false`); else `0`. In the code `m` is 0-indexed, so "odd `m`" is
`m % 2 = 0`. Iwaniec-Kowalski (6.30). -/
noncomputable def rosserWeight (D : ℝ) (upper : Bool) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ m < (decPrimes d).length, (upper = true ↔ m % 2 = 0) →
      (((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ) ^ 3 < D
  then (ArithmeticFunction.moebius d : ℝ) else 0

/-- The linear sieve density condition `Ω₁(K)`: for `2 ≤ w < w'`,
`∏_{p ∣ P, w ≤ p < w'} (1 - g(p))⁻¹ ≤ (log w'/log w)(1 + K/log w)`.
Iwaniec-Kowalski (6.34) with `κ = 1`; Halberstam-Richert `(Ω₂(1))`, `(Ω₂(κ))` p. 142. -/
def LinearDensity (s : BoundingSieve) (K : ℝ) : Prop :=
  ∀ w w' : ℝ, 2 ≤ w → w < w' →
    ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
      (1 - s.nu p)⁻¹ ≤ log w' / log w * (1 + K / log w)

/-- `|λ_d| ≤ 1` for Rosser's weights. -/
theorem abs_rosserWeight_le_one (D : ℝ) (b : Bool) (d : ℕ) : |rosserWeight D b d| ≤ 1 := by
  unfold rosserWeight
  split_ifs
  · exact_mod_cast abs_moebius_le_one
  · simp

/-- LEAF. Rosser's upper weights are an upper bound sieve: `Σ_{d ∣ n} λ⁺_d ≥ [n = 1]` for all
`n`. Proof: the support is closed under deleting the smallest prime, so
`Σ_{d∣n} μ(d) = Σ_{d∣n} λ⁺_d − Σ_{b first exit} [b ∣ n][(n/b, P(p_r)) = 1]`, every first
exit `b = p₁⋯p_r` has `r` odd and `μ(b) = −1`. Iwaniec-Kowalski (6.24) to (6.27) and Section 6.4.
Unit U-1527. -/
theorem rosser_upper_isUpperMoebius (D : ℝ) : IsUpperMoebius (rosserWeight D true) := by
  sorry

/-- LEAF. Rosser's lower weights are a lower bound sieve: `Σ_{d ∣ n} λ⁻_d ≤ [n = 1]` for all
`n`; first exits have `r` even and `μ(b) = +1`. Iwaniec-Kowalski (6.24) to (6.27) and
Section 6.4. Unit U-1527. -/
theorem rosser_lower_le (D : ℝ) (n : ℕ) :
    ∑ d ∈ n.divisors, rosserWeight D false d ≤ if n = 1 then 1 else 0 := by
  sorry

/-- LEAF. Lower bound sieve inequality, the mirror of Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: if `Σ_{d∣n} λ_d ≤ [n=1]` for all `n` then
`S ≥ X Σ_{d∣P} λ_d g(d) − Σ_{d∣P} |λ_d||r_d|`. Iwaniec-Kowalski (6.17), (6.18).
Unit U-1527. -/
theorem siftedSum_ge_of_lower (s : BoundingSieve) (lam : ℕ → ℝ)
    (h : ∀ n : ℕ, ∑ d ∈ n.divisors, lam d ≤ if n = 1 then 1 else 0) :
    s.totalMass * s.mainSum lam - s.errSum lam ≤ s.siftedSum := by
  sorry

/-- LEAF. Support of Rosser's weights: for `D > 1`, `λ^±_d ≠ 0` implies `d < D` or `d` prime
(only the lower weights reach the primes `p ≥ D^{1/3}`). For `r ≥ 2` use the condition at the
last or second to last index and `p_r < p_{r-1}`. Iwaniec-Kowalski Section 6.4, below (6.30).
Unit U-1527. -/
theorem rosserWeight_support (D : ℝ) (hD : 1 < D) (b : Bool) (d : ℕ)
    (h : rosserWeight D b d ≠ 0) : (d : ℝ) < D ∨ d.Prime := by
  sorry

/-- LEAF. Remainder bookkeeping: if every prime of `P` is `< z ≤ D`, then
`Σ_{d∣P} |λ^±_d||r_d| ≤ Σ_{d∣P, d<D} |r_d|`, by `rosserWeight_support` and `|λ| ≤ 1`.
Iwaniec-Kowalski (6.18), Theorem 11.13 remainder `R(D)`. Unit U-1527. -/
theorem errSum_rosser_le (s : BoundingSieve) (z D : ℝ) (hzD : z ≤ D) (hD : 1 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (b : Bool) :
    s.errSum (rosserWeight D b) ≤
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  have hs_errSum : s.errSum (rosserWeight D b) = ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| := rfl
  rw [hs_errSum]
  have H : ∀ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| ≤ if (d : ℝ) < D then |s.rem d| else 0 := by
    intro d hd
    by_cases hdD : (d : ℝ) < D
    · rw [ite_eq_left_iff.mpr (fun hh => False.elim (hh hdD))]
      have := abs_rosserWeight_le_one D b d
      nlinarith [abs_nonneg (s.rem d)]
    · rw [ite_eq_right_iff.mpr (fun hh => False.elim (hdD hh))]
      have h1 : rosserWeight D b d = 0 := by
        by_contra hc
        have := rosserWeight_support D hD b d hc
        rcases this with h_lt | h_prime
        · exact hdD h_lt
        · have hd_primeFactors : d ∈ s.prodPrimes.primeFactors := by
            rw [Nat.mem_primeFactors]
            exact ⟨h_prime, Nat.mem_divisors.mp hd |>.1, fun hh => by
              have hhh := s.prodPrimes_squarefree
              rw [hh] at hhh
              exact not_squarefree_zero hhh⟩
          have h_z := hP d hd_primeFactors
          linarith
      rw [h1]
      simp
  calc ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d|
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) < D then |s.rem d| else 0 := Finset.sum_le_sum (fun d hd => H d hd)
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
      rw [Finset.sum_filter]

/-- LEAF. Deep. Iwaniec's linear sieve, upper main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z ≤ D ≤ z⁵`,
`Σ_{d∣P} λ⁺_d g(d) ≤ V(z)(F(s) + C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- LEAF. Deep. Iwaniec's linear sieve, lower main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `Σ_{d∣P} λ⁻_d g(d) ≥ V(z)(f(s) − C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  sorry

/-- LEAF. Deep. Fundamental lemma of sieve theory, `κ = 1`: given `K ≥ 0` there is `C > 0`
such that whenever all primes of `P` are below `z`, `Ω₁(K)` holds, `z ≥ 2` and `D ≥ z^{10}`,
there are upper and lower bound sieve weights `λ^±` with `|λ^±_d| ≤ 1`, supported on `d ∣ P`,
`d < D`, `λ^±_1 = 1`, `Σ_{d∣n} λ⁺_d ≥ [n=1]` for all `n`,
`Σ_{d∣n} λ⁻_d ≤ [n=1]` for `n ∣ P`, and `|Σ_{d∣P} λ^±_d g(d) − V(z)| ≤ C e^{-s} V(z)`, `s = log D/log z`.
Iwaniec-Kowalski Lemma 6.3 and Theorem 6.9 (`D ≥ z^{9κ+1}`).
Unit U-1527. -/
theorem fundamental_lemma (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  sorry

/-! ### Assemblies: the Jurkat-Richert linear sieve bounds, from the leaves -/

lemma one_lt_of_two_le {z D : ℝ} (hz : 2 ≤ z) (hzD : z ≤ D) : 1 < D := by linarith

/-- **Jurkat-Richert upper bound**, assembled from the leaves `rosser_upper_isUpperMoebius`,
`jr_mainSum_upper`, `errSum_rosser_le` and Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: for `X ≥ 0`, `2 ≤ z ≤ D ≤ z⁵`,
`S(A, P) ≤ X V(z)(F(s) + C (log D)^{-1/3}) + Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4. -/
theorem jr_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.siftedSum ≤ s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))))
        + ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_upper K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have h1 := s.siftedSum_le_mainSum_errSum_of_upperMoebius _ (rosser_upper_isUpperMoebius D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD (one_lt_of_two_le hz hzD) hP true
  have h4 : s.totalMass * s.mainSum (rosserWeight D true) ≤ s.totalMass *
      ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ)))) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-- **Jurkat-Richert lower bound**, assembled from the leaves `rosser_lower_le`,
`siftedSum_ge_of_lower`, `jr_mainSum_lower`, `errSum_rosser_le`: for `X ≥ 0`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `S(A, P) ≥ X V(z)(f(s) − C (log D)^{-1/3}) − Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3. -/
theorem jr_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))))
        - ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| ≤ s.siftedSum := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_lower K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have hz2 : z ≤ z ^ 2 := by nlinarith
  have hzD' : z ≤ D := hz2.trans hzD
  have h1 := siftedSum_ge_of_lower s _ (rosser_lower_le D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD' (one_lt_of_two_le hz hzD') hP false
  have h4 : s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ)))) ≤
      s.totalMass * s.mainSum (rosserWeight D false) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-! ### Vacuity -/

/-- The trivial sieve problem: empty support, `P = 1`, `g = ζ`. -/
noncomputable def trivialSieve : BoundingSieve where
  support := ∅
  prodPrimes := 1
  prodPrimes_squarefree := squarefree_one
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  nu_mult := isMultiplicative_zeta.natCast
  nu_pos_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one
  nu_lt_one_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one

/-- Vacuity of `LinearDensity`: it holds for the trivial sieve with `K = 0`, and the
hypotheses of `jr_upper` hold at `z = D = 2`. -/
example : LinearDensity trivialSieve 0 ∧
    (∀ p ∈ trivialSieve.prodPrimes.primeFactors, (p : ℝ) < 2) := by
  refine ⟨fun w w' hw hww' => ?_, by simp [trivialSieve]⟩
  have hlw : 0 < log w := log_pos (by linarith)
  have hl : log w ≤ log w' := log_le_log (by linarith) hww'.le
  simp only [trivialSieve, Nat.primeFactors_one, Finset.filter_empty, Finset.prod_empty,
    zero_div, add_zero, mul_one]
  rw [le_div_iff₀ hlw]; linarith

end LeanLab.AlmostPrimeSums.Decomp1527b

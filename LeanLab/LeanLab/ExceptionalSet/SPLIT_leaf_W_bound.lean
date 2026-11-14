/-
Split of the sealed statement `leaf_W_bound` of `LeanLab.ExceptionalSet.KaracubaSplit`: the bound
on `W(a) = Σ_{y,z ≤ M} e(f(a + yz))`, `M = [P^{c1/2 - 1/(2n²(n+1))}]`, that the case `n ≥ n0` of
the proof of the source's Theorem 1 establishes on p. 245-248.

The statement to be split asks, for positive `c0, ..., c4` with `c0 < 1`, `c1 < 1`, `c2 + c4 < c1`,
for constants `A, γ, cc > 0` such that under the hypotheses of `KarHyp`, for `n ≥ karN0` and
`P ≥ exp(cc n²)` and every `a` in `[N, N+P-M²]`,

  ‖W(a)‖ ≤ A (M+1)² P^{-γ/n²}.

The proof of the source has three separable parts, and the split follows them.

* Taylor's formula to order `n` at the point `a`: the phase `f(a + yz)` is replaced by its Taylor
  polynomial of degree `n` at `a`, and the Lagrange remainder is bounded by the one derivative bound
  that `KarHyp` states, `|f^{(n+1)}/(n+1)!| ≤ P^{-c1(n+1)}`, together with `yz ≤ M² ≤ P^{c1-1/(n²(n+1))}`,
  which is exactly where the correction `-1/(2n²(n+1))` in `M` is spent. The error per term is
  `P^{-1/n²}`, and there are `(M+1)²` terms. This step uses no cancellation and is the first leaf.

* The Taylor polynomial sum, i.e. `Σ_{y,z} e(f(a) + Σ_{2 ≤ j ≤ n} f^{(j)}(a)/j! (yz)^j)`, is small:
  this is where the mean value theorem, the bound on `Σ min(U, 1/(αx+β))` and Holder's inequality
  enter, and it is the analytic core of the argument, the second leaf. Its exponent is left in the
  crude form produced by bounding the two integers `l` and `k` of that argument from above: with
  `ρ ≤ min(c1/3, c3, c4)` and `L = log(8/(ρ c0²))`, `l ≤ n L` and `k ≤ n²(4 + L²)`, so the exponent
  `ρ (s_1 + ... + s_r)/(8k²)` with `s_1 + ... + s_r ≥ c0² n²/4` is at least
  `ρ c0²/(32 n² (4 + L²)²)`. Stating the weaker exponent keeps this leaf weaker than the paper's
  display (8) and removes the choice of `l` from the assembly.

* The arithmetic that turns the two powers of `P` into one: with `γ = ρ c0²/(64(4+L²)²)` one has
  `γ ≤ 1`, so `P^{-1/n²} ≤ P^{-γ/n²}`, and `γ/n² ≤ ρ c0²/(32 n² (4+L²)²)`, so also
  `P^{-ρc0²/(32n²(4+L²)²)} ≤ P^{-γ/n²}`. This needs only `1 ≤ P` and the monotonicity of `x ↦ P^x`,
  and it is proved in the assembly, not assumed.

Degenerate values: `M = 0` is allowed and then both leaves are the identity `W(a) = e(f(a))`; the
Taylor sum's `yz = 0` term is `e(f(a))` in both leaves, so the difference is `0`. `n ≥ 2` is a
hypothesis of the statement, so `P^{-1/n²}` is not `P^{-1/0}`; `P ≥ 1` makes `P^x` monotone in `x`.
`ρ, c0 > 0` keep the exponents positive, and `4 + L² ≥ 4` keeps every denominator away from zero.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### First leaf: the Taylor reduction -/

/-- LEAF. Taylor's formula to order `n` at the point `a`, p. 245, the step that produces the phase
of the sum the mean value theorem is applied to. For the one derivative bound that the hypothesis
class states on `[N, N+P]`, every point `a + yz` with `y, z ≤ M` lies in that interval and the
Lagrange remainder gives `P^{-1/n²}` per term, so the whole difference of the two sums is at most a
constant times `(M+1)² P^{-1/n²}`. The Taylor polynomial is written out at `a`, so the term `yz = 0`
agrees in the two sums and the `n = 2` case is the usual second order formula. -/
theorem leaf_karW_taylor_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ (c1 : ℝ) (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ),
      0 < P → 2 ≤ n →
      (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1) f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (N + P),
        |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)|
          ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ)))) →
      N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
      ‖karW f (karP2 c1 n P) a -
        ∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
          eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
            iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
        ≤ C * ((karP2 c1 n P : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  sorry

/-! ### Second leaf: the analytic core -/

/-- LEAF. The Taylor polynomial sum of the first leaf, call it `S(a)`, is small, p. 245-248: the
mean value theorem bounds the number of solutions of the resulting system, the spacing bound bounds
the sums over the coefficient denominators, and Holder's inequality raises the whole to the power
`2k` that makes the mean value theorem applicable. The output is `‖S(a)‖ ≤ B (M+1)² P^{-e}` with
`e = ρ c0²/(32 n² (4 + L²)²)`, `ρ ≤ min(c1/3, c3, c4)` and `L = log(8/(ρ c0²))`: the two integers of
that argument are bounded by `l ≤ n L` and `k ≤ n²(4 + L²)`, and `s_1 + ... + s_r ≥ c0² n²/4`. The
exponent is deliberately weaker than the one the argument produces, so the whole choice of `l` sits
inside this leaf and the assembly needs no such choice. -/
theorem leaf_karW_taylor_sum_bound (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ B ρ cc : ℝ, 0 < B ∧ 0 < ρ ∧ ρ ≤ c1 / 3 ∧ ρ ≤ c3 ∧ ρ ≤ c4 ∧ 0 < cc ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ B * ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + (Real.log (8 / (ρ * c0 ^ 2))) ^ 2) ^ 2))) := by
  sorry

/-! ### The assembly -/

/-- The split of `leaf_W_bound`: the statement of that theorem, from the two leaves above and no
other input. Both leaves conclude an estimate with the same `M = karP2 c1 n P` and the same Taylor
polynomial sum, so the assembly only has to add the two bounds and compare the two exponents; the
exponents are compared at `γ = ρ c0²/(64(4+L²)²)`, which is `1/1024` of the size of the allowed
exponent at the smallest allowed parameters and stays positive because the denominator is a square
plus `4`. -/
theorem leaf_W_bound_split (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by
  intro c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  obtain ⟨C, hCpos, hC⟩ := leaf_karW_taylor_reduction
  obtain ⟨B, ρ, cc, hBpos, hρpos, hρc1, hρc3, hρc4, hcc, hBb⟩ :=
    leaf_karW_taylor_sum_bound h1 h3 h4 c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  set L := Real.log (8 / (ρ * c0 ^ 2)) with hL
  set γ := ρ * c0 ^ 2 / (64 * (4 + L ^ 2) ^ 2) with hγdef
  have hLpos : (0 : ℝ) < 4 + L ^ 2 := by positivity
  have hnum : (0 : ℝ) < ρ * c0 ^ 2 := mul_pos hρpos (pow_pos h0 2)
  have hγpos : 0 < γ := by
    rw [hγdef]
    exact div_pos hnum (by positivity)
  have hγ1 : γ ≤ 1 := by
    rw [hγdef, div_le_one (by positivity)]
    have hlt : ρ * c0 ^ 2 < 1 := by nlinarith
    have hsq : (16 : ℝ) ≤ (4 + L ^ 2) ^ 2 := by nlinarith [sq_nonneg L]
    nlinarith
  refine ⟨B + C, γ, cc, by linarith, hγpos, hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH a ha haP
  set M := karP2 c1 n P with hM
  set K := ((M : ℝ) + 1) ^ 2 with hK
  set S : ℂ := ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
    eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j)) with hS
  have hHall := hH
  obtain ⟨hU, hDer, -, -, -⟩ := hHall
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hTay : ‖karW f M a - S‖ ≤ C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    have := hC c1 N P n f T a hP hn hU hDer ha haP
    simpa [hM, hK, hS] using this
  have hAna : ‖S‖ ≤ B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have := hBb N P n f T a hP hn hpred hbig hH ha haP
    simpa [hM, hK, hS, hL] using this
  have hle1 : (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have := div_le_div_of_nonneg_right hγ1 hnpos.le
    linarith
  have hexp : γ / (n : ℝ) ^ 2 ≤ ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2) := by
    rw [hγdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnum, hLpos, hnpos, mul_pos hnum (mul_pos hLpos hnpos)]
  have hle2 : (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    linarith
  have hmain : ‖karW f M a‖ ≤
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have hsplit : karW f M a = (karW f M a - S) + S := by ring
    calc ‖karW f M a‖ = ‖(karW f M a - S) + S‖ := congrArg (fun z : ℂ => ‖z‖) hsplit
      _ ≤ ‖karW f M a - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hTay hAna
  have hcomp :
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    have hA := mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ C * K)
    have hB' := mul_le_mul_of_nonneg_left hle2 (by positivity : (0 : ℝ) ≤ B * K)
    have hring : (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2))
        = C * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) +
          B * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by ring
    rw [hring]
    linarith
  linarith [hmain, hcomp]

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

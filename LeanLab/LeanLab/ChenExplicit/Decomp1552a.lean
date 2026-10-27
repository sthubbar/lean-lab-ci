/-
AI-written Lean code, Claude, 2026-10-26, run 20261026T1219Z-15327, unit U-1552, track T1, DECOMPOSE.
T. Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, proof of Theorem 7.1.

Part a of the decomposition of Yamada's Theorem 7.1, the bound for `S(B, P(y))`:
the blocks `B^(j)` of (105), (106) and the leaves of Lemma 7.3, (108) to (116).
The lab holds Theorem 7.1 only as the cited hypothesis `Thm71W` (Thm71Fix.lean, F-0028).
Every `sorry` below is an OPEN LEAF for a prover; the assembly `lemma73_corr` is in
Decomp1552c.lean, CONDITIONAL ON these leaves.

Corrections built in, see ChenExplicit/STATEMENTS.md, U-1552 block:
* (106) prints `j₀ = [log(y/z)/log(1+ε)] - 1`; the blocks `j ≤ j₀` then miss the primes
  `p₁ ∈ [z(1+ε)^{j₀+1}, y)`. We use `J = ⌈log(y/z)/log(1+ε)⌉` blocks, which cover `[z, y)`.
* (112) is stated on `y ≤ p₂ < (N/p₁)^{1/2}`, the range of `H(p₁)` in (110); the primes
  `(N/p₁)^{1/2} ≤ p₂ < w = ((1+ε)N/p₁)^{1/2}` of (109) get their own leaf `eq112_tail`.
* (116) uses `H(z) = (8/7) log(13/8) / log N`, finding F-0014, not the printed `log(26/21)/log N`.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Bridge

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.D1552

/-- `z = N^{1/8}`, Section 4; definitionally the lab's `zN`. -/
abbrev z8 (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)

/-- `y = N^{1/3}`, Section 4; definitionally the lab's `yN`. -/
abbrev y3 (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)

/-- `w_j = z (1+ε)^j`, (106). -/
def wj (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ := z8 N * (1 + ε) ^ j

/-- Number of blocks, `⌈log(y/z) / log(1+ε)⌉`; corrected from (106), see the header. -/
def Jblk (N : ℕ) (ε : ℝ) : ℕ := ⌈log (y3 N / z8 N) / log (1 + ε)⌉₊

/-- `m = p₁p₂p₃` with `N - m ∈ B^(j)`, (105): `z ≤ p₁ < y ≤ p₂ ≤ p₃`, `w_j p₂p₃ < N`,
`(p₂p₃, N) = 1`, `w_j ≤ p₁ < (1+ε)w_j`. The printed `u p₂p₃ < N` is read as `w_j p₂p₃ < N`,
as the proof uses it. -/
def InBj (N : ℕ) (ε : ℝ) (j m : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z8 N ≤ p₁ ∧ (p₁ : ℝ) < y3 N ∧
    y3 N ≤ p₂ ∧ p₂ ≤ p₃ ∧ wj N ε j * p₂ * p₃ < N ∧ Nat.Coprime (p₂ * p₃) N ∧
    wj N ε j ≤ p₁ ∧ (p₁ : ℝ) < (1 + ε) * wj N ε j ∧ m = p₁ * p₂ * p₃

/-- The block `B^(j)` of (105), as the finite set of products `m = p₁p₂p₃`; its element of
`B^(j)` is the integer `N - m`, which can be negative. For `ε < 1`, `m < (1+ε)N < 2N`. -/
def Bj (N : ℕ) (ε : ℝ) (j : ℕ) : Finset ℕ := (range (2 * N)).filter (InBj N ε j)

/-- Primes `p` with `a ≤ p < b`. -/
def primesIco (a b : ℝ) : Finset ℕ := (range ⌈b⌉₊).filter fun p => p.Prime ∧ a ≤ (p : ℝ)

/-- `w = w(p₁) = ((1+ε)N/p₁)^{1/2}`, (109). -/
def wP (N : ℕ) (ε : ℝ) (p₁ : ℕ) : ℝ := √((1 + ε) * N / p₁)

/-- `h_{p₁}(t) = 1 / log(N/(p₁ t))`, proof of Lemma 7.3. -/
def hP (N : ℕ) (p₁ : ℕ) (t : ℝ) : ℝ := 1 / log (N / (p₁ * t))

/-- `H(u) = ∫_y^{(N/u)^{1/2}} dt / (t log t log(N/(ut)))`, (110); the same integrand as
`Yamada.Hfun` of Eq111.lean. -/
def H (N : ℕ) (u : ℝ) : ℝ :=
  ∫ t in y3 N..((N : ℝ) / u) ^ ((1 : ℝ) / 2), 1 / (t * log t * log (N / (u * t)))

/-- `c₂ - 10⁻⁸ = ∫_{1/8}^{1/3} log(2 - 3β) / (β(1-β)) dβ`, Lemma 7.3. -/
def I73 : ℝ := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))

/-- LEAF. Unit U-1552. Yamada 2015, (109), first inequality, Section 7, proof of Lemma 7.3.
For `0 < ε < 1/100`, the blocks satisfy `Σ_j |B^(j)| ≤ Σ_{z ≤ p₁ < y} Σ_{y ≤ p₂ < w(p₁)}
π((1+ε)N/(p₁p₂))`: each `m = p₁p₂p₃` has `p₁p₂p₃ < (1+ε)N`, so `p₂ < w(p₁)` and
`p₃ ≤ (1+ε)N/(p₁p₂)`, and the block index is fixed by `p₁`. -/
theorem eq109_count (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) ≤
      ∑ p₁ ∈ primesIco (z8 N) (y3 N), ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁),
        (Nat.primeCounting ⌊(1 + ε) * N / (p₁ * p₂)⌋₊ : ℝ) := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (109), second inequality, Section 7, proof of Lemma 7.3.
For even `N > exp exp 36`, `0 < ε < 1/100`, primes `z ≤ p₁ < y ≤ p₂ < w(p₁)`:
`π((1+ε)N/(p₁p₂)) ≤ (1 + ε + 10⁻⁸) N · (1/p₁) · 1/(p₂ log(N/(p₁p₂)))`.
Here `(1+ε)N/(p₁p₂) ≥ w(p₁) > N^{1/3}`, so a Rosser-Schoenfeld bound
`π(t) < t/log t · (1 + 3/(2 log t))` suffices. -/
theorem eq109_pi (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (p₁ : ℕ) (hp₁ : p₁ ∈ primesIco (z8 N) (y3 N)) (p₂ : ℕ)
    (hp₂ : p₂ ∈ primesIco (y3 N) (wP N ε p₁)) :
    (Nat.primeCounting ⌊(1 + ε) * N / (p₁ * p₂)⌋₊ : ℝ) ≤
      (1 + ε + 1 / 10 ^ 8) * N * (1 / p₁) * (1 / (p₂ * log (N / (p₁ * p₂)))) := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (112), Section 7, by Lemma 2.1 and (7).
For `N > exp exp 36` and a prime `z ≤ p₁ < y`: the sum over primes `y ≤ p₂ < (N/p₁)^{1/2}` of
`h_{p₁}(p₂)/p₂` is at most `H(p₁) + h_{p₁}((N/p₁)^{1/2}) / (4 log² y)`. The range is that of
`H(p₁)` in (110), see the header. -/
theorem eq112_main (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (p₁ : ℕ) (hp₁ : p₁ ∈ primesIco (z8 N) (y3 N)) :
    ∑ p₂ ∈ (primesIco (y3 N) (wP N ε p₁)).filter (fun p : ℕ => (p : ℝ) < √(N / p₁)),
        1 / ((p₂ : ℝ) * log (N / (p₁ * p₂))) ≤
      H N p₁ + hP N p₁ (√(N / p₁)) / (4 * log (y3 N) ^ 2) := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (113), Section 7: for `N > exp exp 36` and a prime
`z ≤ p₁ < y`, `h_{p₁}((N/p₁)^{1/2}) / (4 log² y) ≤ 9(1 + e^{-50}) / (4 log² N)`.
Here `h_{p₁}((N/p₁)^{1/2}) = 2 / log(N/p₁) ≤ 3 / log N`. -/
theorem eq113 (N : ℕ) (hN : exp (exp 36) < N) (p₁ : ℕ) (hp₁ : p₁ ∈ primesIco (z8 N) (y3 N)) :
    hP N p₁ (√(N / p₁)) / (4 * log (y3 N) ^ 2) ≤ 9 * (1 + exp (-50)) / (4 * log N ^ 2) := by
  sorry

/-- LEAF. Unit U-1552. Correction to Yamada 2015, (109) and (112), Section 7: the primes
`(N/p₁)^{1/2} ≤ p₂ < w(p₁)` left out of (112). For `N > exp exp 36`, `0 < ε < 1/100` and a
prime `z ≤ p₁ < y`, their sum of `h_{p₁}(p₂)/p₂` is at most `(5ε + 7/log N) / log² N`;
heuristically it is about `4.5 ε / log² N`, from `h ≤ 3/log N` and (7). -/
theorem eq112_tail (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (p₁ : ℕ) (hp₁ : p₁ ∈ primesIco (z8 N) (y3 N)) :
    ∑ p₂ ∈ (primesIco (y3 N) (wP N ε p₁)).filter (fun p : ℕ => ¬ (p : ℝ) < √(N / p₁)),
        1 / ((p₂ : ℝ) * log (N / (p₁ * p₂))) ≤
      (5 * ε + 7 / log N) / log N ^ 2 := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (115), Section 7, from (7):
for `N > exp exp 36`, `9(1 + e^{-50})/4 · Σ_{z ≤ p₁ < y} 1/p₁ ≤ 2.2069`; the sum is close to
`log(8/3) ≈ 0.98083`, and `9/4 · log(8/3) ≈ 2.20687`. -/
theorem eq115 (N : ℕ) (hN : exp (exp 36) < N) :
    9 * (1 + exp (-50)) / 4 * ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 / (p₁ : ℝ)) ≤ 22069 / 10000 := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (116), first inequality, Section 7, by Lemma 2.1 and (7):
for `N > exp exp 36`, `Σ_{z ≤ p₁ < y} H(p₁)/p₁ ≤ ∫_z^y H(u) d log log u + H(z)/(4 log² z)`,
with `d log log u = du/(u log u)`; `H` is decreasing, so `max{H(z), H(y)} = H(z)`. -/
theorem eq116_sum (N : ℕ) (hN : exp (exp 36) < N) :
    ∑ p₁ ∈ primesIco (z8 N) (y3 N), H N p₁ / p₁ ≤
      (∫ u in z8 N..y3 N, H N u / (u * log u)) + H N (z8 N) / (4 * log (z8 N) ^ 2) := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (111) and (116), Section 7: for `N > exp exp 36`,
`∫_z^y H(u) d log log u = (1/log N) ∫_{1/8}^{1/3} log(2 - 3β)/(β(1-β)) dβ`, by `u = N^α`,
`t = N^β` and (111), `H(N^α) = log(2 - 3α) / ((1-α) log N)`. -/
theorem eq116_integral (N : ℕ) (hN : exp (exp 36) < N) :
    (∫ u in z8 N..y3 N, H N u / (u * log u)) = I73 / log N := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (111) at `α = 1/8`, CORRECTED value, finding F-0014:
for `N > exp exp 36`, `H(z) = (8/7) log(13/8) / log N`. The printed `log(26/21)/log N` is wrong;
the lab PROVED `H(z) ≥ (16/7) log(26/21) / log N` in Eq111.lean, `Hz_gt`. -/
theorem Hz_eq (N : ℕ) (hN : exp (exp 36) < N) :
    H N (z8 N) = 8 / 7 * log (13 / 8) / log N := by
  sorry

end LeanLab.ChenExplicit.D1552

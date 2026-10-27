/-
AI-written Lean code, Claude, 2026-10-26, run 20261026T1219Z-15327, unit U-1552, track T1, DECOMPOSE.
T. Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, proof of Theorem 7.1.

Part b: the sieve side of Theorem 7.1, (107) and (117) to (126), with the explicit
Bombieri-Vinogradov type Lemma 7.2, (99). Every `sorry` here is an OPEN LEAF, except
`thm31_upper_applied`, which is Yamada's Theorem 3.1 from his unpublished reference [22] and is
entered as Cited. Proved here, no sorry: `sum_sifted_le`, `abs_r_le`, `eq118`,
`adm_zero`, `lemma72_zero`, the last two vacuity instances.

Corrections built in, see ChenExplicit/STATEMENTS.md, U-1552 block:
* (117) has the coefficient `U_N^(1)` in front of `F(s)/log D`; the printed (40) has `2`,
  the lab's earlier QUESTION; (117) is stated as the proof applies it.
* (123): Lemma 7.2 with `X = N/w_j`, `Y = min{y, (1+ε)w_j}` gives `e^{-144}(1+ε)N / log⁴ Y`;
  (123) prints `log⁴ y`, but `Y ≤ y`. The leaves keep `log⁴ Y_j`, and (124) becomes
  `≤ 1.2 e^{-139} N/(ε log³ N)`, numerically about `1.11 e^{-139}`; Theorem 7.1's `e^{-138}`
  still follows since `2.2 < e`.
* Lemma 7.2 is stated with `Z ≥ z`; the printed `Z > z` fails at `j = 0`, where `Z = z`.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Decomp1552a

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.D1552

open LeanLab.ChenExplicit

/-- `ε₀(N) = 1 / max{57, log log N}`, (47); the same as `Yamada.eps0`. -/
def eps0' (N : ℕ) : ℝ := 1 / max 57 (log (log N))

/-- (46): `q₁` is the largest prime factor of the exceptional modulus `k₁`, and
`q₁ ≥ max{59, 2 + log log N}`; `q₁ = 0` codes `k₁ = 0`, no exceptional modulus. -/
def Adm (N q₁ : ℕ) : Prop := q₁ = 0 ∨ (q₁.Prime ∧ max 59 (2 + log (log N)) ≤ (q₁ : ℝ))

/-- Vacuity instance for `Adm`: `q₁ = 0` is admissible. -/
theorem adm_zero (N : ℕ) : Adm N 0 := Or.inl rfl

/-- `U_N^(1)`, (44) and (131) at `j = 1`: `U_N` times `(q₁-1)/(q₁-2)` when `q₁` is an odd prime
not dividing `N`. -/
def U1 (N q₁ : ℕ) : ℝ :=
  U N * (if q₁.Prime ∧ 2 < q₁ ∧ ¬ q₁ ∣ N then ((q₁ : ℝ) - 1) / ((q₁ : ℝ) - 2) else 1)

/-- `V^(1)(x) = ∏_{p < x, p ∤ N, p ≠ q₁} (1 - ρ(p)/p)` with `ρ(p)/p = 1/(p-1)`, `ρ(2) = 0`. -/
def V1 (N q₁ : ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ (range ⌈x⌉₊).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p ≠ q₁),
    (1 - 1 / ((p : ℝ) - 1))

/-- `N - m` is coprime to `P^(1)(x) = ∏_{p < x, p ∤ N, p ≠ q₁} p`, Section 4. -/
def SiftedZ (N q₁ : ℕ) (x : ℝ) (m : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) < x → ¬ r ∣ N → r ≠ q₁ → ¬ (r : ℤ) ∣ (N : ℤ) - m

/-- `S(B^(j), P^(1)(y))`. -/
def SBj (N q₁ : ℕ) (ε : ℝ) (j : ℕ) : ℕ := ((Bj N ε j).filter (SiftedZ N q₁ (y3 N))).card

/-- `B^# = ⋃_j B^(j)`, (107), as products `m`. -/
def BSharp (N : ℕ) (ε : ℝ) : Finset ℕ := (range (Jblk N ε)).biUnion (Bj N ε)

/-- `D = N^{1/2} / log^{10} N`, Section 7. -/
def Dsv (N : ℕ) : ℝ := √(N : ℝ) / log N ^ 10

/-- `d ∣ P^(1)(y)`: `d` squarefree, every prime factor `< y`, not dividing `N`, not `q₁`. -/
def DivP1 (N q₁ : ℕ) (x : ℝ) (d : ℕ) : Prop :=
  Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < x ∧ ¬ p ∣ N ∧ p ≠ q₁

/-- The moduli `d < D`, `d ∣ P^(1)(y)`, of (117) and (123). -/
def Dset (N q₁ : ℕ) : Finset ℕ := (range ⌈Dsv N⌉₊).filter (DivP1 N q₁ (y3 N))

/-- `#{m ∈ B^(j) : d ∣ N - m}`. -/
def cntDiv (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ :=
  (((Bj N ε j).filter fun m => (d : ℤ) ∣ (N : ℤ) - m).card : ℝ)

/-- `#{m ∈ B^(j) : (m, d) = 1}`. -/
def cntCop (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ :=
  (((Bj N ε j).filter fun m => Nat.Coprime m d).card : ℝ)

/-- `r_d^(j) = |B^(j)_d| - |B^(j)|/φ(d)`, (120). -/
def rj (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := cntDiv N ε j d - ((Bj N ε j).card : ℝ) / d.totient

/-- `r_d^(j,1)`, (121). -/
def r1 (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := cntDiv N ε j d - cntCop N ε j d / d.totient

/-- `r_d^(j,2)`, (122), up to sign: `#{m ∈ B^(j) : (m, d) > 1} / φ(d)`. -/
def r2 (N : ℕ) (ε : ℝ) (j d : ℕ) : ℝ := (((Bj N ε j).card : ℝ) - cntCop N ε j d) / d.totient

/-- `Y_j = min{y, (1+ε)w_j}`, proof of (123). -/
def Yj (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ := min (y3 N) ((1 + ε) * wj N ε j)

/-- Yamada's `F(s) = 2e^γ - s` for `0 ≤ s ≤ 3`, (41); only used at `s = log D / log y < 3`. -/
def F1lin (s : ℝ) : ℝ := 2 * exp eulerMascheroniConstant - s

/-- `r_d^(j) = r_d^(j,1) - r_d^(j,2)`, so `|r_d^(j)| ≤ |r_d^(j,1)| + |r_d^(j,2)|`, (120). PROVED. -/
theorem abs_r_le (N : ℕ) (ε : ℝ) (j d : ℕ) :
    |rj N ε j d| ≤ |r1 N ε j d| + |r2 N ε j d| := by
  have h : rj N ε j d = r1 N ε j d - r2 N ε j d := by
    unfold rj r1 r2; ring
  rw [h]; exact abs_sub _ _

/-- LEAF. Unit U-1552. Yamada 2015, (107), first two inequalities, Section 7: for
`0 < ε < 1/100` and any `q₁`, `S(B, P(y)) ≤ S(B^#, P^(1)(y))`: `B ⊆ B^#` through `b = N - m`,
since `p₁p₂p₃ < N` and `w_j ≤ p₁` give `w_j p₂p₃ < N`, the `J` blocks cover `[z, y)`,
and sifting by fewer primes keeps more elements. -/
theorem eq107_sub (N q₁ : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    SB N (z8 N) (y3 N) ≤ ((BSharp N ε).filter (SiftedZ N q₁ (y3 N))).card := by
  sorry

/-- (107), last inequality: `S(B^#, P^(1)(y)) ≤ Σ_j S(B^(j), P^(1)(y))`. PROVED. -/
theorem sum_sifted_le (N q₁ : ℕ) (ε : ℝ) :
    ((BSharp N ε).filter (SiftedZ N q₁ (y3 N))).card ≤
      ∑ j ∈ range (Jblk N ε), SBj N q₁ ε j := by
  unfold BSharp SBj
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion_le

/-- Cited, not proved in the lab: Yamada 2015, Theorem 3.1, upper bound (40), Section 3,
whose proof is in Yamada's unpublished reference [22], "An explicit formula for the linear
sieve", applied as (117) to `B^(j)` with `D = N^{1/2}/log^{10} N`, `s = log D / log y` and
density `1/φ(d)`: for even `N > exp exp 36`, `0 < ε < 1/100`, admissible `q₁` and `j < J`,
`S(B^(j), P^(1)(y)) ≤ |B^(j)| (V^(1)(y) + U_N^(1) (F(s)/log D + 298.87013/log^{3/2} D))
+ Σ_{d < D, d ∣ P^(1)(y)} |r_d^(j)|`. -/
theorem thm31_upper_applied (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) (j : ℕ) (hj : j < Jblk N ε) :
    (SBj N q₁ ε j : ℝ) ≤
      ((Bj N ε j).card : ℝ) * (V1 N q₁ (y3 N) + U1 N q₁ *
        (F1lin (log (Dsv N) / log (y3 N)) / log (Dsv N) +
          29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))))) +
      ∑ d ∈ Dset N q₁, |rj N ε j d| := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (43) with `θ ≤ 1`, used as (130) at `x = y`: for
`N > exp exp 36` and admissible `q₁`, `V^(1)(y) ≤ U_N^(1)/log y · (1 + 1/(5 log² y))
(1 + 8 log y / y)`; an explicit Mertens product bound, Rosser-Schoenfeld type. -/
theorem eq43_V1 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁) :
    V1 N q₁ (y3 N) ≤ U1 N q₁ / log (y3 N) * (1 + 1 / (5 * log (y3 N) ^ 2)) *
      (1 + 8 * log (y3 N) / y3 N) := by
  sorry

/-- LEAF. Unit U-1552. Numerical step behind (118), Section 7: for `N > exp exp 36`,
`(1 + 1/(5 log² y)) (1 + 8 log y / y) ≤ 1 + 1/(5 log y)`. -/
theorem eq118_num (N : ℕ) (hN : exp (exp 36) < N) :
    (1 + 1 / (5 * log (y3 N) ^ 2)) * (1 + 8 * log (y3 N) / y3 N) ≤ 1 + 1 / (5 * log (y3 N)) := by
  sorry

/-- LEAF. Unit U-1552. Positivity facts used in (118): for `N > exp exp 36`,
`0 < log y` and `0 < log D` with `D = N^{1/2}/log^{10} N`, and `0 ≤ U_N^(1)`. -/
theorem logs_pos (N q₁ : ℕ) (hN : exp (exp 36) < N) :
    0 < log (y3 N) ∧ 0 < log (Dsv N) ∧ 0 ≤ U1 N q₁ := by
  sorry

/-- (118): `V^(1)(y) + U_N^(1) F(s)/log D ≤ U_N^(1) (2e^γ/log D + 1/(5 log² y))`, with the
`298.87013` term carried along. PROVED, CONDITIONAL ON the leaves `eq43_V1`, `eq118_num`,
`logs_pos`. -/
theorem eq118 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁) :
    V1 N q₁ (y3 N) + U1 N q₁ *
        (F1lin (log (Dsv N) / log (y3 N)) / log (Dsv N) +
          29887013 / 100000 / (log (Dsv N) * √(log (Dsv N)))) ≤
      U1 N q₁ * (2 * exp eulerMascheroniConstant / log (Dsv N) +
        29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))) + 1 / (5 * log (y3 N) ^ 2)) := by
  obtain ⟨hy, hD, hU⟩ := logs_pos N q₁ hN
  have hV := eq43_V1 N q₁ hE hN hq
  have hn := eq118_num N hN
  set ℓ := log (y3 N)
  set L := log (Dsv N)
  set u := U1 N q₁
  have hℓ : ℓ ≠ 0 := hy.ne'
  have hL0 : L ≠ 0 := hD.ne'
  have h1 : V1 N q₁ (y3 N) ≤ u / ℓ + u / (5 * ℓ ^ 2) := by
    have hu' : 0 ≤ u / ℓ := div_nonneg hU hy.le
    calc V1 N q₁ (y3 N) ≤ u / ℓ * (1 + 1 / (5 * ℓ ^ 2)) * (1 + 8 * ℓ / y3 N) := hV
      _ = u / ℓ * ((1 + 1 / (5 * ℓ ^ 2)) * (1 + 8 * ℓ / y3 N)) := by ring
      _ ≤ u / ℓ * (1 + 1 / (5 * ℓ)) := mul_le_mul_of_nonneg_left hn hu'
      _ = u / ℓ + u / (5 * ℓ ^ 2) := by field_simp <;> ring
  have h2 : u * (F1lin (L / ℓ) / L) = u * (2 * exp eulerMascheroniConstant / L) - u / ℓ := by
    unfold F1lin; field_simp <;> ring
  calc V1 N q₁ (y3 N) + u * (F1lin (L / ℓ) / L + 29887013 / 100000 / (L * √L))
      = V1 N q₁ (y3 N) + u * (F1lin (L / ℓ) / L) + u * (29887013 / 100000 / (L * √L)) := by ring
    _ ≤ (u / ℓ + u / (5 * ℓ ^ 2)) + (u * (2 * exp eulerMascheroniConstant / L) - u / ℓ) +
        u * (29887013 / 100000 / (L * √L)) := by rw [h2]; linarith
    _ = u * (2 * exp eulerMascheroniConstant / L + 29887013 / 100000 / (L * √L) +
        1 / (5 * ℓ ^ 2)) := by ring

/-- Lemma 7.2, (99), its conclusion at one choice of residues: for `c : ℕ → ℝ` and residues
`res d` coprime to `d`, `Σ_{d < D*, q₁ ∤ d} |Σ_{n<X} Σ_{Z≤p<Y, np ≡ res d (d)} c(n)
- (1/φ(d)) Σ_{n<X} Σ_{Z≤p<Y, (np,d)=1} c(n)| ≤ e^{-144} XY / log⁴ Y`, `D* = (XY)^{1/2}/log^{10} Y`.
Over all `res` this is the printed `max_{(a,d)=1}` form. -/
def Lemma72At (q₁ : ℕ) (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ) : Prop :=
  ∑ d ∈ (range ⌈√(X * Y) / log Y ^ 10⌉₊).filter (fun d => 0 < d ∧ ¬ q₁ ∣ d),
      |∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if (n * p : ℕ) ≡ res d [MOD d] then c n else 0) -
        (1 / (d.totient : ℝ)) * ∑ n ∈ Ico 1 ⌈X⌉₊, ∑ p ∈ primesIco Z Y,
          (if Nat.Coprime (n * p) d then c n else 0)| ≤
    exp (-144) * X * Y / log Y ^ 4

/-- Vacuity instance for `Lemma72At`: it holds for `c = 0`. -/
theorem lemma72_zero (q₁ : ℕ) (res : ℕ → ℕ) (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Lemma72At q₁ (fun _ => 0) res X Y Z := by
  unfold Lemma72At
  simp only [ite_self, sum_const_zero, mul_zero, sub_zero, abs_zero]
  positivity

/-- LEAF. Unit U-1552. Yamada 2015, Lemma 7.2, (99), Section 7, explicit Bombieri-Vinogradov
for bilinear sums, proved there by (101) to (104) from Corollary 2.4 and the large sieve:
for even `N > exp exp 36` there is an admissible `q₁`, (46), such that for all `|c(n)| ≤ 1`,
residues `res d` coprime to `d`, and `X, Y, Z` with `log^{10} Y < X ≤ N/z`, `XY < 2N`,
`Y > z`, `Z ≥ z`, the bound `Lemma72At` holds. -/
theorem lemma72 (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) :
    ∃ q₁ : ℕ, Adm N q₁ ∧ ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (123), Section 7, from Lemma 7.2 with `X = N/w_j`,
`Y = Y_j = min{y, (1+ε)w_j}`, `Z = max{w_j, z}`, residue `N`, and `c(n) = 1` for
`n = p₂p₃`, `y ≤ p₂ ≤ p₃`, `(p₂p₃, N) = 1`: for even `N > exp exp 36`, `0 < ε < 1/100`,
if `q₁` satisfies the conclusion of `lemma72` then for `j < J`,
`Σ_{d<D, d ∣ P^(1)(y)} |r_d^(j,1)| ≤ e^{-144}(1+ε)N / log⁴ Y_j`. The printed (123) has
`log⁴ y` in place of `log⁴ Y_j`; see the header. -/
theorem eq123 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (h72 : ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) (j : ℕ) (hj : j < Jblk N ε) :
    ∑ d ∈ Dset N q₁, |r1 N ε j d| ≤ exp (-144) * (1 + ε) * N / log (Yj N ε j) ^ 4 := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (124), CORRECTED to `log⁴ Y_j`, Section 7: for
`N > exp exp 36`, `0 < ε < 1/100`, `Σ_{j<J} e^{-144}(1+ε)N/log⁴ Y_j ≤ 1.2 e^{-139} N/(ε log³ N)`;
by `log Y_j ≥ log z + (j+1) log(1+ε)` the sum is at most about `(8³/3) e^{-144}/(ε log³ N)`,
numerically `1.11 e^{-139}/(ε log³ N)`. -/
theorem eq124 (N : ℕ) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∑ j ∈ range (Jblk N ε), exp (-144) * (1 + ε) * N / log (Yj N ε j) ^ 4 ≤
      6 / 5 * exp (-139) * N / (ε * log N ^ 3) := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (126), Section 7: for even `N > exp exp 36`,
`0 < ε < 1/100`, admissible `q₁` and `d < D`, `d ∣ P^(1)(y)`:
`Σ_{j<J} r_d^(j,2) ≤ 8 N^{7/8} / φ(d)`; `(m, d) > 1` forces `p₁ ∣ d`, `d < N^{1/2}` has at most
four prime factors `≥ z`, and each gives at most `(1+ε)N/z` products. -/
theorem eq126 (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) (d : ℕ) (hd : d ∈ Dset N q₁) :
    ∑ j ∈ range (Jblk N ε), |r2 N ε j d| ≤ 8 * (N : ℝ) ^ ((7 : ℝ) / 8) / d.totient := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (125), middle step, Section 7: for `N > exp exp 36`,
`Σ_{d<D, d ∣ P^(1)(y)} 1/φ(d) < log N`, from `Σ_{d ≤ x} μ²(d)/φ(d) ≤ log x + 1.4` and
`D < N^{1/2}`. -/
theorem eq125_phi (N q₁ : ℕ) (hN : exp (exp 36) < N) :
    ∑ d ∈ Dset N q₁, 1 / (d.totient : ℝ) < log N := by
  sorry

/-- LEAF. Unit U-1552. Yamada 2015, (125), last step, Section 7: for `N > exp exp 36`,
`8 N^{7/8} log N < e^{-139} N / log³ N`. -/
theorem eq125_num (N : ℕ) (hN : exp (exp 36) < N) :
    8 * (N : ℝ) ^ ((7 : ℝ) / 8) * log N < exp (-139) * N / log N ^ 3 := by
  sorry

end LeanLab.ChenExplicit.D1552

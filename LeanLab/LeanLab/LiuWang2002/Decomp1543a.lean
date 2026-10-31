/-
Unit U-1543, run 20261026T0808Z-17522, track T1. Decomposition of Proposition 6.1 of
Liu-Wang 2002, Acta Arith. 105, pp. 133-175, the explicit Vinogradov estimate for the
exponential sum over primes, pp. 168-174, the step that bounds `S(α)` on the arcs `M4`.
This file holds the objects of Section 6, the Vaughan split (6.7)-(6.8) p. 168-169, and the
dyadic, Cauchy and counting leaves of Lemma 6.7, (6.10)-(6.12) p. 170-171, (6.20) p. 173 and
the first line of p. 174. Source: papers/P0023.pdf, pages rendered with pdftoppm.
Leaves carry `sorry` and are the open work. Three inputs from other papers, two lemmas of
Wang-Chen 1994 and a Rosser-Schoenfeld 1962 bound, also carry `sorry`; their doc comments
say so. Assemblies have real proofs and are CONDITIONAL ON the leaves; they are here and in
Decomp1543b and Decomp1543c.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuWang2002.Vaughan109
import LeanLab.PNTPort.LargeSieve.Basic

/-! CODEX task181, 2026-10-30. AI wrote the Lean code. Binary Goldbach is open.
All ten original open leaves now have kernel checked proofs with build evidence.
The separately cited wc_lemma2 remains an input. The inner_l_sum estimate and the
new block energy estimate are CONDITIONAL ON an explicitly supplied WCLemma2.
Evidence: build/codex-task181.log. Source twins and instances: STATEMENTS.md. -/

namespace LeanLab.LiuWang2002.U1543

open Real Finset ArithmeticFunction

/-! ### Objects of Section 6 -/

/-- `e(x) = exp(2πix)`, p. 144 above (3.8). -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `‖x‖`, the distance from `x` to the nearest integer, Lemma 6.3 p. 169. -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `min(X, 1/(2‖θ‖))`, read as `X` when `θ` is an integer. -/
noncomputable def minK (X θ : ℝ) : ℝ := if nint θ = 0 then X else min X (1 / (2 * nint θ))

/-- The range `cN < n ≤ N` of (6.8) p. 169. -/
noncomputable def rangeN (c : ℝ) (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => c * N < n)

/-- (6.8) p. 169: `∑_{cN<n≤N} f(n) e(αn)`. With `f = Λ` this is `S(α)` of Proposition 6.1;
the paper's (3.8) also counts the endpoint `n = cN`, which changes `S` by at most `log N`. -/
noncomputable def Ssum (f : ℕ → ℝ) (c : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ rangeN c N, (f n : ℂ) * e (α * n)

/-- `Λ1` of (6.8): `Λ(n)` for `n ≤ U`, else `0`. -/
noncomputable def lam1 (U : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ U then vonMangoldt n else 0

/-- `Λ2` of (6.8): `∑_{mt=n, t≤V} μ(t) log m`. -/
noncomputable def lam2 (V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ)

/-- `Λ3` of (6.8): `-∑_{rt | n, r≤U, t≤V} Λ(r) μ(t)`. -/
noncomputable def lam3 (U V : ℝ) (n : ℕ) : ℝ :=
  -∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
    if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n then vonMangoldt r * (moebius t : ℝ) else 0

/-- `a_m = ∑_{r | m, r > U} Λ(r)`, (6.10) p. 170. -/
noncomputable def am (U : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ m.divisors.filter (fun r : ℕ => U < (r : ℝ)), vonMangoldt r

/-- `Λ4` of (6.8): `∑_{mt=n, t>V} μ(t) a_m`. -/
noncomputable def lam4 (U V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => V < (t : ℝ)), (moebius t : ℝ) * am U (n / t)

/-- `U = N^(2/5) log^(-4/5) N`, (6.6) p. 168. -/
noncomputable def Uf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ (-(4 : ℝ) / 5)

/-- `V = N^(2/5) log^(1/5) N`, (6.6) p. 168. -/
noncomputable def Vf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ ((1 : ℝ) / 5)

/-- (6.1) p. 168: `α = a/q + θ/q^2` with `q ≥ 1`, `(a, q) = 1`, `|θ| ≤ 1`. -/
def Dioph (α : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2

/-- The dyadic block `M < t ≤ 2M`, cut to `[1, N]`, of (6.11) p. 170. -/
noncomputable def tBlock (N : ℕ) (M : ℝ) : Finset ℕ := (Icc 1 N).filter (fun t => M < t ∧ (t : ℝ) ≤ 2 * M)

/-- The inner range `cN/t < m ≤ N/t, m > U` of (6.11). -/
noncomputable def mRange (c : ℝ) (N : ℕ) (U : ℝ) (t : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun m => c * N < ((m * t : ℕ) : ℝ) ∧ m * t ≤ N ∧ U < m)

/-- The inner sum `∑_{cN/t<m≤N/t, m>U} a_m e(αmt)` of (6.11). -/
noncomputable def inner (c : ℝ) (N : ℕ) (U α : ℝ) (t : ℕ) : ℂ :=
  ∑ m ∈ mRange c N U t, (am U m : ℂ) * e (α * ((m * t : ℕ) : ℝ))

/-- One dyadic block of `S4`, `∑_{M<t≤2M} μ(t) ∑_m a_m e(αmt)`, (6.11). -/
noncomputable def block (c : ℝ) (N : ℕ) (U M α : ℝ) : ℂ :=
  ∑ t ∈ tBlock N M, (moebius t : ℂ) * inner c N U α t

/-- `J = [log(N/(UV))/log 2] + 1`, (6.10) p. 170. -/
noncomputable def Jn (N : ℕ) (U V : ℝ) : ℕ := ⌊Real.log (N / (U * V)) / Real.log 2⌋₊ + 1

/-- The range `U < m ≤ X` in `[1, N]`, used in (6.12) with `X = N/M_j`. -/
noncomputable def lRange (N : ℕ) (U X : ℝ) : Finset ℕ := (Icc 1 N).filter (fun m => U < m ∧ (m : ℝ) ≤ X)

/-! ### Inputs from other papers -/

/-- Lemma 6.3 p. 169, the statement of Wang-Chen 1994, Lemma 2. -/
def WCLemma2 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → ∀ X : ℝ, 0 < X → ∀ (Y : ℕ) (Z : ℤ), 1 ≤ Y →
    ∑ n ∈ Ioc Z (Z + Y), minK X (α * n) ≤ (((Y / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q)

/-- CITED, not proved in the lab: Lemma 6.3 p. 169 is [WC, Lemma 2], Wang-Chen, Acta Math.
Sinica 37 (1994). The paper says `‖x‖` is the fractional part; we read the distance to the
nearest integer, which gives the weaker statement and is what the proof of Lemma 6.7 uses. -/
theorem wc_lemma2 : WCLemma2 := by sorry

/-! ### Leaves -/

/-- LEAF. Unit U-1543. The Vaughan identity (6.7), coefficientwise: for `V ≥ 1` and `n ≥ 1`,
`Λ(n) = Λ1(n) + Λ2(n) + Λ3(n) + Λ4(n)` with the four functions of (6.8), p. 168-169. It follows
from `Akeno2026.Vaughan86.vaughan_identity` with the roles of `U` and `V` exchanged. -/
theorem vaughan_coeff (U V : ℝ) (hV : 1 ≤ V) (n : ℕ) (hn : 1 ≤ n) :
    (vonMangoldt n : ℝ) = lam1 U n + lam2 V n + lam3 U V n + lam4 U V n := by
  classical
  open LeanLab.LiuWang2002.Vaughan109 in
  open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta in
  have hproof : (vonMangoldt n : ℝ) = lam1 U n + lam2 V n + lam3 U V n + lam4 U V n := by
    classical
    have hl (f : ArithmeticFunction ℝ) (X : ℝ) (k : ℕ) :
        longPart f X k = if X < (k : ℝ) then f k else 0 := by
      change f k - (if (k : ℝ) ≤ X then f k else 0) = _
      split_ifs <;> simp_all <;> linarith
    have h1 : lambda1 U n = lam1 U n := rfl
    have h2 : lambda2 V n = lam2 V n := by
      unfold lambda2 lam2
      rw [mul_apply, Nat.sum_divisorsAntidiagonal
        (fun x y => (shortPart (μ : ArithmeticFunction ℝ) V) x * ArithmeticFunction.log y),
        sum_filter]
      apply sum_congr rfl
      intro t ht
      simp [shortPart, ite_mul]
    have h4 : lambda4 U V n = lam4 U V n := by
      unfold lambda4 lam4
      rw [mul_apply, Nat.sum_divisorsAntidiagonal
        (fun x y => (longPart (μ : ArithmeticFunction ℝ) V) x *
          (longPart Λ U * (ζ : ArithmeticFunction ℝ)) y), sum_filter]
      apply sum_congr rfl
      intro t ht
      rw [hl, coe_mul_zeta_apply]
      simp only [hl, am, sum_filter]
      split_ifs <;> simp_all
    have h3 : lambda3 U V n = lam3 U V n := by
      unfold lambda3 lam3
      rw [ArithmeticFunction.neg_apply, mul_assoc, mul_apply, Nat.sum_divisorsAntidiagonal
        (fun x y => (shortPart Λ U) x *
          (shortPart (μ : ArithmeticFunction ℝ) V * (ζ : ArithmeticFunction ℝ)) y)]
      congr 1
      apply sum_congr rfl
      intro r hr
      rw [coe_mul_zeta_apply, mul_sum]
      have hrn := Nat.dvd_of_mem_divisors hr
      have hn0 := Nat.ne_zero_of_mem_divisors hr
      have hr0 := Nat.pos_of_mem_divisors hr
      have hnr0 : n / r ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hrn) hr0)
      have hset : (n / r).divisors = n.divisors.filter (fun t => r * t ∣ n) := by
        ext t
        simp only [Nat.mem_divisors, mem_filter]
        constructor
        · rintro ⟨ht, _⟩
          have hrt : r * t ∣ n := (Nat.dvd_div_iff_mul_dvd hrn).1 ht
          exact ⟨⟨(dvd_mul_left t r).trans hrt, hn0⟩, hrt⟩
        · rintro ⟨⟨ht, _⟩, hrt⟩
          refine ⟨?_, hnr0⟩
          apply (Nat.dvd_div_iff_mul_dvd hrn).2
          simpa [mul_comm] using hrt
      rw [hset, sum_filter]
      apply sum_congr rfl
      intro t ht
      simp only [shortPart, coe_mk, intCoe_apply]
      split_ifs <;> simp_all
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_coefficients U V)
    simpa only [ArithmeticFunction.add_apply, h1, h2, h3, h4] using h
  exact hproof

/-- LEAF. Unit U-1543. Cauchy's inequality for one dyadic block, (6.11) p. 170:
`|∑_t μ(t) z_t| ≤ (∑_t |μ(t)|)^(1/2) (∑_t |z_t|^2)^(1/2)`, using `μ(t)^2 = |μ(t)|`. -/
theorem block_cauchy (T : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ t ∈ T, (moebius t : ℂ) * z t‖ ≤
      √(∑ t ∈ T, |(moebius t : ℝ)|) * √(∑ t ∈ T, ‖z t‖ ^ 2) := by
  calc
    _ ≤ ∑ t ∈ T, |(moebius t : ℝ)| * ‖z t‖ := by
      simpa [norm_mul] using norm_sum_le T (fun t => (moebius t : ℂ) * z t)
    _ ≤ _ := by
      have hsq (t : ℕ) : |(moebius t : ℝ)| ^ 2 = |(moebius t : ℝ)| := by
        rw [sq_abs, ← Int.cast_pow, ← Int.cast_abs, moebius_sq, abs_moebius]
      simpa only [hsq] using Real.sum_mul_le_sqrt_mul_sqrt T
        (fun t => |(moebius t : ℝ)|) (fun t => ‖z t‖)

/-- LEAF. Unit U-1543. The geometric sum over a run of integers inside `(M, 2M]`:
`|∑_{A<t≤B} e(θt)| ≤ min(M + 0.5, 1/(2‖θ‖))`, used for the first display of p. 171.
The run has at most `[2M] - [M] ≤ M + 0.5` terms. -/
theorem geom_dyadic (θ M : ℝ) (hM : 0 ≤ M) (A B : ℤ) (hA : ⌊M⌋ ≤ A) (hB : B ≤ ⌊2 * M⌋) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ := by
  classical
  have heq (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hnorm (x : ℝ) : ‖e x‖ = 1 := by rw [heq, LeanLab.PNTPort.LargeSieve.norm_e]
  have hmin : 0 ≤ minK (M + 1 / 2) θ := by
    unfold minK nint
    split_ifs
    · linarith
    · exact le_min (by linarith) (by positivity)
  by_cases hab : A ≤ B
  · have hfloor : ((⌊2 * M⌋ - ⌊M⌋ : ℤ) : ℝ) ≤ M + 1 / 2 := by
      have hm := Int.floor_le M
      have hm' := Int.lt_floor_add_one M
      have h2m := Int.floor_le (2 * M)
      have htwo : ⌊2 * M⌋ ≤ 2 * ⌊M⌋ + 1 := by
        have hlt : (⌊2 * M⌋ : ℝ) < ((2 * ⌊M⌋ + 2 : ℤ) : ℝ) := by
          push_cast
          linarith
        have : ⌊2 * M⌋ < 2 * ⌊M⌋ + 2 := by exact_mod_cast hlt
        omega
      by_cases hh : ⌊2 * M⌋ ≤ 2 * ⌊M⌋
      · have hh' : (⌊2 * M⌋ : ℝ) ≤ 2 * ⌊M⌋ := by exact_mod_cast hh
        push_cast
        linarith
      · have hh' : ⌊2 * M⌋ = 2 * ⌊M⌋ + 1 := by omega
        rw [hh'] at h2m ⊢
        push_cast at h2m ⊢
        linarith
    have hcard : (((Ioc A B).card : ℕ) : ℝ) ≤ M + 1 / 2 := by
      rw [Int.card_Ioc]
      have he : ((B - A).toNat : ℤ) = B - A := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
      have he' : (((B - A).toNat : ℕ) : ℝ) = (B : ℝ) - A := by exact_mod_cast he
      rw [he']
      have ha' : (⌊M⌋ : ℝ) ≤ A := by exact_mod_cast hA
      have hb' : (B : ℝ) ≤ ⌊2 * M⌋ := by exact_mod_cast hB
      push_cast at hfloor
      linarith
    have htriv : ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ M + 1 / 2 := by
      calc
        _ ≤ ∑ t ∈ Ioc A B, ‖e (θ * t)‖ := norm_sum_le _ _
        _ = ((Ioc A B).card : ℝ) := by simp only [hnorm, sum_const, nsmul_eq_mul, mul_one]
        _ ≤ _ := hcard
    unfold minK
    split_ifs with hθ
    · exact htriv
    · apply le_min htriv
      have hdist : 0 < LeanLab.PNTPort.LargeSieve.dist0 θ :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hθ)
      have himage : Ioc A B = (range (B - A).toNat).image (fun j : ℕ => A + 1 + j) := by
        ext t
        simp only [mem_Ioc, mem_image, mem_range]
        constructor
        · rintro ⟨htA, htB⟩
          exact ⟨(t - A - 1).toNat, by omega, by omega⟩
        · rintro ⟨j, hj, rfl⟩
          omega
      have hk : (∑ t ∈ Ioc A B, LeanLab.PNTPort.LargeSieve.e (θ * t)) =
          LeanLab.PNTPort.LargeSieve.e (θ * (A + 1)) *
            ∑ j ∈ range (B - A).toNat, LeanLab.PNTPort.LargeSieve.e (θ * j) := by
        rw [himage, sum_image, mul_sum]
        · apply sum_congr rfl
          intro j hj
          rw [← LeanLab.PNTPort.LargeSieve.e_add]
          congr 1
          push_cast
          ring
        · intro i hi j hj hij
          change A + 1 + (i : ℤ) = A + 1 + (j : ℤ) at hij
          omega
      simp_rw [heq]
      rw [hk, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
      simpa only [mul_comm, LeanLab.PNTPort.LargeSieve.dist0, nint] using
        LeanLab.PNTPort.LargeSieve.norm_geom_le (B - A).toNat hdist
  · rw [Ioc_eq_empty_of_le (by omega : B ≤ A), sum_empty, norm_zero]
    exact hmin

/-- Finite symmetric Gram matrix estimate for the square expansion on page 171. -/
theorem task181_schur_energy (S T : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℕ → ℂ) (K : ℕ → ℕ → ℝ)
    (ha : ∀ m ∈ S, 0 ≤ a m) (hK : ∀ m ∈ S, ∀ l ∈ S, 0 ≤ K m l)
    (hsym : ∀ m ∈ S, ∀ l ∈ S, K m l = K l m)
    (hgram : ∀ m ∈ S, ∀ l ∈ S,
      ‖∑ t ∈ T, z t m * starRingEnd ℂ (z t l)‖ ≤ K m l) :
    ∑ t ∈ T, ‖∑ m ∈ S, (a m : ℂ) * z t m‖ ^ 2 ≤
      ∑ m ∈ S, a m ^ 2 * ∑ l ∈ S, K m l := by
  have he :
      (∑ t ∈ T, (∑ m ∈ S, (a m : ℂ) * z t m) *
        starRingEnd ℂ (∑ l ∈ S, (a l : ℂ) * z t l)) =
      ∑ m ∈ S, ∑ l ∈ S, ((a m * a l : ℝ) : ℂ) *
        ∑ t ∈ T, z t m * starRingEnd ℂ (z t l) := by
    calc
      _ = ∑ t ∈ T, ∑ m ∈ S, ∑ l ∈ S,
          ((a m * a l : ℝ) : ℂ) * (z t m * starRingEnd ℂ (z t l)) := by
        apply sum_congr rfl
        intro t ht
        rw [map_sum, sum_mul]
        apply sum_congr rfl
        intro m hm
        rw [mul_sum]
        apply sum_congr rfl
        intro l hl
        simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
        ring
      _ = ∑ m ∈ S, ∑ t ∈ T, ∑ l ∈ S,
          ((a m * a l : ℝ) : ℂ) * (z t m * starRingEnd ℂ (z t l)) := sum_comm
      _ = ∑ m ∈ S, ∑ l ∈ S, ∑ t ∈ T,
          ((a m * a l : ℝ) : ℂ) * (z t m * starRingEnd ℂ (z t l)) := by
        apply sum_congr rfl
        intro m hm
        exact sum_comm
      _ = _ := by simp only [mul_sum]
  have henergy : (∑ t ∈ T, ‖∑ m ∈ S, (a m : ℂ) * z t m‖ ^ 2) =
      ∑ m ∈ S, ∑ l ∈ S, a m * a l *
        (∑ t ∈ T, z t m * starRingEnd ℂ (z t l)).re := by
    have hh := congrArg Complex.re he
    simp only [Complex.re_sum] at hh
    simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hh
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hswap : (∑ m ∈ S, ∑ l ∈ S, a l ^ 2 * K m l) =
      ∑ m ∈ S, ∑ l ∈ S, a m ^ 2 * K m l := by
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    rw [hsym l hl m hm]
  calc
    _ = ∑ m ∈ S, ∑ l ∈ S, a m * a l *
        (∑ t ∈ T, z t m * starRingEnd ℂ (z t l)).re := henergy
    _ ≤ ∑ m ∈ S, ∑ l ∈ S, a m * a l * K m l := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hgram m hm l hl))
        (mul_nonneg (ha m hm) (ha l hl))
    _ ≤ ∑ m ∈ S, ∑ l ∈ S, (a m ^ 2 + a l ^ 2) / 2 * K m l := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_right _ (hK m hm l hl)
      nlinarith [sq_nonneg (a m - a l)]
    _ = _ := by
      simp_rw [add_div, add_mul, div_mul_eq_mul_div, sum_add_distrib, ← sum_div]
      rw [hswap]
      simp only [← mul_sum]
      ring

/-- The geometric estimate on a convex natural subinterval of a dyadic block, page 171. -/
theorem task181_geom_convex (M θ : ℝ) (hM : 0 ≤ M) (s : Finset ℕ)
    (hs : ∀ t ∈ s, M < t ∧ (t : ℝ) ≤ 2 * M)
    (hc : ∀ a ∈ s, ∀ b ∈ s, ∀ t : ℕ, a ≤ t → t ≤ b → t ∈ s)
    (hg : ∀ A B : ℤ, ⌊M⌋ ≤ A → B ≤ ⌊2 * M⌋ →
      ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ) :
    ‖∑ t ∈ s, e (θ * t)‖ ≤ minK (M + 1 / 2) θ := by
  classical
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty, norm_zero]
    unfold minK nint
    split_ifs
    · linarith
    · exact le_min (by linarith) (by positivity)
  · let lo := s.min' hne
    let hi := s.max' hne
    have hlo : lo ∈ s := s.min'_mem hne
    have hhi : hi ∈ s := s.max'_mem hne
    have hlo0 : 0 < lo := by
      have hh := (hs lo hlo).1
      have : (0 : ℝ) < lo := hM.trans_lt hh
      exact_mod_cast this
    have he : s = Icc lo hi := by
      ext t
      constructor
      · intro ht
        exact mem_Icc.mpr ⟨s.min'_le t ht, s.le_max' t ht⟩
      · intro ht
        exact hc lo hlo hi hhi t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2
    have hA : ⌊M⌋ ≤ (lo : ℤ) - 1 := by
      have hh : ⌊M⌋ < (lo : ℤ) := Int.floor_lt.mpr (by simpa using (hs lo hlo).1)
      omega
    have hB : (hi : ℤ) ≤ ⌊2 * M⌋ := Int.le_floor.mpr (by simpa using (hs hi hhi).2)
    have hsum : (∑ t ∈ Icc lo hi, e (θ * t)) =
        ∑ t ∈ Ioc ((lo : ℤ) - 1) (hi : ℤ), e (θ * t) := by
      apply sum_bij (fun (t : ℕ) _ => (t : ℤ))
      · intro t ht
        obtain ⟨hl, hh⟩ := mem_Icc.mp ht
        apply mem_Ioc.mpr
        omega
      · intro a ha b hb heq
        exact_mod_cast heq
      · intro t ht
        obtain ⟨hl, hh⟩ := mem_Ioc.mp ht
        have ht0 : 0 ≤ t := by omega
        refine ⟨t.toNat, mem_Icc.mpr ⟨by omega, by omega⟩, Int.toNat_of_nonneg ht0⟩
      · intro t ht
        simp only [Int.cast_natCast]
    rw [he, hsum]
    exact hg _ _ hA hB

/-- LEAF. Unit U-1543. The first display of p. 171: expanding the square in (6.11) and
summing over `t` first,
`∑_{M<t≤2M} |∑_m a_m e(αmt)|^2 ≤ ∑_{U<m≤N/M} a_m^2 ∑_{U<l≤N/M} min(M + 0.5, 1/(2‖α(m-l)‖))`,
given the geometric sum bound `hgeom`, which is `geom_dyadic`. -/
theorem square_expand (c : ℝ) (N : ℕ) (U M α : ℝ) (hU : 0 ≤ U) (hM : 1 ≤ M)
    (hgeom : ∀ θ : ℝ, ∀ A B : ℤ, ⌊M⌋ ≤ A → B ≤ ⌊2 * M⌋ →
      ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ) :
    ∑ t ∈ tBlock N M, ‖inner c N U α t‖ ^ 2 ≤
      ∑ m ∈ lRange N U (N / M), am U m ^ 2 *
        ∑ l ∈ lRange N U (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
  classical
  let S := lRange N U (N / M)
  let T := tBlock N M
  let z (t m : ℕ) : ℂ := if m ∈ mRange c N U t then e (α * ((m * t : ℕ) : ℝ)) else 0
  let K (m l : ℕ) : ℝ := minK (M + 1 / 2) (α * ((m : ℝ) - l))
  have hMpos : 0 < M := by linarith
  have hi (t : ℕ) (ht : t ∈ T) : LeanLab.LiuWang2002.U1543.inner c N U α t =
      ∑ m ∈ S, (am U m : ℂ) * z t m := by
    have htM := (mem_filter.mp ht).2.1
    have hsub : mRange c N U t ⊆ S := by
      intro m hm
      obtain ⟨hmI, hc, hmt, hUm⟩ := mem_filter.mp hm
      refine mem_filter.mpr ⟨hmI, hUm, ?_⟩
      apply (le_div_iff₀ hMpos).2
      have hmt' : (m : ℝ) * t ≤ N := by exact_mod_cast hmt
      have hh := mul_le_mul_of_nonneg_left htM.le (Nat.cast_nonneg m)
      linarith
    calc
      _ = ∑ m ∈ mRange c N U t, (am U m : ℂ) * z t m := by
        apply sum_congr rfl
        intro m hm
        simp only [z, if_pos hm]
      _ = _ := sum_subset hsub (fun m hm hnot => by simp [z, hnot])
  have hnonneg (θ : ℝ) : 0 ≤ minK (M + 1 / 2) θ := by
    unfold minK nint
    split_ifs
    · linarith
    · exact le_min (by linarith) (by positivity)
  have hsym (m l : ℕ) : K m l = K l m := by
    have hn (x : ℝ) : nint (-x) = nint x := LeanLab.PNTPort.LargeSieve.dist0_neg x
    dsimp [K]
    rw [show α * ((m : ℝ) - l) = -(α * ((l : ℝ) - m)) by ring]
    simp only [minK, hn]
  have heq (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hphase (t m l : ℕ) : e (α * ((m * t : ℕ) : ℝ)) *
      starRingEnd ℂ (e (α * ((l * t : ℕ) : ℝ))) = e ((α * ((m : ℝ) - l)) * t) := by
    simp_rw [heq]
    rw [← LeanLab.PNTPort.LargeSieve.e_neg, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    push_cast
    ring
  have hg (m l : ℕ) : ‖∑ t ∈ T, z t m * starRingEnd ℂ (z t l)‖ ≤ K m l := by
    let Q := T.filter (fun t => m ∈ mRange c N U t ∧ l ∈ mRange c N U t)
    have hsum : (∑ t ∈ T, z t m * starRingEnd ℂ (z t l)) =
        ∑ t ∈ Q, e ((α * ((m : ℝ) - l)) * t) := by
      rw [show Q = T.filter (fun t => m ∈ mRange c N U t ∧ l ∈ mRange c N U t) from rfl, sum_filter]
      apply sum_congr rfl
      intro t ht
      dsimp only [z]
      by_cases hm : m ∈ mRange c N U t <;> by_cases hl : l ∈ mRange c N U t <;>
        simp only [hm, hl, ite_true, ite_false, true_and, false_and, and_false,
          _root_.map_zero, mul_zero, zero_mul]
      exact hphase t m l
    rw [hsum]
    apply task181_geom_convex M (α * ((m : ℝ) - l)) hMpos.le Q
    · intro t ht
      exact (mem_filter.mp (mem_filter.mp ht).1).2
    · intro a ha b hb t hat htb
      obtain ⟨haT, ham, hal⟩ := mem_filter.mp ha
      obtain ⟨hbT, hbm, hbl⟩ := mem_filter.mp hb
      obtain ⟨haI, haM, ha2M⟩ := mem_filter.mp haT
      obtain ⟨hbI, hbM, hb2M⟩ := mem_filter.mp hbT
      obtain ⟨ha1, haN⟩ := mem_Icc.mp haI
      obtain ⟨hb1, hbN⟩ := mem_Icc.mp hbI
      obtain ⟨hmI, hcam, hmaN, hUm⟩ := mem_filter.mp ham
      obtain ⟨_, hcbm, hmbN, _⟩ := mem_filter.mp hbm
      obtain ⟨hlI, hcal, hlaN, hUl⟩ := mem_filter.mp hal
      obtain ⟨_, hcbl, hlbN, _⟩ := mem_filter.mp hbl
      have hat' : (a : ℝ) ≤ t := by exact_mod_cast hat
      have htb' : (t : ℝ) ≤ b := by exact_mod_cast htb
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
        haM.trans_le hat', htb'.trans hb2M⟩, ?_, ?_⟩
      · refine mem_filter.mpr ⟨hmI, ?_, (Nat.mul_le_mul_left m htb).trans hmbN, hUm⟩
        have hh : ((m * a : ℕ) : ℝ) ≤ ((m * t : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left m hat
        exact hcam.trans_le hh
      · refine mem_filter.mpr ⟨hlI, ?_, (Nat.mul_le_mul_left l htb).trans hlbN, hUl⟩
        have hh : ((l * a : ℕ) : ℝ) ≤ ((l * t : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left l hat
        exact hcal.trans_le hh
    · exact hgeom _
  calc
    _ = ∑ t ∈ T, ‖∑ m ∈ S, (am U m : ℂ) * z t m‖ ^ 2 := by
      apply sum_congr rfl
      intro t ht
      rw [hi t ht]
    _ ≤ _ := task181_schur_energy S T (am U) z K
      (fun m hm => sum_nonneg fun r hr => vonMangoldt_nonneg)
      (fun m hm l hl => hnonneg _) (fun m hm l hl => hsym m l)
      (fun m hm l hl => hg m l)

/-- LEAF. Unit U-1543. (6.12) p. 171: Lemma 6.3 applied to the sum over `l`, with
`n = m - l` running over `[Y] - [U]` consecutive integers:
`∑_{U<l≤Y} min(X, 1/(2‖α(m-l)‖)) ≤ ([([Y] - [U])/q] + 1)(5X + q log q)`. -/
theorem inner_l_sum (hwc : WCLemma2) (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (N : ℕ)
    (U Y X : ℝ) (hU : 0 ≤ U) (hX : 0 < X) (m : ℕ) :
    ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l)) ≤
      ((((⌊Y⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q) := by
  classical
  have hk (θ : ℝ) : 0 ≤ minK X θ := by
    unfold minK nint
    split_ifs
    · exact hX.le
    · exact le_min hX.le (by positivity)
  have hmem (l : ℕ) (hl : l ∈ lRange N U Y) : ⌊U⌋₊ < l ∧ l ≤ ⌊Y⌋₊ := by
    obtain ⟨_, hlU, hlY⟩ := mem_filter.mp hl
    exact ⟨(Nat.floor_lt hU).2 hlU, Nat.le_floor hlY⟩
  by_cases hlen : 1 ≤ ⌊Y⌋₊ - ⌊U⌋₊
  · have hfloor : ⌊U⌋₊ ≤ ⌊Y⌋₊ := by omega
    let Z : ℤ := (m : ℤ) - ⌊Y⌋₊ - 1
    have hsub :
        ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l)) ≤
          ∑ n ∈ Ioc Z (Z + (⌊Y⌋₊ - ⌊U⌋₊ : ℕ)), minK X (α * n) := by
      apply sum_le_sum_of_injOn (fun l : ℕ => (m : ℤ) - l)
      · intro i hi j hj hij
        change (m : ℤ) - i = (m : ℤ) - j at hij
        omega
      · intro n hn
        obtain ⟨l, hl, rfl⟩ := mem_image.mp hn
        have hh := hmem l hl
        apply mem_Ioc.mpr
        dsimp [Z]
        omega
      · intro l hl
        simp only [Int.cast_sub, Int.cast_natCast]
        exact le_rfl
      · intro n hn hn'
        exact hk _
    exact hsub.trans (hwc α a q hD X hX (⌊Y⌋₊ - ⌊U⌋₊) Z hlen)
  · have hempty : lRange N U Y = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro l hl
      have := hmem l hl
      omega
    rw [hempty, sum_empty]
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast hD.1
    have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
    positivity

/-- Reindexing the fourth Vaughan sum as the bilinear sum of page 170, display 6.11. -/
theorem task181_S4_reindex (c : ℝ) (N : ℕ) (U V α : ℝ) :
    Ssum (lam4 U V) c N α =
      ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => V < (t : ℝ)),
        (moebius t : ℂ) * inner c N U α t := by
  classical
  have hreindex (F : ℕ → ℕ → ℂ) :
      (∑ n ∈ rangeN c N, ∑ t ∈ n.divisors.filter (fun t : ℕ => V < (t : ℝ)), F n t) =
        ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => V < (t : ℝ)),
          ∑ m ∈ (Icc 1 N).filter (fun m : ℕ =>
            c * N < ((m * t : ℕ) : ℝ) ∧ m * t ≤ N), F (m * t) t := by
    rw [sum_sigma', sum_sigma']
    apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
    · intro p hp
      obtain ⟨hn, ht⟩ := mem_sigma.mp hp
      obtain ⟨hnN, hc⟩ := mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnN
      obtain ⟨htd, htV⟩ := mem_filter.mp ht
      have hdiv := Nat.dvd_of_mem_divisors htd
      have ht0 := Nat.pos_of_mem_divisors htd
      have hn0 : 0 < p.1 := by omega
      have hm0 : 1 ≤ p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd hn0 hdiv) ht0
      apply mem_sigma.mpr
      refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ht0, (Nat.divisor_le htd).trans hnN⟩, htV⟩,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0, (Nat.div_le_self _ _).trans hnN⟩, ?_⟩⟩
      simpa only [Nat.div_mul_cancel hdiv] using And.intro hc hnN
    · intro p hp p' hp' he
      have ht : p.2 = p'.2 := congrArg Sigma.fst he
      have hm : p.1 / p.2 = p'.1 / p'.2 := congrArg (fun x : (_root_.Sigma fun _ : ℕ => ℕ) => x.2) he
      have hd := Nat.dvd_of_mem_divisors (mem_filter.mp (mem_sigma.mp hp).2).1
      have hd' := Nat.dvd_of_mem_divisors (mem_filter.mp (mem_sigma.mp hp').2).1
      have hn : p.1 = p'.1 := by
        calc p.1 = p.1 / p.2 * p.2 := (Nat.div_mul_cancel hd).symm
             _ = p'.1 / p'.2 * p'.2 := by rw [hm, ht]
             _ = p'.1 := Nat.div_mul_cancel hd'
      cases p
      cases p'
      simp_all
    · intro p hp
      obtain ⟨ht, hm⟩ := mem_sigma.mp hp
      obtain ⟨htI, htV⟩ := mem_filter.mp ht
      obtain ⟨ht1, htN⟩ := mem_Icc.mp htI
      obtain ⟨hmI, hc, hprod⟩ := mem_filter.mp hm
      obtain ⟨hm1, hmN⟩ := mem_Icc.mp hmI
      have hn0 : 0 < p.2 * p.1 := Nat.mul_pos hm1 ht1
      refine ⟨⟨p.2 * p.1, p.1⟩, ?_, ?_⟩
      · apply mem_sigma.mpr
        refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0, hprod⟩, hc⟩,
          mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, Nat.ne_of_gt hn0⟩, htV⟩⟩
      · simp only [Nat.mul_div_cancel _ ht1]
    · intro p hp
      have hd := Nat.dvd_of_mem_divisors (mem_filter.mp (mem_sigma.mp hp).2).1
      simp only [Nat.div_mul_cancel hd]
  unfold Ssum lam4
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [hreindex]
  apply sum_congr rfl
  intro t ht
  have ht0 : 0 < t := (mem_Icc.mp (mem_filter.mp ht).1).1
  unfold LeanLab.LiuWang2002.U1543.inner
  rw [mul_sum]
  have hset : mRange c N U t =
      ((Icc 1 N).filter (fun m : ℕ => c * N < ((m * t : ℕ) : ℝ) ∧ m * t ≤ N)).filter
        (fun m : ℕ => U < (m : ℝ)) := by
    ext m
    simp only [mRange, mem_filter, and_assoc]
  rw [hset]
  conv_rhs => rw [sum_filter]
  apply sum_congr rfl
  intro m hm
  rw [Nat.mul_div_cancel m ht0]
  by_cases hu : U < (m : ℝ)
  · rw [if_pos hu]
    push_cast
    ring
  · rw [if_neg hu]
    have ham : am U m = 0 := by
      unfold am
      apply sum_eq_zero
      intro r hr
      obtain ⟨hrd, hUr⟩ := mem_filter.mp hr
      have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le hrd
      linarith
    rw [ham]
    simp

/-- The finite dyadic partition of the t interval in page 170, display 6.10. -/
theorem task181_dyadic_partition (N : ℕ) (V : ℝ) (hV : 0 < V) (J : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ range J, ∑ t ∈ tBlock N (2 ^ j * V), f t) =
      ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => V < t ∧ (t : ℝ) ≤ 2 ^ J * V), f t := by
  classical
  induction J with
  | zero =>
    simp only [range_zero, sum_empty, pow_zero, one_mul]
    symm
    apply sum_eq_zero
    intro t ht
    obtain ⟨_, hlt, hle⟩ := mem_filter.mp ht
    linarith
  | succ J ih =>
    rw [sum_range_succ, ih]
    simp only [tBlock, sum_filter, pow_succ,
      show (2 : ℝ) ^ J * 2 * V = 2 * (2 ^ J * V) by ring]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    have hVJ : V ≤ (2 : ℝ) ^ J * V := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hV.le
    by_cases h1 : V < (t : ℝ) <;>
      by_cases h2 : (t : ℝ) ≤ (2 : ℝ) ^ J * V <;>
      by_cases h3 : (t : ℝ) ≤ 2 * ((2 : ℝ) ^ J * V) <;>
      simp_all <;> nlinarith

/-- LEAF. Unit U-1543. (6.10)-(6.11) p. 170: substituting `n = mt` in `S4`, dropping the
`m ≤ U` terms, where `a_m = 0`, and cutting `V < t < N/U` into the `J` dyadic blocks
`(2^j V, 2^(j+1) V]`, `0 ≤ j < J`, gives `S4(α) = ∑_j block_j`. -/
theorem S4_dyadic (c : ℝ) (N : ℕ) (U V α : ℝ) (hU : 0 < U) (hV : 0 < V) :
    Ssum (lam4 U V) c N α = ∑ j ∈ range (Jn N U V), block c N U (2 ^ j * V) α := by
  classical
  rw [task181_S4_reindex]
  unfold block
  rw [task181_dyadic_partition N V hV]
  have hpow : (N : ℝ) / (U * V) ≤ (2 : ℝ) ^ Jn N U V := by
    apply Real.le_pow_of_log_le (by norm_num)
    have hh := Nat.lt_floor_add_one (Real.log (N / (U * V)) / Real.log 2)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hh' : Real.log (N / (U * V)) / Real.log 2 < (Jn N U V : ℝ) := by
      simpa only [Jn, Nat.cast_add, Nat.cast_one] using hh
    exact ((div_lt_iff₀ hlog2).1 hh').le
  have hcut : (N : ℝ) ≤ U * ((2 : ℝ) ^ Jn N U V * V) := by
    have hh := (div_le_iff₀ (mul_pos hU hV)).1 hpow
    nlinarith
  simp only [sum_filter]
  apply sum_congr rfl
  intro t ht
  by_cases hVt : V < (t : ℝ)
  · simp only [hVt, true_and, ite_true]
    by_cases htcut : (t : ℝ) ≤ (2 : ℝ) ^ Jn N U V * V
    · rw [if_pos htcut]
    · rw [if_neg htcut]
      have hinner : LeanLab.LiuWang2002.U1543.inner c N U α t = 0 := by
        unfold LeanLab.LiuWang2002.U1543.inner
        apply sum_eq_zero
        intro m hm
        obtain ⟨_, hc, hmt, hUm⟩ := mem_filter.mp hm
        have htpos : 0 < (t : ℝ) := hV.trans hVt
        have hh : U * ((2 : ℝ) ^ Jn N U V * V) < (m : ℝ) * t := by
          exact (mul_lt_mul_of_pos_left (lt_of_not_ge htcut) hU).trans
            (mul_lt_mul_of_pos_right hUm htpos)
        have hmt' : (m : ℝ) * t ≤ N := by exact_mod_cast hmt
        linarith
      rw [hinner, mul_zero]
  · simp only [hVt, false_and, ite_false]

/-- The squarefree indicator identity in page 173, display 6.20. -/
theorem task181_squarefree_indicator (n : ℕ) (hn : 1 ≤ n) :
    |(moebius n : ℤ)| = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d := by
  classical
  obtain ⟨b, a, hb, ha, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have han : a ∣ n := by rw [← he, sq]; exact dvd_mul_of_dvd_left (dvd_mul_right a a) b
  have hsub : a.divisors ⊆ n.divisors.filter (fun d => d ^ 2 ∣ n) := by
    intro d hd
    have hda := Nat.dvd_of_mem_divisors hd
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hda.trans han, by omega⟩, ?_⟩
    rw [← he]
    exact (pow_dvd_pow_of_dvd hda 2).trans (dvd_mul_right _ _)
  have hsum : (∑ d ∈ a.divisors, moebius d) =
      ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d := by
    apply sum_subset hsub
    intro d hd hnot
    by_contra hmu
    have hdsf := moebius_ne_zero_iff_squarefree.mp hmu
    have hsq := (mem_filter.mp hd).2
    rw [← he, sq] at hsq
    have hda2 : d ∣ a * a :=
      hsf.dvd_of_squarefree_of_mul_dvd_mul_left (by simpa only [pow_two] using hsq)
    have hda : d ∣ a := (hdsf.dvd_pow_iff_dvd two_ne_zero).mp (by simpa only [sq] using hda2)
    exact hnot (Nat.mem_divisors.mpr ⟨hda, by omega⟩)
  have hsfiff : Squarefree n ↔ a = 1 := by
    constructor
    · intro h
      have hsq : a * a ∣ n := by rw [← he, sq]; exact dvd_mul_right _ _
      exact Nat.isUnit_iff.mp (h a hsq)
    · intro h
      rw [← he, h]
      simpa using hsf
  have hm := congrArg (fun f : ArithmeticFunction ℤ => f a) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hm
  rw [← hsum, abs_moebius, hm]
  simp only [hsfiff]

/-- Counting multiples in a natural interval for page 173, display 6.20. -/
theorem task181_count_multiples (A B d : ℕ) (hAB : A ≤ B) :
    (((Ioc A B).filter (fun t => d ∣ t)).card : ℝ) = (B / d : ℕ) - (A / d : ℕ) := by
  classical
  have hs : (Ioc A B).filter (fun t => d ∣ t) =
      ((Ioc 0 B).filter (fun t => d ∣ t)) \ ((Ioc 0 A).filter (fun t => d ∣ t)) := by
    ext t
    simp only [mem_filter, mem_Ioc, mem_sdiff]
    omega
  have hsub : (Ioc 0 A).filter (fun t => d ∣ t) ⊆ (Ioc 0 B).filter (fun t => d ∣ t) := by
    intro t ht
    obtain ⟨htI, htd⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp htI).1, (mem_Ioc.mp htI).2.trans hAB⟩, htd⟩
  rw [hs, card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.cast_sub (Nat.div_le_div_right hAB)]

/-- The exact squarefree interval formula used on page 173, display 6.20. -/
theorem task181_squarefree_interval (A B : ℕ) (hAB : A ≤ B) :
    (∑ t ∈ Ioc A B, |(moebius t : ℝ)|) =
      ∑ d ∈ Icc 1 (Nat.sqrt B), (moebius d : ℝ) *
        (((B / d ^ 2 : ℕ) : ℝ) - ((A / d ^ 2 : ℕ) : ℝ)) := by
  classical
  have hid (t : ℕ) (ht : t ∈ Ioc A B) :
      |(moebius t : ℝ)| = ∑ d ∈ Icc 1 (Nat.sqrt B),
        if d ^ 2 ∣ t then (moebius d : ℝ) else 0 := by
    obtain ⟨hAt, htB⟩ := mem_Ioc.mp ht
    have ht0 : 0 < t := by omega
    have hset : t.divisors.filter (fun d => d ^ 2 ∣ t) =
        (Icc 1 (Nat.sqrt B)).filter (fun d => d ^ 2 ∣ t) := by
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, hd2⟩
        refine ⟨⟨Nat.pos_of_mem_divisors hd, Nat.le_sqrt'.mpr ?_⟩, hd2⟩
        exact (Nat.le_of_dvd ht0 hd2).trans htB
      · rintro ⟨⟨hd1, hdB⟩, hd2⟩
        refine ⟨Nat.mem_divisors.mpr ⟨?_, by omega⟩, hd2⟩
        exact (dvd_mul_right d d).trans (by simpa only [pow_two] using hd2)
    have hh := task181_squarefree_indicator t ht0
    rw [hset, sum_filter] at hh
    exact_mod_cast hh
  calc
    _ = ∑ t ∈ Ioc A B, ∑ d ∈ Icc 1 (Nat.sqrt B),
        if d ^ 2 ∣ t then (moebius d : ℝ) else 0 := sum_congr rfl hid
    _ = ∑ d ∈ Icc 1 (Nat.sqrt B), ∑ t ∈ Ioc A B,
        if d ^ 2 ∣ t then (moebius d : ℝ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, sum_const, nsmul_eq_mul, task181_count_multiples A B (d ^ 2) hAB]
      ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A finite Mobius density bound used to verify the constant in page 173, display 6.20. -/
theorem task181_moebius_density (K : ℕ) (hK : 960 ≤ K) :
    (∑ d ∈ Icc 1 K, (moebius d : ℝ) / (d : ℝ) ^ 2) ≤ 0.609 := by
  classical
  have hcert : (∑ d ∈ Icc 1 960, (moebius d : ℝ) / (d : ℝ) ^ 2) ≤ 0.60795 := by
    have h : (∑ d ∈ Icc 1 960, (moebius d : ℚ) / (d : ℚ) ^ 2) ≤ 60795 / 100000 := by
      decide +kernel
    have hh : ((∑ d ∈ Icc 1 960, (moebius d : ℚ) / (d : ℚ) ^ 2) : ℝ) ≤
        ((60795 / 100000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hh
    norm_num only at hh
    convert hh using 1 <;> norm_num
  have hsplit : Icc 1 K = Icc 1 960 ∪ Ioc 960 K := by
    ext d
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 960) (Ioc 960 K) := by
    apply disjoint_left.mpr
    intro d hd hd'
    have := mem_Icc.mp hd
    have := mem_Ioc.mp hd'
    omega
  have htail : (∑ d ∈ Ioc 960 K, (moebius d : ℝ) / (d : ℝ) ^ 2) ≤ 1 / 960 := by
    calc
      _ ≤ ∑ d ∈ Ioc 960 K, 1 / (d : ℝ) ^ 2 := by
        apply sum_le_sum
        intro d hd
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have hh : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
        exact (le_abs_self _).trans hh
      _ = ∑ d ∈ Ioc 960 K, ((d : ℝ) ^ 2)⁻¹ := by simp only [one_div]
      _ ≤ (960 : ℝ)⁻¹ - (K : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (by decide) hK
      _ ≤ _ := by
        have hh : 0 ≤ (K : ℝ)⁻¹ := by positivity
        linarith
  rw [hsplit, sum_union hdisj]
  linarith

/-- The floor error bound for the squarefree count in page 173, display 6.20. -/
theorem task181_squarefree_floor_error (M : ℝ) (hM : 0 ≤ M) :
    (∑ t ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |(moebius t : ℝ)|) ≤
      M * (∑ d ∈ Icc 1 (Nat.sqrt ⌊2 * M⌋₊), (moebius d : ℝ) / (d : ℝ) ^ 2) +
        Nat.sqrt ⌊2 * M⌋₊ := by
  have hAB : ⌊M⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_mono (by linarith)
  rw [task181_squarefree_interval _ _ hAB]
  calc
    _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt ⌊2 * M⌋₊), (M * ((moebius d : ℝ) / (d : ℝ) ^ 2) + 1) := by
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < d := (mem_Icc.mp hd).1
      have hdp : 0 < (d : ℝ) ^ 2 := by positivity
      have hM0 : 0 ≤ M / (d : ℝ) ^ 2 := div_nonneg hM hdp.le
      have h2M0 : 0 ≤ 2 * M / (d : ℝ) ^ 2 := by positivity
      have hdiff : |(((⌊2 * M⌋₊ / d ^ 2 : ℕ) : ℝ) -
          ((⌊M⌋₊ / d ^ 2 : ℕ) : ℝ)) - M / (d : ℝ) ^ 2| ≤ 1 := by
        rw [← Nat.floor_div_natCast (2 * M), ← Nat.floor_div_natCast M]
        simp only [Nat.cast_pow]
        have hf1 := Nat.floor_le hM0
        have hf2 := Nat.floor_le h2M0
        have hf1' := Nat.lt_floor_add_one (M / (d : ℝ) ^ 2)
        have hf2' := Nat.lt_floor_add_one (2 * M / (d : ℝ) ^ 2)
        simp only [mul_div_assoc] at hf2 hf2' ⊢
        rw [abs_le]
        constructor <;> linarith
      have hmu : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      have hprod : |(moebius d : ℝ) *
          ((((⌊2 * M⌋₊ / d ^ 2 : ℕ) : ℝ) - ((⌊M⌋₊ / d ^ 2 : ℕ) : ℝ)) - M / (d : ℝ) ^ 2)| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul hmu hdiff (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
      calc
        _ = M * ((moebius d : ℝ) / (d : ℝ) ^ 2) +
            (moebius d : ℝ) * ((((⌊2 * M⌋₊ / d ^ 2 : ℕ) : ℝ) -
              ((⌊M⌋₊ / d ^ 2 : ℕ) : ℝ)) - M / (d : ℝ) ^ 2) := by ring
        _ ≤ _ := by
          have hh := (le_abs_self _).trans hprod
          linarith
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
        Nat.add_sub_cancel]

/-- A derived squarefree count above 460800 that implies page 173, display 6.20. -/
theorem task181_squarefree_large (N : ℕ) (M : ℝ) (hM : 460800 ≤ M) :
    ∑ t ∈ tBlock N M, |(moebius t : ℝ)| ≤ 0.6111 * M := by
  have hM0 : 0 ≤ M := by linarith
  have hK : 960 ≤ Nat.sqrt ⌊2 * M⌋₊ := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_floor
    norm_num
    linarith
  have hKroot : (Nat.sqrt ⌊2 * M⌋₊ : ℝ) ≤ √(2 * M) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).2
    have hh : (Nat.sqrt ⌊2 * M⌋₊ : ℝ) ^ 2 ≤ (⌊2 * M⌋₊ : ℝ) := by
      exact_mod_cast Nat.sqrt_le' ⌊2 * M⌋₊
    exact hh.trans (Nat.floor_le (by positivity))
  have hsqrt : √(2 * M) ≤ 0.0021 * M := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg hM0 (show 0 ≤ (0.0021 : ℝ) ^ 2 * M - 2 by linarith)]
  have hsub : tBlock N M ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ := by
    intro t ht
    obtain ⟨_, htM, ht2M⟩ := mem_filter.mp ht
    exact mem_Ioc.mpr ⟨(Nat.floor_lt hM0).mpr htM, Nat.le_floor ht2M⟩
  calc
    _ ≤ ∑ t ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, |(moebius t : ℝ)| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => abs_nonneg _)
    _ ≤ M * (∑ d ∈ Icc 1 (Nat.sqrt ⌊2 * M⌋₊), (moebius d : ℝ) / (d : ℝ) ^ 2) +
        Nat.sqrt ⌊2 * M⌋₊ := task181_squarefree_floor_error M hM0
    _ ≤ M * 0.609 + √(2 * M) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (task181_moebius_density _ hK) hM0) hKroot
    _ ≤ _ := by linarith

/-- A lower certificate for the printed squarefree threshold on page 173. -/
theorem task181_squarefree_threshold : (460800 : ℝ) ≤ Real.exp 13.066 := by
  calc
    _ ≤ ∑ i ∈ range 22, (13.066 : ℝ) ^ i / (i.factorial : ℝ) := by
      norm_num [sum_range_succ, Nat.factorial]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 22

/-- LEAF. Unit U-1543. (6.20) p. 173: for `M ≥ exp(13.066)`, the squarefree count
`∑_{M<t≤2M} |μ(t)| ≤ 0.6111 M`. -/
theorem squarefree_dyadic (N : ℕ) (M : ℝ) (hM : exp 13.066 ≤ M) :
    ∑ t ∈ tBlock N M, |(moebius t : ℝ)| ≤ 0.6111 * M := by
  exact task181_squarefree_large N M (task181_squarefree_threshold.trans hM)

/-- Displays 6.11 and 6.12 with the Wang and Chen input explicit.
CONDITIONAL ON the supplied WCLemma2. -/
theorem task181_block_energy (hwc : WCLemma2) (c : ℝ) (N : ℕ) (U M α : ℝ) (hU : 0 ≤ U)
    (hM : exp 13.066 ≤ M) (a : ℤ) (q : ℕ) (hD : Dioph α a q) :
    ‖block c N U M α‖ ≤ √(0.6111 * M) *
      √(((((⌊(N : ℝ) / M⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) *
        (5 * (M + 1 / 2) + q * Real.log q) *
          (∑ m ∈ lRange N U (N / M), am U m ^ 2)) := by
  have hM1 : 1 ≤ M := by
    have hh := task181_squarefree_threshold.trans hM
    linarith
  have hX : 0 < M + 1 / 2 := by linarith
  have henergy := square_expand c N U M α hU hM1 (fun θ A B hA hB =>
    geom_dyadic θ M (by linarith) A B hA hB)
  have hrows :
      (∑ m ∈ lRange N U (N / M), am U m ^ 2 *
        ∑ l ∈ lRange N U (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l))) ≤
      ((((⌊(N : ℝ) / M⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) *
        (5 * (M + 1 / 2) + q * Real.log q) *
          (∑ m ∈ lRange N U (N / M), am U m ^ 2) := by
    calc
      _ ≤ ∑ m ∈ lRange N U (N / M), am U m ^ 2 *
          (((((⌊(N : ℝ) / M⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) *
            (5 * (M + 1 / 2) + q * Real.log q)) := by
        apply sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (inner_l_sum hwc α a q hD N U (N / M) (M + 1 / 2) hU hX m) (sq_nonneg _)
      _ = _ := by rw [← sum_mul]; ring
  have hcauchy := block_cauchy (tBlock N M) (LeanLab.LiuWang2002.U1543.inner c N U α)
  calc
    _ ≤ √(∑ t ∈ tBlock N M, |(moebius t : ℝ)|) *
        √(∑ t ∈ tBlock N M, ‖LeanLab.LiuWang2002.U1543.inner c N U α t‖ ^ 2) := hcauchy
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (squarefree_dyadic N M hM))
      (Real.sqrt_le_sqrt (henergy.trans hrows)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- LEAF. Unit U-1543. P. 174, line 1: `∑_{j=1}^J M_j^(1/2) ≤ (2 + √2)(N/U)^(1/2)` with
`M_j = 2^(j-1) V`, given `M_J ≤ N/U`. -/
theorem dyadic_sqrt_sum (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (J : ℕ) (hJ : 1 ≤ J)
    (hJV : 2 ^ (J - 1) * V ≤ N / U) :
    ∑ j ∈ range J, √(2 ^ j * V) ≤ (2 + √2) * √(N / U) := by
  have hs1 : 1 < √(2 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot (j : ℕ) : √((2 : ℝ) ^ j * V) = √(2 : ℝ) ^ j * √V := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, show (2 : ℝ) ^ j * 2 * V = 2 * (2 ^ j * V) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ih, pow_succ]
      ring
  have hp : √(2 : ℝ) ^ J = √(2 : ℝ) ^ (J - 1) * √2 := by
    rw [← pow_succ, Nat.sub_add_cancel hJ]
  have hg := geom_sum_mul (√(2 : ℝ)) J
  have hb : (∑ j ∈ range J, √(2 : ℝ) ^ j) ≤ (2 + √2) * √(2 : ℝ) ^ (J - 1) := by
    rw [hp] at hg
    have hid : ((2 + √(2 : ℝ)) * √(2 : ℝ) ^ (J - 1)) * (√2 - 1) =
        √(2 : ℝ) ^ (J - 1) * √2 := by
      calc
        _ = √(2 : ℝ) ^ (J - 1) * (√(2 : ℝ) ^ 2 + √2 - 2) := by ring
        _ = _ := by rw [hsq]; ring
    nlinarith
  calc
    _ = (∑ j ∈ range J, √(2 : ℝ) ^ j) * √V := by simp_rw [hroot]; rw [Finset.sum_mul]
    _ ≤ (2 + √2) * (√(2 : ℝ) ^ (J - 1) * √V) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg V)
    _ ≤ (2 + √2) * √(N / U) := by
      rw [← hroot]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJV) (by positivity)

/-- LEAF. Unit U-1543. P. 174, line 2: `∑_{j=1}^J M_j^(-1/2) ≤ (2 + √2) V^(-1/2)`. -/
theorem dyadic_invsqrt_sum (V : ℝ) (hV : 0 < V) (J : ℕ) :
    ∑ j ∈ range J, 1 / √(2 ^ j * V) ≤ (2 + √2) / √V := by
  have hs : 0 < √(2 : ℝ) := by positivity
  have hs1 : 1 < √(2 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot (j : ℕ) : √((2 : ℝ) ^ j * V) = √(2 : ℝ) ^ j * √V := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, show (2 : ℝ) ^ j * 2 * V = 2 * (2 ^ j * V) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ih, pow_succ]
      ring
  simp_rw [hroot, one_div, mul_inv]
  rw [← Finset.sum_mul]
  have hg : (∑ j ∈ range J, (1 / √(2 : ℝ)) ^ j) ≤ (1 - 1 / √(2 : ℝ))⁻¹ := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := J)
      (by positivity : 0 ≤ 1 / √(2 : ℝ)) ((div_lt_one hs).2 hs1))
  have hc : (1 - 1 / √(2 : ℝ))⁻¹ = 2 + √2 := by
    have hden : 1 - 1 / √(2 : ℝ) ≠ 0 := by
      have : 1 / √(2 : ℝ) < 1 := (div_lt_one hs).2 hs1
      linarith
    apply inv_eq_of_mul_eq_one_right
    field_simp
    nlinarith
  rw [hc] at hg
  simpa [div_eq_mul_inv, inv_pow] using mul_le_mul_of_nonneg_right hg
    (by positivity : 0 ≤ 1 / √V)

/-- LEAF. Unit U-1543. (6.10) p. 170: with `J = [log(N/(UV))/log 2] + 1` and `UV ≤ N`,
`M_J = 2^(J-1) V ≤ N/U` and `J ≤ 1 + log(N/(UV))/log 2`. -/
theorem J_props (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    2 ^ (Jn N U V - 1) * V ≤ N / U ∧
      (Jn N U V : ℝ) ≤ 1 + Real.log (N / (U * V)) / Real.log 2 := by
  have hprod : 0 < U * V := mul_pos hU hV
  have hx : 1 ≤ (N : ℝ) / (U * V) := (le_div_iff₀ hprod).2 (by simpa using hUV)
  have hxpos : 0 < (N : ℝ) / (U * V) := lt_of_lt_of_le zero_lt_one hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := Nat.floor_le (div_nonneg (Real.log_nonneg hx) hlog2.le)
  constructor
  · simp only [Jn, Nat.add_sub_cancel]
    have hp : (2 : ℝ) ^ ⌊Real.log (N / (U * V)) / Real.log 2⌋₊ ≤ N / (U * V) := by
      apply (Real.pow_le_iff_le_log (by norm_num) hxpos).2
      exact (le_div_iff₀ hlog2).1 hfloor
    calc
      _ ≤ (N / (U * V)) * V := mul_le_mul_of_nonneg_right hp hV.le
      _ = N / U := by field_simp
  · simp only [Jn, Nat.cast_add, Nat.cast_one]
    linarith

/-! ### Assembly -/

/-- (6.7) p. 168: `S = S1 + S2 + S3 + S4`. PROVED, CONDITIONAL ON `vaughan_coeff`. -/
theorem S_split (c : ℝ) (N : ℕ) (U V α : ℝ) (hV : 1 ≤ V) :
    Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
      Ssum (lam1 U) c N α + Ssum (lam2 V) c N α + Ssum (lam3 U V) c N α +
        Ssum (lam4 U V) c N α := by
  unfold Ssum
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
  dsimp only
  rw [vaughan_coeff U V hV n hn1]
  push_cast
  ring

/-- The elementary coefficient bounds for am in page 170, display 6.10. -/
theorem task181_am_bounds (U : ℝ) (m : ℕ) : 0 ≤ am U m ∧ am U m ≤ Real.log m := by
  constructor
  · exact sum_nonneg fun r hr => vonMangoldt_nonneg
  · calc
      _ ≤ ∑ r ∈ m.divisors, (vonMangoldt r : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun r hr hnot => vonMangoldt_nonneg)
      _ = _ := vonMangoldt_sum

/-! ### Vacuity instances -/

/-- Vacuity: `Dioph` holds for `α = 0`, `a = 0`, `q = 1`. PROVED. -/
theorem dioph_inhabited : Dioph 0 0 1 := by
  refine ⟨le_rfl, by decide, ?_⟩
  norm_num

/-- Vacuity: the hypotheses of `WCLemma2` can hold, and its conclusion holds in the case
`q = 1`, `X = 1`, `Y = 1`, `Z = 0`, `α = 0`: `min(1, ...) = 1 ≤ 2 · 5`. PROVED. -/
theorem wcLemma2_instance :
    Dioph 0 0 1 ∧ ∑ n ∈ Ioc (0 : ℤ) (0 + (1 : ℕ)), minK 1 (0 * n) ≤
      ((((1 : ℕ) / 1 : ℕ) : ℝ) + 1) * (5 * 1 + (1 : ℕ) * Real.log (1 : ℕ)) := by
  refine ⟨dioph_inhabited, ?_⟩
  have h : Ioc (0 : ℤ) (0 + (1 : ℕ)) = {1} := by decide
  rw [h, sum_singleton]
  simp [minK, nint]
  norm_num

/-- Nonzero instances of am and the fourth Vaughan sum on pages 169 and 170. -/
theorem task181_nonzero_instances : am 1 2 = Real.log 2 ∧
    LeanLab.LiuWang2002.U1543.inner 0 4 1 0 2 = (Real.log 2 : ℂ) ∧
    Ssum (lam4 1 1) 0 4 0 = -(Real.log 2 : ℂ) ∧ 0 < Real.log (2 : ℝ) := by
  have hI : Icc 1 (4 : ℕ) = {1, 2, 3, 4} := by decide
  have hd1 : (1 : ℕ).divisors = {1} := by decide
  have hd2 : (2 : ℕ).divisors = {1, 2} := by decide
  have hd3 : (3 : ℕ).divisors = {1, 3} := by decide
  have hd4 : (4 : ℕ).divisors = {1, 2, 4} := by decide
  have hv2 : (vonMangoldt 2 : ℝ) = Real.log 2 := vonMangoldt_apply_prime Nat.prime_two
  have hv3 : (vonMangoldt 3 : ℝ) = Real.log 3 := vonMangoldt_apply_prime Nat.prime_three
  have hv4 : (vonMangoldt 4 : ℝ) = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, vonMangoldt_apply_pow (by norm_num), hv2]
  have hmu2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  norm_num [am, LeanLab.LiuWang2002.U1543.inner, mRange, Ssum, rangeN, lam4, hI,
    hd1, hd2, hd3, hd4, e, hv2, hv3, hv4, hmu2, Finset.sum_insert, Finset.sum_singleton,
    Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

end LeanLab.LiuWang2002.U1543
